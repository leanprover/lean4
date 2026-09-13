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
lean_object* l_Lean_Meta_forallMetaTelescopeReducing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_addPPExplicitToExposeDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_mkUnfoldAxiomsNote(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofLazyM(lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "apply"};
static const lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(171, 239, 198, 100, 229, 128, 136, 1)}};
static const lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " is"};
static const lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__5;
static const lean_string_object l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "The full type of "};
static const lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0(lean_object* v___y_203_, lean_object* v_targetType_204_, lean_object* v___y_205_, lean_object* v_term_x3f_206_, lean_object* v_conclusionType_x3f_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Lean_Meta_addPPExplicitToExposeDiff(v___y_203_, v_targetType_204_, v___y_208_, v___y_209_, v___y_210_, v___y_211_);
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v_a_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_255_; 
v_a_214_ = lean_ctor_get(v___x_213_, 0);
v_isSharedCheck_255_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_255_ == 0)
{
v___x_216_ = v___x_213_;
v_isShared_217_ = v_isSharedCheck_255_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_a_214_);
lean_dec(v___x_213_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_255_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v_fst_218_; lean_object* v_snd_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_254_; 
v_fst_218_ = lean_ctor_get(v_a_214_, 0);
v_snd_219_ = lean_ctor_get(v_a_214_, 1);
v_isSharedCheck_254_ = !lean_is_exclusive(v_a_214_);
if (v_isSharedCheck_254_ == 0)
{
v___x_221_ = v_a_214_;
v_isShared_222_ = v_isSharedCheck_254_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_snd_219_);
lean_inc(v_fst_218_);
lean_dec(v_a_214_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_254_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___y_224_; lean_object* v___y_225_; lean_object* v___y_226_; lean_object* v___y_242_; 
if (lean_obj_tag(v_conclusionType_x3f_207_) == 0)
{
lean_object* v___x_252_; 
v___x_252_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__9));
v___y_242_ = v___x_252_;
goto v___jp_241_;
}
else
{
lean_object* v___x_253_; 
v___x_253_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__10));
v___y_242_ = v___x_253_;
goto v___jp_241_;
}
v___jp_223_:
{
lean_object* v___x_228_; 
if (v_isShared_222_ == 0)
{
lean_ctor_set_tag(v___x_221_, 7);
lean_ctor_set(v___x_221_, 1, v___y_226_);
lean_ctor_set(v___x_221_, 0, v___y_224_);
v___x_228_ = v___x_221_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___y_224_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v___y_226_);
v___x_228_ = v_reuseFailAlloc_240_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_238_; 
v___x_229_ = l_Lean_indentExpr(v_fst_218_);
v___x_230_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_228_);
lean_ctor_set(v___x_230_, 1, v___x_229_);
v___x_231_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__1);
v___x_232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_230_);
lean_ctor_set(v___x_232_, 1, v___x_231_);
v___x_233_ = l_Lean_indentExpr(v_snd_219_);
v___x_234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_234_, 0, v___x_232_);
lean_ctor_set(v___x_234_, 1, v___x_233_);
v___x_235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
lean_ctor_set(v___x_235_, 1, v___y_205_);
v___x_236_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
lean_ctor_set(v___x_236_, 1, v___y_225_);
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 0, v___x_236_);
v___x_238_ = v___x_216_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v___x_236_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
v___jp_241_:
{
lean_object* v___x_243_; 
lean_inc(v_snd_219_);
lean_inc(v_fst_218_);
v___x_243_ = l_Lean_Meta_mkUnfoldAxiomsNote(v_fst_218_, v_snd_219_, v___y_208_, v___y_209_, v___y_210_, v___y_211_);
if (lean_obj_tag(v___x_243_) == 0)
{
lean_object* v_a_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v_a_244_ = lean_ctor_get(v___x_243_, 0);
lean_inc(v_a_244_);
lean_dec_ref_known(v___x_243_, 1);
v___x_245_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__3);
lean_inc_ref(v___y_242_);
v___x_246_ = l_Lean_stringToMessageData(v___y_242_);
v___x_247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_245_);
lean_ctor_set(v___x_247_, 1, v___x_246_);
v___x_248_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__5, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__5_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__5);
v___x_249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_247_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
if (lean_obj_tag(v_term_x3f_206_) == 0)
{
lean_object* v___x_250_; 
v___x_250_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8);
v___y_224_ = v___x_249_;
v___y_225_ = v_a_244_;
v___y_226_ = v___x_250_;
goto v___jp_223_;
}
else
{
lean_object* v_val_251_; 
v_val_251_ = lean_ctor_get(v_term_x3f_206_, 0);
lean_inc(v_val_251_);
lean_dec_ref_known(v_term_x3f_206_, 1);
v___y_224_ = v___x_249_;
v___y_225_ = v_a_244_;
v___y_226_ = v_val_251_;
goto v___jp_223_;
}
}
else
{
lean_del_object(v___x_221_);
lean_dec(v_snd_219_);
lean_dec(v_fst_218_);
lean_del_object(v___x_216_);
lean_dec(v_term_x3f_206_);
lean_dec_ref(v___y_205_);
return v___x_243_;
}
}
}
}
}
else
{
lean_object* v_a_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_263_; 
lean_dec(v_term_x3f_206_);
lean_dec_ref(v___y_205_);
v_a_256_ = lean_ctor_get(v___x_213_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_263_ == 0)
{
v___x_258_ = v___x_213_;
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_a_256_);
lean_dec(v___x_213_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_261_; 
if (v_isShared_259_ == 0)
{
v___x_261_ = v___x_258_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_a_256_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___boxed(lean_object* v___y_264_, lean_object* v_targetType_265_, lean_object* v___y_266_, lean_object* v_term_x3f_267_, lean_object* v_conclusionType_x3f_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0(v___y_264_, v_targetType_265_, v___y_266_, v_term_x3f_267_, v_conclusionType_x3f_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_);
lean_dec(v___y_272_);
lean_dec_ref(v___y_271_);
lean_dec(v___y_270_);
lean_dec_ref(v___y_269_);
lean_dec(v_conclusionType_x3f_268_);
return v_res_274_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__3(void){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__2));
v___x_280_ = l_Lean_stringToMessageData(v___x_279_);
return v___x_280_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__5(void){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_282_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__4));
v___x_283_ = l_Lean_stringToMessageData(v___x_282_);
return v___x_283_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__7(void){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__6));
v___x_286_ = l_Lean_stringToMessageData(v___x_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(lean_object* v_mvarId_287_, lean_object* v_eType_288_, lean_object* v_conclusionType_x3f_289_, lean_object* v_targetType_290_, lean_object* v_term_x3f_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_){
_start:
{
lean_object* v___x_297_; lean_object* v___y_299_; lean_object* v___y_300_; lean_object* v___y_310_; lean_object* v___y_311_; lean_object* v___y_312_; lean_object* v___y_320_; 
v___x_297_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1));
if (lean_obj_tag(v_conclusionType_x3f_289_) == 0)
{
lean_inc_ref(v_eType_288_);
v___y_320_ = v_eType_288_;
goto v___jp_319_;
}
else
{
lean_object* v_val_325_; 
v_val_325_ = lean_ctor_get(v_conclusionType_x3f_289_, 0);
lean_inc(v_val_325_);
v___y_320_ = v_val_325_;
goto v___jp_319_;
}
v___jp_298_:
{
lean_object* v___f_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
lean_inc_ref(v_targetType_290_);
v___f_301_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_301_, 0, v___y_299_);
lean_closure_set(v___f_301_, 1, v_targetType_290_);
lean_closure_set(v___f_301_, 2, v___y_300_);
lean_closure_set(v___f_301_, 3, v_term_x3f_291_);
lean_closure_set(v___f_301_, 4, v_conclusionType_x3f_289_);
v___x_302_ = lean_unsigned_to_nat(2u);
v___x_303_ = lean_mk_empty_array_with_capacity(v___x_302_);
v___x_304_ = lean_array_push(v___x_303_, v_eType_288_);
v___x_305_ = lean_array_push(v___x_304_, v_targetType_290_);
v___x_306_ = l_Lean_MessageData_ofLazyM(v___f_301_, v___x_305_);
v___x_307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_307_, 0, v___x_306_);
v___x_308_ = l_Lean_Meta_throwTacticEx___redArg(v___x_297_, v_mvarId_287_, v___x_307_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
return v___x_308_;
}
v___jp_309_:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
lean_inc_ref(v___y_311_);
v___x_313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_313_, 0, v___y_311_);
lean_ctor_set(v___x_313_, 1, v___y_312_);
v___x_314_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__3, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__3);
v___x_315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_315_, 0, v___x_313_);
lean_ctor_set(v___x_315_, 1, v___x_314_);
lean_inc_ref(v_eType_288_);
v___x_316_ = l_Lean_indentExpr(v_eType_288_);
v___x_317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_315_);
lean_ctor_set(v___x_317_, 1, v___x_316_);
v___x_318_ = l_Lean_MessageData_note(v___x_317_);
v___y_299_ = v___y_310_;
v___y_300_ = v___x_318_;
goto v___jp_298_;
}
v___jp_319_:
{
if (lean_obj_tag(v_conclusionType_x3f_289_) == 0)
{
lean_object* v___x_321_; 
v___x_321_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__5, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__5_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__5);
v___y_299_ = v___y_320_;
v___y_300_ = v___x_321_;
goto v___jp_298_;
}
else
{
lean_object* v___x_322_; 
v___x_322_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__7, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__7);
if (lean_obj_tag(v_term_x3f_291_) == 0)
{
lean_object* v___x_323_; 
v___x_323_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8);
v___y_310_ = v___y_320_;
v___y_311_ = v___x_322_;
v___y_312_ = v___x_323_;
goto v___jp_309_;
}
else
{
lean_object* v_val_324_; 
v_val_324_ = lean_ctor_get(v_term_x3f_291_, 0);
lean_inc(v_val_324_);
v___y_310_ = v___y_320_;
v___y_311_ = v___x_322_;
v___y_312_ = v_val_324_;
goto v___jp_309_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___boxed(lean_object* v_mvarId_326_, lean_object* v_eType_327_, lean_object* v_conclusionType_x3f_328_, lean_object* v_targetType_329_, lean_object* v_term_x3f_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(v_mvarId_326_, v_eType_327_, v_conclusionType_x3f_328_, v_targetType_329_, v_term_x3f_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_);
lean_dec(v_a_334_);
lean_dec_ref(v_a_333_);
lean_dec(v_a_332_);
lean_dec_ref(v_a_331_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError(lean_object* v_00_u03b1_337_, lean_object* v_mvarId_338_, lean_object* v_eType_339_, lean_object* v_conclusionType_x3f_340_, lean_object* v_targetType_341_, lean_object* v_term_x3f_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(v_mvarId_338_, v_eType_339_, v_conclusionType_x3f_340_, v_targetType_341_, v_term_x3f_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___boxed(lean_object* v_00_u03b1_349_, lean_object* v_mvarId_350_, lean_object* v_eType_351_, lean_object* v_conclusionType_x3f_352_, lean_object* v_targetType_353_, lean_object* v_term_x3f_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError(v_00_u03b1_349_, v_mvarId_350_, v_eType_351_, v_conclusionType_x3f_352_, v_targetType_353_, v_term_x3f_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_);
lean_dec(v_a_358_);
lean_dec_ref(v_a_357_);
lean_dec(v_a_356_);
lean_dec_ref(v_a_355_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0(lean_object* v_a_361_, lean_object* v_snd_362_, lean_object* v_fst_363_, lean_object* v_____r_364_, uint8_t v_progressAfterEx_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_371_, 0, v_a_361_);
v___x_372_ = lean_box(v_progressAfterEx_365_);
v___x_373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
lean_ctor_set(v___x_373_, 1, v_snd_362_);
v___x_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_374_, 0, v_fst_363_);
lean_ctor_set(v___x_374_, 1, v___x_373_);
v___x_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_371_);
lean_ctor_set(v___x_375_, 1, v___x_374_);
v___x_376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0___boxed(lean_object* v_a_377_, lean_object* v_snd_378_, lean_object* v_fst_379_, lean_object* v_____r_380_, lean_object* v_progressAfterEx_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
uint8_t v_progressAfterEx_boxed_387_; lean_object* v_res_388_; 
v_progressAfterEx_boxed_387_ = lean_unbox(v_progressAfterEx_381_);
v_res_388_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0(v_a_377_, v_snd_378_, v_fst_379_, v_____r_380_, v_progressAfterEx_boxed_387_, v___y_382_, v___y_383_, v___y_384_, v___y_385_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
return v_res_388_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__2(void){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_392_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__1));
v___x_393_ = l_Lean_MessageData_ofFormat(v___x_392_);
return v___x_393_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3(void){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_394_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__2);
v___x_395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0(uint8_t v_allowSynthFailures_396_, lean_object* v_tacticName_397_, lean_object* v_mvarId_398_, lean_object* v_as_399_, size_t v_sz_400_, size_t v_i_401_, lean_object* v_b_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_){
_start:
{
lean_object* v_a_409_; lean_object* v_fst_414_; lean_object* v_fst_415_; lean_object* v_snd_416_; uint8_t v___x_419_; 
v___x_419_ = lean_usize_dec_lt(v_i_401_, v_sz_400_);
if (v___x_419_ == 0)
{
lean_object* v___x_420_; 
lean_dec(v_mvarId_398_);
lean_dec(v_tacticName_397_);
v___x_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_420_, 0, v_b_402_);
return v___x_420_;
}
else
{
lean_object* v_snd_421_; lean_object* v_fst_422_; lean_object* v_fst_423_; lean_object* v_snd_424_; lean_object* v_a_425_; lean_object* v___y_427_; uint8_t v___y_428_; lean_object* v_a_433_; lean_object* v___y_437_; lean_object* v___x_498_; 
v_snd_421_ = lean_ctor_get(v_b_402_, 1);
lean_inc(v_snd_421_);
v_fst_422_ = lean_ctor_get(v_b_402_, 0);
lean_inc(v_fst_422_);
lean_dec_ref(v_b_402_);
v_fst_423_ = lean_ctor_get(v_snd_421_, 0);
lean_inc(v_fst_423_);
v_snd_424_ = lean_ctor_get(v_snd_421_, 1);
lean_inc(v_snd_424_);
lean_dec(v_snd_421_);
v_a_425_ = lean_array_uget_borrowed(v_as_399_, v_i_401_);
lean_inc(v___y_406_);
lean_inc_ref(v___y_405_);
lean_inc(v___y_404_);
lean_inc_ref(v___y_403_);
lean_inc(v_a_425_);
v___x_498_ = lean_infer_type(v_a_425_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v_a_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v_a_499_ = lean_ctor_get(v___x_498_, 0);
lean_inc(v_a_499_);
lean_dec_ref_known(v___x_498_, 1);
v___x_500_ = lean_box(0);
v___x_501_ = l_Lean_Meta_synthInstance(v_a_499_, v___x_500_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v_a_502_; lean_object* v___x_503_; lean_object* v___x_504_; uint8_t v___x_505_; 
v_a_502_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_a_502_);
lean_dec_ref_known(v___x_501_, 1);
v___x_503_ = lean_array_get_size(v_snd_424_);
v___x_504_ = lean_unsigned_to_nat(0u);
v___x_505_ = lean_nat_dec_eq(v___x_503_, v___x_504_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = lean_box(0);
lean_inc(v_snd_424_);
v___x_507_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0(v_a_502_, v_snd_424_, v_fst_422_, v___x_506_, v___x_419_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
v___y_437_ = v___x_507_;
goto v___jp_436_;
}
else
{
lean_object* v___x_508_; uint8_t v___x_509_; lean_object* v___x_510_; 
v___x_508_ = lean_box(0);
v___x_509_ = lean_unbox(v_fst_423_);
lean_inc(v_snd_424_);
v___x_510_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0(v_a_502_, v_snd_424_, v_fst_422_, v___x_508_, v___x_509_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
v___y_437_ = v___x_510_;
goto v___jp_436_;
}
}
else
{
lean_object* v_a_511_; 
lean_dec(v_fst_422_);
v_a_511_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_a_511_);
lean_dec_ref_known(v___x_501_, 1);
v_a_433_ = v_a_511_;
goto v___jp_432_;
}
}
else
{
lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_519_; 
lean_dec(v_snd_424_);
lean_dec(v_fst_423_);
lean_dec(v_fst_422_);
lean_dec(v_mvarId_398_);
lean_dec(v_tacticName_397_);
v_a_512_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_519_ == 0)
{
v___x_514_ = v___x_498_;
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_dec(v___x_498_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_519_;
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
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_a_512_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
v___jp_426_:
{
if (v___y_428_ == 0)
{
lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_429_, 0, v___y_427_);
lean_inc(v_a_425_);
v___x_430_ = lean_array_push(v_snd_424_, v_a_425_);
v_fst_414_ = v___x_429_;
v_fst_415_ = v_fst_423_;
v_snd_416_ = v___x_430_;
goto v___jp_413_;
}
else
{
lean_object* v___x_431_; 
lean_dec(v_snd_424_);
lean_dec(v_fst_423_);
lean_dec(v_mvarId_398_);
lean_dec(v_tacticName_397_);
v___x_431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_431_, 0, v___y_427_);
return v___x_431_;
}
}
v___jp_432_:
{
uint8_t v___x_434_; 
v___x_434_ = l_Lean_Exception_isInterrupt(v_a_433_);
if (v___x_434_ == 0)
{
uint8_t v___x_435_; 
lean_inc_ref(v_a_433_);
v___x_435_ = l_Lean_Exception_isRuntime(v_a_433_);
v___y_427_ = v_a_433_;
v___y_428_ = v___x_435_;
goto v___jp_426_;
}
else
{
v___y_427_ = v_a_433_;
v___y_428_ = v___x_434_;
goto v___jp_426_;
}
}
v___jp_436_:
{
if (lean_obj_tag(v___y_437_) == 0)
{
lean_object* v_a_438_; lean_object* v_snd_439_; lean_object* v_snd_440_; lean_object* v_fst_441_; 
lean_dec(v_snd_424_);
lean_dec(v_fst_423_);
v_a_438_ = lean_ctor_get(v___y_437_, 0);
lean_inc(v_a_438_);
lean_dec_ref_known(v___y_437_, 1);
v_snd_439_ = lean_ctor_get(v_a_438_, 1);
lean_inc(v_snd_439_);
v_snd_440_ = lean_ctor_get(v_snd_439_, 1);
lean_inc(v_snd_440_);
v_fst_441_ = lean_ctor_get(v_a_438_, 0);
lean_inc(v_fst_441_);
lean_dec(v_a_438_);
if (lean_obj_tag(v_fst_441_) == 1)
{
lean_object* v_fst_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_492_; 
v_fst_442_ = lean_ctor_get(v_snd_439_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v_snd_439_);
if (v_isSharedCheck_492_ == 0)
{
lean_object* v_unused_493_; 
v_unused_493_ = lean_ctor_get(v_snd_439_, 1);
lean_dec(v_unused_493_);
v___x_444_ = v_snd_439_;
v_isShared_445_ = v_isSharedCheck_492_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_fst_442_);
lean_dec(v_snd_439_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_492_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v_fst_446_; lean_object* v_snd_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_491_; 
v_fst_446_ = lean_ctor_get(v_snd_440_, 0);
v_snd_447_ = lean_ctor_get(v_snd_440_, 1);
v_isSharedCheck_491_ = !lean_is_exclusive(v_snd_440_);
if (v_isSharedCheck_491_ == 0)
{
v___x_449_ = v_snd_440_;
v_isShared_450_ = v_isSharedCheck_491_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_snd_447_);
lean_inc(v_fst_446_);
lean_dec(v_snd_440_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_491_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v_val_451_; lean_object* v___x_452_; 
v_val_451_ = lean_ctor_get(v_fst_441_, 0);
lean_inc(v_val_451_);
lean_dec_ref_known(v_fst_441_, 1);
lean_inc(v_a_425_);
v___x_452_ = l_Lean_Meta_isExprDefEq(v_a_425_, v_val_451_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
if (lean_obj_tag(v___x_452_) == 0)
{
lean_object* v_a_453_; uint8_t v___x_454_; 
v_a_453_ = lean_ctor_get(v___x_452_, 0);
lean_inc(v_a_453_);
lean_dec_ref_known(v___x_452_, 1);
v___x_454_ = lean_unbox(v_a_453_);
lean_dec(v_a_453_);
if (v___x_454_ == 0)
{
if (v_allowSynthFailures_396_ == 0)
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3);
lean_inc(v_mvarId_398_);
lean_inc(v_tacticName_397_);
v___x_456_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_397_, v_mvarId_398_, v___x_455_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v___x_458_; 
lean_dec_ref_known(v___x_456_, 1);
if (v_isShared_450_ == 0)
{
v___x_458_ = v___x_449_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_fst_446_);
lean_ctor_set(v_reuseFailAlloc_462_, 1, v_snd_447_);
v___x_458_ = v_reuseFailAlloc_462_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
lean_object* v___x_460_; 
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 1, v___x_458_);
v___x_460_ = v___x_444_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_fst_442_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v___x_458_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
v_a_409_ = v___x_460_;
goto v___jp_408_;
}
}
}
else
{
lean_object* v_a_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_470_; 
lean_del_object(v___x_449_);
lean_dec(v_snd_447_);
lean_dec(v_fst_446_);
lean_del_object(v___x_444_);
lean_dec(v_fst_442_);
lean_dec(v_mvarId_398_);
lean_dec(v_tacticName_397_);
v_a_463_ = lean_ctor_get(v___x_456_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_470_ == 0)
{
v___x_465_ = v___x_456_;
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_a_463_);
lean_dec(v___x_456_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_468_; 
if (v_isShared_466_ == 0)
{
v___x_468_ = v___x_465_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_a_463_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
}
else
{
lean_object* v___x_472_; 
if (v_isShared_450_ == 0)
{
v___x_472_ = v___x_449_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_fst_446_);
lean_ctor_set(v_reuseFailAlloc_476_, 1, v_snd_447_);
v___x_472_ = v_reuseFailAlloc_476_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
lean_object* v___x_474_; 
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 1, v___x_472_);
v___x_474_ = v___x_444_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_fst_442_);
lean_ctor_set(v_reuseFailAlloc_475_, 1, v___x_472_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
v_a_409_ = v___x_474_;
goto v___jp_408_;
}
}
}
}
else
{
lean_object* v___x_478_; 
if (v_isShared_450_ == 0)
{
v___x_478_ = v___x_449_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_fst_446_);
lean_ctor_set(v_reuseFailAlloc_482_, 1, v_snd_447_);
v___x_478_ = v_reuseFailAlloc_482_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
lean_object* v___x_480_; 
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 1, v___x_478_);
v___x_480_ = v___x_444_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_fst_442_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v___x_478_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
v_a_409_ = v___x_480_;
goto v___jp_408_;
}
}
}
}
else
{
lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_490_; 
lean_del_object(v___x_449_);
lean_dec(v_snd_447_);
lean_dec(v_fst_446_);
lean_del_object(v___x_444_);
lean_dec(v_fst_442_);
lean_dec(v_mvarId_398_);
lean_dec(v_tacticName_397_);
v_a_483_ = lean_ctor_get(v___x_452_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_452_);
if (v_isSharedCheck_490_ == 0)
{
v___x_485_ = v___x_452_;
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v___x_452_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_488_; 
if (v_isShared_486_ == 0)
{
v___x_488_ = v___x_485_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_a_483_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
}
}
}
else
{
lean_object* v_fst_494_; lean_object* v_fst_495_; lean_object* v_snd_496_; 
lean_dec(v_fst_441_);
v_fst_494_ = lean_ctor_get(v_snd_439_, 0);
lean_inc(v_fst_494_);
lean_dec(v_snd_439_);
v_fst_495_ = lean_ctor_get(v_snd_440_, 0);
lean_inc(v_fst_495_);
v_snd_496_ = lean_ctor_get(v_snd_440_, 1);
lean_inc(v_snd_496_);
lean_dec(v_snd_440_);
v_fst_414_ = v_fst_494_;
v_fst_415_ = v_fst_495_;
v_snd_416_ = v_snd_496_;
goto v___jp_413_;
}
}
else
{
lean_object* v_a_497_; 
v_a_497_ = lean_ctor_get(v___y_437_, 0);
lean_inc(v_a_497_);
lean_dec_ref_known(v___y_437_, 1);
v_a_433_ = v_a_497_;
goto v___jp_432_;
}
}
}
v___jp_408_:
{
size_t v___x_410_; size_t v___x_411_; 
v___x_410_ = ((size_t)1ULL);
v___x_411_ = lean_usize_add(v_i_401_, v___x_410_);
v_i_401_ = v___x_411_;
v_b_402_ = v_a_409_;
goto _start;
}
v___jp_413_:
{
lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_417_, 0, v_fst_415_);
lean_ctor_set(v___x_417_, 1, v_snd_416_);
v___x_418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_418_, 0, v_fst_414_);
lean_ctor_set(v___x_418_, 1, v___x_417_);
v_a_409_ = v___x_418_;
goto v___jp_408_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___boxed(lean_object* v_allowSynthFailures_520_, lean_object* v_tacticName_521_, lean_object* v_mvarId_522_, lean_object* v_as_523_, lean_object* v_sz_524_, lean_object* v_i_525_, lean_object* v_b_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
uint8_t v_allowSynthFailures_boxed_532_; size_t v_sz_boxed_533_; size_t v_i_boxed_534_; lean_object* v_res_535_; 
v_allowSynthFailures_boxed_532_ = lean_unbox(v_allowSynthFailures_520_);
v_sz_boxed_533_ = lean_unbox_usize(v_sz_524_);
lean_dec(v_sz_524_);
v_i_boxed_534_ = lean_unbox_usize(v_i_525_);
lean_dec(v_i_525_);
v_res_535_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0(v_allowSynthFailures_boxed_532_, v_tacticName_521_, v_mvarId_522_, v_as_523_, v_sz_boxed_533_, v_i_boxed_534_, v_b_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec_ref(v_as_523_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step(lean_object* v_tacticName_545_, lean_object* v_mvarId_546_, uint8_t v_allowSynthFailures_547_, lean_object* v_mvars_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_){
_start:
{
lean_object* v_postponed_554_; lean_object* v___x_555_; size_t v_sz_556_; size_t v___x_557_; lean_object* v___x_558_; 
v_postponed_554_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0));
v___x_555_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__2));
v_sz_556_ = lean_array_size(v_mvars_548_);
v___x_557_ = ((size_t)0ULL);
v___x_558_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0(v_allowSynthFailures_547_, v_tacticName_545_, v_mvarId_546_, v_mvars_548_, v_sz_556_, v___x_557_, v___x_555_, v_a_549_, v_a_550_, v_a_551_, v_a_552_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v_a_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_581_; 
v_a_559_ = lean_ctor_get(v___x_558_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_581_ == 0)
{
v___x_561_ = v___x_558_;
v_isShared_562_ = v_isSharedCheck_581_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_a_559_);
lean_dec(v___x_558_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_581_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v_fst_563_; 
v_fst_563_ = lean_ctor_get(v_a_559_, 0);
lean_inc(v_fst_563_);
if (lean_obj_tag(v_fst_563_) == 1)
{
lean_object* v_snd_564_; lean_object* v_fst_565_; uint8_t v___x_566_; 
v_snd_564_ = lean_ctor_get(v_a_559_, 1);
lean_inc(v_snd_564_);
lean_dec(v_a_559_);
v_fst_565_ = lean_ctor_get(v_snd_564_, 0);
v___x_566_ = lean_unbox(v_fst_565_);
if (v___x_566_ == 0)
{
lean_dec(v_snd_564_);
if (v_allowSynthFailures_547_ == 0)
{
lean_object* v_val_567_; lean_object* v___x_569_; 
v_val_567_ = lean_ctor_get(v_fst_563_, 0);
lean_inc(v_val_567_);
lean_dec_ref_known(v_fst_563_, 1);
if (v_isShared_562_ == 0)
{
lean_ctor_set_tag(v___x_561_, 1);
lean_ctor_set(v___x_561_, 0, v_val_567_);
v___x_569_ = v___x_561_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_val_567_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
else
{
lean_object* v___x_572_; 
lean_dec_ref_known(v_fst_563_, 1);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 0, v_postponed_554_);
v___x_572_ = v___x_561_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_postponed_554_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
else
{
lean_object* v_snd_574_; lean_object* v___x_576_; 
lean_dec_ref_known(v_fst_563_, 1);
v_snd_574_ = lean_ctor_get(v_snd_564_, 1);
lean_inc(v_snd_574_);
lean_dec(v_snd_564_);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 0, v_snd_574_);
v___x_576_ = v___x_561_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_snd_574_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
else
{
lean_object* v___x_579_; 
lean_dec(v_fst_563_);
lean_dec(v_a_559_);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 0, v_postponed_554_);
v___x_579_ = v___x_561_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_postponed_554_);
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
else
{
lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_589_; 
v_a_582_ = lean_ctor_get(v___x_558_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_589_ == 0)
{
v___x_584_ = v___x_558_;
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v___x_558_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_587_; 
if (v_isShared_585_ == 0)
{
v___x_587_ = v___x_584_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_a_582_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___boxed(lean_object* v_tacticName_590_, lean_object* v_mvarId_591_, lean_object* v_allowSynthFailures_592_, lean_object* v_mvars_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_){
_start:
{
uint8_t v_allowSynthFailures_boxed_599_; lean_object* v_res_600_; 
v_allowSynthFailures_boxed_599_ = lean_unbox(v_allowSynthFailures_592_);
v_res_600_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step(v_tacticName_590_, v_mvarId_591_, v_allowSynthFailures_boxed_599_, v_mvars_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_);
lean_dec(v_a_597_);
lean_dec_ref(v_a_596_);
lean_dec(v_a_595_);
lean_dec_ref(v_a_594_);
lean_dec_ref(v_mvars_593_);
return v_res_600_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_keys_601_, lean_object* v_i_602_, lean_object* v_k_603_){
_start:
{
lean_object* v___x_604_; uint8_t v___x_605_; 
v___x_604_ = lean_array_get_size(v_keys_601_);
v___x_605_ = lean_nat_dec_lt(v_i_602_, v___x_604_);
if (v___x_605_ == 0)
{
lean_dec(v_i_602_);
return v___x_605_;
}
else
{
lean_object* v_k_x27_606_; uint8_t v___x_607_; 
v_k_x27_606_ = lean_array_fget_borrowed(v_keys_601_, v_i_602_);
v___x_607_ = l_Lean_instBEqMVarId_beq(v_k_603_, v_k_x27_606_);
if (v___x_607_ == 0)
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = lean_unsigned_to_nat(1u);
v___x_609_ = lean_nat_add(v_i_602_, v___x_608_);
lean_dec(v_i_602_);
v_i_602_ = v___x_609_;
goto _start;
}
else
{
lean_dec(v_i_602_);
return v___x_605_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_keys_611_, lean_object* v_i_612_, lean_object* v_k_613_){
_start:
{
uint8_t v_res_614_; lean_object* v_r_615_; 
v_res_614_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_611_, v_i_612_, v_k_613_);
lean_dec(v_k_613_);
lean_dec_ref(v_keys_611_);
v_r_615_ = lean_box(v_res_614_);
return v_r_615_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(lean_object* v_x_616_, size_t v_x_617_, lean_object* v_x_618_){
_start:
{
if (lean_obj_tag(v_x_616_) == 0)
{
lean_object* v_es_619_; lean_object* v___x_620_; size_t v___x_621_; size_t v___x_622_; lean_object* v_j_623_; lean_object* v___x_624_; 
v_es_619_ = lean_ctor_get(v_x_616_, 0);
v___x_620_ = lean_box(2);
v___x_621_ = ((size_t)31ULL);
v___x_622_ = lean_usize_land(v_x_617_, v___x_621_);
v_j_623_ = lean_usize_to_nat(v___x_622_);
v___x_624_ = lean_array_get_borrowed(v___x_620_, v_es_619_, v_j_623_);
lean_dec(v_j_623_);
switch(lean_obj_tag(v___x_624_))
{
case 0:
{
lean_object* v_key_625_; uint8_t v___x_626_; 
v_key_625_ = lean_ctor_get(v___x_624_, 0);
v___x_626_ = l_Lean_instBEqMVarId_beq(v_x_618_, v_key_625_);
return v___x_626_;
}
case 1:
{
lean_object* v_node_627_; size_t v___x_628_; size_t v___x_629_; 
v_node_627_ = lean_ctor_get(v___x_624_, 0);
v___x_628_ = ((size_t)5ULL);
v___x_629_ = lean_usize_shift_right(v_x_617_, v___x_628_);
v_x_616_ = v_node_627_;
v_x_617_ = v___x_629_;
goto _start;
}
default: 
{
uint8_t v___x_631_; 
v___x_631_ = 0;
return v___x_631_;
}
}
}
else
{
lean_object* v_ks_632_; lean_object* v___x_633_; uint8_t v___x_634_; 
v_ks_632_ = lean_ctor_get(v_x_616_, 0);
v___x_633_ = lean_unsigned_to_nat(0u);
v___x_634_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(v_ks_632_, v___x_633_, v_x_618_);
return v___x_634_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_635_, lean_object* v_x_636_, lean_object* v_x_637_){
_start:
{
size_t v_x_2812__boxed_638_; uint8_t v_res_639_; lean_object* v_r_640_; 
v_x_2812__boxed_638_ = lean_unbox_usize(v_x_636_);
lean_dec(v_x_636_);
v_res_639_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(v_x_635_, v_x_2812__boxed_638_, v_x_637_);
lean_dec(v_x_637_);
lean_dec_ref(v_x_635_);
v_r_640_ = lean_box(v_res_639_);
return v_r_640_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(lean_object* v_x_641_, lean_object* v_x_642_){
_start:
{
uint64_t v___x_643_; size_t v___x_644_; uint8_t v___x_645_; 
v___x_643_ = l_Lean_instHashableMVarId_hash(v_x_642_);
v___x_644_ = lean_uint64_to_usize(v___x_643_);
v___x_645_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(v_x_641_, v___x_644_, v_x_642_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg___boxed(lean_object* v_x_646_, lean_object* v_x_647_){
_start:
{
uint8_t v_res_648_; lean_object* v_r_649_; 
v_res_648_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(v_x_646_, v_x_647_);
lean_dec(v_x_647_);
lean_dec_ref(v_x_646_);
v_r_649_ = lean_box(v_res_648_);
return v_r_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(lean_object* v_mvarId_650_, lean_object* v___y_651_){
_start:
{
lean_object* v___x_653_; lean_object* v_mctx_654_; lean_object* v_eAssignment_655_; uint8_t v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_653_ = lean_st_ref_get(v___y_651_);
v_mctx_654_ = lean_ctor_get(v___x_653_, 0);
lean_inc_ref(v_mctx_654_);
lean_dec(v___x_653_);
v_eAssignment_655_ = lean_ctor_get(v_mctx_654_, 8);
lean_inc_ref(v_eAssignment_655_);
lean_dec_ref(v_mctx_654_);
v___x_656_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(v_eAssignment_655_, v_mvarId_650_);
lean_dec_ref(v_eAssignment_655_);
v___x_657_ = lean_box(v___x_656_);
v___x_658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_658_, 0, v___x_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg___boxed(lean_object* v_mvarId_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v_mvarId_659_, v___y_660_);
lean_dec(v___y_660_);
lean_dec(v_mvarId_659_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1(uint8_t v_synthAssignedInstances_663_, lean_object* v_as_664_, size_t v_sz_665_, size_t v_i_666_, lean_object* v_b_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_){
_start:
{
lean_object* v_a_674_; uint8_t v___x_678_; 
v___x_678_ = lean_usize_dec_lt(v_i_666_, v_sz_665_);
if (v___x_678_ == 0)
{
lean_object* v___x_679_; 
v___x_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_679_, 0, v_b_667_);
return v___x_679_;
}
else
{
lean_object* v_snd_680_; lean_object* v_fst_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_731_; 
v_snd_680_ = lean_ctor_get(v_b_667_, 1);
v_fst_681_ = lean_ctor_get(v_b_667_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v_b_667_);
if (v_isSharedCheck_731_ == 0)
{
v___x_683_ = v_b_667_;
v_isShared_684_ = v_isSharedCheck_731_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_snd_680_);
lean_inc(v_fst_681_);
lean_dec(v_b_667_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_731_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v_array_685_; lean_object* v_start_686_; lean_object* v_stop_687_; uint8_t v___x_688_; 
v_array_685_ = lean_ctor_get(v_snd_680_, 0);
v_start_686_ = lean_ctor_get(v_snd_680_, 1);
v_stop_687_ = lean_ctor_get(v_snd_680_, 2);
v___x_688_ = lean_nat_dec_lt(v_start_686_, v_stop_687_);
if (v___x_688_ == 0)
{
lean_object* v___x_690_; 
if (v_isShared_684_ == 0)
{
v___x_690_ = v___x_683_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_fst_681_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v_snd_680_);
v___x_690_ = v_reuseFailAlloc_692_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
lean_object* v___x_691_; 
v___x_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_691_, 0, v___x_690_);
return v___x_691_;
}
}
else
{
lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_727_; 
lean_inc(v_stop_687_);
lean_inc(v_start_686_);
lean_inc_ref(v_array_685_);
v_isSharedCheck_727_ = !lean_is_exclusive(v_snd_680_);
if (v_isSharedCheck_727_ == 0)
{
lean_object* v_unused_728_; lean_object* v_unused_729_; lean_object* v_unused_730_; 
v_unused_728_ = lean_ctor_get(v_snd_680_, 2);
lean_dec(v_unused_728_);
v_unused_729_ = lean_ctor_get(v_snd_680_, 1);
lean_dec(v_unused_729_);
v_unused_730_ = lean_ctor_get(v_snd_680_, 0);
lean_dec(v_unused_730_);
v___x_694_ = v_snd_680_;
v_isShared_695_ = v_isSharedCheck_727_;
goto v_resetjp_693_;
}
else
{
lean_dec(v_snd_680_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_727_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_700_; 
v___x_696_ = lean_array_fget(v_array_685_, v_start_686_);
v___x_697_ = lean_unsigned_to_nat(1u);
v___x_698_ = lean_nat_add(v_start_686_, v___x_697_);
lean_dec(v_start_686_);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 1, v___x_698_);
v___x_700_ = v___x_694_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_array_685_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v___x_698_);
lean_ctor_set(v_reuseFailAlloc_726_, 2, v_stop_687_);
v___x_700_ = v_reuseFailAlloc_726_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
uint8_t v___x_701_; uint8_t v___x_702_; 
v___x_701_ = lean_unbox(v___x_696_);
lean_dec(v___x_696_);
v___x_702_ = l_Lean_BinderInfo_isInstImplicit(v___x_701_);
if (v___x_702_ == 0)
{
lean_object* v___x_704_; 
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 1, v___x_700_);
v___x_704_ = v___x_683_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_fst_681_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v___x_700_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
v_a_674_ = v___x_704_;
goto v___jp_673_;
}
}
else
{
lean_object* v_a_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v_a_706_ = lean_array_uget_borrowed(v_as_664_, v_i_666_);
v___x_707_ = l_Lean_Expr_mvarId_x21(v_a_706_);
v___x_708_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v___x_707_, v___y_669_);
lean_dec(v___x_707_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_a_709_; 
v_a_709_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_a_709_);
lean_dec_ref_known(v___x_708_, 1);
if (v_synthAssignedInstances_663_ == 0)
{
uint8_t v___x_717_; 
v___x_717_ = lean_unbox(v_a_709_);
lean_dec(v_a_709_);
if (v___x_717_ == 0)
{
if (v___x_702_ == 0)
{
goto v___jp_710_;
}
else
{
lean_del_object(v___x_683_);
goto v___jp_714_;
}
}
else
{
goto v___jp_710_;
}
}
else
{
lean_dec(v_a_709_);
lean_del_object(v___x_683_);
goto v___jp_714_;
}
v___jp_710_:
{
lean_object* v___x_712_; 
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 1, v___x_700_);
v___x_712_ = v___x_683_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_fst_681_);
lean_ctor_set(v_reuseFailAlloc_713_, 1, v___x_700_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
v_a_674_ = v___x_712_;
goto v___jp_673_;
}
}
v___jp_714_:
{
lean_object* v___x_715_; lean_object* v___x_716_; 
lean_inc(v_a_706_);
v___x_715_ = lean_array_push(v_fst_681_, v_a_706_);
v___x_716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_716_, 0, v___x_715_);
lean_ctor_set(v___x_716_, 1, v___x_700_);
v_a_674_ = v___x_716_;
goto v___jp_673_;
}
}
else
{
lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_725_; 
lean_dec_ref(v___x_700_);
lean_del_object(v___x_683_);
lean_dec(v_fst_681_);
v_a_718_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_725_ == 0)
{
v___x_720_ = v___x_708_;
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_dec(v___x_708_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_723_; 
if (v_isShared_721_ == 0)
{
v___x_723_ = v___x_720_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_a_718_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
}
}
}
}
}
}
v___jp_673_:
{
size_t v___x_675_; size_t v___x_676_; 
v___x_675_ = ((size_t)1ULL);
v___x_676_ = lean_usize_add(v_i_666_, v___x_675_);
v_i_666_ = v___x_676_;
v_b_667_ = v_a_674_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1___boxed(lean_object* v_synthAssignedInstances_732_, lean_object* v_as_733_, lean_object* v_sz_734_, lean_object* v_i_735_, lean_object* v_b_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
uint8_t v_synthAssignedInstances_boxed_742_; size_t v_sz_boxed_743_; size_t v_i_boxed_744_; lean_object* v_res_745_; 
v_synthAssignedInstances_boxed_742_ = lean_unbox(v_synthAssignedInstances_732_);
v_sz_boxed_743_ = lean_unbox_usize(v_sz_734_);
lean_dec(v_sz_734_);
v_i_boxed_744_ = lean_unbox_usize(v_i_735_);
lean_dec(v_i_735_);
v_res_745_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1(v_synthAssignedInstances_boxed_742_, v_as_733_, v_sz_boxed_743_, v_i_boxed_744_, v_b_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec_ref(v_as_733_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg(lean_object* v_tacticName_746_, lean_object* v_mvarId_747_, uint8_t v_allowSynthFailures_748_, lean_object* v_a_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; uint8_t v___x_757_; 
v___x_755_ = lean_array_get_size(v_a_749_);
v___x_756_ = lean_unsigned_to_nat(0u);
v___x_757_ = lean_nat_dec_eq(v___x_755_, v___x_756_);
if (v___x_757_ == 0)
{
lean_object* v___x_758_; 
lean_inc(v_mvarId_747_);
lean_inc(v_tacticName_746_);
v___x_758_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step(v_tacticName_746_, v_mvarId_747_, v_allowSynthFailures_748_, v_a_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
lean_dec_ref(v_a_749_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v_a_759_; 
v_a_759_ = lean_ctor_get(v___x_758_, 0);
lean_inc(v_a_759_);
lean_dec_ref_known(v___x_758_, 1);
v_a_749_ = v_a_759_;
goto _start;
}
else
{
lean_dec(v_mvarId_747_);
lean_dec(v_tacticName_746_);
return v___x_758_;
}
}
else
{
lean_object* v___x_761_; 
lean_dec(v_mvarId_747_);
lean_dec(v_tacticName_746_);
v___x_761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_761_, 0, v_a_749_);
return v___x_761_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg___boxed(lean_object* v_tacticName_762_, lean_object* v_mvarId_763_, lean_object* v_allowSynthFailures_764_, lean_object* v_a_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
uint8_t v_allowSynthFailures_boxed_771_; lean_object* v_res_772_; 
v_allowSynthFailures_boxed_771_ = lean_unbox(v_allowSynthFailures_764_);
v_res_772_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg(v_tacticName_762_, v_mvarId_763_, v_allowSynthFailures_boxed_771_, v_a_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_synthAppInstances(lean_object* v_tacticName_773_, lean_object* v_mvarId_774_, lean_object* v_mvarsNew_775_, lean_object* v_binderInfos_776_, uint8_t v_synthAssignedInstances_777_, uint8_t v_allowSynthFailures_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_){
_start:
{
lean_object* v___x_784_; lean_object* v_todo_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; size_t v_sz_789_; size_t v___x_790_; lean_object* v___x_791_; 
v___x_784_ = lean_unsigned_to_nat(0u);
v_todo_785_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0));
v___x_786_ = lean_array_get_size(v_binderInfos_776_);
v___x_787_ = l_Array_toSubarray___redArg(v_binderInfos_776_, v___x_784_, v___x_786_);
v___x_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_788_, 0, v_todo_785_);
lean_ctor_set(v___x_788_, 1, v___x_787_);
v_sz_789_ = lean_array_size(v_mvarsNew_775_);
v___x_790_ = ((size_t)0ULL);
v___x_791_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1(v_synthAssignedInstances_777_, v_mvarsNew_775_, v_sz_789_, v___x_790_, v___x_788_, v_a_779_, v_a_780_, v_a_781_, v_a_782_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v_a_792_; lean_object* v_fst_793_; lean_object* v___x_794_; 
v_a_792_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_a_792_);
lean_dec_ref_known(v___x_791_, 1);
v_fst_793_ = lean_ctor_get(v_a_792_, 0);
lean_inc(v_fst_793_);
lean_dec(v_a_792_);
v___x_794_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg(v_tacticName_773_, v_mvarId_774_, v_allowSynthFailures_778_, v_fst_793_, v_a_779_, v_a_780_, v_a_781_, v_a_782_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_802_; 
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_802_ == 0)
{
lean_object* v_unused_803_; 
v_unused_803_ = lean_ctor_get(v___x_794_, 0);
lean_dec(v_unused_803_);
v___x_796_ = v___x_794_;
v_isShared_797_ = v_isSharedCheck_802_;
goto v_resetjp_795_;
}
else
{
lean_dec(v___x_794_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_802_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_798_; lean_object* v___x_800_; 
v___x_798_ = lean_box(0);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 0, v___x_798_);
v___x_800_ = v___x_796_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v___x_798_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
else
{
lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_811_; 
v_a_804_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_811_ == 0)
{
v___x_806_ = v___x_794_;
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_dec(v___x_794_);
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
else
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
lean_dec(v_mvarId_774_);
lean_dec(v_tacticName_773_);
v_a_812_ = lean_ctor_get(v___x_791_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_819_ == 0)
{
v___x_814_ = v___x_791_;
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_791_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_synthAppInstances___boxed(lean_object* v_tacticName_820_, lean_object* v_mvarId_821_, lean_object* v_mvarsNew_822_, lean_object* v_binderInfos_823_, lean_object* v_synthAssignedInstances_824_, lean_object* v_allowSynthFailures_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_){
_start:
{
uint8_t v_synthAssignedInstances_boxed_831_; uint8_t v_allowSynthFailures_boxed_832_; lean_object* v_res_833_; 
v_synthAssignedInstances_boxed_831_ = lean_unbox(v_synthAssignedInstances_824_);
v_allowSynthFailures_boxed_832_ = lean_unbox(v_allowSynthFailures_825_);
v_res_833_ = l_Lean_Meta_synthAppInstances(v_tacticName_820_, v_mvarId_821_, v_mvarsNew_822_, v_binderInfos_823_, v_synthAssignedInstances_boxed_831_, v_allowSynthFailures_boxed_832_, v_a_826_, v_a_827_, v_a_828_, v_a_829_);
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
lean_dec(v_a_827_);
lean_dec_ref(v_a_826_);
lean_dec_ref(v_mvarsNew_822_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0(lean_object* v_mvarId_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v_mvarId_834_, v___y_836_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___boxed(lean_object* v_mvarId_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0(v_mvarId_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec(v_mvarId_841_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2(lean_object* v_tacticName_848_, lean_object* v_mvarId_849_, uint8_t v_allowSynthFailures_850_, lean_object* v_inst_851_, lean_object* v_a_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg(v_tacticName_848_, v_mvarId_849_, v_allowSynthFailures_850_, v_a_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___boxed(lean_object* v_tacticName_859_, lean_object* v_mvarId_860_, lean_object* v_allowSynthFailures_861_, lean_object* v_inst_862_, lean_object* v_a_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
uint8_t v_allowSynthFailures_boxed_869_; lean_object* v_res_870_; 
v_allowSynthFailures_boxed_869_ = lean_unbox(v_allowSynthFailures_861_);
v_res_870_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2(v_tacticName_859_, v_mvarId_860_, v_allowSynthFailures_boxed_869_, v_inst_862_, v_a_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
return v_res_870_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0(lean_object* v_00_u03b2_871_, lean_object* v_x_872_, lean_object* v_x_873_){
_start:
{
uint8_t v___x_874_; 
v___x_874_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(v_x_872_, v_x_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___boxed(lean_object* v_00_u03b2_875_, lean_object* v_x_876_, lean_object* v_x_877_){
_start:
{
uint8_t v_res_878_; lean_object* v_r_879_; 
v_res_878_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0(v_00_u03b2_875_, v_x_876_, v_x_877_);
lean_dec(v_x_877_);
lean_dec_ref(v_x_876_);
v_r_879_ = lean_box(v_res_878_);
return v_r_879_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_880_, lean_object* v_x_881_, size_t v_x_882_, lean_object* v_x_883_){
_start:
{
uint8_t v___x_884_; 
v___x_884_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(v_x_881_, v_x_882_, v_x_883_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_885_, lean_object* v_x_886_, lean_object* v_x_887_, lean_object* v_x_888_){
_start:
{
size_t v_x_3146__boxed_889_; uint8_t v_res_890_; lean_object* v_r_891_; 
v_x_3146__boxed_889_ = lean_unbox_usize(v_x_887_);
lean_dec(v_x_887_);
v_res_890_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1(v_00_u03b2_885_, v_x_886_, v_x_3146__boxed_889_, v_x_888_);
lean_dec(v_x_888_);
lean_dec_ref(v_x_886_);
v_r_891_ = lean_box(v_res_890_);
return v_r_891_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_892_, lean_object* v_keys_893_, lean_object* v_vals_894_, lean_object* v_heq_895_, lean_object* v_i_896_, lean_object* v_k_897_){
_start:
{
uint8_t v___x_898_; 
v___x_898_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_893_, v_i_896_, v_k_897_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_899_, lean_object* v_keys_900_, lean_object* v_vals_901_, lean_object* v_heq_902_, lean_object* v_i_903_, lean_object* v_k_904_){
_start:
{
uint8_t v_res_905_; lean_object* v_r_906_; 
v_res_905_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_899_, v_keys_900_, v_vals_901_, v_heq_902_, v_i_903_, v_k_904_);
lean_dec(v_k_904_);
lean_dec_ref(v_vals_901_);
lean_dec_ref(v_keys_900_);
v_r_906_ = lean_box(v_res_905_);
return v_r_906_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(lean_object* v_newMVars_907_, lean_object* v_binderInfos_908_, lean_object* v_a_909_, lean_object* v_n_910_, lean_object* v_i_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
lean_object* v_zero_917_; uint8_t v_isZero_918_; 
v_zero_917_ = lean_unsigned_to_nat(0u);
v_isZero_918_ = lean_nat_dec_eq(v_i_911_, v_zero_917_);
if (v_isZero_918_ == 1)
{
lean_object* v___x_919_; lean_object* v___x_920_; 
lean_dec(v_i_911_);
lean_dec(v_a_909_);
v___x_919_ = lean_box(0);
v___x_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_920_, 0, v___x_919_);
return v___x_920_;
}
else
{
uint8_t v___x_921_; lean_object* v_one_922_; lean_object* v_n_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v_a_929_; uint8_t v___x_930_; 
v___x_921_ = 0;
v_one_922_ = lean_unsigned_to_nat(1u);
v_n_923_ = lean_nat_sub(v_i_911_, v_one_922_);
lean_dec(v_i_911_);
v___x_924_ = lean_nat_sub(v_n_910_, v_n_923_);
v___x_925_ = lean_nat_sub(v___x_924_, v_one_922_);
lean_dec(v___x_924_);
v___x_926_ = lean_array_fget_borrowed(v_newMVars_907_, v___x_925_);
v___x_927_ = l_Lean_Expr_mvarId_x21(v___x_926_);
v___x_928_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v___x_927_, v___y_913_);
v_a_929_ = lean_ctor_get(v___x_928_, 0);
lean_inc(v_a_929_);
lean_dec_ref(v___x_928_);
v___x_930_ = lean_unbox(v_a_929_);
lean_dec(v_a_929_);
if (v___x_930_ == 0)
{
lean_object* v___x_931_; lean_object* v___x_932_; uint8_t v___x_933_; uint8_t v___x_934_; 
v___x_931_ = lean_box(v___x_921_);
v___x_932_ = lean_array_get(v___x_931_, v_binderInfos_908_, v___x_925_);
lean_dec(v___x_925_);
lean_dec(v___x_931_);
v___x_933_ = lean_unbox(v___x_932_);
lean_dec(v___x_932_);
v___x_934_ = l_Lean_BinderInfo_isInstImplicit(v___x_933_);
if (v___x_934_ == 0)
{
lean_object* v___x_935_; 
lean_inc(v___x_927_);
v___x_935_ = l_Lean_MVarId_getTag(v___x_927_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
if (lean_obj_tag(v___x_935_) == 0)
{
lean_object* v_a_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v_a_936_ = lean_ctor_get(v___x_935_, 0);
lean_inc(v_a_936_);
lean_dec_ref_known(v___x_935_, 1);
lean_inc(v_a_909_);
v___x_937_ = l_Lean_Meta_appendTag(v_a_909_, v_a_936_);
lean_dec(v_a_936_);
v___x_938_ = l_Lean_MVarId_setTag___redArg(v___x_927_, v___x_937_, v___y_913_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_dec_ref_known(v___x_938_, 1);
v_i_911_ = v_n_923_;
goto _start;
}
else
{
lean_dec(v_n_923_);
lean_dec(v_a_909_);
return v___x_938_;
}
}
else
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
lean_dec(v___x_927_);
lean_dec(v_n_923_);
lean_dec(v_a_909_);
v_a_940_ = lean_ctor_get(v___x_935_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_935_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_935_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_940_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
else
{
lean_dec(v___x_927_);
v_i_911_ = v_n_923_;
goto _start;
}
}
else
{
lean_dec(v___x_927_);
lean_dec(v___x_925_);
v_i_911_ = v_n_923_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg___boxed(lean_object* v_newMVars_950_, lean_object* v_binderInfos_951_, lean_object* v_a_952_, lean_object* v_n_953_, lean_object* v_i_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(v_newMVars_950_, v_binderInfos_951_, v_a_952_, v_n_953_, v_i_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v_n_953_);
lean_dec_ref(v_binderInfos_951_);
lean_dec_ref(v_newMVars_950_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendParentTag(lean_object* v_mvarId_961_, lean_object* v_newMVars_962_, lean_object* v_binderInfos_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_){
_start:
{
lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_969_ = l_Lean_instInhabitedExpr;
v___x_970_ = l_Lean_MVarId_getTag(v_mvarId_961_, v_a_964_, v_a_965_, v_a_966_, v_a_967_);
if (lean_obj_tag(v___x_970_) == 0)
{
lean_object* v_a_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_988_; 
v_a_971_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_988_ == 0)
{
v___x_973_ = v___x_970_;
v_isShared_974_ = v_isSharedCheck_988_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_a_971_);
lean_dec(v___x_970_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_988_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_975_; lean_object* v___x_976_; uint8_t v___x_977_; 
v___x_975_ = lean_array_get_size(v_newMVars_962_);
v___x_976_ = lean_unsigned_to_nat(1u);
v___x_977_ = lean_nat_dec_eq(v___x_975_, v___x_976_);
if (v___x_977_ == 0)
{
uint8_t v___x_978_; 
v___x_978_ = l_Lean_Name_isAnonymous(v_a_971_);
if (v___x_978_ == 0)
{
lean_object* v___x_979_; 
lean_del_object(v___x_973_);
v___x_979_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(v_newMVars_962_, v_binderInfos_963_, v_a_971_, v___x_975_, v___x_975_, v_a_964_, v_a_965_, v_a_966_, v_a_967_);
return v___x_979_;
}
else
{
lean_object* v___x_980_; lean_object* v___x_982_; 
lean_dec(v_a_971_);
v___x_980_ = lean_box(0);
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 0, v___x_980_);
v___x_982_ = v___x_973_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v___x_980_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
else
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
lean_del_object(v___x_973_);
v___x_984_ = lean_unsigned_to_nat(0u);
v___x_985_ = lean_array_get_borrowed(v___x_969_, v_newMVars_962_, v___x_984_);
v___x_986_ = l_Lean_Expr_mvarId_x21(v___x_985_);
v___x_987_ = l_Lean_MVarId_setTag___redArg(v___x_986_, v_a_971_, v_a_965_);
return v___x_987_;
}
}
}
else
{
lean_object* v_a_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_996_; 
v_a_989_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_996_ == 0)
{
v___x_991_ = v___x_970_;
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_a_989_);
lean_dec(v___x_970_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_994_; 
if (v_isShared_992_ == 0)
{
v___x_994_ = v___x_991_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_a_989_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendParentTag___boxed(lean_object* v_mvarId_997_, lean_object* v_newMVars_998_, lean_object* v_binderInfos_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_Lean_Meta_appendParentTag(v_mvarId_997_, v_newMVars_998_, v_binderInfos_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
lean_dec(v_a_1003_);
lean_dec_ref(v_a_1002_);
lean_dec(v_a_1001_);
lean_dec_ref(v_a_1000_);
lean_dec_ref(v_binderInfos_999_);
lean_dec_ref(v_newMVars_998_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0(lean_object* v_newMVars_1006_, lean_object* v_binderInfos_1007_, lean_object* v_a_1008_, lean_object* v_n_1009_, lean_object* v_i_1010_, lean_object* v_a_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v___x_1017_; 
v___x_1017_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(v_newMVars_1006_, v_binderInfos_1007_, v_a_1008_, v_n_1009_, v_i_1010_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___boxed(lean_object* v_newMVars_1018_, lean_object* v_binderInfos_1019_, lean_object* v_a_1020_, lean_object* v_n_1021_, lean_object* v_i_1022_, lean_object* v_a_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0(v_newMVars_1018_, v_binderInfos_1019_, v_a_1020_, v_n_1021_, v_i_1022_, v_a_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
lean_dec(v_n_1021_);
lean_dec_ref(v_binderInfos_1019_);
lean_dec_ref(v_newMVars_1018_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_postprocessAppMVars(lean_object* v_tacticName_1030_, lean_object* v_mvarId_1031_, lean_object* v_newMVars_1032_, lean_object* v_binderInfos_1033_, uint8_t v_synthAssignedInstances_1034_, uint8_t v_allowSynthFailures_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = l_Lean_Meta_synthAppInstances(v_tacticName_1030_, v_mvarId_1031_, v_newMVars_1032_, v_binderInfos_1033_, v_synthAssignedInstances_1034_, v_allowSynthFailures_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_postprocessAppMVars___boxed(lean_object* v_tacticName_1042_, lean_object* v_mvarId_1043_, lean_object* v_newMVars_1044_, lean_object* v_binderInfos_1045_, lean_object* v_synthAssignedInstances_1046_, lean_object* v_allowSynthFailures_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_){
_start:
{
uint8_t v_synthAssignedInstances_boxed_1053_; uint8_t v_allowSynthFailures_boxed_1054_; lean_object* v_res_1055_; 
v_synthAssignedInstances_boxed_1053_ = lean_unbox(v_synthAssignedInstances_1046_);
v_allowSynthFailures_boxed_1054_ = lean_unbox(v_allowSynthFailures_1047_);
v_res_1055_ = l_Lean_Meta_postprocessAppMVars(v_tacticName_1042_, v_mvarId_1043_, v_newMVars_1044_, v_binderInfos_1045_, v_synthAssignedInstances_boxed_1053_, v_allowSynthFailures_boxed_1054_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_);
lean_dec(v_a_1051_);
lean_dec_ref(v_a_1050_);
lean_dec(v_a_1049_);
lean_dec_ref(v_a_1048_);
lean_dec_ref(v_newMVars_1044_);
return v_res_1055_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0(lean_object* v_mvar_1056_, lean_object* v_mvarId_1057_){
_start:
{
lean_object* v___x_1058_; uint8_t v___x_1059_; 
v___x_1058_ = l_Lean_Expr_mvarId_x21(v_mvar_1056_);
v___x_1059_ = l_Lean_instBEqMVarId_beq(v_mvarId_1057_, v___x_1058_);
lean_dec(v___x_1058_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0___boxed(lean_object* v_mvar_1060_, lean_object* v_mvarId_1061_){
_start:
{
uint8_t v_res_1062_; lean_object* v_r_1063_; 
v_res_1062_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0(v_mvar_1060_, v_mvarId_1061_);
lean_dec(v_mvarId_1061_);
lean_dec_ref(v_mvar_1060_);
v_r_1063_ = lean_box(v_res_1062_);
return v_r_1063_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0(lean_object* v_mvar_1064_, lean_object* v_as_1065_, size_t v_i_1066_, size_t v_stop_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
uint8_t v___x_1077_; 
v___x_1077_ = lean_usize_dec_eq(v_i_1066_, v_stop_1067_);
if (v___x_1077_ == 0)
{
lean_object* v___x_1078_; uint8_t v___x_1079_; 
v___x_1078_ = lean_array_uget_borrowed(v_as_1065_, v_i_1066_);
v___x_1079_ = lean_expr_eqv(v_mvar_1064_, v___x_1078_);
if (v___x_1079_ == 0)
{
lean_object* v___f_1080_; uint8_t v___x_1081_; lean_object* v___x_1082_; 
lean_inc_ref(v_mvar_1064_);
v___f_1080_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1080_, 0, v_mvar_1064_);
v___x_1081_ = 1;
lean_inc(v___y_1071_);
lean_inc_ref(v___y_1070_);
lean_inc(v___y_1069_);
lean_inc_ref(v___y_1068_);
lean_inc(v___x_1078_);
v___x_1082_ = lean_infer_type(v___x_1078_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1097_; 
v_a_1083_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1085_ = v___x_1082_;
v_isShared_1086_ = v_isSharedCheck_1097_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v___x_1082_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1097_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1087_ = lean_box(0);
v___x_1088_ = l_Lean_FindMVar_main(v___f_1080_, v_a_1083_, v___x_1087_);
if (lean_obj_tag(v___x_1088_) == 0)
{
if (v___x_1079_ == 0)
{
lean_del_object(v___x_1085_);
goto v___jp_1073_;
}
else
{
lean_object* v___x_1089_; lean_object* v___x_1091_; 
lean_dec_ref(v_mvar_1064_);
v___x_1089_ = lean_box(v___x_1081_);
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 0, v___x_1089_);
v___x_1091_ = v___x_1085_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1089_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
else
{
lean_object* v___x_1093_; lean_object* v___x_1095_; 
lean_dec_ref_known(v___x_1088_, 1);
lean_dec_ref(v_mvar_1064_);
v___x_1093_ = lean_box(v___x_1081_);
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 0, v___x_1093_);
v___x_1095_ = v___x_1085_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___x_1093_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
else
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1105_; 
lean_dec_ref(v___f_1080_);
lean_dec_ref(v_mvar_1064_);
v_a_1098_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1100_ = v___x_1082_;
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1082_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1103_; 
if (v_isShared_1101_ == 0)
{
v___x_1103_ = v___x_1100_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_a_1098_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
}
else
{
goto v___jp_1073_;
}
}
else
{
uint8_t v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
lean_dec_ref(v_mvar_1064_);
v___x_1106_ = 0;
v___x_1107_ = lean_box(v___x_1106_);
v___x_1108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1107_);
return v___x_1108_;
}
v___jp_1073_:
{
size_t v___x_1074_; size_t v___x_1075_; 
v___x_1074_ = ((size_t)1ULL);
v___x_1075_ = lean_usize_add(v_i_1066_, v___x_1074_);
v_i_1066_ = v___x_1075_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___boxed(lean_object* v_mvar_1109_, lean_object* v_as_1110_, lean_object* v_i_1111_, lean_object* v_stop_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
size_t v_i_boxed_1118_; size_t v_stop_boxed_1119_; lean_object* v_res_1120_; 
v_i_boxed_1118_ = lean_unbox_usize(v_i_1111_);
lean_dec(v_i_1111_);
v_stop_boxed_1119_ = lean_unbox_usize(v_stop_1112_);
lean_dec(v_stop_1112_);
v_res_1120_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0(v_mvar_1109_, v_as_1110_, v_i_boxed_1118_, v_stop_boxed_1119_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
lean_dec(v___y_1114_);
lean_dec_ref(v___y_1113_);
lean_dec_ref(v_as_1110_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(lean_object* v_mvar_1121_, lean_object* v_otherMVars_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; uint8_t v___x_1130_; 
v___x_1128_ = lean_unsigned_to_nat(0u);
v___x_1129_ = lean_array_get_size(v_otherMVars_1122_);
v___x_1130_ = lean_nat_dec_lt(v___x_1128_, v___x_1129_);
if (v___x_1130_ == 0)
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
lean_dec_ref(v_mvar_1121_);
v___x_1131_ = lean_box(v___x_1130_);
v___x_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1131_);
return v___x_1132_;
}
else
{
if (v___x_1130_ == 0)
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
lean_dec_ref(v_mvar_1121_);
v___x_1133_ = lean_box(v___x_1130_);
v___x_1134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1133_);
return v___x_1134_;
}
else
{
size_t v___x_1135_; size_t v___x_1136_; lean_object* v___x_1137_; 
v___x_1135_ = ((size_t)0ULL);
v___x_1136_ = lean_usize_of_nat(v___x_1129_);
v___x_1137_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0(v_mvar_1121_, v_otherMVars_1122_, v___x_1135_, v___x_1136_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_);
return v___x_1137_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___boxed(lean_object* v_mvar_1138_, lean_object* v_otherMVars_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(v_mvar_1138_, v_otherMVars_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_);
lean_dec(v_a_1143_);
lean_dec_ref(v_a_1142_);
lean_dec(v_a_1141_);
lean_dec_ref(v_a_1140_);
lean_dec_ref(v_otherMVars_1139_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(lean_object* v_mvars_1146_, lean_object* v_as_1147_, size_t v_i_1148_, size_t v_stop_1149_, lean_object* v_b_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v_a_1157_; uint8_t v___x_1161_; 
v___x_1161_ = lean_usize_dec_eq(v_i_1148_, v_stop_1149_);
if (v___x_1161_ == 0)
{
lean_object* v_fst_1162_; lean_object* v_snd_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1188_; 
v_fst_1162_ = lean_ctor_get(v_b_1150_, 0);
v_snd_1163_ = lean_ctor_get(v_b_1150_, 1);
v_isSharedCheck_1188_ = !lean_is_exclusive(v_b_1150_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1165_ = v_b_1150_;
v_isShared_1166_ = v_isSharedCheck_1188_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_snd_1163_);
lean_inc(v_fst_1162_);
lean_dec(v_b_1150_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1188_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1167_; lean_object* v_currMVarId_1168_; lean_object* v___x_1169_; 
v___x_1167_ = lean_array_uget_borrowed(v_as_1147_, v_i_1148_);
v_currMVarId_1168_ = l_Lean_Expr_mvarId_x21(v___x_1167_);
lean_inc(v___x_1167_);
v___x_1169_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(v___x_1167_, v_mvars_1146_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
if (lean_obj_tag(v___x_1169_) == 0)
{
lean_object* v_a_1170_; uint8_t v___x_1171_; 
v_a_1170_ = lean_ctor_get(v___x_1169_, 0);
lean_inc(v_a_1170_);
lean_dec_ref_known(v___x_1169_, 1);
v___x_1171_ = lean_unbox(v_a_1170_);
lean_dec(v_a_1170_);
if (v___x_1171_ == 0)
{
lean_object* v___x_1172_; lean_object* v___x_1174_; 
v___x_1172_ = lean_array_push(v_fst_1162_, v_currMVarId_1168_);
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 0, v___x_1172_);
v___x_1174_ = v___x_1165_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v___x_1172_);
lean_ctor_set(v_reuseFailAlloc_1175_, 1, v_snd_1163_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
v_a_1157_ = v___x_1174_;
goto v___jp_1156_;
}
}
else
{
lean_object* v___x_1176_; lean_object* v___x_1178_; 
v___x_1176_ = lean_array_push(v_snd_1163_, v_currMVarId_1168_);
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 1, v___x_1176_);
v___x_1178_ = v___x_1165_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_fst_1162_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v___x_1176_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
v_a_1157_ = v___x_1178_;
goto v___jp_1156_;
}
}
}
else
{
lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1187_; 
lean_dec(v_currMVarId_1168_);
lean_del_object(v___x_1165_);
lean_dec(v_snd_1163_);
lean_dec(v_fst_1162_);
v_a_1180_ = lean_ctor_get(v___x_1169_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1169_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1182_ = v___x_1169_;
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1169_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1185_; 
if (v_isShared_1183_ == 0)
{
v___x_1185_ = v___x_1182_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_a_1180_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
}
else
{
lean_object* v___x_1189_; 
v___x_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1189_, 0, v_b_1150_);
return v___x_1189_;
}
v___jp_1156_:
{
size_t v___x_1158_; size_t v___x_1159_; 
v___x_1158_ = ((size_t)1ULL);
v___x_1159_ = lean_usize_add(v_i_1148_, v___x_1158_);
v_i_1148_ = v___x_1159_;
v_b_1150_ = v_a_1157_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0___boxed(lean_object* v_mvars_1190_, lean_object* v_as_1191_, lean_object* v_i_1192_, lean_object* v_stop_1193_, lean_object* v_b_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
size_t v_i_boxed_1200_; size_t v_stop_boxed_1201_; lean_object* v_res_1202_; 
v_i_boxed_1200_ = lean_unbox_usize(v_i_1192_);
lean_dec(v_i_1192_);
v_stop_boxed_1201_ = lean_unbox_usize(v_stop_1193_);
lean_dec(v_stop_1193_);
v_res_1202_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(v_mvars_1190_, v_as_1191_, v_i_boxed_1200_, v_stop_boxed_1201_, v_b_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec_ref(v_as_1191_);
lean_dec_ref(v_mvars_1190_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(lean_object* v_mvars_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_){
_start:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; uint8_t v___x_1216_; 
v___x_1213_ = lean_unsigned_to_nat(0u);
v___x_1214_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1));
v___x_1215_ = lean_array_get_size(v_mvars_1207_);
v___x_1216_ = lean_nat_dec_lt(v___x_1213_, v___x_1215_);
if (v___x_1216_ == 0)
{
lean_object* v___x_1217_; 
v___x_1217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1214_);
return v___x_1217_;
}
else
{
uint8_t v___x_1218_; 
v___x_1218_ = lean_nat_dec_le(v___x_1215_, v___x_1215_);
if (v___x_1218_ == 0)
{
if (v___x_1216_ == 0)
{
lean_object* v___x_1219_; 
v___x_1219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1214_);
return v___x_1219_;
}
else
{
size_t v___x_1220_; size_t v___x_1221_; lean_object* v___x_1222_; 
v___x_1220_ = ((size_t)0ULL);
v___x_1221_ = lean_usize_of_nat(v___x_1215_);
v___x_1222_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(v_mvars_1207_, v_mvars_1207_, v___x_1220_, v___x_1221_, v___x_1214_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
return v___x_1222_;
}
}
else
{
size_t v___x_1223_; size_t v___x_1224_; lean_object* v___x_1225_; 
v___x_1223_ = ((size_t)0ULL);
v___x_1224_ = lean_usize_of_nat(v___x_1215_);
v___x_1225_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(v_mvars_1207_, v_mvars_1207_, v___x_1223_, v___x_1224_, v___x_1214_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
return v___x_1225_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___boxed(lean_object* v_mvars_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(v_mvars_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_);
lean_dec(v_a_1230_);
lean_dec_ref(v_a_1229_);
lean_dec(v_a_1228_);
lean_dec_ref(v_a_1227_);
lean_dec_ref(v_mvars_1226_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals_spec__0(lean_object* v_a_1233_, lean_object* v_a_1234_){
_start:
{
if (lean_obj_tag(v_a_1233_) == 0)
{
lean_object* v___x_1235_; 
v___x_1235_ = l_List_reverse___redArg(v_a_1234_);
return v___x_1235_;
}
else
{
lean_object* v_head_1236_; lean_object* v_tail_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1246_; 
v_head_1236_ = lean_ctor_get(v_a_1233_, 0);
v_tail_1237_ = lean_ctor_get(v_a_1233_, 1);
v_isSharedCheck_1246_ = !lean_is_exclusive(v_a_1233_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1239_ = v_a_1233_;
v_isShared_1240_ = v_isSharedCheck_1246_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_tail_1237_);
lean_inc(v_head_1236_);
lean_dec(v_a_1233_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1246_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1241_; lean_object* v___x_1243_; 
v___x_1241_ = l_Lean_Expr_mvarId_x21(v_head_1236_);
lean_dec(v_head_1236_);
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 1, v_a_1234_);
lean_ctor_set(v___x_1239_, 0, v___x_1241_);
v___x_1243_ = v___x_1239_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v___x_1241_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v_a_1234_);
v___x_1243_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
v_a_1233_ = v_tail_1237_;
v_a_1234_ = v___x_1243_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(lean_object* v_mvars_1247_, uint8_t v_x_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_){
_start:
{
switch(v_x_1248_)
{
case 0:
{
lean_object* v___x_1254_; 
v___x_1254_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(v_mvars_1247_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_);
lean_dec_ref(v_mvars_1247_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v_a_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1267_; 
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1257_ = v___x_1254_;
v_isShared_1258_ = v_isSharedCheck_1267_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_a_1255_);
lean_dec(v___x_1254_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1267_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v_fst_1259_; lean_object* v_snd_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1265_; 
v_fst_1259_ = lean_ctor_get(v_a_1255_, 0);
lean_inc(v_fst_1259_);
v_snd_1260_ = lean_ctor_get(v_a_1255_, 1);
lean_inc(v_snd_1260_);
lean_dec(v_a_1255_);
v___x_1261_ = lean_array_to_list(v_fst_1259_);
v___x_1262_ = lean_array_to_list(v_snd_1260_);
v___x_1263_ = l_List_appendTR___redArg(v___x_1261_, v___x_1262_);
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 0, v___x_1263_);
v___x_1265_ = v___x_1257_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v___x_1263_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
}
else
{
lean_object* v_a_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1275_; 
v_a_1268_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1270_ = v___x_1254_;
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_a_1268_);
lean_dec(v___x_1254_);
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
case 1:
{
lean_object* v___x_1276_; 
v___x_1276_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(v_mvars_1247_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_);
lean_dec_ref(v_mvars_1247_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1286_; 
v_a_1277_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1279_ = v___x_1276_;
v_isShared_1280_ = v_isSharedCheck_1286_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_dec(v___x_1276_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1286_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v_fst_1281_; lean_object* v___x_1282_; lean_object* v___x_1284_; 
v_fst_1281_ = lean_ctor_get(v_a_1277_, 0);
lean_inc(v_fst_1281_);
lean_dec(v_a_1277_);
v___x_1282_ = lean_array_to_list(v_fst_1281_);
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 0, v___x_1282_);
v___x_1284_ = v___x_1279_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v___x_1282_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
}
}
}
else
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1294_; 
v_a_1287_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1289_ = v___x_1276_;
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1276_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1292_; 
if (v_isShared_1290_ == 0)
{
v___x_1292_ = v___x_1289_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_a_1287_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
}
default: 
{
lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1295_ = lean_array_to_list(v_mvars_1247_);
v___x_1296_ = lean_box(0);
v___x_1297_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals_spec__0(v___x_1295_, v___x_1296_);
v___x_1298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1297_);
return v___x_1298_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals___boxed(lean_object* v_mvars_1299_, lean_object* v_x_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_){
_start:
{
uint8_t v_x_816__boxed_1306_; lean_object* v_res_1307_; 
v_x_816__boxed_1306_ = lean_unbox(v_x_1300_);
v_res_1307_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(v_mvars_1299_, v_x_816__boxed_1306_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
lean_dec(v_a_1304_);
lean_dec_ref(v_a_1303_);
lean_dec(v_a_1302_);
lean_dec_ref(v_a_1301_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(uint8_t v_approx_1308_, lean_object* v_a_1309_, lean_object* v_b_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_){
_start:
{
if (v_approx_1308_ == 0)
{
lean_object* v___x_1316_; 
v___x_1316_ = l_Lean_Meta_isExprDefEqGuarded(v_a_1309_, v_b_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
return v___x_1316_;
}
else
{
lean_object* v___x_1317_; uint8_t v_constApprox_1318_; uint8_t v_isDefEqStuckEx_1319_; uint8_t v_unificationHints_1320_; uint8_t v_proofIrrelevance_1321_; uint8_t v_assignSyntheticOpaque_1322_; uint8_t v_offsetCnstrs_1323_; uint8_t v_transparency_1324_; uint8_t v_etaStruct_1325_; uint8_t v_univApprox_1326_; uint8_t v_iota_1327_; uint8_t v_beta_1328_; uint8_t v_proj_1329_; uint8_t v_zeta_1330_; uint8_t v_zetaDelta_1331_; uint8_t v_zetaUnused_1332_; uint8_t v_zetaHave_1333_; uint8_t v_canUnfoldPredicateConfig_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1355_; 
v___x_1317_ = l_Lean_Meta_Context_config(v_a_1311_);
v_constApprox_1318_ = lean_ctor_get_uint8(v___x_1317_, 3);
v_isDefEqStuckEx_1319_ = lean_ctor_get_uint8(v___x_1317_, 4);
v_unificationHints_1320_ = lean_ctor_get_uint8(v___x_1317_, 5);
v_proofIrrelevance_1321_ = lean_ctor_get_uint8(v___x_1317_, 6);
v_assignSyntheticOpaque_1322_ = lean_ctor_get_uint8(v___x_1317_, 7);
v_offsetCnstrs_1323_ = lean_ctor_get_uint8(v___x_1317_, 8);
v_transparency_1324_ = lean_ctor_get_uint8(v___x_1317_, 9);
v_etaStruct_1325_ = lean_ctor_get_uint8(v___x_1317_, 10);
v_univApprox_1326_ = lean_ctor_get_uint8(v___x_1317_, 11);
v_iota_1327_ = lean_ctor_get_uint8(v___x_1317_, 12);
v_beta_1328_ = lean_ctor_get_uint8(v___x_1317_, 13);
v_proj_1329_ = lean_ctor_get_uint8(v___x_1317_, 14);
v_zeta_1330_ = lean_ctor_get_uint8(v___x_1317_, 15);
v_zetaDelta_1331_ = lean_ctor_get_uint8(v___x_1317_, 16);
v_zetaUnused_1332_ = lean_ctor_get_uint8(v___x_1317_, 17);
v_zetaHave_1333_ = lean_ctor_get_uint8(v___x_1317_, 18);
v_canUnfoldPredicateConfig_1334_ = lean_ctor_get_uint8(v___x_1317_, 19);
v_isSharedCheck_1355_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1336_ = v___x_1317_;
v_isShared_1337_ = v_isSharedCheck_1355_;
goto v_resetjp_1335_;
}
else
{
lean_dec(v___x_1317_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1355_;
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
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, 3, v_constApprox_1318_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, 4, v_isDefEqStuckEx_1319_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, 5, v_unificationHints_1320_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, 6, v_proofIrrelevance_1321_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, 7, v_assignSyntheticOpaque_1322_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, 8, v_offsetCnstrs_1323_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, 9, v_transparency_1324_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, 10, v_etaStruct_1325_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, 11, v_univApprox_1326_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, 12, v_iota_1327_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, 13, v_beta_1328_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, 14, v_proj_1329_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, 15, v_zeta_1330_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, 16, v_zetaDelta_1331_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, 17, v_zetaUnused_1332_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, 18, v_zetaHave_1333_);
lean_ctor_set_uint8(v_reuseFailAlloc_1354_, 19, v_canUnfoldPredicateConfig_1334_);
v___x_1339_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
uint8_t v_trackZetaDelta_1340_; lean_object* v_zetaDeltaSet_1341_; lean_object* v_lctx_1342_; lean_object* v_localInstances_1343_; lean_object* v_defEqCtx_x3f_1344_; lean_object* v_synthPendingDepth_1345_; lean_object* v_customCanUnfoldPredicate_x3f_1346_; uint8_t v_univApprox_1347_; uint8_t v_inTypeClassResolution_1348_; uint8_t v_cacheInferType_1349_; uint64_t v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
lean_ctor_set_uint8(v___x_1339_, 0, v_approx_1308_);
lean_ctor_set_uint8(v___x_1339_, 1, v_approx_1308_);
lean_ctor_set_uint8(v___x_1339_, 2, v_approx_1308_);
v_trackZetaDelta_1340_ = lean_ctor_get_uint8(v_a_1311_, sizeof(void*)*7);
v_zetaDeltaSet_1341_ = lean_ctor_get(v_a_1311_, 1);
v_lctx_1342_ = lean_ctor_get(v_a_1311_, 2);
v_localInstances_1343_ = lean_ctor_get(v_a_1311_, 3);
v_defEqCtx_x3f_1344_ = lean_ctor_get(v_a_1311_, 4);
v_synthPendingDepth_1345_ = lean_ctor_get(v_a_1311_, 5);
v_customCanUnfoldPredicate_x3f_1346_ = lean_ctor_get(v_a_1311_, 6);
v_univApprox_1347_ = lean_ctor_get_uint8(v_a_1311_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1348_ = lean_ctor_get_uint8(v_a_1311_, sizeof(void*)*7 + 2);
v_cacheInferType_1349_ = lean_ctor_get_uint8(v_a_1311_, sizeof(void*)*7 + 3);
v___x_1350_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1339_);
v___x_1351_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1351_, 0, v___x_1339_);
lean_ctor_set_uint64(v___x_1351_, sizeof(void*)*1, v___x_1350_);
lean_inc(v_customCanUnfoldPredicate_x3f_1346_);
lean_inc(v_synthPendingDepth_1345_);
lean_inc(v_defEqCtx_x3f_1344_);
lean_inc_ref(v_localInstances_1343_);
lean_inc_ref(v_lctx_1342_);
lean_inc(v_zetaDeltaSet_1341_);
v___x_1352_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1352_, 0, v___x_1351_);
lean_ctor_set(v___x_1352_, 1, v_zetaDeltaSet_1341_);
lean_ctor_set(v___x_1352_, 2, v_lctx_1342_);
lean_ctor_set(v___x_1352_, 3, v_localInstances_1343_);
lean_ctor_set(v___x_1352_, 4, v_defEqCtx_x3f_1344_);
lean_ctor_set(v___x_1352_, 5, v_synthPendingDepth_1345_);
lean_ctor_set(v___x_1352_, 6, v_customCanUnfoldPredicate_x3f_1346_);
lean_ctor_set_uint8(v___x_1352_, sizeof(void*)*7, v_trackZetaDelta_1340_);
lean_ctor_set_uint8(v___x_1352_, sizeof(void*)*7 + 1, v_univApprox_1347_);
lean_ctor_set_uint8(v___x_1352_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1348_);
lean_ctor_set_uint8(v___x_1352_, sizeof(void*)*7 + 3, v_cacheInferType_1349_);
v___x_1353_ = l_Lean_Meta_isExprDefEqGuarded(v_a_1309_, v_b_1310_, v___x_1352_, v_a_1312_, v_a_1313_, v_a_1314_);
lean_dec_ref_known(v___x_1352_, 7);
return v___x_1353_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply___boxed(lean_object* v_approx_1356_, lean_object* v_a_1357_, lean_object* v_b_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_){
_start:
{
uint8_t v_approx_boxed_1364_; lean_object* v_res_1365_; 
v_approx_boxed_1364_ = lean_unbox(v_approx_1356_);
v_res_1365_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(v_approx_boxed_1364_, v_a_1357_, v_b_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
lean_dec(v_a_1362_);
lean_dec_ref(v_a_1361_);
lean_dec(v_a_1360_);
lean_dec_ref(v_a_1359_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go(lean_object* v_mvarId_1366_, lean_object* v_cfg_1367_, lean_object* v_term_x3f_1368_, lean_object* v_targetType_1369_, lean_object* v_eType_1370_, lean_object* v_rangeNumArgs_1371_, lean_object* v_i_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_){
_start:
{
lean_object* v_lower_1378_; lean_object* v_upper_1379_; uint8_t v___x_1380_; 
v_lower_1378_ = lean_ctor_get(v_rangeNumArgs_1371_, 0);
v_upper_1379_ = lean_ctor_get(v_rangeNumArgs_1371_, 1);
v___x_1380_ = lean_nat_dec_lt(v_i_1372_, v_upper_1379_);
if (v___x_1380_ == 0)
{
lean_object* v___x_1381_; uint8_t v___x_1382_; 
lean_dec(v_i_1372_);
v___x_1381_ = lean_unsigned_to_nat(0u);
v___x_1382_ = lean_nat_dec_eq(v_lower_1378_, v___x_1381_);
if (v___x_1382_ == 0)
{
lean_object* v___x_1383_; uint8_t v___x_1384_; lean_object* v___x_1385_; 
lean_inc(v_lower_1378_);
v___x_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1383_, 0, v_lower_1378_);
v___x_1384_ = 0;
lean_inc_ref(v_eType_1370_);
v___x_1385_ = l_Lean_Meta_forallMetaTelescopeReducing(v_eType_1370_, v___x_1383_, v___x_1384_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v_a_1386_; lean_object* v_snd_1387_; lean_object* v_snd_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
v_a_1386_ = lean_ctor_get(v___x_1385_, 0);
lean_inc(v_a_1386_);
lean_dec_ref_known(v___x_1385_, 1);
v_snd_1387_ = lean_ctor_get(v_a_1386_, 1);
lean_inc(v_snd_1387_);
lean_dec(v_a_1386_);
v_snd_1388_ = lean_ctor_get(v_snd_1387_, 1);
lean_inc(v_snd_1388_);
lean_dec(v_snd_1387_);
v___x_1389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1389_, 0, v_snd_1388_);
v___x_1390_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(v_mvarId_1366_, v_eType_1370_, v___x_1389_, v_targetType_1369_, v_term_x3f_1368_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_);
return v___x_1390_;
}
else
{
lean_object* v_a_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1398_; 
lean_dec_ref(v_eType_1370_);
lean_dec_ref(v_targetType_1369_);
lean_dec(v_term_x3f_1368_);
lean_dec(v_mvarId_1366_);
v_a_1391_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1393_ = v___x_1385_;
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_a_1391_);
lean_dec(v___x_1385_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1396_; 
if (v_isShared_1394_ == 0)
{
v___x_1396_ = v___x_1393_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_a_1391_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
return v___x_1396_;
}
}
}
}
else
{
lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1399_ = lean_box(0);
v___x_1400_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(v_mvarId_1366_, v_eType_1370_, v___x_1399_, v_targetType_1369_, v_term_x3f_1368_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_);
return v___x_1400_;
}
}
else
{
lean_object* v___x_1401_; 
v___x_1401_ = l_Lean_Meta_saveState___redArg(v_a_1374_, v_a_1376_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v_a_1402_; lean_object* v___x_1403_; uint8_t v___x_1404_; lean_object* v___x_1405_; 
v_a_1402_ = lean_ctor_get(v___x_1401_, 0);
lean_inc(v_a_1402_);
lean_dec_ref_known(v___x_1401_, 1);
lean_inc(v_i_1372_);
v___x_1403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1403_, 0, v_i_1372_);
v___x_1404_ = 0;
lean_inc_ref(v_eType_1370_);
v___x_1405_ = l_Lean_Meta_forallMetaTelescopeReducing(v_eType_1370_, v___x_1403_, v___x_1404_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_);
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v_a_1406_; lean_object* v_snd_1407_; lean_object* v_fst_1408_; lean_object* v_fst_1409_; lean_object* v_snd_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1448_; 
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
lean_inc(v_a_1406_);
lean_dec_ref_known(v___x_1405_, 1);
v_snd_1407_ = lean_ctor_get(v_a_1406_, 1);
lean_inc(v_snd_1407_);
v_fst_1408_ = lean_ctor_get(v_a_1406_, 0);
lean_inc(v_fst_1408_);
lean_dec(v_a_1406_);
v_fst_1409_ = lean_ctor_get(v_snd_1407_, 0);
v_snd_1410_ = lean_ctor_get(v_snd_1407_, 1);
v_isSharedCheck_1448_ = !lean_is_exclusive(v_snd_1407_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1412_ = v_snd_1407_;
v_isShared_1413_ = v_isSharedCheck_1448_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_snd_1410_);
lean_inc(v_fst_1409_);
lean_dec(v_snd_1407_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1448_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
uint8_t v_approx_1414_; lean_object* v___x_1415_; 
v_approx_1414_ = lean_ctor_get_uint8(v_cfg_1367_, 3);
lean_inc_ref(v_targetType_1369_);
v___x_1415_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(v_approx_1414_, v_snd_1410_, v_targetType_1369_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1439_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1418_ = v___x_1415_;
v_isShared_1419_ = v_isSharedCheck_1439_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1415_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1439_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
uint8_t v___x_1420_; 
v___x_1420_ = lean_unbox(v_a_1416_);
lean_dec(v_a_1416_);
if (v___x_1420_ == 0)
{
lean_object* v___x_1421_; 
lean_del_object(v___x_1418_);
lean_del_object(v___x_1412_);
lean_dec(v_fst_1409_);
lean_dec(v_fst_1408_);
v___x_1421_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1402_, v_a_1374_, v_a_1376_);
lean_dec(v_a_1402_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v___x_1422_; lean_object* v___x_1423_; 
lean_dec_ref_known(v___x_1421_, 1);
v___x_1422_ = lean_unsigned_to_nat(1u);
v___x_1423_ = lean_nat_add(v_i_1372_, v___x_1422_);
lean_dec(v_i_1372_);
v_i_1372_ = v___x_1423_;
goto _start;
}
else
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1432_; 
lean_dec(v_i_1372_);
lean_dec_ref(v_eType_1370_);
lean_dec_ref(v_targetType_1369_);
lean_dec(v_term_x3f_1368_);
lean_dec(v_mvarId_1366_);
v_a_1425_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1427_ = v___x_1421_;
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1421_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1430_; 
if (v_isShared_1428_ == 0)
{
v___x_1430_ = v___x_1427_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_a_1425_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
}
else
{
lean_object* v___x_1434_; 
lean_dec(v_a_1402_);
lean_dec(v_i_1372_);
lean_dec_ref(v_eType_1370_);
lean_dec_ref(v_targetType_1369_);
lean_dec(v_term_x3f_1368_);
lean_dec(v_mvarId_1366_);
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 1, v_fst_1409_);
lean_ctor_set(v___x_1412_, 0, v_fst_1408_);
v___x_1434_ = v___x_1412_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_fst_1408_);
lean_ctor_set(v_reuseFailAlloc_1438_, 1, v_fst_1409_);
v___x_1434_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
lean_object* v___x_1436_; 
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 0, v___x_1434_);
v___x_1436_ = v___x_1418_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1434_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
}
else
{
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1447_; 
lean_del_object(v___x_1412_);
lean_dec(v_fst_1409_);
lean_dec(v_fst_1408_);
lean_dec(v_a_1402_);
lean_dec(v_i_1372_);
lean_dec_ref(v_eType_1370_);
lean_dec_ref(v_targetType_1369_);
lean_dec(v_term_x3f_1368_);
lean_dec(v_mvarId_1366_);
v_a_1440_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1442_ = v___x_1415_;
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1415_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1445_; 
if (v_isShared_1443_ == 0)
{
v___x_1445_ = v___x_1442_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_a_1440_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
}
}
else
{
lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1456_; 
lean_dec(v_a_1402_);
lean_dec(v_i_1372_);
lean_dec_ref(v_eType_1370_);
lean_dec_ref(v_targetType_1369_);
lean_dec(v_term_x3f_1368_);
lean_dec(v_mvarId_1366_);
v_a_1449_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1451_ = v___x_1405_;
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1405_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1454_; 
if (v_isShared_1452_ == 0)
{
v___x_1454_ = v___x_1451_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_a_1449_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
}
}
else
{
lean_object* v_a_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1464_; 
lean_dec(v_i_1372_);
lean_dec_ref(v_eType_1370_);
lean_dec_ref(v_targetType_1369_);
lean_dec(v_term_x3f_1368_);
lean_dec(v_mvarId_1366_);
v_a_1457_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1459_ = v___x_1401_;
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v___x_1401_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1462_; 
if (v_isShared_1460_ == 0)
{
v___x_1462_ = v___x_1459_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_a_1457_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go___boxed(lean_object* v_mvarId_1465_, lean_object* v_cfg_1466_, lean_object* v_term_x3f_1467_, lean_object* v_targetType_1468_, lean_object* v_eType_1469_, lean_object* v_rangeNumArgs_1470_, lean_object* v_i_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go(v_mvarId_1465_, v_cfg_1466_, v_term_x3f_1467_, v_targetType_1468_, v_eType_1469_, v_rangeNumArgs_1470_, v_i_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_);
lean_dec(v_a_1475_);
lean_dec_ref(v_a_1474_);
lean_dec(v_a_1473_);
lean_dec_ref(v_a_1472_);
lean_dec_ref(v_rangeNumArgs_1470_);
lean_dec_ref(v_cfg_1466_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go_match__1_splitter___redArg(lean_object* v_x_1478_, lean_object* v_h__1_1479_){
_start:
{
lean_object* v_snd_1480_; lean_object* v_fst_1481_; lean_object* v_fst_1482_; lean_object* v_snd_1483_; lean_object* v___x_1484_; 
v_snd_1480_ = lean_ctor_get(v_x_1478_, 1);
lean_inc(v_snd_1480_);
v_fst_1481_ = lean_ctor_get(v_x_1478_, 0);
lean_inc(v_fst_1481_);
lean_dec_ref(v_x_1478_);
v_fst_1482_ = lean_ctor_get(v_snd_1480_, 0);
lean_inc(v_fst_1482_);
v_snd_1483_ = lean_ctor_get(v_snd_1480_, 1);
lean_inc(v_snd_1483_);
lean_dec(v_snd_1480_);
v___x_1484_ = lean_apply_3(v_h__1_1479_, v_fst_1481_, v_fst_1482_, v_snd_1483_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go_match__1_splitter(lean_object* v_motive_1485_, lean_object* v_x_1486_, lean_object* v_h__1_1487_){
_start:
{
lean_object* v_snd_1488_; lean_object* v_fst_1489_; lean_object* v_fst_1490_; lean_object* v_snd_1491_; lean_object* v___x_1492_; 
v_snd_1488_ = lean_ctor_get(v_x_1486_, 1);
lean_inc(v_snd_1488_);
v_fst_1489_ = lean_ctor_get(v_x_1486_, 0);
lean_inc(v_fst_1489_);
lean_dec_ref(v_x_1486_);
v_fst_1490_ = lean_ctor_get(v_snd_1488_, 0);
lean_inc(v_fst_1490_);
v_snd_1491_ = lean_ctor_get(v_snd_1488_, 1);
lean_inc(v_snd_1491_);
lean_dec(v_snd_1488_);
v___x_1492_ = lean_apply_3(v_h__1_1487_, v_fst_1489_, v_fst_1490_, v_snd_1491_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(lean_object* v_e_1493_, lean_object* v___y_1494_){
_start:
{
uint8_t v___x_1496_; 
v___x_1496_ = l_Lean_Expr_hasMVar(v_e_1493_);
if (v___x_1496_ == 0)
{
lean_object* v___x_1497_; 
v___x_1497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1497_, 0, v_e_1493_);
return v___x_1497_;
}
else
{
lean_object* v___x_1498_; lean_object* v_mctx_1499_; lean_object* v___x_1500_; lean_object* v_fst_1501_; lean_object* v_snd_1502_; lean_object* v___x_1503_; lean_object* v_cache_1504_; lean_object* v_zetaDeltaFVarIds_1505_; lean_object* v_postponed_1506_; lean_object* v_diag_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1516_; 
v___x_1498_ = lean_st_ref_get(v___y_1494_);
v_mctx_1499_ = lean_ctor_get(v___x_1498_, 0);
lean_inc_ref(v_mctx_1499_);
lean_dec(v___x_1498_);
v___x_1500_ = l_Lean_instantiateMVarsCore(v_mctx_1499_, v_e_1493_);
v_fst_1501_ = lean_ctor_get(v___x_1500_, 0);
lean_inc(v_fst_1501_);
v_snd_1502_ = lean_ctor_get(v___x_1500_, 1);
lean_inc(v_snd_1502_);
lean_dec_ref(v___x_1500_);
v___x_1503_ = lean_st_ref_take(v___y_1494_);
v_cache_1504_ = lean_ctor_get(v___x_1503_, 1);
v_zetaDeltaFVarIds_1505_ = lean_ctor_get(v___x_1503_, 2);
v_postponed_1506_ = lean_ctor_get(v___x_1503_, 3);
v_diag_1507_ = lean_ctor_get(v___x_1503_, 4);
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1516_ == 0)
{
lean_object* v_unused_1517_; 
v_unused_1517_ = lean_ctor_get(v___x_1503_, 0);
lean_dec(v_unused_1517_);
v___x_1509_ = v___x_1503_;
v_isShared_1510_ = v_isSharedCheck_1516_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_diag_1507_);
lean_inc(v_postponed_1506_);
lean_inc(v_zetaDeltaFVarIds_1505_);
lean_inc(v_cache_1504_);
lean_dec(v___x_1503_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1516_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1512_; 
if (v_isShared_1510_ == 0)
{
lean_ctor_set(v___x_1509_, 0, v_snd_1502_);
v___x_1512_ = v___x_1509_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_snd_1502_);
lean_ctor_set(v_reuseFailAlloc_1515_, 1, v_cache_1504_);
lean_ctor_set(v_reuseFailAlloc_1515_, 2, v_zetaDeltaFVarIds_1505_);
lean_ctor_set(v_reuseFailAlloc_1515_, 3, v_postponed_1506_);
lean_ctor_set(v_reuseFailAlloc_1515_, 4, v_diag_1507_);
v___x_1512_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1513_ = lean_st_ref_put(v___y_1494_, v___x_1512_);
v___x_1514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1514_, 0, v_fst_1501_);
return v___x_1514_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg___boxed(lean_object* v_e_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_e_1518_, v___y_1519_);
lean_dec(v___y_1519_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0(lean_object* v_e_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
lean_object* v___x_1528_; 
v___x_1528_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_e_1522_, v___y_1524_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___boxed(lean_object* v_e_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
lean_object* v_res_1535_; 
v_res_1535_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0(v_e_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(lean_object* v_mvarId_1536_, lean_object* v_x_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_){
_start:
{
lean_object* v___x_1543_; 
v___x_1543_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1536_, v_x_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
if (lean_obj_tag(v___x_1543_) == 0)
{
lean_object* v_a_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1551_; 
v_a_1544_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1546_ = v___x_1543_;
v_isShared_1547_ = v_isSharedCheck_1551_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_a_1544_);
lean_dec(v___x_1543_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1551_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v___x_1549_; 
if (v_isShared_1547_ == 0)
{
v___x_1549_ = v___x_1546_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v_a_1544_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
}
else
{
lean_object* v_a_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1559_; 
v_a_1552_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1554_ = v___x_1543_;
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_a_1552_);
lean_dec(v___x_1543_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1557_; 
if (v_isShared_1555_ == 0)
{
v___x_1557_ = v___x_1554_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_a_1552_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg___boxed(lean_object* v_mvarId_1560_, lean_object* v_x_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_1560_, v_x_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_);
lean_dec(v___y_1565_);
lean_dec_ref(v___y_1564_);
lean_dec(v___y_1563_);
lean_dec_ref(v___y_1562_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6(lean_object* v_00_u03b1_1568_, lean_object* v_mvarId_1569_, lean_object* v_x_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
lean_object* v___x_1576_; 
v___x_1576_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_1569_, v_x_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___boxed(lean_object* v_00_u03b1_1577_, lean_object* v_mvarId_1578_, lean_object* v_x_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6(v_00_u03b1_1577_, v_mvarId_1578_, v_x_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
lean_dec(v___y_1583_);
lean_dec_ref(v___y_1582_);
lean_dec(v___y_1581_);
lean_dec_ref(v___y_1580_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(lean_object* v_as_1586_, size_t v_i_1587_, size_t v_stop_1588_, lean_object* v_b_1589_, lean_object* v___y_1590_){
_start:
{
lean_object* v_a_1593_; uint8_t v___x_1597_; 
v___x_1597_ = lean_usize_dec_eq(v_i_1587_, v_stop_1588_);
if (v___x_1597_ == 0)
{
lean_object* v___x_1598_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1598_ = lean_array_uget_borrowed(v_as_1586_, v_i_1587_);
v___x_1601_ = l_Lean_Expr_mvarId_x21(v___x_1598_);
v___x_1602_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v___x_1601_, v___y_1590_);
lean_dec(v___x_1601_);
if (lean_obj_tag(v___x_1602_) == 0)
{
lean_object* v_a_1603_; uint8_t v___x_1604_; 
v_a_1603_ = lean_ctor_get(v___x_1602_, 0);
lean_inc(v_a_1603_);
lean_dec_ref_known(v___x_1602_, 1);
v___x_1604_ = lean_unbox(v_a_1603_);
lean_dec(v_a_1603_);
if (v___x_1604_ == 0)
{
goto v___jp_1599_;
}
else
{
v_a_1593_ = v_b_1589_;
goto v___jp_1592_;
}
}
else
{
if (lean_obj_tag(v___x_1602_) == 0)
{
lean_object* v_a_1605_; uint8_t v___x_1606_; 
v_a_1605_ = lean_ctor_get(v___x_1602_, 0);
lean_inc(v_a_1605_);
lean_dec_ref_known(v___x_1602_, 1);
v___x_1606_ = lean_unbox(v_a_1605_);
lean_dec(v_a_1605_);
if (v___x_1606_ == 0)
{
v_a_1593_ = v_b_1589_;
goto v___jp_1592_;
}
else
{
goto v___jp_1599_;
}
}
else
{
lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1614_; 
lean_dec_ref(v_b_1589_);
v_a_1607_ = lean_ctor_get(v___x_1602_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1602_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1609_ = v___x_1602_;
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1602_);
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
v___jp_1599_:
{
lean_object* v___x_1600_; 
lean_inc(v___x_1598_);
v___x_1600_ = lean_array_push(v_b_1589_, v___x_1598_);
v_a_1593_ = v___x_1600_;
goto v___jp_1592_;
}
}
else
{
lean_object* v___x_1615_; 
v___x_1615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1615_, 0, v_b_1589_);
return v___x_1615_;
}
v___jp_1592_:
{
size_t v___x_1594_; size_t v___x_1595_; 
v___x_1594_ = ((size_t)1ULL);
v___x_1595_ = lean_usize_add(v_i_1587_, v___x_1594_);
v_i_1587_ = v___x_1595_;
v_b_1589_ = v_a_1593_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg___boxed(lean_object* v_as_1616_, lean_object* v_i_1617_, lean_object* v_stop_1618_, lean_object* v_b_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_){
_start:
{
size_t v_i_boxed_1622_; size_t v_stop_boxed_1623_; lean_object* v_res_1624_; 
v_i_boxed_1622_ = lean_unbox_usize(v_i_1617_);
lean_dec(v_i_1617_);
v_stop_boxed_1623_ = lean_unbox_usize(v_stop_1618_);
lean_dec(v_stop_1618_);
v_res_1624_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_as_1616_, v_i_boxed_1622_, v_stop_boxed_1623_, v_b_1619_, v___y_1620_);
lean_dec(v___y_1620_);
lean_dec_ref(v_as_1616_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_apply_spec__3(lean_object* v_as_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
if (lean_obj_tag(v_as_1625_) == 0)
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1631_ = lean_box(0);
v___x_1632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1631_);
return v___x_1632_;
}
else
{
lean_object* v_head_1633_; lean_object* v_tail_1634_; lean_object* v___x_1635_; 
v_head_1633_ = lean_ctor_get(v_as_1625_, 0);
lean_inc(v_head_1633_);
v_tail_1634_ = lean_ctor_get(v_as_1625_, 1);
lean_inc(v_tail_1634_);
lean_dec_ref_known(v_as_1625_, 2);
v___x_1635_ = l_Lean_MVarId_headBetaType(v_head_1633_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_dec_ref_known(v___x_1635_, 1);
v_as_1625_ = v_tail_1634_;
goto _start;
}
else
{
lean_dec(v_tail_1634_);
return v___x_1635_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_apply_spec__3___boxed(lean_object* v_as_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_){
_start:
{
lean_object* v_res_1643_; 
v_res_1643_ = l_List_forM___at___00Lean_MVarId_apply_spec__3(v_as_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
lean_dec(v___y_1639_);
lean_dec_ref(v___y_1638_);
return v_res_1643_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9___redArg(lean_object* v_x_1644_, lean_object* v_x_1645_, lean_object* v_x_1646_, lean_object* v_x_1647_){
_start:
{
lean_object* v_ks_1648_; lean_object* v_vs_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1673_; 
v_ks_1648_ = lean_ctor_get(v_x_1644_, 0);
v_vs_1649_ = lean_ctor_get(v_x_1644_, 1);
v_isSharedCheck_1673_ = !lean_is_exclusive(v_x_1644_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1651_ = v_x_1644_;
v_isShared_1652_ = v_isSharedCheck_1673_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_vs_1649_);
lean_inc(v_ks_1648_);
lean_dec(v_x_1644_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1673_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1653_; uint8_t v___x_1654_; 
v___x_1653_ = lean_array_get_size(v_ks_1648_);
v___x_1654_ = lean_nat_dec_lt(v_x_1645_, v___x_1653_);
if (v___x_1654_ == 0)
{
lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1658_; 
lean_dec(v_x_1645_);
v___x_1655_ = lean_array_push(v_ks_1648_, v_x_1646_);
v___x_1656_ = lean_array_push(v_vs_1649_, v_x_1647_);
if (v_isShared_1652_ == 0)
{
lean_ctor_set(v___x_1651_, 1, v___x_1656_);
lean_ctor_set(v___x_1651_, 0, v___x_1655_);
v___x_1658_ = v___x_1651_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v___x_1655_);
lean_ctor_set(v_reuseFailAlloc_1659_, 1, v___x_1656_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
else
{
lean_object* v_k_x27_1660_; uint8_t v___x_1661_; 
v_k_x27_1660_ = lean_array_fget_borrowed(v_ks_1648_, v_x_1645_);
v___x_1661_ = l_Lean_instBEqMVarId_beq(v_x_1646_, v_k_x27_1660_);
if (v___x_1661_ == 0)
{
lean_object* v___x_1663_; 
if (v_isShared_1652_ == 0)
{
v___x_1663_ = v___x_1651_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_ks_1648_);
lean_ctor_set(v_reuseFailAlloc_1667_, 1, v_vs_1649_);
v___x_1663_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1664_ = lean_unsigned_to_nat(1u);
v___x_1665_ = lean_nat_add(v_x_1645_, v___x_1664_);
lean_dec(v_x_1645_);
v_x_1644_ = v___x_1663_;
v_x_1645_ = v___x_1665_;
goto _start;
}
}
else
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1671_; 
v___x_1668_ = lean_array_fset(v_ks_1648_, v_x_1645_, v_x_1646_);
v___x_1669_ = lean_array_fset(v_vs_1649_, v_x_1645_, v_x_1647_);
lean_dec(v_x_1645_);
if (v_isShared_1652_ == 0)
{
lean_ctor_set(v___x_1651_, 1, v___x_1669_);
lean_ctor_set(v___x_1651_, 0, v___x_1668_);
v___x_1671_ = v___x_1651_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v___x_1668_);
lean_ctor_set(v_reuseFailAlloc_1672_, 1, v___x_1669_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8___redArg(lean_object* v_n_1674_, lean_object* v_k_1675_, lean_object* v_v_1676_){
_start:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1677_ = lean_unsigned_to_nat(0u);
v___x_1678_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9___redArg(v_n_1674_, v___x_1677_, v_k_1675_, v_v_1676_);
return v___x_1678_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1679_; 
v___x_1679_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(lean_object* v_x_1680_, size_t v_x_1681_, size_t v_x_1682_, lean_object* v_x_1683_, lean_object* v_x_1684_){
_start:
{
if (lean_obj_tag(v_x_1680_) == 0)
{
lean_object* v_es_1685_; size_t v___x_1686_; size_t v___x_1687_; lean_object* v_j_1688_; lean_object* v___x_1689_; uint8_t v___x_1690_; 
v_es_1685_ = lean_ctor_get(v_x_1680_, 0);
v___x_1686_ = ((size_t)31ULL);
v___x_1687_ = lean_usize_land(v_x_1681_, v___x_1686_);
v_j_1688_ = lean_usize_to_nat(v___x_1687_);
v___x_1689_ = lean_array_get_size(v_es_1685_);
v___x_1690_ = lean_nat_dec_lt(v_j_1688_, v___x_1689_);
if (v___x_1690_ == 0)
{
lean_dec(v_j_1688_);
lean_dec(v_x_1684_);
lean_dec(v_x_1683_);
return v_x_1680_;
}
else
{
lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1729_; 
lean_inc_ref(v_es_1685_);
v_isSharedCheck_1729_ = !lean_is_exclusive(v_x_1680_);
if (v_isSharedCheck_1729_ == 0)
{
lean_object* v_unused_1730_; 
v_unused_1730_ = lean_ctor_get(v_x_1680_, 0);
lean_dec(v_unused_1730_);
v___x_1692_ = v_x_1680_;
v_isShared_1693_ = v_isSharedCheck_1729_;
goto v_resetjp_1691_;
}
else
{
lean_dec(v_x_1680_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1729_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v_v_1694_; lean_object* v___x_1695_; lean_object* v_xs_x27_1696_; lean_object* v___y_1698_; 
v_v_1694_ = lean_array_fget(v_es_1685_, v_j_1688_);
v___x_1695_ = lean_box(0);
v_xs_x27_1696_ = lean_array_fset(v_es_1685_, v_j_1688_, v___x_1695_);
switch(lean_obj_tag(v_v_1694_))
{
case 0:
{
lean_object* v_key_1703_; lean_object* v_val_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1714_; 
v_key_1703_ = lean_ctor_get(v_v_1694_, 0);
v_val_1704_ = lean_ctor_get(v_v_1694_, 1);
v_isSharedCheck_1714_ = !lean_is_exclusive(v_v_1694_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1706_ = v_v_1694_;
v_isShared_1707_ = v_isSharedCheck_1714_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_val_1704_);
lean_inc(v_key_1703_);
lean_dec(v_v_1694_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1714_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
uint8_t v___x_1708_; 
v___x_1708_ = l_Lean_instBEqMVarId_beq(v_x_1683_, v_key_1703_);
if (v___x_1708_ == 0)
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
lean_del_object(v___x_1706_);
v___x_1709_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1703_, v_val_1704_, v_x_1683_, v_x_1684_);
v___x_1710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1709_);
v___y_1698_ = v___x_1710_;
goto v___jp_1697_;
}
else
{
lean_object* v___x_1712_; 
lean_dec(v_val_1704_);
lean_dec(v_key_1703_);
if (v_isShared_1707_ == 0)
{
lean_ctor_set(v___x_1706_, 1, v_x_1684_);
lean_ctor_set(v___x_1706_, 0, v_x_1683_);
v___x_1712_ = v___x_1706_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_x_1683_);
lean_ctor_set(v_reuseFailAlloc_1713_, 1, v_x_1684_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
v___y_1698_ = v___x_1712_;
goto v___jp_1697_;
}
}
}
}
case 1:
{
lean_object* v_node_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1727_; 
v_node_1715_ = lean_ctor_get(v_v_1694_, 0);
v_isSharedCheck_1727_ = !lean_is_exclusive(v_v_1694_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1717_ = v_v_1694_;
v_isShared_1718_ = v_isSharedCheck_1727_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_node_1715_);
lean_dec(v_v_1694_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1727_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
size_t v___x_1719_; size_t v___x_1720_; size_t v___x_1721_; size_t v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1725_; 
v___x_1719_ = ((size_t)5ULL);
v___x_1720_ = lean_usize_shift_right(v_x_1681_, v___x_1719_);
v___x_1721_ = ((size_t)1ULL);
v___x_1722_ = lean_usize_add(v_x_1682_, v___x_1721_);
v___x_1723_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_node_1715_, v___x_1720_, v___x_1722_, v_x_1683_, v_x_1684_);
if (v_isShared_1718_ == 0)
{
lean_ctor_set(v___x_1717_, 0, v___x_1723_);
v___x_1725_ = v___x_1717_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v___x_1723_);
v___x_1725_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
v___y_1698_ = v___x_1725_;
goto v___jp_1697_;
}
}
}
default: 
{
lean_object* v___x_1728_; 
v___x_1728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1728_, 0, v_x_1683_);
lean_ctor_set(v___x_1728_, 1, v_x_1684_);
v___y_1698_ = v___x_1728_;
goto v___jp_1697_;
}
}
v___jp_1697_:
{
lean_object* v___x_1699_; lean_object* v___x_1701_; 
v___x_1699_ = lean_array_fset(v_xs_x27_1696_, v_j_1688_, v___y_1698_);
lean_dec(v_j_1688_);
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 0, v___x_1699_);
v___x_1701_ = v___x_1692_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v___x_1699_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
}
}
else
{
lean_object* v_ks_1731_; lean_object* v_vs_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1750_; 
v_ks_1731_ = lean_ctor_get(v_x_1680_, 0);
v_vs_1732_ = lean_ctor_get(v_x_1680_, 1);
v_isSharedCheck_1750_ = !lean_is_exclusive(v_x_1680_);
if (v_isSharedCheck_1750_ == 0)
{
v___x_1734_ = v_x_1680_;
v_isShared_1735_ = v_isSharedCheck_1750_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_vs_1732_);
lean_inc(v_ks_1731_);
lean_dec(v_x_1680_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1750_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1737_; 
if (v_isShared_1735_ == 0)
{
v___x_1737_ = v___x_1734_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_ks_1731_);
lean_ctor_set(v_reuseFailAlloc_1749_, 1, v_vs_1732_);
v___x_1737_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
lean_object* v_newNode_1738_; size_t v___x_1739_; uint8_t v___x_1740_; 
v_newNode_1738_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8___redArg(v___x_1737_, v_x_1683_, v_x_1684_);
v___x_1739_ = ((size_t)7ULL);
v___x_1740_ = lean_usize_dec_le(v___x_1739_, v_x_1682_);
if (v___x_1740_ == 0)
{
lean_object* v___x_1741_; lean_object* v___x_1742_; uint8_t v___x_1743_; 
v___x_1741_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1738_);
v___x_1742_ = lean_unsigned_to_nat(4u);
v___x_1743_ = lean_nat_dec_lt(v___x_1741_, v___x_1742_);
lean_dec(v___x_1741_);
if (v___x_1743_ == 0)
{
lean_object* v_ks_1744_; lean_object* v_vs_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
v_ks_1744_ = lean_ctor_get(v_newNode_1738_, 0);
lean_inc_ref(v_ks_1744_);
v_vs_1745_ = lean_ctor_get(v_newNode_1738_, 1);
lean_inc_ref(v_vs_1745_);
lean_dec_ref(v_newNode_1738_);
v___x_1746_ = lean_unsigned_to_nat(0u);
v___x_1747_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0);
v___x_1748_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(v_x_1682_, v_ks_1744_, v_vs_1745_, v___x_1746_, v___x_1747_);
lean_dec_ref(v_vs_1745_);
lean_dec_ref(v_ks_1744_);
return v___x_1748_;
}
else
{
return v_newNode_1738_;
}
}
else
{
return v_newNode_1738_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(size_t v_depth_1751_, lean_object* v_keys_1752_, lean_object* v_vals_1753_, lean_object* v_i_1754_, lean_object* v_entries_1755_){
_start:
{
lean_object* v___x_1756_; uint8_t v___x_1757_; 
v___x_1756_ = lean_array_get_size(v_keys_1752_);
v___x_1757_ = lean_nat_dec_lt(v_i_1754_, v___x_1756_);
if (v___x_1757_ == 0)
{
lean_dec(v_i_1754_);
return v_entries_1755_;
}
else
{
lean_object* v_k_1758_; lean_object* v_v_1759_; uint64_t v___x_1760_; size_t v_h_1761_; size_t v___x_1762_; lean_object* v___x_1763_; size_t v___x_1764_; size_t v___x_1765_; size_t v___x_1766_; size_t v_h_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
v_k_1758_ = lean_array_fget_borrowed(v_keys_1752_, v_i_1754_);
v_v_1759_ = lean_array_fget_borrowed(v_vals_1753_, v_i_1754_);
v___x_1760_ = l_Lean_instHashableMVarId_hash(v_k_1758_);
v_h_1761_ = lean_uint64_to_usize(v___x_1760_);
v___x_1762_ = ((size_t)5ULL);
v___x_1763_ = lean_unsigned_to_nat(1u);
v___x_1764_ = ((size_t)1ULL);
v___x_1765_ = lean_usize_sub(v_depth_1751_, v___x_1764_);
v___x_1766_ = lean_usize_mul(v___x_1762_, v___x_1765_);
v_h_1767_ = lean_usize_shift_right(v_h_1761_, v___x_1766_);
v___x_1768_ = lean_nat_add(v_i_1754_, v___x_1763_);
lean_dec(v_i_1754_);
lean_inc(v_v_1759_);
lean_inc(v_k_1758_);
v___x_1769_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_entries_1755_, v_h_1767_, v_depth_1751_, v_k_1758_, v_v_1759_);
v_i_1754_ = v___x_1768_;
v_entries_1755_ = v___x_1769_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg___boxed(lean_object* v_depth_1771_, lean_object* v_keys_1772_, lean_object* v_vals_1773_, lean_object* v_i_1774_, lean_object* v_entries_1775_){
_start:
{
size_t v_depth_boxed_1776_; lean_object* v_res_1777_; 
v_depth_boxed_1776_ = lean_unbox_usize(v_depth_1771_);
lean_dec(v_depth_1771_);
v_res_1777_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(v_depth_boxed_1776_, v_keys_1772_, v_vals_1773_, v_i_1774_, v_entries_1775_);
lean_dec_ref(v_vals_1773_);
lean_dec_ref(v_keys_1772_);
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_x_1778_, lean_object* v_x_1779_, lean_object* v_x_1780_, lean_object* v_x_1781_, lean_object* v_x_1782_){
_start:
{
size_t v_x_7086__boxed_1783_; size_t v_x_7087__boxed_1784_; lean_object* v_res_1785_; 
v_x_7086__boxed_1783_ = lean_unbox_usize(v_x_1779_);
lean_dec(v_x_1779_);
v_x_7087__boxed_1784_ = lean_unbox_usize(v_x_1780_);
lean_dec(v_x_1780_);
v_res_1785_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_x_1778_, v_x_7086__boxed_1783_, v_x_7087__boxed_1784_, v_x_1781_, v_x_1782_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1___redArg(lean_object* v_x_1786_, lean_object* v_x_1787_, lean_object* v_x_1788_){
_start:
{
uint64_t v___x_1789_; size_t v___x_1790_; size_t v___x_1791_; lean_object* v___x_1792_; 
v___x_1789_ = l_Lean_instHashableMVarId_hash(v_x_1787_);
v___x_1790_ = lean_uint64_to_usize(v___x_1789_);
v___x_1791_ = ((size_t)1ULL);
v___x_1792_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_x_1786_, v___x_1790_, v___x_1791_, v_x_1787_, v_x_1788_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(lean_object* v_mvarId_1793_, lean_object* v_val_1794_, lean_object* v___y_1795_){
_start:
{
lean_object* v___x_1797_; lean_object* v_mctx_1798_; lean_object* v_cache_1799_; lean_object* v_zetaDeltaFVarIds_1800_; lean_object* v_postponed_1801_; lean_object* v_diag_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1831_; 
v___x_1797_ = lean_st_ref_take(v___y_1795_);
v_mctx_1798_ = lean_ctor_get(v___x_1797_, 0);
v_cache_1799_ = lean_ctor_get(v___x_1797_, 1);
v_zetaDeltaFVarIds_1800_ = lean_ctor_get(v___x_1797_, 2);
v_postponed_1801_ = lean_ctor_get(v___x_1797_, 3);
v_diag_1802_ = lean_ctor_get(v___x_1797_, 4);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1804_ = v___x_1797_;
v_isShared_1805_ = v_isSharedCheck_1831_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_diag_1802_);
lean_inc(v_postponed_1801_);
lean_inc(v_zetaDeltaFVarIds_1800_);
lean_inc(v_cache_1799_);
lean_inc(v_mctx_1798_);
lean_dec(v___x_1797_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1831_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v_depth_1806_; lean_object* v_levelAssignDepth_1807_; lean_object* v_lmvarCounter_1808_; lean_object* v_mvarCounter_1809_; lean_object* v_lDecls_1810_; lean_object* v_decls_1811_; lean_object* v_userNames_1812_; lean_object* v_lAssignment_1813_; lean_object* v_eAssignment_1814_; lean_object* v_dAssignment_1815_; lean_object* v_instanceTypedMVars_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1830_; 
v_depth_1806_ = lean_ctor_get(v_mctx_1798_, 0);
v_levelAssignDepth_1807_ = lean_ctor_get(v_mctx_1798_, 1);
v_lmvarCounter_1808_ = lean_ctor_get(v_mctx_1798_, 2);
v_mvarCounter_1809_ = lean_ctor_get(v_mctx_1798_, 3);
v_lDecls_1810_ = lean_ctor_get(v_mctx_1798_, 4);
v_decls_1811_ = lean_ctor_get(v_mctx_1798_, 5);
v_userNames_1812_ = lean_ctor_get(v_mctx_1798_, 6);
v_lAssignment_1813_ = lean_ctor_get(v_mctx_1798_, 7);
v_eAssignment_1814_ = lean_ctor_get(v_mctx_1798_, 8);
v_dAssignment_1815_ = lean_ctor_get(v_mctx_1798_, 9);
v_instanceTypedMVars_1816_ = lean_ctor_get(v_mctx_1798_, 10);
v_isSharedCheck_1830_ = !lean_is_exclusive(v_mctx_1798_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1818_ = v_mctx_1798_;
v_isShared_1819_ = v_isSharedCheck_1830_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_instanceTypedMVars_1816_);
lean_inc(v_dAssignment_1815_);
lean_inc(v_eAssignment_1814_);
lean_inc(v_lAssignment_1813_);
lean_inc(v_userNames_1812_);
lean_inc(v_decls_1811_);
lean_inc(v_lDecls_1810_);
lean_inc(v_mvarCounter_1809_);
lean_inc(v_lmvarCounter_1808_);
lean_inc(v_levelAssignDepth_1807_);
lean_inc(v_depth_1806_);
lean_dec(v_mctx_1798_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1830_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1823_; 
v___x_1820_ = lean_box(0);
v___x_1821_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1___redArg(v_eAssignment_1814_, v_mvarId_1793_, v_val_1794_);
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 8, v___x_1821_);
v___x_1823_ = v___x_1818_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_depth_1806_);
lean_ctor_set(v_reuseFailAlloc_1829_, 1, v_levelAssignDepth_1807_);
lean_ctor_set(v_reuseFailAlloc_1829_, 2, v_lmvarCounter_1808_);
lean_ctor_set(v_reuseFailAlloc_1829_, 3, v_mvarCounter_1809_);
lean_ctor_set(v_reuseFailAlloc_1829_, 4, v_lDecls_1810_);
lean_ctor_set(v_reuseFailAlloc_1829_, 5, v_decls_1811_);
lean_ctor_set(v_reuseFailAlloc_1829_, 6, v_userNames_1812_);
lean_ctor_set(v_reuseFailAlloc_1829_, 7, v_lAssignment_1813_);
lean_ctor_set(v_reuseFailAlloc_1829_, 8, v___x_1821_);
lean_ctor_set(v_reuseFailAlloc_1829_, 9, v_dAssignment_1815_);
lean_ctor_set(v_reuseFailAlloc_1829_, 10, v_instanceTypedMVars_1816_);
v___x_1823_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
lean_object* v___x_1825_; 
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 0, v___x_1823_);
v___x_1825_ = v___x_1804_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v___x_1823_);
lean_ctor_set(v_reuseFailAlloc_1828_, 1, v_cache_1799_);
lean_ctor_set(v_reuseFailAlloc_1828_, 2, v_zetaDeltaFVarIds_1800_);
lean_ctor_set(v_reuseFailAlloc_1828_, 3, v_postponed_1801_);
lean_ctor_set(v_reuseFailAlloc_1828_, 4, v_diag_1802_);
v___x_1825_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; 
v___x_1826_ = lean_st_ref_put(v___y_1795_, v___x_1825_);
v___x_1827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1820_);
return v___x_1827_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg___boxed(lean_object* v_mvarId_1832_, lean_object* v_val_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_){
_start:
{
lean_object* v_res_1836_; 
v_res_1836_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_1832_, v_val_1833_, v___y_1834_);
lean_dec(v___y_1834_);
return v_res_1836_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_MVarId_apply_spec__2(lean_object* v_a_1837_, lean_object* v_x_1838_){
_start:
{
if (lean_obj_tag(v_x_1838_) == 0)
{
uint8_t v___x_1839_; 
v___x_1839_ = 0;
return v___x_1839_;
}
else
{
lean_object* v_head_1840_; lean_object* v_tail_1841_; uint8_t v___x_1842_; 
v_head_1840_ = lean_ctor_get(v_x_1838_, 0);
v_tail_1841_ = lean_ctor_get(v_x_1838_, 1);
v___x_1842_ = l_Lean_instBEqMVarId_beq(v_a_1837_, v_head_1840_);
if (v___x_1842_ == 0)
{
v_x_1838_ = v_tail_1841_;
goto _start;
}
else
{
return v___x_1842_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_MVarId_apply_spec__2___boxed(lean_object* v_a_1844_, lean_object* v_x_1845_){
_start:
{
uint8_t v_res_1846_; lean_object* v_r_1847_; 
v_res_1846_ = l_List_elem___at___00Lean_MVarId_apply_spec__2(v_a_1844_, v_x_1845_);
lean_dec(v_x_1845_);
lean_dec(v_a_1844_);
v_r_1847_ = lean_box(v_res_1846_);
return v_r_1847_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(lean_object* v_a_1848_, lean_object* v_as_1849_, size_t v_i_1850_, size_t v_stop_1851_, lean_object* v_b_1852_){
_start:
{
lean_object* v___y_1854_; uint8_t v___x_1858_; 
v___x_1858_ = lean_usize_dec_eq(v_i_1850_, v_stop_1851_);
if (v___x_1858_ == 0)
{
lean_object* v___x_1859_; uint8_t v___x_1860_; 
v___x_1859_ = lean_array_uget_borrowed(v_as_1849_, v_i_1850_);
v___x_1860_ = l_List_elem___at___00Lean_MVarId_apply_spec__2(v___x_1859_, v_a_1848_);
if (v___x_1860_ == 0)
{
lean_object* v___x_1861_; 
lean_inc(v___x_1859_);
v___x_1861_ = lean_array_push(v_b_1852_, v___x_1859_);
v___y_1854_ = v___x_1861_;
goto v___jp_1853_;
}
else
{
v___y_1854_ = v_b_1852_;
goto v___jp_1853_;
}
}
else
{
return v_b_1852_;
}
v___jp_1853_:
{
size_t v___x_1855_; size_t v___x_1856_; 
v___x_1855_ = ((size_t)1ULL);
v___x_1856_ = lean_usize_add(v_i_1850_, v___x_1855_);
v_i_1850_ = v___x_1856_;
v_b_1852_ = v___y_1854_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4___boxed(lean_object* v_a_1862_, lean_object* v_as_1863_, lean_object* v_i_1864_, lean_object* v_stop_1865_, lean_object* v_b_1866_){
_start:
{
size_t v_i_boxed_1867_; size_t v_stop_boxed_1868_; lean_object* v_res_1869_; 
v_i_boxed_1867_ = lean_unbox_usize(v_i_1864_);
lean_dec(v_i_1864_);
v_stop_boxed_1868_ = lean_unbox_usize(v_stop_1865_);
lean_dec(v_stop_1865_);
v_res_1869_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(v_a_1862_, v_as_1863_, v_i_boxed_1867_, v_stop_boxed_1868_, v_b_1866_);
lean_dec_ref(v_as_1863_);
lean_dec(v_a_1862_);
return v_res_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___lam__0(lean_object* v_mvarId_1870_, lean_object* v___x_1871_, lean_object* v_e_1872_, lean_object* v_cfg_1873_, lean_object* v_term_x3f_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_){
_start:
{
lean_object* v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v___y_1885_; lean_object* v___y_1886_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v___y_1911_; lean_object* v___y_1912_; uint8_t v___y_1913_; lean_object* v___y_1914_; lean_object* v_a_1915_; lean_object* v___y_1948_; lean_object* v___y_1949_; lean_object* v___y_1950_; lean_object* v___y_1951_; lean_object* v___y_1952_; lean_object* v___y_1953_; uint8_t v___y_1954_; lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v___x_1966_; 
lean_inc(v___x_1871_);
lean_inc(v_mvarId_1870_);
v___x_1966_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1870_, v___x_1871_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v___x_1967_; 
lean_dec_ref_known(v___x_1966_, 1);
lean_inc(v_mvarId_1870_);
v___x_1967_ = l_Lean_MVarId_getType(v_mvarId_1870_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v_a_1968_; lean_object* v___x_1969_; 
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
lean_inc(v_a_1968_);
lean_dec_ref_known(v___x_1967_, 1);
lean_inc(v___y_1878_);
lean_inc_ref(v___y_1877_);
lean_inc(v___y_1876_);
lean_inc_ref(v___y_1875_);
lean_inc_ref(v_e_1872_);
v___x_1969_ = lean_infer_type(v_e_1872_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_object* v_a_1970_; lean_object* v_rangeNumArgs_1972_; lean_object* v_lower_1973_; lean_object* v___y_1974_; lean_object* v___y_1975_; lean_object* v___y_1976_; lean_object* v___y_1977_; lean_object* v___x_2017_; 
v_a_1970_ = lean_ctor_get(v___x_1969_, 0);
lean_inc_n(v_a_1970_, 2);
lean_dec_ref_known(v___x_1969_, 1);
v___x_2017_ = l_Lean_Meta_getExpectedNumArgsAux(v_a_1970_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_object* v_a_2018_; lean_object* v_snd_2019_; uint8_t v___x_2020_; 
v_a_2018_ = lean_ctor_get(v___x_2017_, 0);
lean_inc(v_a_2018_);
lean_dec_ref_known(v___x_2017_, 1);
v_snd_2019_ = lean_ctor_get(v_a_2018_, 1);
v___x_2020_ = lean_unbox(v_snd_2019_);
if (v___x_2020_ == 0)
{
lean_object* v_fst_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2041_; 
v_fst_2021_ = lean_ctor_get(v_a_2018_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v_a_2018_);
if (v_isSharedCheck_2041_ == 0)
{
lean_object* v_unused_2042_; 
v_unused_2042_ = lean_ctor_get(v_a_2018_, 1);
lean_dec(v_unused_2042_);
v___x_2023_ = v_a_2018_;
v_isShared_2024_ = v_isSharedCheck_2041_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_fst_2021_);
lean_dec(v_a_2018_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2041_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2025_; 
lean_inc(v_a_1968_);
v___x_2025_ = l_Lean_Meta_getExpectedNumArgs(v_a_1968_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
if (lean_obj_tag(v___x_2025_) == 0)
{
lean_object* v_a_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2031_; 
v_a_2026_ = lean_ctor_get(v___x_2025_, 0);
lean_inc(v_a_2026_);
lean_dec_ref_known(v___x_2025_, 1);
v___x_2027_ = lean_nat_sub(v_fst_2021_, v_a_2026_);
lean_dec(v_a_2026_);
v___x_2028_ = lean_unsigned_to_nat(1u);
v___x_2029_ = lean_nat_add(v_fst_2021_, v___x_2028_);
lean_dec(v_fst_2021_);
lean_inc(v___x_2027_);
if (v_isShared_2024_ == 0)
{
lean_ctor_set(v___x_2023_, 1, v___x_2029_);
lean_ctor_set(v___x_2023_, 0, v___x_2027_);
v___x_2031_ = v___x_2023_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v___x_2027_);
lean_ctor_set(v_reuseFailAlloc_2032_, 1, v___x_2029_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
v_rangeNumArgs_1972_ = v___x_2031_;
v_lower_1973_ = v___x_2027_;
v___y_1974_ = v___y_1875_;
v___y_1975_ = v___y_1876_;
v___y_1976_ = v___y_1877_;
v___y_1977_ = v___y_1878_;
goto v___jp_1971_;
}
}
else
{
lean_object* v_a_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2040_; 
lean_del_object(v___x_2023_);
lean_dec(v_fst_2021_);
lean_dec(v_a_1970_);
lean_dec(v_a_1968_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v_term_x3f_1874_);
lean_dec_ref(v_e_1872_);
lean_dec(v___x_1871_);
lean_dec(v_mvarId_1870_);
v_a_2033_ = lean_ctor_get(v___x_2025_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2035_ = v___x_2025_;
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_a_2033_);
lean_dec(v___x_2025_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2038_; 
if (v_isShared_2036_ == 0)
{
v___x_2038_ = v___x_2035_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_a_2033_);
v___x_2038_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
return v___x_2038_;
}
}
}
}
}
else
{
lean_object* v_fst_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2052_; 
v_fst_2043_ = lean_ctor_get(v_a_2018_, 0);
v_isSharedCheck_2052_ = !lean_is_exclusive(v_a_2018_);
if (v_isSharedCheck_2052_ == 0)
{
lean_object* v_unused_2053_; 
v_unused_2053_ = lean_ctor_get(v_a_2018_, 1);
lean_dec(v_unused_2053_);
v___x_2045_ = v_a_2018_;
v_isShared_2046_ = v_isSharedCheck_2052_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_fst_2043_);
lean_dec(v_a_2018_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2052_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2050_; 
v___x_2047_ = lean_unsigned_to_nat(1u);
v___x_2048_ = lean_nat_add(v_fst_2043_, v___x_2047_);
lean_inc(v_fst_2043_);
if (v_isShared_2046_ == 0)
{
lean_ctor_set(v___x_2045_, 1, v___x_2048_);
v___x_2050_ = v___x_2045_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_fst_2043_);
lean_ctor_set(v_reuseFailAlloc_2051_, 1, v___x_2048_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
v_rangeNumArgs_1972_ = v___x_2050_;
v_lower_1973_ = v_fst_2043_;
v___y_1974_ = v___y_1875_;
v___y_1975_ = v___y_1876_;
v___y_1976_ = v___y_1877_;
v___y_1977_ = v___y_1878_;
goto v___jp_1971_;
}
}
}
}
else
{
lean_object* v_a_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2061_; 
lean_dec(v_a_1970_);
lean_dec(v_a_1968_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v_term_x3f_1874_);
lean_dec_ref(v_e_1872_);
lean_dec(v___x_1871_);
lean_dec(v_mvarId_1870_);
v_a_2054_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2061_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_2056_ = v___x_2017_;
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_a_2054_);
lean_dec(v___x_2017_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2059_; 
if (v_isShared_2057_ == 0)
{
v___x_2059_ = v___x_2056_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_a_2054_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
return v___x_2059_;
}
}
}
v___jp_1971_:
{
lean_object* v___x_1978_; 
lean_inc(v_mvarId_1870_);
v___x_1978_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go(v_mvarId_1870_, v_cfg_1873_, v_term_x3f_1874_, v_a_1968_, v_a_1970_, v_rangeNumArgs_1972_, v_lower_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_);
lean_dec_ref(v_rangeNumArgs_1972_);
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_object* v_a_1979_; lean_object* v_fst_1980_; lean_object* v_snd_1981_; uint8_t v_newGoals_1982_; uint8_t v_synthAssignedInstances_1983_; uint8_t v_allowSynthFailures_1984_; lean_object* v___x_1985_; 
v_a_1979_ = lean_ctor_get(v___x_1978_, 0);
lean_inc(v_a_1979_);
lean_dec_ref_known(v___x_1978_, 1);
v_fst_1980_ = lean_ctor_get(v_a_1979_, 0);
lean_inc(v_fst_1980_);
v_snd_1981_ = lean_ctor_get(v_a_1979_, 1);
lean_inc_n(v_snd_1981_, 2);
lean_dec(v_a_1979_);
v_newGoals_1982_ = lean_ctor_get_uint8(v_cfg_1873_, 0);
v_synthAssignedInstances_1983_ = lean_ctor_get_uint8(v_cfg_1873_, 1);
v_allowSynthFailures_1984_ = lean_ctor_get_uint8(v_cfg_1873_, 2);
lean_inc(v_mvarId_1870_);
v___x_1985_ = l_Lean_Meta_synthAppInstances(v___x_1871_, v_mvarId_1870_, v_fst_1980_, v_snd_1981_, v_synthAssignedInstances_1983_, v_allowSynthFailures_1984_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_);
if (lean_obj_tag(v___x_1985_) == 0)
{
lean_object* v___x_1986_; lean_object* v_a_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; uint8_t v___x_1993_; 
lean_dec_ref_known(v___x_1985_, 1);
v___x_1986_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_e_1872_, v___y_1975_);
v_a_1987_ = lean_ctor_get(v___x_1986_, 0);
lean_inc_n(v_a_1987_, 2);
lean_dec_ref(v___x_1986_);
v___x_1988_ = l_Lean_mkAppN(v_a_1987_, v_fst_1980_);
lean_inc(v_mvarId_1870_);
v___x_1989_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_1870_, v___x_1988_, v___y_1975_);
lean_dec_ref(v___x_1989_);
v___x_1990_ = lean_unsigned_to_nat(0u);
v___x_1991_ = lean_array_get_size(v_fst_1980_);
v___x_1992_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0));
v___x_1993_ = lean_nat_dec_lt(v___x_1990_, v___x_1991_);
if (v___x_1993_ == 0)
{
lean_dec(v_fst_1980_);
v___y_1907_ = v___y_1974_;
v___y_1908_ = v_snd_1981_;
v___y_1909_ = v___y_1977_;
v___y_1910_ = v___x_1990_;
v___y_1911_ = v___y_1975_;
v___y_1912_ = v_a_1987_;
v___y_1913_ = v_newGoals_1982_;
v___y_1914_ = v___y_1976_;
v_a_1915_ = v___x_1992_;
goto v___jp_1906_;
}
else
{
uint8_t v___x_1994_; 
v___x_1994_ = lean_nat_dec_le(v___x_1991_, v___x_1991_);
if (v___x_1994_ == 0)
{
if (v___x_1993_ == 0)
{
lean_dec(v_fst_1980_);
v___y_1907_ = v___y_1974_;
v___y_1908_ = v_snd_1981_;
v___y_1909_ = v___y_1977_;
v___y_1910_ = v___x_1990_;
v___y_1911_ = v___y_1975_;
v___y_1912_ = v_a_1987_;
v___y_1913_ = v_newGoals_1982_;
v___y_1914_ = v___y_1976_;
v_a_1915_ = v___x_1992_;
goto v___jp_1906_;
}
else
{
size_t v___x_1995_; size_t v___x_1996_; lean_object* v___x_1997_; 
v___x_1995_ = ((size_t)0ULL);
v___x_1996_ = lean_usize_of_nat(v___x_1991_);
v___x_1997_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_fst_1980_, v___x_1995_, v___x_1996_, v___x_1992_, v___y_1975_);
lean_dec(v_fst_1980_);
v___y_1948_ = v___y_1974_;
v___y_1949_ = v_snd_1981_;
v___y_1950_ = v___y_1977_;
v___y_1951_ = v___y_1975_;
v___y_1952_ = v___x_1990_;
v___y_1953_ = v_a_1987_;
v___y_1954_ = v_newGoals_1982_;
v___y_1955_ = v___y_1976_;
v___y_1956_ = v___x_1997_;
goto v___jp_1947_;
}
}
else
{
size_t v___x_1998_; size_t v___x_1999_; lean_object* v___x_2000_; 
v___x_1998_ = ((size_t)0ULL);
v___x_1999_ = lean_usize_of_nat(v___x_1991_);
v___x_2000_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_fst_1980_, v___x_1998_, v___x_1999_, v___x_1992_, v___y_1975_);
lean_dec(v_fst_1980_);
v___y_1948_ = v___y_1974_;
v___y_1949_ = v_snd_1981_;
v___y_1950_ = v___y_1977_;
v___y_1951_ = v___y_1975_;
v___y_1952_ = v___x_1990_;
v___y_1953_ = v_a_1987_;
v___y_1954_ = v_newGoals_1982_;
v___y_1955_ = v___y_1976_;
v___y_1956_ = v___x_2000_;
goto v___jp_1947_;
}
}
}
else
{
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2008_; 
lean_dec(v_snd_1981_);
lean_dec(v_fst_1980_);
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
lean_dec_ref(v_e_1872_);
lean_dec(v_mvarId_1870_);
v_a_2001_ = lean_ctor_get(v___x_1985_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_2003_ = v___x_1985_;
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___x_1985_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2006_; 
if (v_isShared_2004_ == 0)
{
v___x_2006_ = v___x_2003_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_a_2001_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
}
else
{
lean_object* v_a_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2016_; 
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
lean_dec_ref(v_e_1872_);
lean_dec(v___x_1871_);
lean_dec(v_mvarId_1870_);
v_a_2009_ = lean_ctor_get(v___x_1978_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_2011_ = v___x_1978_;
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_a_2009_);
lean_dec(v___x_1978_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v___x_2014_; 
if (v_isShared_2012_ == 0)
{
v___x_2014_ = v___x_2011_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_a_2009_);
v___x_2014_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
return v___x_2014_;
}
}
}
}
}
else
{
lean_object* v_a_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2069_; 
lean_dec(v_a_1968_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v_term_x3f_1874_);
lean_dec_ref(v_e_1872_);
lean_dec(v___x_1871_);
lean_dec(v_mvarId_1870_);
v_a_2062_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2064_ = v___x_1969_;
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_a_2062_);
lean_dec(v___x_1969_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2067_; 
if (v_isShared_2065_ == 0)
{
v___x_2067_ = v___x_2064_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_a_2062_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
}
}
else
{
lean_object* v_a_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2077_; 
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v_term_x3f_1874_);
lean_dec_ref(v_e_1872_);
lean_dec(v___x_1871_);
lean_dec(v_mvarId_1870_);
v_a_2070_ = lean_ctor_get(v___x_1967_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2072_ = v___x_1967_;
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_a_2070_);
lean_dec(v___x_1967_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2075_; 
if (v_isShared_2073_ == 0)
{
v___x_2075_ = v___x_2072_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_a_2070_);
v___x_2075_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
return v___x_2075_;
}
}
}
}
else
{
lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2085_; 
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v_term_x3f_1874_);
lean_dec_ref(v_e_1872_);
lean_dec(v___x_1871_);
lean_dec(v_mvarId_1870_);
v_a_2078_ = lean_ctor_get(v___x_1966_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2080_ = v___x_1966_;
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_a_2078_);
lean_dec(v___x_1966_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2083_; 
if (v_isShared_2081_ == 0)
{
v___x_2083_ = v___x_2080_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_a_2078_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
v___jp_1880_:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1887_ = lean_array_to_list(v___y_1886_);
v___x_1888_ = l_List_appendTR___redArg(v___y_1884_, v___x_1887_);
lean_inc(v___x_1888_);
v___x_1889_ = l_List_forM___at___00Lean_MVarId_apply_spec__3(v___x_1888_, v___y_1881_, v___y_1883_, v___y_1885_, v___y_1882_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1885_);
lean_dec(v___y_1883_);
lean_dec_ref(v___y_1881_);
if (lean_obj_tag(v___x_1889_) == 0)
{
lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1896_; 
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1896_ == 0)
{
lean_object* v_unused_1897_; 
v_unused_1897_ = lean_ctor_get(v___x_1889_, 0);
lean_dec(v_unused_1897_);
v___x_1891_ = v___x_1889_;
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
else
{
lean_dec(v___x_1889_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1894_; 
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 0, v___x_1888_);
v___x_1894_ = v___x_1891_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v___x_1888_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
return v___x_1894_;
}
}
}
else
{
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
lean_dec(v___x_1888_);
v_a_1898_ = lean_ctor_get(v___x_1889_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1900_ = v___x_1889_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1889_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
if (v_isShared_1901_ == 0)
{
v___x_1903_ = v___x_1900_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1898_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
v___jp_1906_:
{
lean_object* v___x_1916_; 
v___x_1916_ = l_Lean_Meta_appendParentTag(v_mvarId_1870_, v_a_1915_, v___y_1908_, v___y_1907_, v___y_1911_, v___y_1914_, v___y_1909_);
lean_dec_ref(v___y_1908_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v___x_1917_; 
lean_dec_ref_known(v___x_1916_, 1);
v___x_1917_ = l_Lean_Meta_getMVarsNoDelayed(v___y_1912_, v___y_1907_, v___y_1911_, v___y_1914_, v___y_1909_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; lean_object* v___x_1919_; 
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_a_1918_);
lean_dec_ref_known(v___x_1917_, 1);
v___x_1919_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(v_a_1915_, v___y_1913_, v___y_1907_, v___y_1911_, v___y_1914_, v___y_1909_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_object* v_a_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; uint8_t v___x_1923_; 
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
lean_inc(v_a_1920_);
lean_dec_ref_known(v___x_1919_, 1);
v___x_1921_ = lean_array_get_size(v_a_1918_);
v___x_1922_ = lean_mk_empty_array_with_capacity(v___y_1910_);
v___x_1923_ = lean_nat_dec_lt(v___y_1910_, v___x_1921_);
if (v___x_1923_ == 0)
{
lean_dec(v_a_1918_);
v___y_1881_ = v___y_1907_;
v___y_1882_ = v___y_1909_;
v___y_1883_ = v___y_1911_;
v___y_1884_ = v_a_1920_;
v___y_1885_ = v___y_1914_;
v___y_1886_ = v___x_1922_;
goto v___jp_1880_;
}
else
{
uint8_t v___x_1924_; 
v___x_1924_ = lean_nat_dec_le(v___x_1921_, v___x_1921_);
if (v___x_1924_ == 0)
{
if (v___x_1923_ == 0)
{
lean_dec(v_a_1918_);
v___y_1881_ = v___y_1907_;
v___y_1882_ = v___y_1909_;
v___y_1883_ = v___y_1911_;
v___y_1884_ = v_a_1920_;
v___y_1885_ = v___y_1914_;
v___y_1886_ = v___x_1922_;
goto v___jp_1880_;
}
else
{
size_t v___x_1925_; size_t v___x_1926_; lean_object* v___x_1927_; 
v___x_1925_ = ((size_t)0ULL);
v___x_1926_ = lean_usize_of_nat(v___x_1921_);
v___x_1927_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(v_a_1920_, v_a_1918_, v___x_1925_, v___x_1926_, v___x_1922_);
lean_dec(v_a_1918_);
v___y_1881_ = v___y_1907_;
v___y_1882_ = v___y_1909_;
v___y_1883_ = v___y_1911_;
v___y_1884_ = v_a_1920_;
v___y_1885_ = v___y_1914_;
v___y_1886_ = v___x_1927_;
goto v___jp_1880_;
}
}
else
{
size_t v___x_1928_; size_t v___x_1929_; lean_object* v___x_1930_; 
v___x_1928_ = ((size_t)0ULL);
v___x_1929_ = lean_usize_of_nat(v___x_1921_);
v___x_1930_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(v_a_1920_, v_a_1918_, v___x_1928_, v___x_1929_, v___x_1922_);
lean_dec(v_a_1918_);
v___y_1881_ = v___y_1907_;
v___y_1882_ = v___y_1909_;
v___y_1883_ = v___y_1911_;
v___y_1884_ = v_a_1920_;
v___y_1885_ = v___y_1914_;
v___y_1886_ = v___x_1930_;
goto v___jp_1880_;
}
}
}
else
{
lean_dec(v_a_1918_);
lean_dec_ref(v___y_1914_);
lean_dec(v___y_1911_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1907_);
return v___x_1919_;
}
}
else
{
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1938_; 
lean_dec_ref(v_a_1915_);
lean_dec_ref(v___y_1914_);
lean_dec(v___y_1911_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1907_);
v_a_1931_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1933_ = v___x_1917_;
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___x_1917_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1936_; 
if (v_isShared_1934_ == 0)
{
v___x_1936_ = v___x_1933_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_a_1931_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
}
else
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1946_; 
lean_dec_ref(v_a_1915_);
lean_dec_ref(v___y_1914_);
lean_dec_ref(v___y_1912_);
lean_dec(v___y_1911_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1907_);
v_a_1939_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1941_ = v___x_1916_;
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1916_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1944_; 
if (v_isShared_1942_ == 0)
{
v___x_1944_ = v___x_1941_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_a_1939_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
}
v___jp_1947_:
{
if (lean_obj_tag(v___y_1956_) == 0)
{
lean_object* v_a_1957_; 
v_a_1957_ = lean_ctor_get(v___y_1956_, 0);
lean_inc(v_a_1957_);
lean_dec_ref_known(v___y_1956_, 1);
v___y_1907_ = v___y_1948_;
v___y_1908_ = v___y_1949_;
v___y_1909_ = v___y_1950_;
v___y_1910_ = v___y_1952_;
v___y_1911_ = v___y_1951_;
v___y_1912_ = v___y_1953_;
v___y_1913_ = v___y_1954_;
v___y_1914_ = v___y_1955_;
v_a_1915_ = v_a_1957_;
goto v___jp_1906_;
}
else
{
lean_object* v_a_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1965_; 
lean_dec_ref(v___y_1955_);
lean_dec_ref(v___y_1953_);
lean_dec(v___y_1951_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
lean_dec_ref(v___y_1948_);
lean_dec(v_mvarId_1870_);
v_a_1958_ = lean_ctor_get(v___y_1956_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___y_1956_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1960_ = v___y_1956_;
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_a_1958_);
lean_dec(v___y_1956_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1963_; 
if (v_isShared_1961_ == 0)
{
v___x_1963_ = v___x_1960_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_a_1958_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___lam__0___boxed(lean_object* v_mvarId_2086_, lean_object* v___x_2087_, lean_object* v_e_2088_, lean_object* v_cfg_2089_, lean_object* v_term_x3f_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_){
_start:
{
lean_object* v_res_2096_; 
v_res_2096_ = l_Lean_MVarId_apply___lam__0(v_mvarId_2086_, v___x_2087_, v_e_2088_, v_cfg_2089_, v_term_x3f_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
lean_dec_ref(v_cfg_2089_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply(lean_object* v_mvarId_2097_, lean_object* v_e_2098_, lean_object* v_cfg_2099_, lean_object* v_term_x3f_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_){
_start:
{
lean_object* v___x_2106_; lean_object* v___f_2107_; lean_object* v___x_2108_; 
v___x_2106_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1));
lean_inc(v_mvarId_2097_);
v___f_2107_ = lean_alloc_closure((void*)(l_Lean_MVarId_apply___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2107_, 0, v_mvarId_2097_);
lean_closure_set(v___f_2107_, 1, v___x_2106_);
lean_closure_set(v___f_2107_, 2, v_e_2098_);
lean_closure_set(v___f_2107_, 3, v_cfg_2099_);
lean_closure_set(v___f_2107_, 4, v_term_x3f_2100_);
v___x_2108_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2097_, v___f_2107_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_);
return v___x_2108_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___boxed(lean_object* v_mvarId_2109_, lean_object* v_e_2110_, lean_object* v_cfg_2111_, lean_object* v_term_x3f_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_){
_start:
{
lean_object* v_res_2118_; 
v_res_2118_ = l_Lean_MVarId_apply(v_mvarId_2109_, v_e_2110_, v_cfg_2111_, v_term_x3f_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_);
lean_dec(v_a_2116_);
lean_dec_ref(v_a_2115_);
lean_dec(v_a_2114_);
lean_dec_ref(v_a_2113_);
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1(lean_object* v_mvarId_2119_, lean_object* v_val_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_){
_start:
{
lean_object* v___x_2126_; 
v___x_2126_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2119_, v_val_2120_, v___y_2122_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___boxed(lean_object* v_mvarId_2127_, lean_object* v_val_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_){
_start:
{
lean_object* v_res_2134_; 
v_res_2134_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1(v_mvarId_2127_, v_val_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
return v_res_2134_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5(lean_object* v_as_2135_, size_t v_i_2136_, size_t v_stop_2137_, lean_object* v_b_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_){
_start:
{
lean_object* v___x_2144_; 
v___x_2144_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_as_2135_, v_i_2136_, v_stop_2137_, v_b_2138_, v___y_2140_);
return v___x_2144_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___boxed(lean_object* v_as_2145_, lean_object* v_i_2146_, lean_object* v_stop_2147_, lean_object* v_b_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_){
_start:
{
size_t v_i_boxed_2154_; size_t v_stop_boxed_2155_; lean_object* v_res_2156_; 
v_i_boxed_2154_ = lean_unbox_usize(v_i_2146_);
lean_dec(v_i_2146_);
v_stop_boxed_2155_ = lean_unbox_usize(v_stop_2147_);
lean_dec(v_stop_2147_);
v_res_2156_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5(v_as_2145_, v_i_boxed_2154_, v_stop_boxed_2155_, v_b_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
lean_dec(v___y_2152_);
lean_dec_ref(v___y_2151_);
lean_dec(v___y_2150_);
lean_dec_ref(v___y_2149_);
lean_dec_ref(v_as_2145_);
return v_res_2156_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1(lean_object* v_00_u03b2_2157_, lean_object* v_x_2158_, lean_object* v_x_2159_, lean_object* v_x_2160_){
_start:
{
lean_object* v___x_2161_; 
v___x_2161_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1___redArg(v_x_2158_, v_x_2159_, v_x_2160_);
return v___x_2161_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_2162_, lean_object* v_x_2163_, size_t v_x_2164_, size_t v_x_2165_, lean_object* v_x_2166_, lean_object* v_x_2167_){
_start:
{
lean_object* v___x_2168_; 
v___x_2168_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_x_2163_, v_x_2164_, v_x_2165_, v_x_2166_, v_x_2167_);
return v___x_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2169_, lean_object* v_x_2170_, lean_object* v_x_2171_, lean_object* v_x_2172_, lean_object* v_x_2173_, lean_object* v_x_2174_){
_start:
{
size_t v_x_7815__boxed_2175_; size_t v_x_7816__boxed_2176_; lean_object* v_res_2177_; 
v_x_7815__boxed_2175_ = lean_unbox_usize(v_x_2171_);
lean_dec(v_x_2171_);
v_x_7816__boxed_2176_ = lean_unbox_usize(v_x_2172_);
lean_dec(v_x_2172_);
v_res_2177_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3(v_00_u03b2_2169_, v_x_2170_, v_x_7815__boxed_2175_, v_x_7816__boxed_2176_, v_x_2173_, v_x_2174_);
return v_res_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_2178_, lean_object* v_n_2179_, lean_object* v_k_2180_, lean_object* v_v_2181_){
_start:
{
lean_object* v___x_2182_; 
v___x_2182_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8___redArg(v_n_2179_, v_k_2180_, v_v_2181_);
return v___x_2182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9(lean_object* v_00_u03b2_2183_, size_t v_depth_2184_, lean_object* v_keys_2185_, lean_object* v_vals_2186_, lean_object* v_heq_2187_, lean_object* v_i_2188_, lean_object* v_entries_2189_){
_start:
{
lean_object* v___x_2190_; 
v___x_2190_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(v_depth_2184_, v_keys_2185_, v_vals_2186_, v_i_2188_, v_entries_2189_);
return v___x_2190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___boxed(lean_object* v_00_u03b2_2191_, lean_object* v_depth_2192_, lean_object* v_keys_2193_, lean_object* v_vals_2194_, lean_object* v_heq_2195_, lean_object* v_i_2196_, lean_object* v_entries_2197_){
_start:
{
size_t v_depth_boxed_2198_; lean_object* v_res_2199_; 
v_depth_boxed_2198_ = lean_unbox_usize(v_depth_2192_);
lean_dec(v_depth_2192_);
v_res_2199_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9(v_00_u03b2_2191_, v_depth_boxed_2198_, v_keys_2193_, v_vals_2194_, v_heq_2195_, v_i_2196_, v_entries_2197_);
lean_dec_ref(v_vals_2194_);
lean_dec_ref(v_keys_2193_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9(lean_object* v_00_u03b2_2200_, lean_object* v_x_2201_, lean_object* v_x_2202_, lean_object* v_x_2203_, lean_object* v_x_2204_){
_start:
{
lean_object* v___x_2205_; 
v___x_2205_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9___redArg(v_x_2201_, v_x_2202_, v_x_2203_, v_x_2204_);
return v___x_2205_;
}
}
static lean_object* _init_l_Lean_MVarId_applyConst___closed__1(void){
_start:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2207_ = ((lean_object*)(l_Lean_MVarId_applyConst___closed__0));
v___x_2208_ = l_Lean_stringToMessageData(v___x_2207_);
return v___x_2208_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyConst(lean_object* v_mvar_2209_, lean_object* v_c_2210_, lean_object* v_cfg_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_){
_start:
{
lean_object* v___x_2217_; 
lean_inc(v_c_2210_);
v___x_2217_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_c_2210_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_object* v_a_2218_; lean_object* v___x_2219_; uint8_t v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
v_a_2218_ = lean_ctor_get(v___x_2217_, 0);
lean_inc(v_a_2218_);
lean_dec_ref_known(v___x_2217_, 1);
v___x_2219_ = lean_obj_once(&l_Lean_MVarId_applyConst___closed__1, &l_Lean_MVarId_applyConst___closed__1_once, _init_l_Lean_MVarId_applyConst___closed__1);
v___x_2220_ = 0;
v___x_2221_ = l_Lean_MessageData_ofConstName(v_c_2210_, v___x_2220_);
v___x_2222_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2219_);
lean_ctor_set(v___x_2222_, 1, v___x_2221_);
v___x_2223_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2222_);
lean_ctor_set(v___x_2223_, 1, v___x_2219_);
v___x_2224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2224_, 0, v___x_2223_);
v___x_2225_ = l_Lean_MVarId_apply(v_mvar_2209_, v_a_2218_, v_cfg_2211_, v___x_2224_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_);
return v___x_2225_;
}
else
{
lean_object* v_a_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2233_; 
lean_dec_ref(v_cfg_2211_);
lean_dec(v_c_2210_);
lean_dec(v_mvar_2209_);
v_a_2226_ = lean_ctor_get(v___x_2217_, 0);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2217_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2228_ = v___x_2217_;
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_a_2226_);
lean_dec(v___x_2217_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v___x_2231_; 
if (v_isShared_2229_ == 0)
{
v___x_2231_ = v___x_2228_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_a_2226_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyConst___boxed(lean_object* v_mvar_2234_, lean_object* v_c_2235_, lean_object* v_cfg_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_){
_start:
{
lean_object* v_res_2242_; 
v_res_2242_ = l_Lean_MVarId_applyConst(v_mvar_2234_, v_c_2235_, v_cfg_2236_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_);
lean_dec(v_a_2240_);
lean_dec_ref(v_a_2239_);
lean_dec(v_a_2238_);
lean_dec_ref(v_a_2237_);
return v_res_2242_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1(lean_object* v_msgData_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_){
_start:
{
lean_object* v___x_2249_; lean_object* v_env_2250_; lean_object* v___x_2251_; lean_object* v_toCold_2252_; lean_object* v_mctx_2253_; lean_object* v_lctx_2254_; lean_object* v_options_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2249_ = lean_st_ref_get(v___y_2247_);
v_env_2250_ = lean_ctor_get(v___x_2249_, 0);
lean_inc_ref(v_env_2250_);
lean_dec(v___x_2249_);
v___x_2251_ = lean_st_ref_get(v___y_2245_);
v_toCold_2252_ = lean_ctor_get(v___y_2246_, 0);
v_mctx_2253_ = lean_ctor_get(v___x_2251_, 0);
lean_inc_ref(v_mctx_2253_);
lean_dec(v___x_2251_);
v_lctx_2254_ = lean_ctor_get(v___y_2244_, 2);
v_options_2255_ = lean_ctor_get(v_toCold_2252_, 2);
lean_inc_ref(v_options_2255_);
lean_inc_ref(v_lctx_2254_);
v___x_2256_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2256_, 0, v_env_2250_);
lean_ctor_set(v___x_2256_, 1, v_mctx_2253_);
lean_ctor_set(v___x_2256_, 2, v_lctx_2254_);
lean_ctor_set(v___x_2256_, 3, v_options_2255_);
v___x_2257_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2257_, 0, v___x_2256_);
lean_ctor_set(v___x_2257_, 1, v_msgData_2243_);
v___x_2258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2257_);
return v___x_2258_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1___boxed(lean_object* v_msgData_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_){
_start:
{
lean_object* v_res_2265_; 
v_res_2265_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1(v_msgData_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
return v_res_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(lean_object* v_msg_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_){
_start:
{
lean_object* v_ref_2272_; lean_object* v___x_2273_; lean_object* v_a_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2282_; 
v_ref_2272_ = lean_ctor_get(v___y_2269_, 2);
v___x_2273_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1(v_msg_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_);
v_a_2274_ = lean_ctor_get(v___x_2273_, 0);
v_isSharedCheck_2282_ = !lean_is_exclusive(v___x_2273_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2276_ = v___x_2273_;
v_isShared_2277_ = v_isSharedCheck_2282_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_a_2274_);
lean_dec(v___x_2273_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2282_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v___x_2278_; lean_object* v___x_2280_; 
lean_inc(v_ref_2272_);
v___x_2278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2278_, 0, v_ref_2272_);
lean_ctor_set(v___x_2278_, 1, v_a_2274_);
if (v_isShared_2277_ == 0)
{
lean_ctor_set_tag(v___x_2276_, 1);
lean_ctor_set(v___x_2276_, 0, v___x_2278_);
v___x_2280_ = v___x_2276_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v___x_2278_);
v___x_2280_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
return v___x_2280_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg___boxed(lean_object* v_msg_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_){
_start:
{
lean_object* v_res_2289_; 
v_res_2289_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v_msg_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_);
lean_dec(v___y_2287_);
lean_dec_ref(v___y_2286_);
lean_dec(v___y_2285_);
lean_dec_ref(v___y_2284_);
return v_res_2289_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0(size_t v_sz_2290_, size_t v_i_2291_, lean_object* v_bs_2292_){
_start:
{
uint8_t v___x_2293_; 
v___x_2293_ = lean_usize_dec_lt(v_i_2291_, v_sz_2290_);
if (v___x_2293_ == 0)
{
return v_bs_2292_;
}
else
{
lean_object* v_v_2294_; lean_object* v___x_2295_; lean_object* v_bs_x27_2296_; lean_object* v___x_2297_; size_t v___x_2298_; size_t v___x_2299_; lean_object* v___x_2300_; 
v_v_2294_ = lean_array_uget(v_bs_2292_, v_i_2291_);
v___x_2295_ = lean_unsigned_to_nat(0u);
v_bs_x27_2296_ = lean_array_uset(v_bs_2292_, v_i_2291_, v___x_2295_);
v___x_2297_ = l_Lean_Expr_mvarId_x21(v_v_2294_);
lean_dec(v_v_2294_);
v___x_2298_ = ((size_t)1ULL);
v___x_2299_ = lean_usize_add(v_i_2291_, v___x_2298_);
v___x_2300_ = lean_array_uset(v_bs_x27_2296_, v_i_2291_, v___x_2297_);
v_i_2291_ = v___x_2299_;
v_bs_2292_ = v___x_2300_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0___boxed(lean_object* v_sz_2302_, lean_object* v_i_2303_, lean_object* v_bs_2304_){
_start:
{
size_t v_sz_boxed_2305_; size_t v_i_boxed_2306_; lean_object* v_res_2307_; 
v_sz_boxed_2305_ = lean_unbox_usize(v_sz_2302_);
lean_dec(v_sz_2302_);
v_i_boxed_2306_ = lean_unbox_usize(v_i_2303_);
lean_dec(v_i_2303_);
v_res_2307_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0(v_sz_boxed_2305_, v_i_boxed_2306_, v_bs_2304_);
return v_res_2307_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2309_; lean_object* v___x_2310_; 
v___x_2309_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__0));
v___x_2310_ = l_Lean_stringToMessageData(v___x_2309_);
return v___x_2310_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; 
v___x_2312_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__2));
v___x_2313_ = l_Lean_stringToMessageData(v___x_2312_);
return v___x_2313_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2315_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__4));
v___x_2316_ = l_Lean_stringToMessageData(v___x_2315_);
return v___x_2316_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__7(void){
_start:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2318_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__6));
v___x_2319_ = l_Lean_stringToMessageData(v___x_2318_);
return v___x_2319_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__9(void){
_start:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2321_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__8));
v___x_2322_ = l_Lean_stringToMessageData(v___x_2321_);
return v___x_2322_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__11(void){
_start:
{
lean_object* v___x_2324_; lean_object* v___x_2325_; 
v___x_2324_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__10));
v___x_2325_ = l_Lean_stringToMessageData(v___x_2324_);
return v___x_2325_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN___lam__0(lean_object* v_mvarId_2326_, lean_object* v___x_2327_, lean_object* v_e_2328_, lean_object* v_n_2329_, uint8_t v_useApproxDefEq_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_){
_start:
{
lean_object* v___x_2336_; 
lean_inc(v_mvarId_2326_);
v___x_2336_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2326_, v___x_2327_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v___x_2337_; 
lean_dec_ref_known(v___x_2336_, 1);
lean_inc(v_mvarId_2326_);
v___x_2337_ = l_Lean_MVarId_getType(v_mvarId_2326_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v_a_2338_; lean_object* v___x_2339_; 
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
lean_inc(v_a_2338_);
lean_dec_ref_known(v___x_2337_, 1);
lean_inc(v___y_2334_);
lean_inc_ref(v___y_2333_);
lean_inc(v___y_2332_);
lean_inc_ref(v___y_2331_);
lean_inc_ref(v_e_2328_);
v___x_2339_ = lean_infer_type(v_e_2328_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v_a_2340_; uint8_t v___x_2341_; lean_object* v___x_2342_; 
v_a_2340_ = lean_ctor_get(v___x_2339_, 0);
lean_inc(v_a_2340_);
lean_dec_ref_known(v___x_2339_, 1);
v___x_2341_ = 0;
lean_inc(v_n_2329_);
v___x_2342_ = l_Lean_Meta_forallMetaBoundedTelescope(v_a_2340_, v_n_2329_, v___x_2341_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_object* v_a_2343_; lean_object* v_fst_2344_; lean_object* v_snd_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2435_; 
v_a_2343_ = lean_ctor_get(v___x_2342_, 0);
lean_inc(v_a_2343_);
lean_dec_ref_known(v___x_2342_, 1);
v_fst_2344_ = lean_ctor_get(v_a_2343_, 0);
v_snd_2345_ = lean_ctor_get(v_a_2343_, 1);
v_isSharedCheck_2435_ = !lean_is_exclusive(v_a_2343_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2347_ = v_a_2343_;
v_isShared_2348_ = v_isSharedCheck_2435_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_snd_2345_);
lean_inc(v_fst_2344_);
lean_dec(v_a_2343_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2435_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___y_2350_; lean_object* v_snd_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2433_; 
v_snd_2365_ = lean_ctor_get(v_snd_2345_, 1);
v_isSharedCheck_2433_ = !lean_is_exclusive(v_snd_2345_);
if (v_isSharedCheck_2433_ == 0)
{
lean_object* v_unused_2434_; 
v_unused_2434_ = lean_ctor_get(v_snd_2345_, 0);
lean_dec(v_unused_2434_);
v___x_2367_ = v_snd_2345_;
v_isShared_2368_ = v_isSharedCheck_2433_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_snd_2365_);
lean_dec(v_snd_2345_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2433_;
goto v_resetjp_2366_;
}
v___jp_2349_:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2363_; 
lean_inc(v_fst_2344_);
v___x_2351_ = l_Lean_Expr_beta(v_e_2328_, v_fst_2344_);
v___x_2352_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2326_, v___x_2351_, v___y_2350_);
lean_dec(v___y_2350_);
v_isSharedCheck_2363_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2363_ == 0)
{
lean_object* v_unused_2364_; 
v_unused_2364_ = lean_ctor_get(v___x_2352_, 0);
lean_dec(v_unused_2364_);
v___x_2354_ = v___x_2352_;
v_isShared_2355_ = v_isSharedCheck_2363_;
goto v_resetjp_2353_;
}
else
{
lean_dec(v___x_2352_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2363_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
size_t v_sz_2356_; size_t v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2361_; 
v_sz_2356_ = lean_array_size(v_fst_2344_);
v___x_2357_ = ((size_t)0ULL);
v___x_2358_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0(v_sz_2356_, v___x_2357_, v_fst_2344_);
v___x_2359_ = lean_array_to_list(v___x_2358_);
if (v_isShared_2355_ == 0)
{
lean_ctor_set(v___x_2354_, 0, v___x_2359_);
v___x_2361_ = v___x_2354_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v___x_2359_);
v___x_2361_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
return v___x_2361_;
}
}
}
v_resetjp_2366_:
{
lean_object* v___y_2370_; lean_object* v___y_2371_; lean_object* v___y_2372_; lean_object* v___y_2373_; lean_object* v___x_2413_; uint8_t v___x_2414_; 
v___x_2413_ = lean_array_get_size(v_fst_2344_);
v___x_2414_ = lean_nat_dec_eq(v___x_2413_, v_n_2329_);
if (v___x_2414_ == 0)
{
lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v_a_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2432_; 
lean_del_object(v___x_2367_);
lean_del_object(v___x_2347_);
lean_dec(v_fst_2344_);
lean_dec(v_a_2338_);
lean_dec_ref(v_e_2328_);
lean_dec(v_mvarId_2326_);
v___x_2415_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__9, &l_Lean_MVarId_applyN___lam__0___closed__9_once, _init_l_Lean_MVarId_applyN___lam__0___closed__9);
v___x_2416_ = l_Nat_reprFast(v_n_2329_);
v___x_2417_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2417_, 0, v___x_2416_);
v___x_2418_ = l_Lean_MessageData_ofFormat(v___x_2417_);
v___x_2419_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2419_, 0, v___x_2415_);
lean_ctor_set(v___x_2419_, 1, v___x_2418_);
v___x_2420_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__11, &l_Lean_MVarId_applyN___lam__0___closed__11_once, _init_l_Lean_MVarId_applyN___lam__0___closed__11);
v___x_2421_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2421_, 0, v___x_2419_);
lean_ctor_set(v___x_2421_, 1, v___x_2420_);
v___x_2422_ = l_Lean_indentExpr(v_snd_2365_);
v___x_2423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2421_);
lean_ctor_set(v___x_2423_, 1, v___x_2422_);
v___x_2424_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_2423_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_);
lean_dec(v___y_2334_);
lean_dec_ref(v___y_2333_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
v_a_2425_ = lean_ctor_get(v___x_2424_, 0);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2427_ = v___x_2424_;
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_a_2425_);
lean_dec(v___x_2424_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2430_; 
if (v_isShared_2428_ == 0)
{
v___x_2430_ = v___x_2427_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v_a_2425_);
v___x_2430_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
return v___x_2430_;
}
}
}
else
{
v___y_2370_ = v___y_2331_;
v___y_2371_ = v___y_2332_;
v___y_2372_ = v___y_2333_;
v___y_2373_ = v___y_2334_;
goto v___jp_2369_;
}
v___jp_2369_:
{
lean_object* v___x_2374_; 
lean_inc(v_a_2338_);
lean_inc(v_snd_2365_);
v___x_2374_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(v_useApproxDefEq_2330_, v_snd_2365_, v_a_2338_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_);
if (lean_obj_tag(v___x_2374_) == 0)
{
lean_object* v_a_2375_; uint8_t v___x_2376_; 
v_a_2375_ = lean_ctor_get(v___x_2374_, 0);
lean_inc(v_a_2375_);
lean_dec_ref_known(v___x_2374_, 1);
v___x_2376_ = lean_unbox(v_a_2375_);
lean_dec(v_a_2375_);
if (v___x_2376_ == 0)
{
lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2380_; 
lean_dec(v_fst_2344_);
lean_dec_ref(v_e_2328_);
lean_dec(v_mvarId_2326_);
v___x_2377_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__1, &l_Lean_MVarId_applyN___lam__0___closed__1_once, _init_l_Lean_MVarId_applyN___lam__0___closed__1);
v___x_2378_ = l_Lean_indentExpr(v_a_2338_);
if (v_isShared_2368_ == 0)
{
lean_ctor_set_tag(v___x_2367_, 7);
lean_ctor_set(v___x_2367_, 1, v___x_2378_);
lean_ctor_set(v___x_2367_, 0, v___x_2377_);
v___x_2380_ = v___x_2367_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v___x_2377_);
lean_ctor_set(v_reuseFailAlloc_2404_, 1, v___x_2378_);
v___x_2380_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
lean_object* v___x_2381_; lean_object* v___x_2383_; 
v___x_2381_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__3, &l_Lean_MVarId_applyN___lam__0___closed__3_once, _init_l_Lean_MVarId_applyN___lam__0___closed__3);
if (v_isShared_2348_ == 0)
{
lean_ctor_set_tag(v___x_2347_, 7);
lean_ctor_set(v___x_2347_, 1, v___x_2381_);
lean_ctor_set(v___x_2347_, 0, v___x_2380_);
v___x_2383_ = v___x_2347_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v___x_2380_);
lean_ctor_set(v_reuseFailAlloc_2403_, 1, v___x_2381_);
v___x_2383_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v_a_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2402_; 
v___x_2384_ = l_Lean_indentExpr(v_snd_2365_);
v___x_2385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2385_, 0, v___x_2383_);
lean_ctor_set(v___x_2385_, 1, v___x_2384_);
v___x_2386_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__5, &l_Lean_MVarId_applyN___lam__0___closed__5_once, _init_l_Lean_MVarId_applyN___lam__0___closed__5);
v___x_2387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2385_);
lean_ctor_set(v___x_2387_, 1, v___x_2386_);
v___x_2388_ = l_Nat_reprFast(v_n_2329_);
v___x_2389_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2388_);
v___x_2390_ = l_Lean_MessageData_ofFormat(v___x_2389_);
v___x_2391_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2387_);
lean_ctor_set(v___x_2391_, 1, v___x_2390_);
v___x_2392_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__7, &l_Lean_MVarId_applyN___lam__0___closed__7_once, _init_l_Lean_MVarId_applyN___lam__0___closed__7);
v___x_2393_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2391_);
lean_ctor_set(v___x_2393_, 1, v___x_2392_);
v___x_2394_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_2393_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_);
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
lean_dec(v___y_2371_);
lean_dec_ref(v___y_2370_);
v_a_2395_ = lean_ctor_get(v___x_2394_, 0);
v_isSharedCheck_2402_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2397_ = v___x_2394_;
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_a_2395_);
lean_dec(v___x_2394_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2400_; 
if (v_isShared_2398_ == 0)
{
v___x_2400_ = v___x_2397_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v_a_2395_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
return v___x_2400_;
}
}
}
}
}
else
{
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
lean_dec_ref(v___y_2370_);
lean_del_object(v___x_2367_);
lean_dec(v_snd_2365_);
lean_del_object(v___x_2347_);
lean_dec(v_a_2338_);
lean_dec(v_n_2329_);
v___y_2350_ = v___y_2371_;
goto v___jp_2349_;
}
}
else
{
lean_object* v_a_2405_; lean_object* v___x_2407_; uint8_t v_isShared_2408_; uint8_t v_isSharedCheck_2412_; 
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
lean_dec(v___y_2371_);
lean_dec_ref(v___y_2370_);
lean_del_object(v___x_2367_);
lean_dec(v_snd_2365_);
lean_del_object(v___x_2347_);
lean_dec(v_fst_2344_);
lean_dec(v_a_2338_);
lean_dec(v_n_2329_);
lean_dec_ref(v_e_2328_);
lean_dec(v_mvarId_2326_);
v_a_2405_ = lean_ctor_get(v___x_2374_, 0);
v_isSharedCheck_2412_ = !lean_is_exclusive(v___x_2374_);
if (v_isSharedCheck_2412_ == 0)
{
v___x_2407_ = v___x_2374_;
v_isShared_2408_ = v_isSharedCheck_2412_;
goto v_resetjp_2406_;
}
else
{
lean_inc(v_a_2405_);
lean_dec(v___x_2374_);
v___x_2407_ = lean_box(0);
v_isShared_2408_ = v_isSharedCheck_2412_;
goto v_resetjp_2406_;
}
v_resetjp_2406_:
{
lean_object* v___x_2410_; 
if (v_isShared_2408_ == 0)
{
v___x_2410_ = v___x_2407_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v_a_2405_);
v___x_2410_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
return v___x_2410_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2443_; 
lean_dec(v_a_2338_);
lean_dec(v___y_2334_);
lean_dec_ref(v___y_2333_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec(v_n_2329_);
lean_dec_ref(v_e_2328_);
lean_dec(v_mvarId_2326_);
v_a_2436_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2438_ = v___x_2342_;
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_dec(v___x_2342_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2441_; 
if (v_isShared_2439_ == 0)
{
v___x_2441_ = v___x_2438_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_a_2436_);
v___x_2441_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
return v___x_2441_;
}
}
}
}
else
{
lean_object* v_a_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2451_; 
lean_dec(v_a_2338_);
lean_dec(v___y_2334_);
lean_dec_ref(v___y_2333_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec(v_n_2329_);
lean_dec_ref(v_e_2328_);
lean_dec(v_mvarId_2326_);
v_a_2444_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2446_ = v___x_2339_;
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_a_2444_);
lean_dec(v___x_2339_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v___x_2449_; 
if (v_isShared_2447_ == 0)
{
v___x_2449_ = v___x_2446_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v_a_2444_);
v___x_2449_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
return v___x_2449_;
}
}
}
}
else
{
lean_object* v_a_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2459_; 
lean_dec(v___y_2334_);
lean_dec_ref(v___y_2333_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec(v_n_2329_);
lean_dec_ref(v_e_2328_);
lean_dec(v_mvarId_2326_);
v_a_2452_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2454_ = v___x_2337_;
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_a_2452_);
lean_dec(v___x_2337_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2457_; 
if (v_isShared_2455_ == 0)
{
v___x_2457_ = v___x_2454_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v_a_2452_);
v___x_2457_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
return v___x_2457_;
}
}
}
}
else
{
lean_object* v_a_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2467_; 
lean_dec(v___y_2334_);
lean_dec_ref(v___y_2333_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec(v_n_2329_);
lean_dec_ref(v_e_2328_);
lean_dec(v_mvarId_2326_);
v_a_2460_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2462_ = v___x_2336_;
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_a_2460_);
lean_dec(v___x_2336_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2465_; 
if (v_isShared_2463_ == 0)
{
v___x_2465_ = v___x_2462_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_a_2460_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
return v___x_2465_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN___lam__0___boxed(lean_object* v_mvarId_2468_, lean_object* v___x_2469_, lean_object* v_e_2470_, lean_object* v_n_2471_, lean_object* v_useApproxDefEq_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_){
_start:
{
uint8_t v_useApproxDefEq_boxed_2478_; lean_object* v_res_2479_; 
v_useApproxDefEq_boxed_2478_ = lean_unbox(v_useApproxDefEq_2472_);
v_res_2479_ = l_Lean_MVarId_applyN___lam__0(v_mvarId_2468_, v___x_2469_, v_e_2470_, v_n_2471_, v_useApproxDefEq_boxed_2478_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_);
return v_res_2479_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN(lean_object* v_mvarId_2480_, lean_object* v_e_2481_, lean_object* v_n_2482_, uint8_t v_useApproxDefEq_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_){
_start:
{
lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___f_2491_; lean_object* v___x_2492_; 
v___x_2489_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1));
v___x_2490_ = lean_box(v_useApproxDefEq_2483_);
lean_inc(v_mvarId_2480_);
v___f_2491_ = lean_alloc_closure((void*)(l_Lean_MVarId_applyN___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2491_, 0, v_mvarId_2480_);
lean_closure_set(v___f_2491_, 1, v___x_2489_);
lean_closure_set(v___f_2491_, 2, v_e_2481_);
lean_closure_set(v___f_2491_, 3, v_n_2482_);
lean_closure_set(v___f_2491_, 4, v___x_2490_);
v___x_2492_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2480_, v___f_2491_, v_a_2484_, v_a_2485_, v_a_2486_, v_a_2487_);
return v___x_2492_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN___boxed(lean_object* v_mvarId_2493_, lean_object* v_e_2494_, lean_object* v_n_2495_, lean_object* v_useApproxDefEq_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_){
_start:
{
uint8_t v_useApproxDefEq_boxed_2502_; lean_object* v_res_2503_; 
v_useApproxDefEq_boxed_2502_ = lean_unbox(v_useApproxDefEq_2496_);
v_res_2503_ = l_Lean_MVarId_applyN(v_mvarId_2493_, v_e_2494_, v_n_2495_, v_useApproxDefEq_boxed_2502_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_);
lean_dec(v_a_2500_);
lean_dec_ref(v_a_2499_);
lean_dec(v_a_2498_);
lean_dec_ref(v_a_2497_);
return v_res_2503_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1(lean_object* v_00_u03b1_2504_, lean_object* v_msg_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_){
_start:
{
lean_object* v___x_2511_; 
v___x_2511_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v_msg_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_);
return v___x_2511_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___boxed(lean_object* v_00_u03b1_2512_, lean_object* v_msg_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_){
_start:
{
lean_object* v_res_2519_; 
v_res_2519_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1(v_00_u03b1_2512_, v_msg_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_);
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
lean_dec(v___y_2515_);
lean_dec_ref(v___y_2514_);
return v_res_2519_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6(void){
_start:
{
lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2530_ = lean_box(0);
v___x_2531_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__5));
v___x_2532_ = l_Lean_mkConst(v___x_2531_, v___x_2530_);
return v___x_2532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(lean_object* v_tag_2533_, lean_object* v_type_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_){
_start:
{
lean_object* v___x_2541_; 
lean_inc(v_a_2539_);
lean_inc_ref(v_a_2538_);
lean_inc(v_a_2537_);
lean_inc_ref(v_a_2536_);
v___x_2541_ = lean_whnf(v_type_2534_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_);
if (lean_obj_tag(v___x_2541_) == 0)
{
lean_object* v_a_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; uint8_t v___x_2545_; 
v_a_2542_ = lean_ctor_get(v___x_2541_, 0);
lean_inc(v_a_2542_);
lean_dec_ref_known(v___x_2541_, 1);
v___x_2543_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__1));
v___x_2544_ = lean_unsigned_to_nat(2u);
v___x_2545_ = l_Lean_Expr_isAppOfArity(v_a_2542_, v___x_2543_, v___x_2544_);
if (v___x_2545_ == 0)
{
lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; 
v___x_2546_ = lean_st_ref_get(v_a_2535_);
v___x_2547_ = lean_array_get_size(v___x_2546_);
lean_dec(v___x_2546_);
v___x_2548_ = lean_unsigned_to_nat(1u);
v___x_2549_ = lean_nat_add(v___x_2547_, v___x_2548_);
v___x_2550_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__3));
v___x_2551_ = lean_name_append_index_after(v___x_2550_, v___x_2549_);
v___x_2552_ = l_Lean_Name_append(v_tag_2533_, v___x_2551_);
v___x_2553_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_2542_, v___x_2552_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_);
if (lean_obj_tag(v___x_2553_) == 0)
{
lean_object* v_a_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2565_; 
v_a_2554_ = lean_ctor_get(v___x_2553_, 0);
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2556_ = v___x_2553_;
v_isShared_2557_ = v_isSharedCheck_2565_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_a_2554_);
lean_dec(v___x_2553_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2565_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2563_; 
v___x_2558_ = lean_st_ref_take(v_a_2535_);
v___x_2559_ = l_Lean_Expr_mvarId_x21(v_a_2554_);
v___x_2560_ = lean_array_push(v___x_2558_, v___x_2559_);
v___x_2561_ = lean_st_ref_put(v_a_2535_, v___x_2560_);
if (v_isShared_2557_ == 0)
{
v___x_2563_ = v___x_2556_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v_a_2554_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
return v___x_2563_;
}
}
}
else
{
return v___x_2553_;
}
}
else
{
lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; 
v___x_2566_ = l_Lean_Expr_appFn_x21(v_a_2542_);
v___x_2567_ = l_Lean_Expr_appArg_x21(v___x_2566_);
lean_dec_ref(v___x_2566_);
v___x_2568_ = l_Lean_Expr_appArg_x21(v_a_2542_);
lean_dec(v_a_2542_);
lean_inc_ref(v___x_2567_);
lean_inc(v_tag_2533_);
v___x_2569_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_tag_2533_, v___x_2567_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_);
if (lean_obj_tag(v___x_2569_) == 0)
{
lean_object* v_a_2570_; lean_object* v___x_2571_; 
v_a_2570_ = lean_ctor_get(v___x_2569_, 0);
lean_inc(v_a_2570_);
lean_dec_ref_known(v___x_2569_, 1);
lean_inc_ref(v___x_2568_);
v___x_2571_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_tag_2533_, v___x_2568_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_);
if (lean_obj_tag(v___x_2571_) == 0)
{
lean_object* v_a_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2581_; 
v_a_2572_ = lean_ctor_get(v___x_2571_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2574_ = v___x_2571_;
v_isShared_2575_ = v_isSharedCheck_2581_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_a_2572_);
lean_dec(v___x_2571_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2581_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2579_; 
v___x_2576_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6, &l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6);
v___x_2577_ = l_Lean_mkApp4(v___x_2576_, v___x_2567_, v___x_2568_, v_a_2570_, v_a_2572_);
if (v_isShared_2575_ == 0)
{
lean_ctor_set(v___x_2574_, 0, v___x_2577_);
v___x_2579_ = v___x_2574_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v___x_2577_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
else
{
lean_dec(v_a_2570_);
lean_dec_ref(v___x_2568_);
lean_dec_ref(v___x_2567_);
return v___x_2571_;
}
}
else
{
lean_dec_ref(v___x_2568_);
lean_dec_ref(v___x_2567_);
lean_dec(v_tag_2533_);
return v___x_2569_;
}
}
}
else
{
lean_dec(v_tag_2533_);
return v___x_2541_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___boxed(lean_object* v_tag_2582_, lean_object* v_type_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_){
_start:
{
lean_object* v_res_2590_; 
v_res_2590_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_tag_2582_, v_type_2583_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_);
lean_dec(v_a_2588_);
lean_dec_ref(v_a_2587_);
lean_dec(v_a_2586_);
lean_dec_ref(v_a_2585_);
lean_dec(v_a_2584_);
return v_res_2590_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore___lam__0(lean_object* v_mvarId_2591_, lean_object* v___x_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_){
_start:
{
lean_object* v___x_2598_; 
lean_inc(v_mvarId_2591_);
v___x_2598_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2591_, v___x_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_);
if (lean_obj_tag(v___x_2598_) == 0)
{
lean_object* v___x_2599_; 
lean_dec_ref_known(v___x_2598_, 1);
lean_inc(v_mvarId_2591_);
v___x_2599_ = l_Lean_MVarId_getType_x27(v_mvarId_2591_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_);
if (lean_obj_tag(v___x_2599_) == 0)
{
lean_object* v_a_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2645_; 
v_a_2600_ = lean_ctor_get(v___x_2599_, 0);
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2599_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2602_ = v___x_2599_;
v_isShared_2603_ = v_isSharedCheck_2645_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_a_2600_);
lean_dec(v___x_2599_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2645_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v___x_2604_; lean_object* v___x_2605_; uint8_t v___x_2606_; 
v___x_2604_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__1));
v___x_2605_ = lean_unsigned_to_nat(2u);
v___x_2606_ = l_Lean_Expr_isAppOfArity(v_a_2600_, v___x_2604_, v___x_2605_);
if (v___x_2606_ == 0)
{
lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2610_; 
lean_dec(v_a_2600_);
v___x_2607_ = lean_box(0);
v___x_2608_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2608_, 0, v_mvarId_2591_);
lean_ctor_set(v___x_2608_, 1, v___x_2607_);
if (v_isShared_2603_ == 0)
{
lean_ctor_set(v___x_2602_, 0, v___x_2608_);
v___x_2610_ = v___x_2602_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v___x_2608_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
return v___x_2610_;
}
}
else
{
lean_object* v___x_2612_; 
lean_del_object(v___x_2602_);
lean_inc(v_mvarId_2591_);
v___x_2612_ = l_Lean_MVarId_getTag(v_mvarId_2591_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_);
if (lean_obj_tag(v___x_2612_) == 0)
{
lean_object* v_a_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; 
v_a_2613_ = lean_ctor_get(v___x_2612_, 0);
lean_inc(v_a_2613_);
lean_dec_ref_known(v___x_2612_, 1);
v___x_2614_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__0));
v___x_2615_ = lean_st_mk_ref(v___x_2614_);
v___x_2616_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_a_2613_, v_a_2600_, v___x_2615_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_);
if (lean_obj_tag(v___x_2616_) == 0)
{
lean_object* v_a_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2627_; 
v_a_2617_ = lean_ctor_get(v___x_2616_, 0);
lean_inc(v_a_2617_);
lean_dec_ref_known(v___x_2616_, 1);
v___x_2618_ = lean_st_ref_get(v___x_2615_);
lean_dec(v___x_2615_);
v___x_2619_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2591_, v_a_2617_, v___y_2594_);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2619_);
if (v_isSharedCheck_2627_ == 0)
{
lean_object* v_unused_2628_; 
v_unused_2628_ = lean_ctor_get(v___x_2619_, 0);
lean_dec(v_unused_2628_);
v___x_2621_ = v___x_2619_;
v_isShared_2622_ = v_isSharedCheck_2627_;
goto v_resetjp_2620_;
}
else
{
lean_dec(v___x_2619_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2627_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2623_; lean_object* v___x_2625_; 
v___x_2623_ = lean_array_to_list(v___x_2618_);
if (v_isShared_2622_ == 0)
{
lean_ctor_set(v___x_2621_, 0, v___x_2623_);
v___x_2625_ = v___x_2621_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v___x_2623_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
}
}
}
else
{
lean_object* v_a_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2636_; 
lean_dec(v___x_2615_);
lean_dec(v_mvarId_2591_);
v_a_2629_ = lean_ctor_get(v___x_2616_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2616_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2631_ = v___x_2616_;
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_a_2629_);
lean_dec(v___x_2616_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___x_2634_; 
if (v_isShared_2632_ == 0)
{
v___x_2634_ = v___x_2631_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_a_2629_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
}
}
else
{
lean_object* v_a_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2644_; 
lean_dec(v_a_2600_);
lean_dec(v_mvarId_2591_);
v_a_2637_ = lean_ctor_get(v___x_2612_, 0);
v_isSharedCheck_2644_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2639_ = v___x_2612_;
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_a_2637_);
lean_dec(v___x_2612_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___x_2642_; 
if (v_isShared_2640_ == 0)
{
v___x_2642_ = v___x_2639_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_a_2637_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
return v___x_2642_;
}
}
}
}
}
}
else
{
lean_object* v_a_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2653_; 
lean_dec(v_mvarId_2591_);
v_a_2646_ = lean_ctor_get(v___x_2599_, 0);
v_isSharedCheck_2653_ = !lean_is_exclusive(v___x_2599_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2648_ = v___x_2599_;
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_a_2646_);
lean_dec(v___x_2599_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v___x_2651_; 
if (v_isShared_2649_ == 0)
{
v___x_2651_ = v___x_2648_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v_a_2646_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
}
}
else
{
lean_object* v_a_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2661_; 
lean_dec(v_mvarId_2591_);
v_a_2654_ = lean_ctor_get(v___x_2598_, 0);
v_isSharedCheck_2661_ = !lean_is_exclusive(v___x_2598_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2656_ = v___x_2598_;
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_a_2654_);
lean_dec(v___x_2598_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2659_; 
if (v_isShared_2657_ == 0)
{
v___x_2659_ = v___x_2656_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_a_2654_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore___lam__0___boxed(lean_object* v_mvarId_2662_, lean_object* v___x_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_){
_start:
{
lean_object* v_res_2669_; 
v_res_2669_ = l_Lean_MVarId_splitAndCore___lam__0(v_mvarId_2662_, v___x_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_);
lean_dec(v___y_2667_);
lean_dec_ref(v___y_2666_);
lean_dec(v___y_2665_);
lean_dec_ref(v___y_2664_);
return v_res_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore(lean_object* v_mvarId_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_){
_start:
{
lean_object* v___x_2679_; lean_object* v___f_2680_; lean_object* v___x_2681_; 
v___x_2679_ = ((lean_object*)(l_Lean_MVarId_splitAndCore___closed__1));
lean_inc(v_mvarId_2673_);
v___f_2680_ = lean_alloc_closure((void*)(l_Lean_MVarId_splitAndCore___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2680_, 0, v_mvarId_2673_);
lean_closure_set(v___f_2680_, 1, v___x_2679_);
v___x_2681_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2673_, v___f_2680_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_);
return v___x_2681_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore___boxed(lean_object* v_mvarId_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_){
_start:
{
lean_object* v_res_2688_; 
v_res_2688_ = l_Lean_MVarId_splitAndCore(v_mvarId_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_);
lean_dec(v_a_2686_);
lean_dec_ref(v_a_2685_);
lean_dec(v_a_2684_);
lean_dec_ref(v_a_2683_);
return v_res_2688_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAnd(lean_object* v_mvarId_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_){
_start:
{
lean_object* v___x_2695_; 
v___x_2695_ = l_Lean_MVarId_splitAndCore(v_mvarId_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_);
return v___x_2695_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAnd___boxed(lean_object* v_mvarId_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_){
_start:
{
lean_object* v_res_2702_; 
v_res_2702_ = l_Lean_MVarId_splitAnd(v_mvarId_2696_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_);
lean_dec(v_a_2700_);
lean_dec_ref(v_a_2699_);
lean_dec(v_a_2698_);
lean_dec_ref(v_a_2697_);
return v_res_2702_;
}
}
static lean_object* _init_l_Lean_MVarId_exfalso___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; 
v___x_2706_ = lean_box(0);
v___x_2707_ = ((lean_object*)(l_Lean_MVarId_exfalso___lam__0___closed__1));
v___x_2708_ = l_Lean_mkConst(v___x_2707_, v___x_2706_);
return v___x_2708_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso___lam__0(lean_object* v_mvarId_2713_, lean_object* v___x_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_){
_start:
{
lean_object* v___x_2720_; 
lean_inc(v_mvarId_2713_);
v___x_2720_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2713_, v___x_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
if (lean_obj_tag(v___x_2720_) == 0)
{
lean_object* v___x_2721_; 
lean_dec_ref_known(v___x_2720_, 1);
lean_inc(v_mvarId_2713_);
v___x_2721_ = l_Lean_MVarId_getType(v_mvarId_2713_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
if (lean_obj_tag(v___x_2721_) == 0)
{
lean_object* v_a_2722_; lean_object* v___x_2723_; lean_object* v_a_2724_; lean_object* v___x_2725_; 
v_a_2722_ = lean_ctor_get(v___x_2721_, 0);
lean_inc(v_a_2722_);
lean_dec_ref_known(v___x_2721_, 1);
v___x_2723_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_a_2722_, v___y_2716_);
v_a_2724_ = lean_ctor_get(v___x_2723_, 0);
lean_inc_n(v_a_2724_, 2);
lean_dec_ref(v___x_2723_);
v___x_2725_ = l_Lean_Meta_getLevel(v_a_2724_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
if (lean_obj_tag(v___x_2725_) == 0)
{
lean_object* v_a_2726_; lean_object* v___x_2727_; 
v_a_2726_ = lean_ctor_get(v___x_2725_, 0);
lean_inc(v_a_2726_);
lean_dec_ref_known(v___x_2725_, 1);
lean_inc(v_mvarId_2713_);
v___x_2727_ = l_Lean_MVarId_getTag(v_mvarId_2713_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
if (lean_obj_tag(v___x_2727_) == 0)
{
lean_object* v_a_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; 
v_a_2728_ = lean_ctor_get(v___x_2727_, 0);
lean_inc(v_a_2728_);
lean_dec_ref_known(v___x_2727_, 1);
v___x_2729_ = lean_box(0);
v___x_2730_ = lean_obj_once(&l_Lean_MVarId_exfalso___lam__0___closed__2, &l_Lean_MVarId_exfalso___lam__0___closed__2_once, _init_l_Lean_MVarId_exfalso___lam__0___closed__2);
v___x_2731_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_2730_, v_a_2728_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
if (lean_obj_tag(v___x_2731_) == 0)
{
lean_object* v_a_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2745_; 
v_a_2732_ = lean_ctor_get(v___x_2731_, 0);
lean_inc_n(v_a_2732_, 2);
lean_dec_ref_known(v___x_2731_, 1);
v___x_2733_ = ((lean_object*)(l_Lean_MVarId_exfalso___lam__0___closed__4));
v___x_2734_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2734_, 0, v_a_2726_);
lean_ctor_set(v___x_2734_, 1, v___x_2729_);
v___x_2735_ = l_Lean_mkConst(v___x_2733_, v___x_2734_);
v___x_2736_ = l_Lean_mkAppB(v___x_2735_, v_a_2724_, v_a_2732_);
v___x_2737_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2713_, v___x_2736_, v___y_2716_);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___x_2737_);
if (v_isSharedCheck_2745_ == 0)
{
lean_object* v_unused_2746_; 
v_unused_2746_ = lean_ctor_get(v___x_2737_, 0);
lean_dec(v_unused_2746_);
v___x_2739_ = v___x_2737_;
v_isShared_2740_ = v_isSharedCheck_2745_;
goto v_resetjp_2738_;
}
else
{
lean_dec(v___x_2737_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2745_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v___x_2741_; lean_object* v___x_2743_; 
v___x_2741_ = l_Lean_Expr_mvarId_x21(v_a_2732_);
lean_dec(v_a_2732_);
if (v_isShared_2740_ == 0)
{
lean_ctor_set(v___x_2739_, 0, v___x_2741_);
v___x_2743_ = v___x_2739_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v___x_2741_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
}
else
{
lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2754_; 
lean_dec(v_a_2726_);
lean_dec(v_a_2724_);
lean_dec(v_mvarId_2713_);
v_a_2747_ = lean_ctor_get(v___x_2731_, 0);
v_isSharedCheck_2754_ = !lean_is_exclusive(v___x_2731_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2749_ = v___x_2731_;
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_dec(v___x_2731_);
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
lean_dec(v_a_2726_);
lean_dec(v_a_2724_);
lean_dec(v_mvarId_2713_);
v_a_2755_ = lean_ctor_get(v___x_2727_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2727_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2757_ = v___x_2727_;
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_dec(v___x_2727_);
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
else
{
lean_object* v_a_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2770_; 
lean_dec(v_a_2724_);
lean_dec(v_mvarId_2713_);
v_a_2763_ = lean_ctor_get(v___x_2725_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2765_ = v___x_2725_;
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_a_2763_);
lean_dec(v___x_2725_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___x_2768_; 
if (v_isShared_2766_ == 0)
{
v___x_2768_ = v___x_2765_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v_a_2763_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
}
}
else
{
lean_object* v_a_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2778_; 
lean_dec(v_mvarId_2713_);
v_a_2771_ = lean_ctor_get(v___x_2721_, 0);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2721_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2773_ = v___x_2721_;
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_a_2771_);
lean_dec(v___x_2721_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v___x_2776_; 
if (v_isShared_2774_ == 0)
{
v___x_2776_ = v___x_2773_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_a_2771_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
}
}
else
{
lean_object* v_a_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2786_; 
lean_dec(v_mvarId_2713_);
v_a_2779_ = lean_ctor_get(v___x_2720_, 0);
v_isSharedCheck_2786_ = !lean_is_exclusive(v___x_2720_);
if (v_isSharedCheck_2786_ == 0)
{
v___x_2781_ = v___x_2720_;
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_a_2779_);
lean_dec(v___x_2720_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v___x_2784_; 
if (v_isShared_2782_ == 0)
{
v___x_2784_ = v___x_2781_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_a_2779_);
v___x_2784_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
return v___x_2784_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso___lam__0___boxed(lean_object* v_mvarId_2787_, lean_object* v___x_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_){
_start:
{
lean_object* v_res_2794_; 
v_res_2794_ = l_Lean_MVarId_exfalso___lam__0(v_mvarId_2787_, v___x_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_);
lean_dec(v___y_2792_);
lean_dec_ref(v___y_2791_);
lean_dec(v___y_2790_);
lean_dec_ref(v___y_2789_);
return v_res_2794_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso(lean_object* v_mvarId_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_){
_start:
{
lean_object* v___x_2804_; lean_object* v___f_2805_; lean_object* v___x_2806_; 
v___x_2804_ = ((lean_object*)(l_Lean_MVarId_exfalso___closed__1));
lean_inc(v_mvarId_2798_);
v___f_2805_ = lean_alloc_closure((void*)(l_Lean_MVarId_exfalso___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2805_, 0, v_mvarId_2798_);
lean_closure_set(v___f_2805_, 1, v___x_2804_);
v___x_2806_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2798_, v___f_2805_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_);
return v___x_2806_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso___boxed(lean_object* v_mvarId_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_){
_start:
{
lean_object* v_res_2813_; 
v_res_2813_ = l_Lean_MVarId_exfalso(v_mvarId_2807_, v_a_2808_, v_a_2809_, v_a_2810_, v_a_2811_);
lean_dec(v_a_2811_);
lean_dec_ref(v_a_2810_);
lean_dec(v_a_2809_);
lean_dec_ref(v_a_2808_);
return v_res_2813_;
}
}
static lean_object* _init_l_Lean_MVarId_nthConstructor___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2817_; lean_object* v___x_2818_; 
v___x_2817_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__1));
v___x_2818_ = l_Lean_MessageData_ofFormat(v___x_2817_);
return v___x_2818_;
}
}
static lean_object* _init_l_Lean_MVarId_nthConstructor___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2819_; lean_object* v___x_2820_; 
v___x_2819_ = lean_obj_once(&l_Lean_MVarId_nthConstructor___lam__0___closed__2, &l_Lean_MVarId_nthConstructor___lam__0___closed__2_once, _init_l_Lean_MVarId_nthConstructor___lam__0___closed__2);
v___x_2820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2820_, 0, v___x_2819_);
return v___x_2820_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___lam__0(lean_object* v_name_2825_, lean_object* v_goal_2826_, lean_object* v_idx_2827_, lean_object* v_expected_x3f_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_){
_start:
{
lean_object* v___x_2837_; 
lean_inc(v_name_2825_);
lean_inc(v_goal_2826_);
v___x_2837_ = l_Lean_MVarId_checkNotAssigned(v_goal_2826_, v_name_2825_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_);
if (lean_obj_tag(v___x_2837_) == 0)
{
lean_object* v___x_2838_; 
lean_dec_ref_known(v___x_2837_, 1);
lean_inc(v_goal_2826_);
v___x_2838_ = l_Lean_MVarId_getType_x27(v_goal_2826_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_);
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_object* v_a_2839_; lean_object* v___x_2840_; 
v_a_2839_ = lean_ctor_get(v___x_2838_, 0);
lean_inc(v_a_2839_);
lean_dec_ref_known(v___x_2838_, 1);
v___x_2840_ = l_Lean_Expr_getAppFn(v_a_2839_);
lean_dec(v_a_2839_);
if (lean_obj_tag(v___x_2840_) == 4)
{
lean_object* v_declName_2841_; lean_object* v_us_2842_; lean_object* v___x_2843_; lean_object* v_env_2844_; uint8_t v___x_2845_; lean_object* v___x_2846_; 
v_declName_2841_ = lean_ctor_get(v___x_2840_, 0);
lean_inc(v_declName_2841_);
v_us_2842_ = lean_ctor_get(v___x_2840_, 1);
lean_inc(v_us_2842_);
lean_dec_ref_known(v___x_2840_, 2);
v___x_2843_ = lean_st_ref_get(v___y_2832_);
v_env_2844_ = lean_ctor_get(v___x_2843_, 0);
lean_inc_ref(v_env_2844_);
lean_dec(v___x_2843_);
v___x_2845_ = 0;
v___x_2846_ = l_Lean_Environment_find_x3f(v_env_2844_, v_declName_2841_, v___x_2845_);
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_dec(v_us_2842_);
lean_dec(v_expected_x3f_2828_);
lean_dec(v_idx_2827_);
goto v___jp_2834_;
}
else
{
lean_object* v_val_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2917_; 
v_val_2847_ = lean_ctor_get(v___x_2846_, 0);
v_isSharedCheck_2917_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2849_ = v___x_2846_;
v_isShared_2850_ = v_isSharedCheck_2917_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_val_2847_);
lean_dec(v___x_2846_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2917_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
if (lean_obj_tag(v_val_2847_) == 5)
{
lean_object* v_val_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2916_; 
v_val_2851_ = lean_ctor_get(v_val_2847_, 0);
v_isSharedCheck_2916_ = !lean_is_exclusive(v_val_2847_);
if (v_isSharedCheck_2916_ == 0)
{
v___x_2853_ = v_val_2847_;
v_isShared_2854_ = v_isSharedCheck_2916_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_val_2851_);
lean_dec(v_val_2847_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2916_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v___y_2856_; lean_object* v___y_2857_; lean_object* v___y_2858_; lean_object* v___y_2859_; 
if (lean_obj_tag(v_expected_x3f_2828_) == 1)
{
lean_object* v_val_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2915_; 
v_val_2886_ = lean_ctor_get(v_expected_x3f_2828_, 0);
v_isSharedCheck_2915_ = !lean_is_exclusive(v_expected_x3f_2828_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2888_ = v_expected_x3f_2828_;
v_isShared_2889_ = v_isSharedCheck_2915_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_val_2886_);
lean_dec(v_expected_x3f_2828_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2915_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v_ctors_2890_; lean_object* v___x_2891_; uint8_t v___x_2892_; 
v_ctors_2890_ = lean_ctor_get(v_val_2851_, 4);
v___x_2891_ = l_List_lengthTR___redArg(v_ctors_2890_);
v___x_2892_ = lean_nat_dec_eq(v___x_2891_, v_val_2886_);
lean_dec(v___x_2891_);
if (v___x_2892_ == 0)
{
uint8_t v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2904_; 
v___x_2893_ = 1;
lean_inc(v_name_2825_);
v___x_2894_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2825_, v___x_2893_);
v___x_2895_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__7));
v___x_2896_ = lean_string_append(v___x_2894_, v___x_2895_);
v___x_2897_ = l_Nat_reprFast(v_val_2886_);
v___x_2898_ = lean_string_append(v___x_2896_, v___x_2897_);
lean_dec_ref(v___x_2897_);
v___x_2899_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__6));
v___x_2900_ = lean_string_append(v___x_2898_, v___x_2899_);
v___x_2901_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2900_);
v___x_2902_ = l_Lean_MessageData_ofFormat(v___x_2901_);
if (v_isShared_2889_ == 0)
{
lean_ctor_set(v___x_2888_, 0, v___x_2902_);
v___x_2904_ = v___x_2888_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v___x_2902_);
v___x_2904_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
lean_object* v___x_2905_; 
lean_inc(v_goal_2826_);
lean_inc(v_name_2825_);
v___x_2905_ = l_Lean_Meta_throwTacticEx___redArg(v_name_2825_, v_goal_2826_, v___x_2904_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_);
if (lean_obj_tag(v___x_2905_) == 0)
{
lean_dec_ref_known(v___x_2905_, 1);
v___y_2856_ = v___y_2829_;
v___y_2857_ = v___y_2830_;
v___y_2858_ = v___y_2831_;
v___y_2859_ = v___y_2832_;
goto v___jp_2855_;
}
else
{
lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2913_; 
lean_del_object(v___x_2853_);
lean_dec_ref(v_val_2851_);
lean_del_object(v___x_2849_);
lean_dec(v_us_2842_);
lean_dec(v_idx_2827_);
lean_dec(v_goal_2826_);
lean_dec(v_name_2825_);
v_a_2906_ = lean_ctor_get(v___x_2905_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2905_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2908_ = v___x_2905_;
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v___x_2905_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2911_; 
if (v_isShared_2909_ == 0)
{
v___x_2911_ = v___x_2908_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_a_2906_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
}
}
else
{
lean_del_object(v___x_2888_);
lean_dec(v_val_2886_);
v___y_2856_ = v___y_2829_;
v___y_2857_ = v___y_2830_;
v___y_2858_ = v___y_2831_;
v___y_2859_ = v___y_2832_;
goto v___jp_2855_;
}
}
}
else
{
lean_dec(v_expected_x3f_2828_);
v___y_2856_ = v___y_2829_;
v___y_2857_ = v___y_2830_;
v___y_2858_ = v___y_2831_;
v___y_2859_ = v___y_2832_;
goto v___jp_2855_;
}
v___jp_2855_:
{
lean_object* v_ctors_2860_; lean_object* v___x_2861_; uint8_t v___x_2862_; 
v_ctors_2860_ = lean_ctor_get(v_val_2851_, 4);
lean_inc(v_ctors_2860_);
lean_dec_ref(v_val_2851_);
v___x_2861_ = l_List_lengthTR___redArg(v_ctors_2860_);
v___x_2862_ = lean_nat_dec_lt(v_idx_2827_, v___x_2861_);
if (v___x_2862_ == 0)
{
lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2873_; 
lean_dec(v_ctors_2860_);
lean_dec(v_us_2842_);
v___x_2863_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__4));
v___x_2864_ = l_Nat_reprFast(v_idx_2827_);
v___x_2865_ = lean_string_append(v___x_2863_, v___x_2864_);
lean_dec_ref(v___x_2864_);
v___x_2866_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__5));
v___x_2867_ = lean_string_append(v___x_2865_, v___x_2866_);
v___x_2868_ = l_Nat_reprFast(v___x_2861_);
v___x_2869_ = lean_string_append(v___x_2867_, v___x_2868_);
lean_dec_ref(v___x_2868_);
v___x_2870_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__6));
v___x_2871_ = lean_string_append(v___x_2869_, v___x_2870_);
if (v_isShared_2854_ == 0)
{
lean_ctor_set_tag(v___x_2853_, 3);
lean_ctor_set(v___x_2853_, 0, v___x_2871_);
v___x_2873_ = v___x_2853_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v___x_2871_);
v___x_2873_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
lean_object* v___x_2874_; lean_object* v___x_2876_; 
v___x_2874_ = l_Lean_MessageData_ofFormat(v___x_2873_);
if (v_isShared_2850_ == 0)
{
lean_ctor_set(v___x_2849_, 0, v___x_2874_);
v___x_2876_ = v___x_2849_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v___x_2874_);
v___x_2876_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
lean_object* v___x_2877_; 
v___x_2877_ = l_Lean_Meta_throwTacticEx___redArg(v_name_2825_, v_goal_2826_, v___x_2876_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
return v___x_2877_;
}
}
}
else
{
lean_object* v___x_2880_; lean_object* v___x_2881_; uint8_t v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; 
lean_dec(v___x_2861_);
lean_del_object(v___x_2853_);
lean_del_object(v___x_2849_);
lean_dec(v_name_2825_);
v___x_2880_ = l_List_get___redArg(v_ctors_2860_, v_idx_2827_);
lean_dec(v_ctors_2860_);
v___x_2881_ = l_Lean_mkConst(v___x_2880_, v_us_2842_);
v___x_2882_ = 0;
v___x_2883_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_2883_, 0, v___x_2882_);
lean_ctor_set_uint8(v___x_2883_, 1, v___x_2862_);
lean_ctor_set_uint8(v___x_2883_, 2, v___x_2845_);
lean_ctor_set_uint8(v___x_2883_, 3, v___x_2862_);
v___x_2884_ = lean_box(0);
v___x_2885_ = l_Lean_MVarId_apply(v_goal_2826_, v___x_2881_, v___x_2883_, v___x_2884_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
return v___x_2885_;
}
}
}
}
else
{
lean_del_object(v___x_2849_);
lean_dec(v_val_2847_);
lean_dec(v_us_2842_);
lean_dec(v_expected_x3f_2828_);
lean_dec(v_idx_2827_);
goto v___jp_2834_;
}
}
}
}
else
{
lean_dec_ref(v___x_2840_);
lean_dec(v_expected_x3f_2828_);
lean_dec(v_idx_2827_);
goto v___jp_2834_;
}
}
else
{
lean_object* v_a_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2925_; 
lean_dec(v_expected_x3f_2828_);
lean_dec(v_idx_2827_);
lean_dec(v_goal_2826_);
lean_dec(v_name_2825_);
v_a_2918_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_2925_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2925_ == 0)
{
v___x_2920_ = v___x_2838_;
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_a_2918_);
lean_dec(v___x_2838_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
lean_object* v___x_2923_; 
if (v_isShared_2921_ == 0)
{
v___x_2923_ = v___x_2920_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v_a_2918_);
v___x_2923_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
return v___x_2923_;
}
}
}
}
else
{
lean_object* v_a_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2933_; 
lean_dec(v_expected_x3f_2828_);
lean_dec(v_idx_2827_);
lean_dec(v_goal_2826_);
lean_dec(v_name_2825_);
v_a_2926_ = lean_ctor_get(v___x_2837_, 0);
v_isSharedCheck_2933_ = !lean_is_exclusive(v___x_2837_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2928_ = v___x_2837_;
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_a_2926_);
lean_dec(v___x_2837_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
lean_object* v___x_2931_; 
if (v_isShared_2929_ == 0)
{
v___x_2931_ = v___x_2928_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_a_2926_);
v___x_2931_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
return v___x_2931_;
}
}
}
v___jp_2834_:
{
lean_object* v___x_2835_; lean_object* v___x_2836_; 
v___x_2835_ = lean_obj_once(&l_Lean_MVarId_nthConstructor___lam__0___closed__3, &l_Lean_MVarId_nthConstructor___lam__0___closed__3_once, _init_l_Lean_MVarId_nthConstructor___lam__0___closed__3);
v___x_2836_ = l_Lean_Meta_throwTacticEx___redArg(v_name_2825_, v_goal_2826_, v___x_2835_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_);
return v___x_2836_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___lam__0___boxed(lean_object* v_name_2934_, lean_object* v_goal_2935_, lean_object* v_idx_2936_, lean_object* v_expected_x3f_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_){
_start:
{
lean_object* v_res_2943_; 
v_res_2943_ = l_Lean_MVarId_nthConstructor___lam__0(v_name_2934_, v_goal_2935_, v_idx_2936_, v_expected_x3f_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2938_);
return v_res_2943_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor(lean_object* v_name_2944_, lean_object* v_idx_2945_, lean_object* v_expected_x3f_2946_, lean_object* v_goal_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_){
_start:
{
lean_object* v___f_2953_; lean_object* v___x_2954_; 
lean_inc(v_goal_2947_);
v___f_2953_ = lean_alloc_closure((void*)(l_Lean_MVarId_nthConstructor___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2953_, 0, v_name_2944_);
lean_closure_set(v___f_2953_, 1, v_goal_2947_);
lean_closure_set(v___f_2953_, 2, v_idx_2945_);
lean_closure_set(v___f_2953_, 3, v_expected_x3f_2946_);
v___x_2954_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_goal_2947_, v___f_2953_, v_a_2948_, v_a_2949_, v_a_2950_, v_a_2951_);
return v___x_2954_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___boxed(lean_object* v_name_2955_, lean_object* v_idx_2956_, lean_object* v_expected_x3f_2957_, lean_object* v_goal_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_){
_start:
{
lean_object* v_res_2964_; 
v_res_2964_ = l_Lean_MVarId_nthConstructor(v_name_2955_, v_idx_2956_, v_expected_x3f_2957_, v_goal_2958_, v_a_2959_, v_a_2960_, v_a_2961_, v_a_2962_);
lean_dec(v_a_2962_);
lean_dec_ref(v_a_2961_);
lean_dec(v_a_2960_);
lean_dec_ref(v_a_2959_);
return v_res_2964_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(lean_object* v_x_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_){
_start:
{
lean_object* v___x_2971_; 
v___x_2971_ = l_Lean_Meta_saveState___redArg(v___y_2967_, v___y_2969_);
if (lean_obj_tag(v___x_2971_) == 0)
{
lean_object* v_a_2972_; lean_object* v___x_2973_; 
v_a_2972_ = lean_ctor_get(v___x_2971_, 0);
lean_inc(v_a_2972_);
lean_dec_ref_known(v___x_2971_, 1);
lean_inc(v___y_2969_);
lean_inc_ref(v___y_2968_);
lean_inc(v___y_2967_);
lean_inc_ref(v___y_2966_);
v___x_2973_ = lean_apply_5(v_x_2965_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_, lean_box(0));
if (lean_obj_tag(v___x_2973_) == 0)
{
lean_object* v_a_2974_; lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_2982_; 
lean_dec(v_a_2972_);
v_a_2974_ = lean_ctor_get(v___x_2973_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2973_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2976_ = v___x_2973_;
v_isShared_2977_ = v_isSharedCheck_2982_;
goto v_resetjp_2975_;
}
else
{
lean_inc(v_a_2974_);
lean_dec(v___x_2973_);
v___x_2976_ = lean_box(0);
v_isShared_2977_ = v_isSharedCheck_2982_;
goto v_resetjp_2975_;
}
v_resetjp_2975_:
{
lean_object* v___x_2978_; lean_object* v___x_2980_; 
v___x_2978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2978_, 0, v_a_2974_);
if (v_isShared_2977_ == 0)
{
lean_ctor_set(v___x_2976_, 0, v___x_2978_);
v___x_2980_ = v___x_2976_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v___x_2978_);
v___x_2980_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
return v___x_2980_;
}
}
}
else
{
lean_object* v_a_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_3012_; 
v_a_2983_ = lean_ctor_get(v___x_2973_, 0);
v_isSharedCheck_3012_ = !lean_is_exclusive(v___x_2973_);
if (v_isSharedCheck_3012_ == 0)
{
v___x_2985_ = v___x_2973_;
v_isShared_2986_ = v_isSharedCheck_3012_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_a_2983_);
lean_dec(v___x_2973_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_3012_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
uint8_t v___y_2988_; uint8_t v___x_3010_; 
v___x_3010_ = l_Lean_Exception_isInterrupt(v_a_2983_);
if (v___x_3010_ == 0)
{
uint8_t v___x_3011_; 
lean_inc(v_a_2983_);
v___x_3011_ = l_Lean_Exception_isRuntime(v_a_2983_);
v___y_2988_ = v___x_3011_;
goto v___jp_2987_;
}
else
{
v___y_2988_ = v___x_3010_;
goto v___jp_2987_;
}
v___jp_2987_:
{
if (v___y_2988_ == 0)
{
lean_object* v___x_2989_; 
lean_del_object(v___x_2985_);
lean_dec(v_a_2983_);
v___x_2989_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2972_, v___y_2967_, v___y_2969_);
lean_dec(v_a_2972_);
if (lean_obj_tag(v___x_2989_) == 0)
{
lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_2997_; 
v_isSharedCheck_2997_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_2997_ == 0)
{
lean_object* v_unused_2998_; 
v_unused_2998_ = lean_ctor_get(v___x_2989_, 0);
lean_dec(v_unused_2998_);
v___x_2991_ = v___x_2989_;
v_isShared_2992_ = v_isSharedCheck_2997_;
goto v_resetjp_2990_;
}
else
{
lean_dec(v___x_2989_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_2997_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2993_; lean_object* v___x_2995_; 
v___x_2993_ = lean_box(0);
if (v_isShared_2992_ == 0)
{
lean_ctor_set(v___x_2991_, 0, v___x_2993_);
v___x_2995_ = v___x_2991_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v___x_2993_);
v___x_2995_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
return v___x_2995_;
}
}
}
else
{
lean_object* v_a_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3006_; 
v_a_2999_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_3001_ = v___x_2989_;
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_a_2999_);
lean_dec(v___x_2989_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3004_; 
if (v_isShared_3002_ == 0)
{
v___x_3004_ = v___x_3001_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_a_2999_);
v___x_3004_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
return v___x_3004_;
}
}
}
}
else
{
lean_object* v___x_3008_; 
lean_dec(v_a_2972_);
if (v_isShared_2986_ == 0)
{
v___x_3008_ = v___x_2985_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_a_2983_);
v___x_3008_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
return v___x_3008_;
}
}
}
}
}
}
else
{
lean_object* v_a_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3020_; 
lean_dec_ref(v_x_2965_);
v_a_3013_ = lean_ctor_get(v___x_2971_, 0);
v_isSharedCheck_3020_ = !lean_is_exclusive(v___x_2971_);
if (v_isSharedCheck_3020_ == 0)
{
v___x_3015_ = v___x_2971_;
v_isShared_3016_ = v_isSharedCheck_3020_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_a_3013_);
lean_dec(v___x_2971_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3020_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v___x_3018_; 
if (v_isShared_3016_ == 0)
{
v___x_3018_ = v___x_3015_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v_a_3013_);
v___x_3018_ = v_reuseFailAlloc_3019_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
return v___x_3018_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg___boxed(lean_object* v_x_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_){
_start:
{
lean_object* v_res_3027_; 
v_res_3027_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v_x_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_);
lean_dec(v___y_3025_);
lean_dec_ref(v___y_3024_);
lean_dec(v___y_3023_);
lean_dec_ref(v___y_3022_);
return v_res_3027_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0(lean_object* v_00_u03b1_3028_, lean_object* v_x_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_){
_start:
{
lean_object* v___x_3035_; 
v___x_3035_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v_x_3029_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_);
return v___x_3035_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___boxed(lean_object* v_00_u03b1_3036_, lean_object* v_x_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_){
_start:
{
lean_object* v_res_3043_; 
v_res_3043_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0(v_00_u03b1_3036_, v_x_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_);
lean_dec(v___y_3041_);
lean_dec_ref(v___y_3040_);
lean_dec(v___y_3039_);
lean_dec_ref(v___y_3038_);
return v_res_3043_;
}
}
static lean_object* _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3045_; lean_object* v___x_3046_; 
v___x_3045_ = ((lean_object*)(l_Lean_MVarId_iffOfEq___lam__0___closed__0));
v___x_3046_ = l_Lean_stringToMessageData(v___x_3045_);
return v___x_3046_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq___lam__0(lean_object* v_mvarId_3047_, lean_object* v___x_3048_, lean_object* v___x_3049_, lean_object* v___x_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_){
_start:
{
lean_object* v___x_3059_; 
v___x_3059_ = l_Lean_MVarId_apply(v_mvarId_3047_, v___x_3048_, v___x_3049_, v___x_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_);
if (lean_obj_tag(v___x_3059_) == 0)
{
lean_object* v_a_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3069_; 
v_a_3060_ = lean_ctor_get(v___x_3059_, 0);
v_isSharedCheck_3069_ = !lean_is_exclusive(v___x_3059_);
if (v_isSharedCheck_3069_ == 0)
{
v___x_3062_ = v___x_3059_;
v_isShared_3063_ = v_isSharedCheck_3069_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_a_3060_);
lean_dec(v___x_3059_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3069_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
if (lean_obj_tag(v_a_3060_) == 1)
{
lean_object* v_tail_3064_; 
v_tail_3064_ = lean_ctor_get(v_a_3060_, 1);
if (lean_obj_tag(v_tail_3064_) == 0)
{
lean_object* v_head_3065_; lean_object* v___x_3067_; 
v_head_3065_ = lean_ctor_get(v_a_3060_, 0);
lean_inc(v_head_3065_);
lean_dec_ref_known(v_a_3060_, 2);
if (v_isShared_3063_ == 0)
{
lean_ctor_set(v___x_3062_, 0, v_head_3065_);
v___x_3067_ = v___x_3062_;
goto v_reusejp_3066_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v_head_3065_);
v___x_3067_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3066_;
}
v_reusejp_3066_:
{
return v___x_3067_;
}
}
else
{
lean_dec_ref_known(v_a_3060_, 2);
lean_del_object(v___x_3062_);
goto v___jp_3056_;
}
}
else
{
lean_del_object(v___x_3062_);
lean_dec(v_a_3060_);
goto v___jp_3056_;
}
}
}
else
{
lean_object* v_a_3070_; lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3077_; 
v_a_3070_ = lean_ctor_get(v___x_3059_, 0);
v_isSharedCheck_3077_ = !lean_is_exclusive(v___x_3059_);
if (v_isSharedCheck_3077_ == 0)
{
v___x_3072_ = v___x_3059_;
v_isShared_3073_ = v_isSharedCheck_3077_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_a_3070_);
lean_dec(v___x_3059_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3077_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
lean_object* v___x_3075_; 
if (v_isShared_3073_ == 0)
{
v___x_3075_ = v___x_3072_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v_a_3070_);
v___x_3075_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
return v___x_3075_;
}
}
}
v___jp_3056_:
{
lean_object* v___x_3057_; lean_object* v___x_3058_; 
v___x_3057_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3058_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3057_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_);
return v___x_3058_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq___lam__0___boxed(lean_object* v_mvarId_3078_, lean_object* v___x_3079_, lean_object* v___x_3080_, lean_object* v___x_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_){
_start:
{
lean_object* v_res_3087_; 
v_res_3087_ = l_Lean_MVarId_iffOfEq___lam__0(v_mvarId_3078_, v___x_3079_, v___x_3080_, v___x_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_);
lean_dec(v___y_3085_);
lean_dec_ref(v___y_3084_);
lean_dec(v___y_3083_);
lean_dec_ref(v___y_3082_);
return v_res_3087_;
}
}
static lean_object* _init_l_Lean_MVarId_iffOfEq___closed__2(void){
_start:
{
lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; 
v___x_3091_ = lean_box(0);
v___x_3092_ = ((lean_object*)(l_Lean_MVarId_iffOfEq___closed__1));
v___x_3093_ = l_Lean_mkConst(v___x_3092_, v___x_3091_);
return v___x_3093_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq(lean_object* v_mvarId_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_){
_start:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___f_3107_; lean_object* v___x_3108_; 
v___x_3104_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___closed__2, &l_Lean_MVarId_iffOfEq___closed__2_once, _init_l_Lean_MVarId_iffOfEq___closed__2);
v___x_3105_ = ((lean_object*)(l_Lean_MVarId_iffOfEq___closed__3));
v___x_3106_ = lean_box(0);
lean_inc(v_mvarId_3098_);
v___f_3107_ = lean_alloc_closure((void*)(l_Lean_MVarId_iffOfEq___lam__0___boxed), 9, 4);
lean_closure_set(v___f_3107_, 0, v_mvarId_3098_);
lean_closure_set(v___f_3107_, 1, v___x_3104_);
lean_closure_set(v___f_3107_, 2, v___x_3105_);
lean_closure_set(v___f_3107_, 3, v___x_3106_);
v___x_3108_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v___f_3107_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_);
if (lean_obj_tag(v___x_3108_) == 0)
{
lean_object* v_a_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3120_; 
v_a_3109_ = lean_ctor_get(v___x_3108_, 0);
v_isSharedCheck_3120_ = !lean_is_exclusive(v___x_3108_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3111_ = v___x_3108_;
v_isShared_3112_ = v_isSharedCheck_3120_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_a_3109_);
lean_dec(v___x_3108_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3120_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
if (lean_obj_tag(v_a_3109_) == 0)
{
lean_object* v___x_3114_; 
if (v_isShared_3112_ == 0)
{
lean_ctor_set(v___x_3111_, 0, v_mvarId_3098_);
v___x_3114_ = v___x_3111_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v_mvarId_3098_);
v___x_3114_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
return v___x_3114_;
}
}
else
{
lean_object* v_val_3116_; lean_object* v___x_3118_; 
lean_dec(v_mvarId_3098_);
v_val_3116_ = lean_ctor_get(v_a_3109_, 0);
lean_inc(v_val_3116_);
lean_dec_ref_known(v_a_3109_, 1);
if (v_isShared_3112_ == 0)
{
lean_ctor_set(v___x_3111_, 0, v_val_3116_);
v___x_3118_ = v___x_3111_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v_val_3116_);
v___x_3118_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
return v___x_3118_;
}
}
}
}
else
{
lean_object* v_a_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3128_; 
lean_dec(v_mvarId_3098_);
v_a_3121_ = lean_ctor_get(v___x_3108_, 0);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_3108_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3123_ = v___x_3108_;
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_a_3121_);
lean_dec(v___x_3108_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v___x_3126_; 
if (v_isShared_3124_ == 0)
{
v___x_3126_ = v___x_3123_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v_a_3121_);
v___x_3126_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
return v___x_3126_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq___boxed(lean_object* v_mvarId_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_){
_start:
{
lean_object* v_res_3135_; 
v_res_3135_ = l_Lean_MVarId_iffOfEq(v_mvarId_3129_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_);
lean_dec(v_a_3133_);
lean_dec_ref(v_a_3132_);
lean_dec(v_a_3131_);
lean_dec_ref(v_a_3130_);
return v_res_3135_;
}
}
static lean_object* _init_l_Lean_MVarId_propext___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; 
v___x_3139_ = lean_box(0);
v___x_3140_ = ((lean_object*)(l_Lean_MVarId_propext___lam__0___closed__1));
v___x_3141_ = l_Lean_mkConst(v___x_3140_, v___x_3139_);
return v___x_3141_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___lam__0(lean_object* v_mvarId_3145_, uint8_t v___x_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_){
_start:
{
lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; uint8_t v___y_3160_; lean_object* v___y_3186_; lean_object* v___x_3224_; uint8_t v_transparency_3225_; uint8_t v___x_3226_; 
v___x_3224_ = l_Lean_Meta_Context_config(v___y_3147_);
v_transparency_3225_ = lean_ctor_get_uint8(v___x_3224_, 9);
lean_dec_ref(v___x_3224_);
v___x_3226_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3225_, v___x_3146_);
if (v___x_3226_ == 0)
{
lean_object* v_keyedConfig_3227_; uint8_t v_trackZetaDelta_3228_; lean_object* v_zetaDeltaSet_3229_; lean_object* v_lctx_3230_; lean_object* v_localInstances_3231_; lean_object* v_defEqCtx_x3f_3232_; lean_object* v_synthPendingDepth_3233_; lean_object* v_customCanUnfoldPredicate_x3f_3234_; uint8_t v_univApprox_3235_; uint8_t v_inTypeClassResolution_3236_; uint8_t v_cacheInferType_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; 
v_keyedConfig_3227_ = lean_ctor_get(v___y_3147_, 0);
v_trackZetaDelta_3228_ = lean_ctor_get_uint8(v___y_3147_, sizeof(void*)*7);
v_zetaDeltaSet_3229_ = lean_ctor_get(v___y_3147_, 1);
v_lctx_3230_ = lean_ctor_get(v___y_3147_, 2);
v_localInstances_3231_ = lean_ctor_get(v___y_3147_, 3);
v_defEqCtx_x3f_3232_ = lean_ctor_get(v___y_3147_, 4);
v_synthPendingDepth_3233_ = lean_ctor_get(v___y_3147_, 5);
v_customCanUnfoldPredicate_x3f_3234_ = lean_ctor_get(v___y_3147_, 6);
v_univApprox_3235_ = lean_ctor_get_uint8(v___y_3147_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3236_ = lean_ctor_get_uint8(v___y_3147_, sizeof(void*)*7 + 2);
v_cacheInferType_3237_ = lean_ctor_get_uint8(v___y_3147_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3227_);
v___x_3238_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3146_, v_keyedConfig_3227_);
lean_inc(v_customCanUnfoldPredicate_x3f_3234_);
lean_inc(v_synthPendingDepth_3233_);
lean_inc(v_defEqCtx_x3f_3232_);
lean_inc_ref(v_localInstances_3231_);
lean_inc_ref(v_lctx_3230_);
lean_inc(v_zetaDeltaSet_3229_);
v___x_3239_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3239_, 0, v___x_3238_);
lean_ctor_set(v___x_3239_, 1, v_zetaDeltaSet_3229_);
lean_ctor_set(v___x_3239_, 2, v_lctx_3230_);
lean_ctor_set(v___x_3239_, 3, v_localInstances_3231_);
lean_ctor_set(v___x_3239_, 4, v_defEqCtx_x3f_3232_);
lean_ctor_set(v___x_3239_, 5, v_synthPendingDepth_3233_);
lean_ctor_set(v___x_3239_, 6, v_customCanUnfoldPredicate_x3f_3234_);
lean_ctor_set_uint8(v___x_3239_, sizeof(void*)*7, v_trackZetaDelta_3228_);
lean_ctor_set_uint8(v___x_3239_, sizeof(void*)*7 + 1, v_univApprox_3235_);
lean_ctor_set_uint8(v___x_3239_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3236_);
lean_ctor_set_uint8(v___x_3239_, sizeof(void*)*7 + 3, v_cacheInferType_3237_);
lean_inc(v_mvarId_3145_);
v___x_3240_ = l_Lean_MVarId_getType_x27(v_mvarId_3145_, v___x_3239_, v___y_3148_, v___y_3149_, v___y_3150_);
lean_dec_ref_known(v___x_3239_, 7);
v___y_3186_ = v___x_3240_;
goto v___jp_3185_;
}
else
{
lean_object* v___x_3241_; 
lean_inc(v_mvarId_3145_);
v___x_3241_ = l_Lean_MVarId_getType_x27(v_mvarId_3145_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_);
v___y_3186_ = v___x_3241_;
goto v___jp_3185_;
}
v___jp_3152_:
{
lean_object* v___x_3157_; lean_object* v___x_3158_; 
v___x_3157_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3158_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3157_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_);
lean_dec_ref(v___y_3153_);
return v___x_3158_;
}
v___jp_3159_:
{
lean_object* v___x_3161_; uint8_t v___x_3162_; uint8_t v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; 
v___x_3161_ = lean_obj_once(&l_Lean_MVarId_propext___lam__0___closed__2, &l_Lean_MVarId_propext___lam__0___closed__2_once, _init_l_Lean_MVarId_propext___lam__0___closed__2);
v___x_3162_ = 0;
v___x_3163_ = 0;
v___x_3164_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3164_, 0, v___x_3162_);
lean_ctor_set_uint8(v___x_3164_, 1, v___y_3160_);
lean_ctor_set_uint8(v___x_3164_, 2, v___x_3163_);
lean_ctor_set_uint8(v___x_3164_, 3, v___y_3160_);
v___x_3165_ = lean_box(0);
v___x_3166_ = l_Lean_MVarId_apply(v_mvarId_3145_, v___x_3161_, v___x_3164_, v___x_3165_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_);
if (lean_obj_tag(v___x_3166_) == 0)
{
lean_object* v_a_3167_; lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3176_; 
v_a_3167_ = lean_ctor_get(v___x_3166_, 0);
v_isSharedCheck_3176_ = !lean_is_exclusive(v___x_3166_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3169_ = v___x_3166_;
v_isShared_3170_ = v_isSharedCheck_3176_;
goto v_resetjp_3168_;
}
else
{
lean_inc(v_a_3167_);
lean_dec(v___x_3166_);
v___x_3169_ = lean_box(0);
v_isShared_3170_ = v_isSharedCheck_3176_;
goto v_resetjp_3168_;
}
v_resetjp_3168_:
{
if (lean_obj_tag(v_a_3167_) == 1)
{
lean_object* v_tail_3171_; 
v_tail_3171_ = lean_ctor_get(v_a_3167_, 1);
if (lean_obj_tag(v_tail_3171_) == 0)
{
lean_object* v_head_3172_; lean_object* v___x_3174_; 
lean_dec_ref(v___y_3147_);
v_head_3172_ = lean_ctor_get(v_a_3167_, 0);
lean_inc(v_head_3172_);
lean_dec_ref_known(v_a_3167_, 2);
if (v_isShared_3170_ == 0)
{
lean_ctor_set(v___x_3169_, 0, v_head_3172_);
v___x_3174_ = v___x_3169_;
goto v_reusejp_3173_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v_head_3172_);
v___x_3174_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3173_;
}
v_reusejp_3173_:
{
return v___x_3174_;
}
}
else
{
lean_dec_ref_known(v_a_3167_, 2);
lean_del_object(v___x_3169_);
v___y_3153_ = v___y_3147_;
v___y_3154_ = v___y_3148_;
v___y_3155_ = v___y_3149_;
v___y_3156_ = v___y_3150_;
goto v___jp_3152_;
}
}
else
{
lean_del_object(v___x_3169_);
lean_dec(v_a_3167_);
v___y_3153_ = v___y_3147_;
v___y_3154_ = v___y_3148_;
v___y_3155_ = v___y_3149_;
v___y_3156_ = v___y_3150_;
goto v___jp_3152_;
}
}
}
else
{
lean_object* v_a_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3184_; 
lean_dec_ref(v___y_3147_);
v_a_3177_ = lean_ctor_get(v___x_3166_, 0);
v_isSharedCheck_3184_ = !lean_is_exclusive(v___x_3166_);
if (v_isSharedCheck_3184_ == 0)
{
v___x_3179_ = v___x_3166_;
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_a_3177_);
lean_dec(v___x_3166_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
lean_object* v___x_3182_; 
if (v_isShared_3180_ == 0)
{
v___x_3182_ = v___x_3179_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v_a_3177_);
v___x_3182_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
return v___x_3182_;
}
}
}
}
v___jp_3185_:
{
if (lean_obj_tag(v___y_3186_) == 0)
{
lean_object* v_a_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; uint8_t v___x_3190_; 
v_a_3187_ = lean_ctor_get(v___y_3186_, 0);
lean_inc(v_a_3187_);
lean_dec_ref_known(v___y_3186_, 1);
v___x_3188_ = ((lean_object*)(l_Lean_MVarId_propext___lam__0___closed__4));
v___x_3189_ = lean_unsigned_to_nat(3u);
v___x_3190_ = l_Lean_Expr_isAppOfArity(v_a_3187_, v___x_3188_, v___x_3189_);
if (v___x_3190_ == 0)
{
lean_object* v___x_3191_; lean_object* v___x_3192_; 
lean_dec(v_a_3187_);
lean_dec(v_mvarId_3145_);
v___x_3191_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3192_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3191_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_);
lean_dec_ref(v___y_3147_);
return v___x_3192_;
}
else
{
lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; 
v___x_3193_ = l_Lean_Expr_appFn_x21(v_a_3187_);
lean_dec(v_a_3187_);
v___x_3194_ = l_Lean_Expr_appArg_x21(v___x_3193_);
lean_dec_ref(v___x_3193_);
v___x_3195_ = l_Lean_Meta_isProp(v___x_3194_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_);
if (lean_obj_tag(v___x_3195_) == 0)
{
lean_object* v_a_3196_; uint8_t v___x_3197_; 
v_a_3196_ = lean_ctor_get(v___x_3195_, 0);
lean_inc(v_a_3196_);
lean_dec_ref_known(v___x_3195_, 1);
v___x_3197_ = lean_unbox(v_a_3196_);
lean_dec(v_a_3196_);
if (v___x_3197_ == 0)
{
lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v_a_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3207_; 
lean_dec(v_mvarId_3145_);
v___x_3198_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3199_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3198_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_);
lean_dec_ref(v___y_3147_);
v_a_3200_ = lean_ctor_get(v___x_3199_, 0);
v_isSharedCheck_3207_ = !lean_is_exclusive(v___x_3199_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3202_ = v___x_3199_;
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_a_3200_);
lean_dec(v___x_3199_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___x_3205_; 
if (v_isShared_3203_ == 0)
{
v___x_3205_ = v___x_3202_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_a_3200_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
return v___x_3205_;
}
}
}
else
{
v___y_3160_ = v___x_3190_;
goto v___jp_3159_;
}
}
else
{
lean_object* v_a_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3215_; 
lean_dec_ref(v___y_3147_);
lean_dec(v_mvarId_3145_);
v_a_3208_ = lean_ctor_get(v___x_3195_, 0);
v_isSharedCheck_3215_ = !lean_is_exclusive(v___x_3195_);
if (v_isSharedCheck_3215_ == 0)
{
v___x_3210_ = v___x_3195_;
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_a_3208_);
lean_dec(v___x_3195_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v___x_3213_; 
if (v_isShared_3211_ == 0)
{
v___x_3213_ = v___x_3210_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v_a_3208_);
v___x_3213_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
return v___x_3213_;
}
}
}
}
}
else
{
lean_object* v_a_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3223_; 
lean_dec_ref(v___y_3147_);
lean_dec(v_mvarId_3145_);
v_a_3216_ = lean_ctor_get(v___y_3186_, 0);
v_isSharedCheck_3223_ = !lean_is_exclusive(v___y_3186_);
if (v_isSharedCheck_3223_ == 0)
{
v___x_3218_ = v___y_3186_;
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_a_3216_);
lean_dec(v___y_3186_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
lean_object* v___x_3221_; 
if (v_isShared_3219_ == 0)
{
v___x_3221_ = v___x_3218_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_a_3216_);
v___x_3221_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
return v___x_3221_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___lam__0___boxed(lean_object* v_mvarId_3242_, lean_object* v___x_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_){
_start:
{
uint8_t v___x_2525__boxed_3249_; lean_object* v_res_3250_; 
v___x_2525__boxed_3249_ = lean_unbox(v___x_3243_);
v_res_3250_ = l_Lean_MVarId_propext___lam__0(v_mvarId_3242_, v___x_2525__boxed_3249_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec(v___y_3245_);
return v_res_3250_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext(lean_object* v_mvarId_3251_, lean_object* v_a_3252_, lean_object* v_a_3253_, lean_object* v_a_3254_, lean_object* v_a_3255_){
_start:
{
uint8_t v___x_3257_; lean_object* v___x_3258_; lean_object* v___f_3259_; lean_object* v___x_3260_; 
v___x_3257_ = 2;
v___x_3258_ = lean_box(v___x_3257_);
lean_inc(v_mvarId_3251_);
v___f_3259_ = lean_alloc_closure((void*)(l_Lean_MVarId_propext___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3259_, 0, v_mvarId_3251_);
lean_closure_set(v___f_3259_, 1, v___x_3258_);
v___x_3260_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v___f_3259_, v_a_3252_, v_a_3253_, v_a_3254_, v_a_3255_);
if (lean_obj_tag(v___x_3260_) == 0)
{
lean_object* v_a_3261_; lean_object* v___x_3263_; uint8_t v_isShared_3264_; uint8_t v_isSharedCheck_3272_; 
v_a_3261_ = lean_ctor_get(v___x_3260_, 0);
v_isSharedCheck_3272_ = !lean_is_exclusive(v___x_3260_);
if (v_isSharedCheck_3272_ == 0)
{
v___x_3263_ = v___x_3260_;
v_isShared_3264_ = v_isSharedCheck_3272_;
goto v_resetjp_3262_;
}
else
{
lean_inc(v_a_3261_);
lean_dec(v___x_3260_);
v___x_3263_ = lean_box(0);
v_isShared_3264_ = v_isSharedCheck_3272_;
goto v_resetjp_3262_;
}
v_resetjp_3262_:
{
if (lean_obj_tag(v_a_3261_) == 0)
{
lean_object* v___x_3266_; 
if (v_isShared_3264_ == 0)
{
lean_ctor_set(v___x_3263_, 0, v_mvarId_3251_);
v___x_3266_ = v___x_3263_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v_mvarId_3251_);
v___x_3266_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
return v___x_3266_;
}
}
else
{
lean_object* v_val_3268_; lean_object* v___x_3270_; 
lean_dec(v_mvarId_3251_);
v_val_3268_ = lean_ctor_get(v_a_3261_, 0);
lean_inc(v_val_3268_);
lean_dec_ref_known(v_a_3261_, 1);
if (v_isShared_3264_ == 0)
{
lean_ctor_set(v___x_3263_, 0, v_val_3268_);
v___x_3270_ = v___x_3263_;
goto v_reusejp_3269_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v_val_3268_);
v___x_3270_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3269_;
}
v_reusejp_3269_:
{
return v___x_3270_;
}
}
}
}
else
{
lean_object* v_a_3273_; lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3280_; 
lean_dec(v_mvarId_3251_);
v_a_3273_ = lean_ctor_get(v___x_3260_, 0);
v_isSharedCheck_3280_ = !lean_is_exclusive(v___x_3260_);
if (v_isSharedCheck_3280_ == 0)
{
v___x_3275_ = v___x_3260_;
v_isShared_3276_ = v_isSharedCheck_3280_;
goto v_resetjp_3274_;
}
else
{
lean_inc(v_a_3273_);
lean_dec(v___x_3260_);
v___x_3275_ = lean_box(0);
v_isShared_3276_ = v_isSharedCheck_3280_;
goto v_resetjp_3274_;
}
v_resetjp_3274_:
{
lean_object* v___x_3278_; 
if (v_isShared_3276_ == 0)
{
v___x_3278_ = v___x_3275_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v_a_3273_);
v___x_3278_ = v_reuseFailAlloc_3279_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
return v___x_3278_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___boxed(lean_object* v_mvarId_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_){
_start:
{
lean_object* v_res_3287_; 
v_res_3287_ = l_Lean_MVarId_propext(v_mvarId_3281_, v_a_3282_, v_a_3283_, v_a_3284_, v_a_3285_);
lean_dec(v_a_3285_);
lean_dec_ref(v_a_3284_);
lean_dec(v_a_3283_);
lean_dec_ref(v_a_3282_);
return v_res_3287_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__0(lean_object* v_mvarId_3294_, lean_object* v___x_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_){
_start:
{
lean_object* v___y_3302_; lean_object* v___x_3346_; 
lean_inc(v_mvarId_3294_);
v___x_3346_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3294_, v___x_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_);
if (lean_obj_tag(v___x_3346_) == 0)
{
lean_object* v___x_3347_; uint8_t v_transparency_3348_; uint8_t v___x_3349_; uint8_t v___x_3350_; 
lean_dec_ref_known(v___x_3346_, 1);
v___x_3347_ = l_Lean_Meta_Context_config(v___y_3296_);
v_transparency_3348_ = lean_ctor_get_uint8(v___x_3347_, 9);
lean_dec_ref(v___x_3347_);
v___x_3349_ = 2;
v___x_3350_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3348_, v___x_3349_);
if (v___x_3350_ == 0)
{
lean_object* v_keyedConfig_3351_; uint8_t v_trackZetaDelta_3352_; lean_object* v_zetaDeltaSet_3353_; lean_object* v_lctx_3354_; lean_object* v_localInstances_3355_; lean_object* v_defEqCtx_x3f_3356_; lean_object* v_synthPendingDepth_3357_; lean_object* v_customCanUnfoldPredicate_x3f_3358_; uint8_t v_univApprox_3359_; uint8_t v_inTypeClassResolution_3360_; uint8_t v_cacheInferType_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; 
v_keyedConfig_3351_ = lean_ctor_get(v___y_3296_, 0);
v_trackZetaDelta_3352_ = lean_ctor_get_uint8(v___y_3296_, sizeof(void*)*7);
v_zetaDeltaSet_3353_ = lean_ctor_get(v___y_3296_, 1);
v_lctx_3354_ = lean_ctor_get(v___y_3296_, 2);
v_localInstances_3355_ = lean_ctor_get(v___y_3296_, 3);
v_defEqCtx_x3f_3356_ = lean_ctor_get(v___y_3296_, 4);
v_synthPendingDepth_3357_ = lean_ctor_get(v___y_3296_, 5);
v_customCanUnfoldPredicate_x3f_3358_ = lean_ctor_get(v___y_3296_, 6);
v_univApprox_3359_ = lean_ctor_get_uint8(v___y_3296_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3360_ = lean_ctor_get_uint8(v___y_3296_, sizeof(void*)*7 + 2);
v_cacheInferType_3361_ = lean_ctor_get_uint8(v___y_3296_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3351_);
v___x_3362_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3349_, v_keyedConfig_3351_);
lean_inc(v_customCanUnfoldPredicate_x3f_3358_);
lean_inc(v_synthPendingDepth_3357_);
lean_inc(v_defEqCtx_x3f_3356_);
lean_inc_ref(v_localInstances_3355_);
lean_inc_ref(v_lctx_3354_);
lean_inc(v_zetaDeltaSet_3353_);
v___x_3363_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3363_, 0, v___x_3362_);
lean_ctor_set(v___x_3363_, 1, v_zetaDeltaSet_3353_);
lean_ctor_set(v___x_3363_, 2, v_lctx_3354_);
lean_ctor_set(v___x_3363_, 3, v_localInstances_3355_);
lean_ctor_set(v___x_3363_, 4, v_defEqCtx_x3f_3356_);
lean_ctor_set(v___x_3363_, 5, v_synthPendingDepth_3357_);
lean_ctor_set(v___x_3363_, 6, v_customCanUnfoldPredicate_x3f_3358_);
lean_ctor_set_uint8(v___x_3363_, sizeof(void*)*7, v_trackZetaDelta_3352_);
lean_ctor_set_uint8(v___x_3363_, sizeof(void*)*7 + 1, v_univApprox_3359_);
lean_ctor_set_uint8(v___x_3363_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3360_);
lean_ctor_set_uint8(v___x_3363_, sizeof(void*)*7 + 3, v_cacheInferType_3361_);
lean_inc(v_mvarId_3294_);
v___x_3364_ = l_Lean_MVarId_getType_x27(v_mvarId_3294_, v___x_3363_, v___y_3297_, v___y_3298_, v___y_3299_);
lean_dec_ref_known(v___x_3363_, 7);
v___y_3302_ = v___x_3364_;
goto v___jp_3301_;
}
else
{
lean_object* v___x_3365_; 
lean_inc(v_mvarId_3294_);
v___x_3365_ = l_Lean_MVarId_getType_x27(v_mvarId_3294_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_);
v___y_3302_ = v___x_3365_;
goto v___jp_3301_;
}
}
else
{
lean_object* v_a_3366_; lean_object* v___x_3368_; uint8_t v_isShared_3369_; uint8_t v_isSharedCheck_3373_; 
lean_dec_ref(v___y_3296_);
lean_dec(v_mvarId_3294_);
v_a_3366_ = lean_ctor_get(v___x_3346_, 0);
v_isSharedCheck_3373_ = !lean_is_exclusive(v___x_3346_);
if (v_isSharedCheck_3373_ == 0)
{
v___x_3368_ = v___x_3346_;
v_isShared_3369_ = v_isSharedCheck_3373_;
goto v_resetjp_3367_;
}
else
{
lean_inc(v_a_3366_);
lean_dec(v___x_3346_);
v___x_3368_ = lean_box(0);
v_isShared_3369_ = v_isSharedCheck_3373_;
goto v_resetjp_3367_;
}
v_resetjp_3367_:
{
lean_object* v___x_3371_; 
if (v_isShared_3369_ == 0)
{
v___x_3371_ = v___x_3368_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v_a_3366_);
v___x_3371_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
return v___x_3371_;
}
}
}
v___jp_3301_:
{
if (lean_obj_tag(v___y_3302_) == 0)
{
lean_object* v_a_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; uint8_t v___x_3306_; 
v_a_3303_ = lean_ctor_get(v___y_3302_, 0);
lean_inc(v_a_3303_);
lean_dec_ref_known(v___y_3302_, 1);
v___x_3304_ = ((lean_object*)(l_Lean_MVarId_proofIrrelHeq___lam__0___closed__1));
v___x_3305_ = lean_unsigned_to_nat(4u);
v___x_3306_ = l_Lean_Expr_isAppOfArity(v_a_3303_, v___x_3304_, v___x_3305_);
if (v___x_3306_ == 0)
{
lean_object* v___x_3307_; lean_object* v___x_3308_; 
lean_dec(v_a_3303_);
lean_dec(v_mvarId_3294_);
v___x_3307_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3308_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3307_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_);
lean_dec_ref(v___y_3296_);
return v___x_3308_;
}
else
{
lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; 
v___x_3309_ = l_Lean_Expr_appFn_x21(v_a_3303_);
v___x_3310_ = l_Lean_Expr_appFn_x21(v___x_3309_);
lean_dec_ref(v___x_3309_);
v___x_3311_ = l_Lean_Expr_appArg_x21(v___x_3310_);
lean_dec_ref(v___x_3310_);
v___x_3312_ = l_Lean_Expr_appArg_x21(v_a_3303_);
lean_dec(v_a_3303_);
v___x_3313_ = ((lean_object*)(l_Lean_MVarId_proofIrrelHeq___lam__0___closed__3));
v___x_3314_ = lean_unsigned_to_nat(2u);
v___x_3315_ = lean_mk_empty_array_with_capacity(v___x_3314_);
v___x_3316_ = lean_array_push(v___x_3315_, v___x_3311_);
v___x_3317_ = lean_array_push(v___x_3316_, v___x_3312_);
v___x_3318_ = l_Lean_Meta_mkAppM(v___x_3313_, v___x_3317_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_);
lean_dec_ref(v___y_3296_);
if (lean_obj_tag(v___x_3318_) == 0)
{
lean_object* v_a_3319_; lean_object* v___x_3320_; lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3328_; 
v_a_3319_ = lean_ctor_get(v___x_3318_, 0);
lean_inc(v_a_3319_);
lean_dec_ref_known(v___x_3318_, 1);
v___x_3320_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_3294_, v_a_3319_, v___y_3297_);
v_isSharedCheck_3328_ = !lean_is_exclusive(v___x_3320_);
if (v_isSharedCheck_3328_ == 0)
{
lean_object* v_unused_3329_; 
v_unused_3329_ = lean_ctor_get(v___x_3320_, 0);
lean_dec(v_unused_3329_);
v___x_3322_ = v___x_3320_;
v_isShared_3323_ = v_isSharedCheck_3328_;
goto v_resetjp_3321_;
}
else
{
lean_dec(v___x_3320_);
v___x_3322_ = lean_box(0);
v_isShared_3323_ = v_isSharedCheck_3328_;
goto v_resetjp_3321_;
}
v_resetjp_3321_:
{
lean_object* v___x_3324_; lean_object* v___x_3326_; 
v___x_3324_ = lean_box(v___x_3306_);
if (v_isShared_3323_ == 0)
{
lean_ctor_set(v___x_3322_, 0, v___x_3324_);
v___x_3326_ = v___x_3322_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3327_; 
v_reuseFailAlloc_3327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3327_, 0, v___x_3324_);
v___x_3326_ = v_reuseFailAlloc_3327_;
goto v_reusejp_3325_;
}
v_reusejp_3325_:
{
return v___x_3326_;
}
}
}
else
{
lean_object* v_a_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3337_; 
lean_dec(v_mvarId_3294_);
v_a_3330_ = lean_ctor_get(v___x_3318_, 0);
v_isSharedCheck_3337_ = !lean_is_exclusive(v___x_3318_);
if (v_isSharedCheck_3337_ == 0)
{
v___x_3332_ = v___x_3318_;
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_a_3330_);
lean_dec(v___x_3318_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v___x_3335_; 
if (v_isShared_3333_ == 0)
{
v___x_3335_ = v___x_3332_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v_a_3330_);
v___x_3335_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
return v___x_3335_;
}
}
}
}
}
else
{
lean_object* v_a_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3345_; 
lean_dec_ref(v___y_3296_);
lean_dec(v_mvarId_3294_);
v_a_3338_ = lean_ctor_get(v___y_3302_, 0);
v_isSharedCheck_3345_ = !lean_is_exclusive(v___y_3302_);
if (v_isSharedCheck_3345_ == 0)
{
v___x_3340_ = v___y_3302_;
v_isShared_3341_ = v_isSharedCheck_3345_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_a_3338_);
lean_dec(v___y_3302_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3345_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
lean_object* v___x_3343_; 
if (v_isShared_3341_ == 0)
{
v___x_3343_ = v___x_3340_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v_a_3338_);
v___x_3343_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
return v___x_3343_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__0___boxed(lean_object* v_mvarId_3374_, lean_object* v___x_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_){
_start:
{
lean_object* v_res_3381_; 
v_res_3381_ = l_Lean_MVarId_proofIrrelHeq___lam__0(v_mvarId_3374_, v___x_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_);
lean_dec(v___y_3379_);
lean_dec_ref(v___y_3378_);
lean_dec(v___y_3377_);
return v_res_3381_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__1(lean_object* v___f_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_){
_start:
{
lean_object* v___x_3388_; 
v___x_3388_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v___f_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_);
if (lean_obj_tag(v___x_3388_) == 0)
{
lean_object* v_a_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3402_; 
v_a_3389_ = lean_ctor_get(v___x_3388_, 0);
v_isSharedCheck_3402_ = !lean_is_exclusive(v___x_3388_);
if (v_isSharedCheck_3402_ == 0)
{
v___x_3391_ = v___x_3388_;
v_isShared_3392_ = v_isSharedCheck_3402_;
goto v_resetjp_3390_;
}
else
{
lean_inc(v_a_3389_);
lean_dec(v___x_3388_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3402_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
if (lean_obj_tag(v_a_3389_) == 0)
{
uint8_t v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3396_; 
v___x_3393_ = 0;
v___x_3394_ = lean_box(v___x_3393_);
if (v_isShared_3392_ == 0)
{
lean_ctor_set(v___x_3391_, 0, v___x_3394_);
v___x_3396_ = v___x_3391_;
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
else
{
lean_object* v_val_3398_; lean_object* v___x_3400_; 
v_val_3398_ = lean_ctor_get(v_a_3389_, 0);
lean_inc(v_val_3398_);
lean_dec_ref_known(v_a_3389_, 1);
if (v_isShared_3392_ == 0)
{
lean_ctor_set(v___x_3391_, 0, v_val_3398_);
v___x_3400_ = v___x_3391_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v_val_3398_);
v___x_3400_ = v_reuseFailAlloc_3401_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
return v___x_3400_;
}
}
}
}
else
{
lean_object* v_a_3403_; lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3410_; 
v_a_3403_ = lean_ctor_get(v___x_3388_, 0);
v_isSharedCheck_3410_ = !lean_is_exclusive(v___x_3388_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3405_ = v___x_3388_;
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
else
{
lean_inc(v_a_3403_);
lean_dec(v___x_3388_);
v___x_3405_ = lean_box(0);
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
v_resetjp_3404_:
{
lean_object* v___x_3408_; 
if (v_isShared_3406_ == 0)
{
v___x_3408_ = v___x_3405_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v_a_3403_);
v___x_3408_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
return v___x_3408_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__1___boxed(lean_object* v___f_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_){
_start:
{
lean_object* v_res_3417_; 
v_res_3417_ = l_Lean_MVarId_proofIrrelHeq___lam__1(v___f_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_);
lean_dec(v___y_3415_);
lean_dec_ref(v___y_3414_);
lean_dec(v___y_3413_);
lean_dec_ref(v___y_3412_);
return v_res_3417_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq(lean_object* v_mvarId_3421_, lean_object* v_a_3422_, lean_object* v_a_3423_, lean_object* v_a_3424_, lean_object* v_a_3425_){
_start:
{
lean_object* v___x_3427_; lean_object* v___f_3428_; lean_object* v___f_3429_; lean_object* v___x_3430_; 
v___x_3427_ = ((lean_object*)(l_Lean_MVarId_proofIrrelHeq___closed__1));
lean_inc(v_mvarId_3421_);
v___f_3428_ = lean_alloc_closure((void*)(l_Lean_MVarId_proofIrrelHeq___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3428_, 0, v_mvarId_3421_);
lean_closure_set(v___f_3428_, 1, v___x_3427_);
v___f_3429_ = lean_alloc_closure((void*)(l_Lean_MVarId_proofIrrelHeq___lam__1___boxed), 6, 1);
lean_closure_set(v___f_3429_, 0, v___f_3428_);
v___x_3430_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_3421_, v___f_3429_, v_a_3422_, v_a_3423_, v_a_3424_, v_a_3425_);
return v___x_3430_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___boxed(lean_object* v_mvarId_3431_, lean_object* v_a_3432_, lean_object* v_a_3433_, lean_object* v_a_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_){
_start:
{
lean_object* v_res_3437_; 
v_res_3437_ = l_Lean_MVarId_proofIrrelHeq(v_mvarId_3431_, v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_);
lean_dec(v_a_3435_);
lean_dec_ref(v_a_3434_);
lean_dec(v_a_3433_);
lean_dec_ref(v_a_3432_);
return v_res_3437_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim___lam__0(lean_object* v_mvarId_3442_, lean_object* v___x_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_){
_start:
{
lean_object* v___y_3450_; lean_object* v___x_3493_; 
lean_inc(v_mvarId_3442_);
v___x_3493_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3442_, v___x_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_);
if (lean_obj_tag(v___x_3493_) == 0)
{
lean_object* v___x_3494_; uint8_t v_transparency_3495_; uint8_t v___x_3496_; uint8_t v___x_3497_; 
lean_dec_ref_known(v___x_3493_, 1);
v___x_3494_ = l_Lean_Meta_Context_config(v___y_3444_);
v_transparency_3495_ = lean_ctor_get_uint8(v___x_3494_, 9);
lean_dec_ref(v___x_3494_);
v___x_3496_ = 2;
v___x_3497_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3495_, v___x_3496_);
if (v___x_3497_ == 0)
{
lean_object* v_keyedConfig_3498_; uint8_t v_trackZetaDelta_3499_; lean_object* v_zetaDeltaSet_3500_; lean_object* v_lctx_3501_; lean_object* v_localInstances_3502_; lean_object* v_defEqCtx_x3f_3503_; lean_object* v_synthPendingDepth_3504_; lean_object* v_customCanUnfoldPredicate_x3f_3505_; uint8_t v_univApprox_3506_; uint8_t v_inTypeClassResolution_3507_; uint8_t v_cacheInferType_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; 
v_keyedConfig_3498_ = lean_ctor_get(v___y_3444_, 0);
v_trackZetaDelta_3499_ = lean_ctor_get_uint8(v___y_3444_, sizeof(void*)*7);
v_zetaDeltaSet_3500_ = lean_ctor_get(v___y_3444_, 1);
v_lctx_3501_ = lean_ctor_get(v___y_3444_, 2);
v_localInstances_3502_ = lean_ctor_get(v___y_3444_, 3);
v_defEqCtx_x3f_3503_ = lean_ctor_get(v___y_3444_, 4);
v_synthPendingDepth_3504_ = lean_ctor_get(v___y_3444_, 5);
v_customCanUnfoldPredicate_x3f_3505_ = lean_ctor_get(v___y_3444_, 6);
v_univApprox_3506_ = lean_ctor_get_uint8(v___y_3444_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3507_ = lean_ctor_get_uint8(v___y_3444_, sizeof(void*)*7 + 2);
v_cacheInferType_3508_ = lean_ctor_get_uint8(v___y_3444_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3498_);
v___x_3509_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3496_, v_keyedConfig_3498_);
lean_inc(v_customCanUnfoldPredicate_x3f_3505_);
lean_inc(v_synthPendingDepth_3504_);
lean_inc(v_defEqCtx_x3f_3503_);
lean_inc_ref(v_localInstances_3502_);
lean_inc_ref(v_lctx_3501_);
lean_inc(v_zetaDeltaSet_3500_);
v___x_3510_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3510_, 0, v___x_3509_);
lean_ctor_set(v___x_3510_, 1, v_zetaDeltaSet_3500_);
lean_ctor_set(v___x_3510_, 2, v_lctx_3501_);
lean_ctor_set(v___x_3510_, 3, v_localInstances_3502_);
lean_ctor_set(v___x_3510_, 4, v_defEqCtx_x3f_3503_);
lean_ctor_set(v___x_3510_, 5, v_synthPendingDepth_3504_);
lean_ctor_set(v___x_3510_, 6, v_customCanUnfoldPredicate_x3f_3505_);
lean_ctor_set_uint8(v___x_3510_, sizeof(void*)*7, v_trackZetaDelta_3499_);
lean_ctor_set_uint8(v___x_3510_, sizeof(void*)*7 + 1, v_univApprox_3506_);
lean_ctor_set_uint8(v___x_3510_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3507_);
lean_ctor_set_uint8(v___x_3510_, sizeof(void*)*7 + 3, v_cacheInferType_3508_);
lean_inc(v_mvarId_3442_);
v___x_3511_ = l_Lean_MVarId_getType_x27(v_mvarId_3442_, v___x_3510_, v___y_3445_, v___y_3446_, v___y_3447_);
lean_dec_ref_known(v___x_3510_, 7);
v___y_3450_ = v___x_3511_;
goto v___jp_3449_;
}
else
{
lean_object* v___x_3512_; 
lean_inc(v_mvarId_3442_);
v___x_3512_ = l_Lean_MVarId_getType_x27(v_mvarId_3442_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_);
v___y_3450_ = v___x_3512_;
goto v___jp_3449_;
}
}
else
{
lean_object* v_a_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3520_; 
lean_dec_ref(v___y_3444_);
lean_dec(v_mvarId_3442_);
v_a_3513_ = lean_ctor_get(v___x_3493_, 0);
v_isSharedCheck_3520_ = !lean_is_exclusive(v___x_3493_);
if (v_isSharedCheck_3520_ == 0)
{
v___x_3515_ = v___x_3493_;
v_isShared_3516_ = v_isSharedCheck_3520_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_a_3513_);
lean_dec(v___x_3493_);
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
v___jp_3449_:
{
if (lean_obj_tag(v___y_3450_) == 0)
{
lean_object* v_a_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; uint8_t v___x_3454_; 
v_a_3451_ = lean_ctor_get(v___y_3450_, 0);
lean_inc(v_a_3451_);
lean_dec_ref_known(v___y_3450_, 1);
v___x_3452_ = ((lean_object*)(l_Lean_MVarId_propext___lam__0___closed__4));
v___x_3453_ = lean_unsigned_to_nat(3u);
v___x_3454_ = l_Lean_Expr_isAppOfArity(v_a_3451_, v___x_3452_, v___x_3453_);
if (v___x_3454_ == 0)
{
lean_object* v___x_3455_; lean_object* v___x_3456_; 
lean_dec(v_a_3451_);
lean_dec(v_mvarId_3442_);
v___x_3455_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3456_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3455_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_);
lean_dec_ref(v___y_3444_);
return v___x_3456_;
}
else
{
lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; 
v___x_3457_ = l_Lean_Expr_appFn_x21(v_a_3451_);
v___x_3458_ = l_Lean_Expr_appArg_x21(v___x_3457_);
lean_dec_ref(v___x_3457_);
v___x_3459_ = l_Lean_Expr_appArg_x21(v_a_3451_);
lean_dec(v_a_3451_);
v___x_3460_ = ((lean_object*)(l_Lean_MVarId_subsingletonElim___lam__0___closed__1));
v___x_3461_ = lean_unsigned_to_nat(2u);
v___x_3462_ = lean_mk_empty_array_with_capacity(v___x_3461_);
v___x_3463_ = lean_array_push(v___x_3462_, v___x_3458_);
v___x_3464_ = lean_array_push(v___x_3463_, v___x_3459_);
v___x_3465_ = l_Lean_Meta_mkAppM(v___x_3460_, v___x_3464_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_);
lean_dec_ref(v___y_3444_);
if (lean_obj_tag(v___x_3465_) == 0)
{
lean_object* v_a_3466_; lean_object* v___x_3467_; lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3475_; 
v_a_3466_ = lean_ctor_get(v___x_3465_, 0);
lean_inc(v_a_3466_);
lean_dec_ref_known(v___x_3465_, 1);
v___x_3467_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_3442_, v_a_3466_, v___y_3445_);
v_isSharedCheck_3475_ = !lean_is_exclusive(v___x_3467_);
if (v_isSharedCheck_3475_ == 0)
{
lean_object* v_unused_3476_; 
v_unused_3476_ = lean_ctor_get(v___x_3467_, 0);
lean_dec(v_unused_3476_);
v___x_3469_ = v___x_3467_;
v_isShared_3470_ = v_isSharedCheck_3475_;
goto v_resetjp_3468_;
}
else
{
lean_dec(v___x_3467_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3475_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
lean_object* v___x_3471_; lean_object* v___x_3473_; 
v___x_3471_ = lean_box(v___x_3454_);
if (v_isShared_3470_ == 0)
{
lean_ctor_set(v___x_3469_, 0, v___x_3471_);
v___x_3473_ = v___x_3469_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v___x_3471_);
v___x_3473_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
return v___x_3473_;
}
}
}
else
{
lean_object* v_a_3477_; lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3484_; 
lean_dec(v_mvarId_3442_);
v_a_3477_ = lean_ctor_get(v___x_3465_, 0);
v_isSharedCheck_3484_ = !lean_is_exclusive(v___x_3465_);
if (v_isSharedCheck_3484_ == 0)
{
v___x_3479_ = v___x_3465_;
v_isShared_3480_ = v_isSharedCheck_3484_;
goto v_resetjp_3478_;
}
else
{
lean_inc(v_a_3477_);
lean_dec(v___x_3465_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3484_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
lean_object* v___x_3482_; 
if (v_isShared_3480_ == 0)
{
v___x_3482_ = v___x_3479_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v_a_3477_);
v___x_3482_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
return v___x_3482_;
}
}
}
}
}
else
{
lean_object* v_a_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3492_; 
lean_dec_ref(v___y_3444_);
lean_dec(v_mvarId_3442_);
v_a_3485_ = lean_ctor_get(v___y_3450_, 0);
v_isSharedCheck_3492_ = !lean_is_exclusive(v___y_3450_);
if (v_isSharedCheck_3492_ == 0)
{
v___x_3487_ = v___y_3450_;
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_a_3485_);
lean_dec(v___y_3450_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v___x_3490_; 
if (v_isShared_3488_ == 0)
{
v___x_3490_ = v___x_3487_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v_a_3485_);
v___x_3490_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
return v___x_3490_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim___lam__0___boxed(lean_object* v_mvarId_3521_, lean_object* v___x_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_){
_start:
{
lean_object* v_res_3528_; 
v_res_3528_ = l_Lean_MVarId_subsingletonElim___lam__0(v_mvarId_3521_, v___x_3522_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_);
lean_dec(v___y_3526_);
lean_dec_ref(v___y_3525_);
lean_dec(v___y_3524_);
return v_res_3528_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim(lean_object* v_mvarId_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_){
_start:
{
lean_object* v___x_3538_; lean_object* v___f_3539_; lean_object* v___f_3540_; lean_object* v___x_3541_; 
v___x_3538_ = ((lean_object*)(l_Lean_MVarId_subsingletonElim___closed__1));
lean_inc(v_mvarId_3532_);
v___f_3539_ = lean_alloc_closure((void*)(l_Lean_MVarId_subsingletonElim___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3539_, 0, v_mvarId_3532_);
lean_closure_set(v___f_3539_, 1, v___x_3538_);
v___f_3540_ = lean_alloc_closure((void*)(l_Lean_MVarId_proofIrrelHeq___lam__1___boxed), 6, 1);
lean_closure_set(v___f_3540_, 0, v___f_3539_);
v___x_3541_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_3532_, v___f_3540_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_);
return v___x_3541_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim___boxed(lean_object* v_mvarId_3542_, lean_object* v_a_3543_, lean_object* v_a_3544_, lean_object* v_a_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_){
_start:
{
lean_object* v_res_3548_; 
v_res_3548_ = l_Lean_MVarId_subsingletonElim(v_mvarId_3542_, v_a_3543_, v_a_3544_, v_a_3545_, v_a_3546_);
lean_dec(v_a_3546_);
lean_dec_ref(v_a_3545_);
lean_dec(v_a_3544_);
lean_dec_ref(v_a_3543_);
return v_res_3548_;
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
