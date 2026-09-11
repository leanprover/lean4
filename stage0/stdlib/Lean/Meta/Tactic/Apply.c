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
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_getMVarsNoDelayed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
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
lean_object* v_a_421_; lean_object* v___x_422_; 
v_a_421_ = lean_array_uget_borrowed(v_as_399_, v_i_401_);
lean_inc(v___y_406_);
lean_inc_ref(v___y_405_);
lean_inc(v___y_404_);
lean_inc_ref(v___y_403_);
lean_inc(v_a_421_);
v___x_422_ = lean_infer_type(v_a_421_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
if (lean_obj_tag(v___x_422_) == 0)
{
lean_object* v_snd_423_; lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_517_; 
v_snd_423_ = lean_ctor_get(v_b_402_, 1);
lean_inc(v_snd_423_);
v_a_424_ = lean_ctor_get(v___x_422_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_517_ == 0)
{
v___x_426_ = v___x_422_;
v_isShared_427_ = v_isSharedCheck_517_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_dec(v___x_422_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_517_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v_fst_428_; lean_object* v_fst_429_; lean_object* v_snd_430_; lean_object* v___y_432_; uint8_t v___y_433_; lean_object* v_a_440_; lean_object* v___y_444_; lean_object* v___x_505_; lean_object* v___x_506_; 
v_fst_428_ = lean_ctor_get(v_b_402_, 0);
lean_inc(v_fst_428_);
lean_dec_ref(v_b_402_);
v_fst_429_ = lean_ctor_get(v_snd_423_, 0);
lean_inc(v_fst_429_);
v_snd_430_ = lean_ctor_get(v_snd_423_, 1);
lean_inc(v_snd_430_);
lean_dec(v_snd_423_);
v___x_505_ = lean_box(0);
v___x_506_ = l_Lean_Meta_synthInstance(v_a_424_, v___x_505_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v_a_507_; lean_object* v___x_508_; lean_object* v___x_509_; uint8_t v___x_510_; 
v_a_507_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_a_507_);
lean_dec_ref_known(v___x_506_, 1);
v___x_508_ = lean_array_get_size(v_snd_430_);
v___x_509_ = lean_unsigned_to_nat(0u);
v___x_510_ = lean_nat_dec_eq(v___x_508_, v___x_509_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_511_ = lean_box(0);
lean_inc(v_snd_430_);
v___x_512_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0(v_a_507_, v_snd_430_, v_fst_428_, v___x_511_, v___x_419_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
v___y_444_ = v___x_512_;
goto v___jp_443_;
}
else
{
lean_object* v___x_513_; uint8_t v___x_514_; lean_object* v___x_515_; 
v___x_513_ = lean_box(0);
v___x_514_ = lean_unbox(v_fst_429_);
lean_inc(v_snd_430_);
v___x_515_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0(v_a_507_, v_snd_430_, v_fst_428_, v___x_513_, v___x_514_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
v___y_444_ = v___x_515_;
goto v___jp_443_;
}
}
else
{
lean_object* v_a_516_; 
lean_dec(v_fst_428_);
v_a_516_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_a_516_);
lean_dec_ref_known(v___x_506_, 1);
v_a_440_ = v_a_516_;
goto v___jp_439_;
}
v___jp_431_:
{
if (v___y_433_ == 0)
{
lean_object* v___x_434_; lean_object* v___x_435_; 
lean_del_object(v___x_426_);
v___x_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_434_, 0, v___y_432_);
lean_inc(v_a_421_);
v___x_435_ = lean_array_push(v_snd_430_, v_a_421_);
v_fst_414_ = v___x_434_;
v_fst_415_ = v_fst_429_;
v_snd_416_ = v___x_435_;
goto v___jp_413_;
}
else
{
lean_object* v___x_437_; 
lean_dec(v_snd_430_);
lean_dec(v_fst_429_);
lean_dec(v_mvarId_398_);
lean_dec(v_tacticName_397_);
if (v_isShared_427_ == 0)
{
lean_ctor_set_tag(v___x_426_, 1);
lean_ctor_set(v___x_426_, 0, v___y_432_);
v___x_437_ = v___x_426_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v___y_432_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
v___jp_439_:
{
uint8_t v___x_441_; 
v___x_441_ = l_Lean_Exception_isInterrupt(v_a_440_);
if (v___x_441_ == 0)
{
uint8_t v___x_442_; 
lean_inc_ref(v_a_440_);
v___x_442_ = l_Lean_Exception_isRuntime(v_a_440_);
v___y_432_ = v_a_440_;
v___y_433_ = v___x_442_;
goto v___jp_431_;
}
else
{
v___y_432_ = v_a_440_;
v___y_433_ = v___x_441_;
goto v___jp_431_;
}
}
v___jp_443_:
{
if (lean_obj_tag(v___y_444_) == 0)
{
lean_object* v_a_445_; lean_object* v_snd_446_; lean_object* v_snd_447_; lean_object* v_fst_448_; 
lean_dec(v_snd_430_);
lean_dec(v_fst_429_);
lean_del_object(v___x_426_);
v_a_445_ = lean_ctor_get(v___y_444_, 0);
lean_inc(v_a_445_);
lean_dec_ref_known(v___y_444_, 1);
v_snd_446_ = lean_ctor_get(v_a_445_, 1);
lean_inc(v_snd_446_);
v_snd_447_ = lean_ctor_get(v_snd_446_, 1);
lean_inc(v_snd_447_);
v_fst_448_ = lean_ctor_get(v_a_445_, 0);
lean_inc(v_fst_448_);
lean_dec(v_a_445_);
if (lean_obj_tag(v_fst_448_) == 1)
{
lean_object* v_fst_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_499_; 
v_fst_449_ = lean_ctor_get(v_snd_446_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v_snd_446_);
if (v_isSharedCheck_499_ == 0)
{
lean_object* v_unused_500_; 
v_unused_500_ = lean_ctor_get(v_snd_446_, 1);
lean_dec(v_unused_500_);
v___x_451_ = v_snd_446_;
v_isShared_452_ = v_isSharedCheck_499_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_fst_449_);
lean_dec(v_snd_446_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_499_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v_fst_453_; lean_object* v_snd_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_498_; 
v_fst_453_ = lean_ctor_get(v_snd_447_, 0);
v_snd_454_ = lean_ctor_get(v_snd_447_, 1);
v_isSharedCheck_498_ = !lean_is_exclusive(v_snd_447_);
if (v_isSharedCheck_498_ == 0)
{
v___x_456_ = v_snd_447_;
v_isShared_457_ = v_isSharedCheck_498_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_snd_454_);
lean_inc(v_fst_453_);
lean_dec(v_snd_447_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_498_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v_val_458_; lean_object* v___x_459_; 
v_val_458_ = lean_ctor_get(v_fst_448_, 0);
lean_inc(v_val_458_);
lean_dec_ref_known(v_fst_448_, 1);
lean_inc(v_a_421_);
v___x_459_ = l_Lean_Meta_isExprDefEq(v_a_421_, v_val_458_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
if (lean_obj_tag(v___x_459_) == 0)
{
lean_object* v_a_460_; uint8_t v___x_461_; 
v_a_460_ = lean_ctor_get(v___x_459_, 0);
lean_inc(v_a_460_);
lean_dec_ref_known(v___x_459_, 1);
v___x_461_ = lean_unbox(v_a_460_);
lean_dec(v_a_460_);
if (v___x_461_ == 0)
{
if (v_allowSynthFailures_396_ == 0)
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3);
lean_inc(v_mvarId_398_);
lean_inc(v_tacticName_397_);
v___x_463_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_397_, v_mvarId_398_, v___x_462_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
if (lean_obj_tag(v___x_463_) == 0)
{
lean_object* v___x_465_; 
lean_dec_ref_known(v___x_463_, 1);
if (v_isShared_457_ == 0)
{
v___x_465_ = v___x_456_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_fst_453_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v_snd_454_);
v___x_465_ = v_reuseFailAlloc_469_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
lean_object* v___x_467_; 
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 1, v___x_465_);
v___x_467_ = v___x_451_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_fst_449_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v___x_465_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
v_a_409_ = v___x_467_;
goto v___jp_408_;
}
}
}
else
{
lean_object* v_a_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_477_; 
lean_del_object(v___x_456_);
lean_dec(v_snd_454_);
lean_dec(v_fst_453_);
lean_del_object(v___x_451_);
lean_dec(v_fst_449_);
lean_dec(v_mvarId_398_);
lean_dec(v_tacticName_397_);
v_a_470_ = lean_ctor_get(v___x_463_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_477_ == 0)
{
v___x_472_ = v___x_463_;
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_a_470_);
lean_dec(v___x_463_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_475_; 
if (v_isShared_473_ == 0)
{
v___x_475_ = v___x_472_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_a_470_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
}
else
{
lean_object* v___x_479_; 
if (v_isShared_457_ == 0)
{
v___x_479_ = v___x_456_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_fst_453_);
lean_ctor_set(v_reuseFailAlloc_483_, 1, v_snd_454_);
v___x_479_ = v_reuseFailAlloc_483_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
lean_object* v___x_481_; 
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 1, v___x_479_);
v___x_481_ = v___x_451_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_fst_449_);
lean_ctor_set(v_reuseFailAlloc_482_, 1, v___x_479_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
v_a_409_ = v___x_481_;
goto v___jp_408_;
}
}
}
}
else
{
lean_object* v___x_485_; 
if (v_isShared_457_ == 0)
{
v___x_485_ = v___x_456_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_fst_453_);
lean_ctor_set(v_reuseFailAlloc_489_, 1, v_snd_454_);
v___x_485_ = v_reuseFailAlloc_489_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
lean_object* v___x_487_; 
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 1, v___x_485_);
v___x_487_ = v___x_451_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_fst_449_);
lean_ctor_set(v_reuseFailAlloc_488_, 1, v___x_485_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
v_a_409_ = v___x_487_;
goto v___jp_408_;
}
}
}
}
else
{
lean_object* v_a_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_497_; 
lean_del_object(v___x_456_);
lean_dec(v_snd_454_);
lean_dec(v_fst_453_);
lean_del_object(v___x_451_);
lean_dec(v_fst_449_);
lean_dec(v_mvarId_398_);
lean_dec(v_tacticName_397_);
v_a_490_ = lean_ctor_get(v___x_459_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_459_);
if (v_isSharedCheck_497_ == 0)
{
v___x_492_ = v___x_459_;
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_a_490_);
lean_dec(v___x_459_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_495_; 
if (v_isShared_493_ == 0)
{
v___x_495_ = v___x_492_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_a_490_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
}
}
}
else
{
lean_object* v_fst_501_; lean_object* v_fst_502_; lean_object* v_snd_503_; 
lean_dec(v_fst_448_);
v_fst_501_ = lean_ctor_get(v_snd_446_, 0);
lean_inc(v_fst_501_);
lean_dec(v_snd_446_);
v_fst_502_ = lean_ctor_get(v_snd_447_, 0);
lean_inc(v_fst_502_);
v_snd_503_ = lean_ctor_get(v_snd_447_, 1);
lean_inc(v_snd_503_);
lean_dec(v_snd_447_);
v_fst_414_ = v_fst_501_;
v_fst_415_ = v_fst_502_;
v_snd_416_ = v_snd_503_;
goto v___jp_413_;
}
}
else
{
lean_object* v_a_504_; 
v_a_504_ = lean_ctor_get(v___y_444_, 0);
lean_inc(v_a_504_);
lean_dec_ref_known(v___y_444_, 1);
v_a_440_ = v_a_504_;
goto v___jp_439_;
}
}
}
}
else
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_525_; 
lean_dec_ref(v_b_402_);
lean_dec(v_mvarId_398_);
lean_dec(v_tacticName_397_);
v_a_518_ = lean_ctor_get(v___x_422_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_525_ == 0)
{
v___x_520_ = v___x_422_;
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_422_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_523_; 
if (v_isShared_521_ == 0)
{
v___x_523_ = v___x_520_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_a_518_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___boxed(lean_object* v_allowSynthFailures_526_, lean_object* v_tacticName_527_, lean_object* v_mvarId_528_, lean_object* v_as_529_, lean_object* v_sz_530_, lean_object* v_i_531_, lean_object* v_b_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_){
_start:
{
uint8_t v_allowSynthFailures_boxed_538_; size_t v_sz_boxed_539_; size_t v_i_boxed_540_; lean_object* v_res_541_; 
v_allowSynthFailures_boxed_538_ = lean_unbox(v_allowSynthFailures_526_);
v_sz_boxed_539_ = lean_unbox_usize(v_sz_530_);
lean_dec(v_sz_530_);
v_i_boxed_540_ = lean_unbox_usize(v_i_531_);
lean_dec(v_i_531_);
v_res_541_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0(v_allowSynthFailures_boxed_538_, v_tacticName_527_, v_mvarId_528_, v_as_529_, v_sz_boxed_539_, v_i_boxed_540_, v_b_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
lean_dec_ref(v_as_529_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step(lean_object* v_tacticName_551_, lean_object* v_mvarId_552_, uint8_t v_allowSynthFailures_553_, lean_object* v_mvars_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_){
_start:
{
lean_object* v_postponed_560_; lean_object* v___x_561_; size_t v_sz_562_; size_t v___x_563_; lean_object* v___x_564_; 
v_postponed_560_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0));
v___x_561_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__2));
v_sz_562_ = lean_array_size(v_mvars_554_);
v___x_563_ = ((size_t)0ULL);
v___x_564_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0(v_allowSynthFailures_553_, v_tacticName_551_, v_mvarId_552_, v_mvars_554_, v_sz_562_, v___x_563_, v___x_561_, v_a_555_, v_a_556_, v_a_557_, v_a_558_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_587_; 
v_a_565_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_587_ == 0)
{
v___x_567_ = v___x_564_;
v_isShared_568_ = v_isSharedCheck_587_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_564_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_587_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v_fst_569_; 
v_fst_569_ = lean_ctor_get(v_a_565_, 0);
lean_inc(v_fst_569_);
if (lean_obj_tag(v_fst_569_) == 1)
{
lean_object* v_snd_570_; lean_object* v_fst_571_; uint8_t v___x_572_; 
v_snd_570_ = lean_ctor_get(v_a_565_, 1);
lean_inc(v_snd_570_);
lean_dec(v_a_565_);
v_fst_571_ = lean_ctor_get(v_snd_570_, 0);
v___x_572_ = lean_unbox(v_fst_571_);
if (v___x_572_ == 0)
{
lean_dec(v_snd_570_);
if (v_allowSynthFailures_553_ == 0)
{
lean_object* v_val_573_; lean_object* v___x_575_; 
v_val_573_ = lean_ctor_get(v_fst_569_, 0);
lean_inc(v_val_573_);
lean_dec_ref_known(v_fst_569_, 1);
if (v_isShared_568_ == 0)
{
lean_ctor_set_tag(v___x_567_, 1);
lean_ctor_set(v___x_567_, 0, v_val_573_);
v___x_575_ = v___x_567_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_val_573_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
else
{
lean_object* v___x_578_; 
lean_dec_ref_known(v_fst_569_, 1);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 0, v_postponed_560_);
v___x_578_ = v___x_567_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_postponed_560_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
else
{
lean_object* v_snd_580_; lean_object* v___x_582_; 
lean_dec_ref_known(v_fst_569_, 1);
v_snd_580_ = lean_ctor_get(v_snd_570_, 1);
lean_inc(v_snd_580_);
lean_dec(v_snd_570_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 0, v_snd_580_);
v___x_582_ = v___x_567_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_snd_580_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
else
{
lean_object* v___x_585_; 
lean_dec(v_fst_569_);
lean_dec(v_a_565_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 0, v_postponed_560_);
v___x_585_ = v___x_567_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_postponed_560_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
else
{
lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_595_; 
v_a_588_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_595_ == 0)
{
v___x_590_ = v___x_564_;
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v___x_564_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_593_; 
if (v_isShared_591_ == 0)
{
v___x_593_ = v___x_590_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_a_588_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___boxed(lean_object* v_tacticName_596_, lean_object* v_mvarId_597_, lean_object* v_allowSynthFailures_598_, lean_object* v_mvars_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_){
_start:
{
uint8_t v_allowSynthFailures_boxed_605_; lean_object* v_res_606_; 
v_allowSynthFailures_boxed_605_ = lean_unbox(v_allowSynthFailures_598_);
v_res_606_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step(v_tacticName_596_, v_mvarId_597_, v_allowSynthFailures_boxed_605_, v_mvars_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_);
lean_dec(v_a_603_);
lean_dec_ref(v_a_602_);
lean_dec(v_a_601_);
lean_dec_ref(v_a_600_);
lean_dec_ref(v_mvars_599_);
return v_res_606_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_keys_607_, lean_object* v_i_608_, lean_object* v_k_609_){
_start:
{
lean_object* v___x_610_; uint8_t v___x_611_; 
v___x_610_ = lean_array_get_size(v_keys_607_);
v___x_611_ = lean_nat_dec_lt(v_i_608_, v___x_610_);
if (v___x_611_ == 0)
{
lean_dec(v_i_608_);
return v___x_611_;
}
else
{
lean_object* v_k_x27_612_; uint8_t v___x_613_; 
v_k_x27_612_ = lean_array_fget_borrowed(v_keys_607_, v_i_608_);
v___x_613_ = l_Lean_instBEqMVarId_beq(v_k_609_, v_k_x27_612_);
if (v___x_613_ == 0)
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = lean_unsigned_to_nat(1u);
v___x_615_ = lean_nat_add(v_i_608_, v___x_614_);
lean_dec(v_i_608_);
v_i_608_ = v___x_615_;
goto _start;
}
else
{
lean_dec(v_i_608_);
return v___x_611_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_keys_617_, lean_object* v_i_618_, lean_object* v_k_619_){
_start:
{
uint8_t v_res_620_; lean_object* v_r_621_; 
v_res_620_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_617_, v_i_618_, v_k_619_);
lean_dec(v_k_619_);
lean_dec_ref(v_keys_617_);
v_r_621_ = lean_box(v_res_620_);
return v_r_621_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(lean_object* v_x_622_, size_t v_x_623_, lean_object* v_x_624_){
_start:
{
if (lean_obj_tag(v_x_622_) == 0)
{
lean_object* v_es_625_; lean_object* v___x_626_; size_t v___x_627_; size_t v___x_628_; lean_object* v_j_629_; lean_object* v___x_630_; 
v_es_625_ = lean_ctor_get(v_x_622_, 0);
v___x_626_ = lean_box(2);
v___x_627_ = ((size_t)31ULL);
v___x_628_ = lean_usize_land(v_x_623_, v___x_627_);
v_j_629_ = lean_usize_to_nat(v___x_628_);
v___x_630_ = lean_array_get_borrowed(v___x_626_, v_es_625_, v_j_629_);
lean_dec(v_j_629_);
switch(lean_obj_tag(v___x_630_))
{
case 0:
{
lean_object* v_key_631_; uint8_t v___x_632_; 
v_key_631_ = lean_ctor_get(v___x_630_, 0);
v___x_632_ = l_Lean_instBEqMVarId_beq(v_x_624_, v_key_631_);
return v___x_632_;
}
case 1:
{
lean_object* v_node_633_; size_t v___x_634_; size_t v___x_635_; 
v_node_633_ = lean_ctor_get(v___x_630_, 0);
v___x_634_ = ((size_t)5ULL);
v___x_635_ = lean_usize_shift_right(v_x_623_, v___x_634_);
v_x_622_ = v_node_633_;
v_x_623_ = v___x_635_;
goto _start;
}
default: 
{
uint8_t v___x_637_; 
v___x_637_ = 0;
return v___x_637_;
}
}
}
else
{
lean_object* v_ks_638_; lean_object* v___x_639_; uint8_t v___x_640_; 
v_ks_638_ = lean_ctor_get(v_x_622_, 0);
v___x_639_ = lean_unsigned_to_nat(0u);
v___x_640_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(v_ks_638_, v___x_639_, v_x_624_);
return v___x_640_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_641_, lean_object* v_x_642_, lean_object* v_x_643_){
_start:
{
size_t v_x_2811__boxed_644_; uint8_t v_res_645_; lean_object* v_r_646_; 
v_x_2811__boxed_644_ = lean_unbox_usize(v_x_642_);
lean_dec(v_x_642_);
v_res_645_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(v_x_641_, v_x_2811__boxed_644_, v_x_643_);
lean_dec(v_x_643_);
lean_dec_ref(v_x_641_);
v_r_646_ = lean_box(v_res_645_);
return v_r_646_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(lean_object* v_x_647_, lean_object* v_x_648_){
_start:
{
uint64_t v___x_649_; size_t v___x_650_; uint8_t v___x_651_; 
v___x_649_ = l_Lean_instHashableMVarId_hash(v_x_648_);
v___x_650_ = lean_uint64_to_usize(v___x_649_);
v___x_651_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(v_x_647_, v___x_650_, v_x_648_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg___boxed(lean_object* v_x_652_, lean_object* v_x_653_){
_start:
{
uint8_t v_res_654_; lean_object* v_r_655_; 
v_res_654_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(v_x_652_, v_x_653_);
lean_dec(v_x_653_);
lean_dec_ref(v_x_652_);
v_r_655_ = lean_box(v_res_654_);
return v_r_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(lean_object* v_mvarId_656_, lean_object* v___y_657_){
_start:
{
lean_object* v___x_659_; lean_object* v_mctx_660_; lean_object* v_eAssignment_661_; uint8_t v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_659_ = lean_st_ref_get(v___y_657_);
v_mctx_660_ = lean_ctor_get(v___x_659_, 0);
lean_inc_ref(v_mctx_660_);
lean_dec(v___x_659_);
v_eAssignment_661_ = lean_ctor_get(v_mctx_660_, 8);
lean_inc_ref(v_eAssignment_661_);
lean_dec_ref(v_mctx_660_);
v___x_662_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(v_eAssignment_661_, v_mvarId_656_);
lean_dec_ref(v_eAssignment_661_);
v___x_663_ = lean_box(v___x_662_);
v___x_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_664_, 0, v___x_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg___boxed(lean_object* v_mvarId_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v_mvarId_665_, v___y_666_);
lean_dec(v___y_666_);
lean_dec(v_mvarId_665_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1(uint8_t v_synthAssignedInstances_669_, lean_object* v_as_670_, size_t v_sz_671_, size_t v_i_672_, lean_object* v_b_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v_a_680_; uint8_t v___x_684_; 
v___x_684_ = lean_usize_dec_lt(v_i_672_, v_sz_671_);
if (v___x_684_ == 0)
{
lean_object* v___x_685_; 
v___x_685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_685_, 0, v_b_673_);
return v___x_685_;
}
else
{
lean_object* v_snd_686_; lean_object* v_fst_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_737_; 
v_snd_686_ = lean_ctor_get(v_b_673_, 1);
v_fst_687_ = lean_ctor_get(v_b_673_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v_b_673_);
if (v_isSharedCheck_737_ == 0)
{
v___x_689_ = v_b_673_;
v_isShared_690_ = v_isSharedCheck_737_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_snd_686_);
lean_inc(v_fst_687_);
lean_dec(v_b_673_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_737_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v_array_691_; lean_object* v_start_692_; lean_object* v_stop_693_; uint8_t v___x_694_; 
v_array_691_ = lean_ctor_get(v_snd_686_, 0);
v_start_692_ = lean_ctor_get(v_snd_686_, 1);
v_stop_693_ = lean_ctor_get(v_snd_686_, 2);
v___x_694_ = lean_nat_dec_lt(v_start_692_, v_stop_693_);
if (v___x_694_ == 0)
{
lean_object* v___x_696_; 
if (v_isShared_690_ == 0)
{
v___x_696_ = v___x_689_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_fst_687_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v_snd_686_);
v___x_696_ = v_reuseFailAlloc_698_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
lean_object* v___x_697_; 
v___x_697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_697_, 0, v___x_696_);
return v___x_697_;
}
}
else
{
lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_733_; 
lean_inc(v_stop_693_);
lean_inc(v_start_692_);
lean_inc_ref(v_array_691_);
v_isSharedCheck_733_ = !lean_is_exclusive(v_snd_686_);
if (v_isSharedCheck_733_ == 0)
{
lean_object* v_unused_734_; lean_object* v_unused_735_; lean_object* v_unused_736_; 
v_unused_734_ = lean_ctor_get(v_snd_686_, 2);
lean_dec(v_unused_734_);
v_unused_735_ = lean_ctor_get(v_snd_686_, 1);
lean_dec(v_unused_735_);
v_unused_736_ = lean_ctor_get(v_snd_686_, 0);
lean_dec(v_unused_736_);
v___x_700_ = v_snd_686_;
v_isShared_701_ = v_isSharedCheck_733_;
goto v_resetjp_699_;
}
else
{
lean_dec(v_snd_686_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_733_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_706_; 
v___x_702_ = lean_array_fget(v_array_691_, v_start_692_);
v___x_703_ = lean_unsigned_to_nat(1u);
v___x_704_ = lean_nat_add(v_start_692_, v___x_703_);
lean_dec(v_start_692_);
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 1, v___x_704_);
v___x_706_ = v___x_700_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_array_691_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v___x_704_);
lean_ctor_set(v_reuseFailAlloc_732_, 2, v_stop_693_);
v___x_706_ = v_reuseFailAlloc_732_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
uint8_t v___x_707_; uint8_t v___x_708_; 
v___x_707_ = lean_unbox(v___x_702_);
lean_dec(v___x_702_);
v___x_708_ = l_Lean_BinderInfo_isInstImplicit(v___x_707_);
if (v___x_708_ == 0)
{
lean_object* v___x_710_; 
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 1, v___x_706_);
v___x_710_ = v___x_689_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_fst_687_);
lean_ctor_set(v_reuseFailAlloc_711_, 1, v___x_706_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
v_a_680_ = v___x_710_;
goto v___jp_679_;
}
}
else
{
lean_object* v_a_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v_a_712_ = lean_array_uget_borrowed(v_as_670_, v_i_672_);
v___x_713_ = l_Lean_Expr_mvarId_x21(v_a_712_);
v___x_714_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v___x_713_, v___y_675_);
lean_dec(v___x_713_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v_a_715_; 
v_a_715_ = lean_ctor_get(v___x_714_, 0);
lean_inc(v_a_715_);
lean_dec_ref_known(v___x_714_, 1);
if (v_synthAssignedInstances_669_ == 0)
{
uint8_t v___x_723_; 
v___x_723_ = lean_unbox(v_a_715_);
lean_dec(v_a_715_);
if (v___x_723_ == 0)
{
if (v___x_708_ == 0)
{
goto v___jp_716_;
}
else
{
lean_del_object(v___x_689_);
goto v___jp_720_;
}
}
else
{
goto v___jp_716_;
}
}
else
{
lean_dec(v_a_715_);
lean_del_object(v___x_689_);
goto v___jp_720_;
}
v___jp_716_:
{
lean_object* v___x_718_; 
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 1, v___x_706_);
v___x_718_ = v___x_689_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_fst_687_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v___x_706_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
v_a_680_ = v___x_718_;
goto v___jp_679_;
}
}
v___jp_720_:
{
lean_object* v___x_721_; lean_object* v___x_722_; 
lean_inc(v_a_712_);
v___x_721_ = lean_array_push(v_fst_687_, v_a_712_);
v___x_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
lean_ctor_set(v___x_722_, 1, v___x_706_);
v_a_680_ = v___x_722_;
goto v___jp_679_;
}
}
else
{
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_731_; 
lean_dec_ref(v___x_706_);
lean_del_object(v___x_689_);
lean_dec(v_fst_687_);
v_a_724_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_731_ == 0)
{
v___x_726_ = v___x_714_;
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___x_714_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_729_; 
if (v_isShared_727_ == 0)
{
v___x_729_ = v___x_726_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_a_724_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
}
}
}
}
}
v___jp_679_:
{
size_t v___x_681_; size_t v___x_682_; 
v___x_681_ = ((size_t)1ULL);
v___x_682_ = lean_usize_add(v_i_672_, v___x_681_);
v_i_672_ = v___x_682_;
v_b_673_ = v_a_680_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1___boxed(lean_object* v_synthAssignedInstances_738_, lean_object* v_as_739_, lean_object* v_sz_740_, lean_object* v_i_741_, lean_object* v_b_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_){
_start:
{
uint8_t v_synthAssignedInstances_boxed_748_; size_t v_sz_boxed_749_; size_t v_i_boxed_750_; lean_object* v_res_751_; 
v_synthAssignedInstances_boxed_748_ = lean_unbox(v_synthAssignedInstances_738_);
v_sz_boxed_749_ = lean_unbox_usize(v_sz_740_);
lean_dec(v_sz_740_);
v_i_boxed_750_ = lean_unbox_usize(v_i_741_);
lean_dec(v_i_741_);
v_res_751_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1(v_synthAssignedInstances_boxed_748_, v_as_739_, v_sz_boxed_749_, v_i_boxed_750_, v_b_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_);
lean_dec(v___y_746_);
lean_dec_ref(v___y_745_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec_ref(v_as_739_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg(lean_object* v_tacticName_752_, lean_object* v_mvarId_753_, uint8_t v_allowSynthFailures_754_, lean_object* v_a_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_){
_start:
{
lean_object* v___x_761_; lean_object* v___x_762_; uint8_t v___x_763_; 
v___x_761_ = lean_array_get_size(v_a_755_);
v___x_762_ = lean_unsigned_to_nat(0u);
v___x_763_ = lean_nat_dec_eq(v___x_761_, v___x_762_);
if (v___x_763_ == 0)
{
lean_object* v___x_764_; 
lean_inc(v_mvarId_753_);
lean_inc(v_tacticName_752_);
v___x_764_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step(v_tacticName_752_, v_mvarId_753_, v_allowSynthFailures_754_, v_a_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
lean_dec_ref(v_a_755_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_object* v_a_765_; 
v_a_765_ = lean_ctor_get(v___x_764_, 0);
lean_inc(v_a_765_);
lean_dec_ref_known(v___x_764_, 1);
v_a_755_ = v_a_765_;
goto _start;
}
else
{
lean_dec(v_mvarId_753_);
lean_dec(v_tacticName_752_);
return v___x_764_;
}
}
else
{
lean_object* v___x_767_; 
lean_dec(v_mvarId_753_);
lean_dec(v_tacticName_752_);
v___x_767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_767_, 0, v_a_755_);
return v___x_767_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg___boxed(lean_object* v_tacticName_768_, lean_object* v_mvarId_769_, lean_object* v_allowSynthFailures_770_, lean_object* v_a_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
uint8_t v_allowSynthFailures_boxed_777_; lean_object* v_res_778_; 
v_allowSynthFailures_boxed_777_ = lean_unbox(v_allowSynthFailures_770_);
v_res_778_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg(v_tacticName_768_, v_mvarId_769_, v_allowSynthFailures_boxed_777_, v_a_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_synthAppInstances(lean_object* v_tacticName_779_, lean_object* v_mvarId_780_, lean_object* v_mvarsNew_781_, lean_object* v_binderInfos_782_, uint8_t v_synthAssignedInstances_783_, uint8_t v_allowSynthFailures_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_){
_start:
{
lean_object* v___x_790_; lean_object* v_todo_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; size_t v_sz_795_; size_t v___x_796_; lean_object* v___x_797_; 
v___x_790_ = lean_unsigned_to_nat(0u);
v_todo_791_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0));
v___x_792_ = lean_array_get_size(v_binderInfos_782_);
v___x_793_ = l_Array_toSubarray___redArg(v_binderInfos_782_, v___x_790_, v___x_792_);
v___x_794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_794_, 0, v_todo_791_);
lean_ctor_set(v___x_794_, 1, v___x_793_);
v_sz_795_ = lean_array_size(v_mvarsNew_781_);
v___x_796_ = ((size_t)0ULL);
v___x_797_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1(v_synthAssignedInstances_783_, v_mvarsNew_781_, v_sz_795_, v___x_796_, v___x_794_, v_a_785_, v_a_786_, v_a_787_, v_a_788_);
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v_a_798_; lean_object* v_fst_799_; lean_object* v___x_800_; 
v_a_798_ = lean_ctor_get(v___x_797_, 0);
lean_inc(v_a_798_);
lean_dec_ref_known(v___x_797_, 1);
v_fst_799_ = lean_ctor_get(v_a_798_, 0);
lean_inc(v_fst_799_);
lean_dec(v_a_798_);
v___x_800_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg(v_tacticName_779_, v_mvarId_780_, v_allowSynthFailures_784_, v_fst_799_, v_a_785_, v_a_786_, v_a_787_, v_a_788_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_808_; 
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_808_ == 0)
{
lean_object* v_unused_809_; 
v_unused_809_ = lean_ctor_get(v___x_800_, 0);
lean_dec(v_unused_809_);
v___x_802_ = v___x_800_;
v_isShared_803_ = v_isSharedCheck_808_;
goto v_resetjp_801_;
}
else
{
lean_dec(v___x_800_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_808_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_804_; lean_object* v___x_806_; 
v___x_804_ = lean_box(0);
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 0, v___x_804_);
v___x_806_ = v___x_802_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_804_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
}
else
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
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
else
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_825_; 
lean_dec(v_mvarId_780_);
lean_dec(v_tacticName_779_);
v_a_818_ = lean_ctor_get(v___x_797_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_825_ == 0)
{
v___x_820_ = v___x_797_;
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_797_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_823_; 
if (v_isShared_821_ == 0)
{
v___x_823_ = v___x_820_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_a_818_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_synthAppInstances___boxed(lean_object* v_tacticName_826_, lean_object* v_mvarId_827_, lean_object* v_mvarsNew_828_, lean_object* v_binderInfos_829_, lean_object* v_synthAssignedInstances_830_, lean_object* v_allowSynthFailures_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_){
_start:
{
uint8_t v_synthAssignedInstances_boxed_837_; uint8_t v_allowSynthFailures_boxed_838_; lean_object* v_res_839_; 
v_synthAssignedInstances_boxed_837_ = lean_unbox(v_synthAssignedInstances_830_);
v_allowSynthFailures_boxed_838_ = lean_unbox(v_allowSynthFailures_831_);
v_res_839_ = l_Lean_Meta_synthAppInstances(v_tacticName_826_, v_mvarId_827_, v_mvarsNew_828_, v_binderInfos_829_, v_synthAssignedInstances_boxed_837_, v_allowSynthFailures_boxed_838_, v_a_832_, v_a_833_, v_a_834_, v_a_835_);
lean_dec(v_a_835_);
lean_dec_ref(v_a_834_);
lean_dec(v_a_833_);
lean_dec_ref(v_a_832_);
lean_dec_ref(v_mvarsNew_828_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0(lean_object* v_mvarId_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v_mvarId_840_, v___y_842_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___boxed(lean_object* v_mvarId_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0(v_mvarId_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec(v_mvarId_847_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2(lean_object* v_tacticName_854_, lean_object* v_mvarId_855_, uint8_t v_allowSynthFailures_856_, lean_object* v_inst_857_, lean_object* v_a_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg(v_tacticName_854_, v_mvarId_855_, v_allowSynthFailures_856_, v_a_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2___boxed(lean_object* v_tacticName_865_, lean_object* v_mvarId_866_, lean_object* v_allowSynthFailures_867_, lean_object* v_inst_868_, lean_object* v_a_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
uint8_t v_allowSynthFailures_boxed_875_; lean_object* v_res_876_; 
v_allowSynthFailures_boxed_875_ = lean_unbox(v_allowSynthFailures_867_);
v_res_876_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_synthAppInstances_spec__2(v_tacticName_865_, v_mvarId_866_, v_allowSynthFailures_boxed_875_, v_inst_868_, v_a_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_);
lean_dec(v___y_873_);
lean_dec_ref(v___y_872_);
lean_dec(v___y_871_);
lean_dec_ref(v___y_870_);
return v_res_876_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0(lean_object* v_00_u03b2_877_, lean_object* v_x_878_, lean_object* v_x_879_){
_start:
{
uint8_t v___x_880_; 
v___x_880_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(v_x_878_, v_x_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___boxed(lean_object* v_00_u03b2_881_, lean_object* v_x_882_, lean_object* v_x_883_){
_start:
{
uint8_t v_res_884_; lean_object* v_r_885_; 
v_res_884_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0(v_00_u03b2_881_, v_x_882_, v_x_883_);
lean_dec(v_x_883_);
lean_dec_ref(v_x_882_);
v_r_885_ = lean_box(v_res_884_);
return v_r_885_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_886_, lean_object* v_x_887_, size_t v_x_888_, lean_object* v_x_889_){
_start:
{
uint8_t v___x_890_; 
v___x_890_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(v_x_887_, v_x_888_, v_x_889_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_891_, lean_object* v_x_892_, lean_object* v_x_893_, lean_object* v_x_894_){
_start:
{
size_t v_x_3145__boxed_895_; uint8_t v_res_896_; lean_object* v_r_897_; 
v_x_3145__boxed_895_ = lean_unbox_usize(v_x_893_);
lean_dec(v_x_893_);
v_res_896_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1(v_00_u03b2_891_, v_x_892_, v_x_3145__boxed_895_, v_x_894_);
lean_dec(v_x_894_);
lean_dec_ref(v_x_892_);
v_r_897_ = lean_box(v_res_896_);
return v_r_897_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_898_, lean_object* v_keys_899_, lean_object* v_vals_900_, lean_object* v_heq_901_, lean_object* v_i_902_, lean_object* v_k_903_){
_start:
{
uint8_t v___x_904_; 
v___x_904_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_899_, v_i_902_, v_k_903_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_905_, lean_object* v_keys_906_, lean_object* v_vals_907_, lean_object* v_heq_908_, lean_object* v_i_909_, lean_object* v_k_910_){
_start:
{
uint8_t v_res_911_; lean_object* v_r_912_; 
v_res_911_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_905_, v_keys_906_, v_vals_907_, v_heq_908_, v_i_909_, v_k_910_);
lean_dec(v_k_910_);
lean_dec_ref(v_vals_907_);
lean_dec_ref(v_keys_906_);
v_r_912_ = lean_box(v_res_911_);
return v_r_912_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(lean_object* v_newMVars_913_, lean_object* v_binderInfos_914_, lean_object* v_a_915_, lean_object* v_n_916_, lean_object* v_i_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v_zero_923_; uint8_t v_isZero_924_; 
v_zero_923_ = lean_unsigned_to_nat(0u);
v_isZero_924_ = lean_nat_dec_eq(v_i_917_, v_zero_923_);
if (v_isZero_924_ == 1)
{
lean_object* v___x_925_; lean_object* v___x_926_; 
lean_dec(v_i_917_);
lean_dec(v_a_915_);
v___x_925_ = lean_box(0);
v___x_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_926_, 0, v___x_925_);
return v___x_926_;
}
else
{
lean_object* v_one_927_; lean_object* v_n_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v_a_934_; uint8_t v___x_935_; 
v_one_927_ = lean_unsigned_to_nat(1u);
v_n_928_ = lean_nat_sub(v_i_917_, v_one_927_);
lean_dec(v_i_917_);
v___x_929_ = lean_nat_sub(v_n_916_, v_n_928_);
v___x_930_ = lean_nat_sub(v___x_929_, v_one_927_);
lean_dec(v___x_929_);
v___x_931_ = lean_array_fget_borrowed(v_newMVars_913_, v___x_930_);
v___x_932_ = l_Lean_Expr_mvarId_x21(v___x_931_);
v___x_933_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v___x_932_, v___y_919_);
v_a_934_ = lean_ctor_get(v___x_933_, 0);
lean_inc(v_a_934_);
lean_dec_ref(v___x_933_);
v___x_935_ = lean_unbox(v_a_934_);
lean_dec(v_a_934_);
if (v___x_935_ == 0)
{
uint8_t v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; uint8_t v___x_939_; uint8_t v___x_940_; 
v___x_936_ = 0;
v___x_937_ = lean_box(v___x_936_);
v___x_938_ = lean_array_get(v___x_937_, v_binderInfos_914_, v___x_930_);
lean_dec(v___x_930_);
lean_dec(v___x_937_);
v___x_939_ = lean_unbox(v___x_938_);
lean_dec(v___x_938_);
v___x_940_ = l_Lean_BinderInfo_isInstImplicit(v___x_939_);
if (v___x_940_ == 0)
{
lean_object* v___x_941_; 
lean_inc(v___x_932_);
v___x_941_ = l_Lean_MVarId_getTag(v___x_932_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
if (lean_obj_tag(v___x_941_) == 0)
{
lean_object* v_a_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v_a_942_ = lean_ctor_get(v___x_941_, 0);
lean_inc(v_a_942_);
lean_dec_ref_known(v___x_941_, 1);
lean_inc(v_a_915_);
v___x_943_ = l_Lean_Meta_appendTag(v_a_915_, v_a_942_);
lean_dec(v_a_942_);
v___x_944_ = l_Lean_MVarId_setTag___redArg(v___x_932_, v___x_943_, v___y_919_);
if (lean_obj_tag(v___x_944_) == 0)
{
lean_dec_ref_known(v___x_944_, 1);
v_i_917_ = v_n_928_;
goto _start;
}
else
{
lean_dec(v_n_928_);
lean_dec(v_a_915_);
return v___x_944_;
}
}
else
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_953_; 
lean_dec(v___x_932_);
lean_dec(v_n_928_);
lean_dec(v_a_915_);
v_a_946_ = lean_ctor_get(v___x_941_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_953_ == 0)
{
v___x_948_ = v___x_941_;
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v___x_941_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_951_; 
if (v_isShared_949_ == 0)
{
v___x_951_ = v___x_948_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_a_946_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
}
else
{
lean_dec(v___x_932_);
v_i_917_ = v_n_928_;
goto _start;
}
}
else
{
lean_dec(v___x_932_);
lean_dec(v___x_930_);
v_i_917_ = v_n_928_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg___boxed(lean_object* v_newMVars_956_, lean_object* v_binderInfos_957_, lean_object* v_a_958_, lean_object* v_n_959_, lean_object* v_i_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(v_newMVars_956_, v_binderInfos_957_, v_a_958_, v_n_959_, v_i_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v_n_959_);
lean_dec_ref(v_binderInfos_957_);
lean_dec_ref(v_newMVars_956_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendParentTag(lean_object* v_mvarId_967_, lean_object* v_newMVars_968_, lean_object* v_binderInfos_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = l_Lean_MVarId_getTag(v_mvarId_967_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_994_; 
v_a_976_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_994_ == 0)
{
v___x_978_ = v___x_975_;
v_isShared_979_ = v_isSharedCheck_994_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_975_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_994_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_980_; lean_object* v___x_981_; uint8_t v___x_982_; 
v___x_980_ = lean_array_get_size(v_newMVars_968_);
v___x_981_ = lean_unsigned_to_nat(1u);
v___x_982_ = lean_nat_dec_eq(v___x_980_, v___x_981_);
if (v___x_982_ == 0)
{
uint8_t v___x_983_; 
v___x_983_ = l_Lean_Name_isAnonymous(v_a_976_);
if (v___x_983_ == 0)
{
lean_object* v___x_984_; 
lean_del_object(v___x_978_);
v___x_984_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(v_newMVars_968_, v_binderInfos_969_, v_a_976_, v___x_980_, v___x_980_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
return v___x_984_;
}
else
{
lean_object* v___x_985_; lean_object* v___x_987_; 
lean_dec(v_a_976_);
v___x_985_ = lean_box(0);
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 0, v___x_985_);
v___x_987_ = v___x_978_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v___x_985_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
else
{
lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
lean_del_object(v___x_978_);
v___x_989_ = l_Lean_instInhabitedExpr;
v___x_990_ = lean_unsigned_to_nat(0u);
v___x_991_ = lean_array_get_borrowed(v___x_989_, v_newMVars_968_, v___x_990_);
v___x_992_ = l_Lean_Expr_mvarId_x21(v___x_991_);
v___x_993_ = l_Lean_MVarId_setTag___redArg(v___x_992_, v_a_976_, v_a_971_);
return v___x_993_;
}
}
}
else
{
lean_object* v_a_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1002_; 
v_a_995_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_997_ = v___x_975_;
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_a_995_);
lean_dec(v___x_975_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_1000_; 
if (v_isShared_998_ == 0)
{
v___x_1000_ = v___x_997_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_a_995_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendParentTag___boxed(lean_object* v_mvarId_1003_, lean_object* v_newMVars_1004_, lean_object* v_binderInfos_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_Lean_Meta_appendParentTag(v_mvarId_1003_, v_newMVars_1004_, v_binderInfos_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_);
lean_dec(v_a_1009_);
lean_dec_ref(v_a_1008_);
lean_dec(v_a_1007_);
lean_dec_ref(v_a_1006_);
lean_dec_ref(v_binderInfos_1005_);
lean_dec_ref(v_newMVars_1004_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0(lean_object* v_newMVars_1012_, lean_object* v_binderInfos_1013_, lean_object* v_a_1014_, lean_object* v_n_1015_, lean_object* v_i_1016_, lean_object* v_a_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v___x_1023_; 
v___x_1023_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(v_newMVars_1012_, v_binderInfos_1013_, v_a_1014_, v_n_1015_, v_i_1016_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___boxed(lean_object* v_newMVars_1024_, lean_object* v_binderInfos_1025_, lean_object* v_a_1026_, lean_object* v_n_1027_, lean_object* v_i_1028_, lean_object* v_a_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0(v_newMVars_1024_, v_binderInfos_1025_, v_a_1026_, v_n_1027_, v_i_1028_, v_a_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec(v_n_1027_);
lean_dec_ref(v_binderInfos_1025_);
lean_dec_ref(v_newMVars_1024_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_postprocessAppMVars(lean_object* v_tacticName_1036_, lean_object* v_mvarId_1037_, lean_object* v_newMVars_1038_, lean_object* v_binderInfos_1039_, uint8_t v_synthAssignedInstances_1040_, uint8_t v_allowSynthFailures_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_){
_start:
{
lean_object* v___x_1047_; 
v___x_1047_ = l_Lean_Meta_synthAppInstances(v_tacticName_1036_, v_mvarId_1037_, v_newMVars_1038_, v_binderInfos_1039_, v_synthAssignedInstances_1040_, v_allowSynthFailures_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_postprocessAppMVars___boxed(lean_object* v_tacticName_1048_, lean_object* v_mvarId_1049_, lean_object* v_newMVars_1050_, lean_object* v_binderInfos_1051_, lean_object* v_synthAssignedInstances_1052_, lean_object* v_allowSynthFailures_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_){
_start:
{
uint8_t v_synthAssignedInstances_boxed_1059_; uint8_t v_allowSynthFailures_boxed_1060_; lean_object* v_res_1061_; 
v_synthAssignedInstances_boxed_1059_ = lean_unbox(v_synthAssignedInstances_1052_);
v_allowSynthFailures_boxed_1060_ = lean_unbox(v_allowSynthFailures_1053_);
v_res_1061_ = l_Lean_Meta_postprocessAppMVars(v_tacticName_1048_, v_mvarId_1049_, v_newMVars_1050_, v_binderInfos_1051_, v_synthAssignedInstances_boxed_1059_, v_allowSynthFailures_boxed_1060_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_);
lean_dec(v_a_1057_);
lean_dec_ref(v_a_1056_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec_ref(v_newMVars_1050_);
return v_res_1061_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0(lean_object* v_mvar_1062_, lean_object* v_mvarId_1063_){
_start:
{
lean_object* v___x_1064_; uint8_t v___x_1065_; 
v___x_1064_ = l_Lean_Expr_mvarId_x21(v_mvar_1062_);
v___x_1065_ = l_Lean_instBEqMVarId_beq(v_mvarId_1063_, v___x_1064_);
lean_dec(v___x_1064_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0___boxed(lean_object* v_mvar_1066_, lean_object* v_mvarId_1067_){
_start:
{
uint8_t v_res_1068_; lean_object* v_r_1069_; 
v_res_1068_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0(v_mvar_1066_, v_mvarId_1067_);
lean_dec(v_mvarId_1067_);
lean_dec_ref(v_mvar_1066_);
v_r_1069_ = lean_box(v_res_1068_);
return v_r_1069_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0(lean_object* v_mvar_1070_, lean_object* v_as_1071_, size_t v_i_1072_, size_t v_stop_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_){
_start:
{
uint8_t v___x_1083_; 
v___x_1083_ = lean_usize_dec_eq(v_i_1072_, v_stop_1073_);
if (v___x_1083_ == 0)
{
lean_object* v___x_1084_; uint8_t v___x_1085_; 
v___x_1084_ = lean_array_uget_borrowed(v_as_1071_, v_i_1072_);
v___x_1085_ = lean_expr_eqv(v_mvar_1070_, v___x_1084_);
if (v___x_1085_ == 0)
{
lean_object* v___x_1086_; 
lean_inc(v___y_1077_);
lean_inc_ref(v___y_1076_);
lean_inc(v___y_1075_);
lean_inc_ref(v___y_1074_);
lean_inc(v___x_1084_);
v___x_1086_ = lean_infer_type(v___x_1084_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1103_; 
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1089_ = v___x_1086_;
v_isShared_1090_ = v_isSharedCheck_1103_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1086_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1103_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___f_1091_; uint8_t v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
lean_inc_ref(v_mvar_1070_);
v___f_1091_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1091_, 0, v_mvar_1070_);
v___x_1092_ = 1;
v___x_1093_ = lean_box(0);
v___x_1094_ = l_Lean_FindMVar_main(v___f_1091_, v_a_1087_, v___x_1093_);
if (lean_obj_tag(v___x_1094_) == 0)
{
if (v___x_1085_ == 0)
{
lean_del_object(v___x_1089_);
goto v___jp_1079_;
}
else
{
lean_object* v___x_1095_; lean_object* v___x_1097_; 
lean_dec_ref(v_mvar_1070_);
v___x_1095_ = lean_box(v___x_1092_);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 0, v___x_1095_);
v___x_1097_ = v___x_1089_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v___x_1095_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
else
{
lean_object* v___x_1099_; lean_object* v___x_1101_; 
lean_dec_ref_known(v___x_1094_, 1);
lean_dec_ref(v_mvar_1070_);
v___x_1099_ = lean_box(v___x_1092_);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 0, v___x_1099_);
v___x_1101_ = v___x_1089_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v___x_1099_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
else
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1111_; 
lean_dec_ref(v_mvar_1070_);
v_a_1104_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1106_ = v___x_1086_;
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1086_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
if (v_isShared_1107_ == 0)
{
v___x_1109_ = v___x_1106_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1104_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
}
else
{
goto v___jp_1079_;
}
}
else
{
uint8_t v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
lean_dec_ref(v_mvar_1070_);
v___x_1112_ = 0;
v___x_1113_ = lean_box(v___x_1112_);
v___x_1114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1113_);
return v___x_1114_;
}
v___jp_1079_:
{
size_t v___x_1080_; size_t v___x_1081_; 
v___x_1080_ = ((size_t)1ULL);
v___x_1081_ = lean_usize_add(v_i_1072_, v___x_1080_);
v_i_1072_ = v___x_1081_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___boxed(lean_object* v_mvar_1115_, lean_object* v_as_1116_, lean_object* v_i_1117_, lean_object* v_stop_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
size_t v_i_boxed_1124_; size_t v_stop_boxed_1125_; lean_object* v_res_1126_; 
v_i_boxed_1124_ = lean_unbox_usize(v_i_1117_);
lean_dec(v_i_1117_);
v_stop_boxed_1125_ = lean_unbox_usize(v_stop_1118_);
lean_dec(v_stop_1118_);
v_res_1126_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0(v_mvar_1115_, v_as_1116_, v_i_boxed_1124_, v_stop_boxed_1125_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
lean_dec(v___y_1120_);
lean_dec_ref(v___y_1119_);
lean_dec_ref(v_as_1116_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(lean_object* v_mvar_1127_, lean_object* v_otherMVars_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; uint8_t v___x_1136_; 
v___x_1134_ = lean_unsigned_to_nat(0u);
v___x_1135_ = lean_array_get_size(v_otherMVars_1128_);
v___x_1136_ = lean_nat_dec_lt(v___x_1134_, v___x_1135_);
if (v___x_1136_ == 0)
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
lean_dec_ref(v_mvar_1127_);
v___x_1137_ = lean_box(v___x_1136_);
v___x_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1137_);
return v___x_1138_;
}
else
{
if (v___x_1136_ == 0)
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
lean_dec_ref(v_mvar_1127_);
v___x_1139_ = lean_box(v___x_1136_);
v___x_1140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1139_);
return v___x_1140_;
}
else
{
size_t v___x_1141_; size_t v___x_1142_; lean_object* v___x_1143_; 
v___x_1141_ = ((size_t)0ULL);
v___x_1142_ = lean_usize_of_nat(v___x_1135_);
v___x_1143_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0(v_mvar_1127_, v_otherMVars_1128_, v___x_1141_, v___x_1142_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_);
return v___x_1143_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___boxed(lean_object* v_mvar_1144_, lean_object* v_otherMVars_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(v_mvar_1144_, v_otherMVars_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_);
lean_dec(v_a_1149_);
lean_dec_ref(v_a_1148_);
lean_dec(v_a_1147_);
lean_dec_ref(v_a_1146_);
lean_dec_ref(v_otherMVars_1145_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(lean_object* v_mvars_1152_, lean_object* v_as_1153_, size_t v_i_1154_, size_t v_stop_1155_, lean_object* v_b_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
uint8_t v___x_1162_; 
v___x_1162_ = lean_usize_dec_eq(v_i_1154_, v_stop_1155_);
if (v___x_1162_ == 0)
{
lean_object* v_fst_1163_; lean_object* v_snd_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1194_; 
v_fst_1163_ = lean_ctor_get(v_b_1156_, 0);
v_snd_1164_ = lean_ctor_get(v_b_1156_, 1);
v_isSharedCheck_1194_ = !lean_is_exclusive(v_b_1156_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1166_ = v_b_1156_;
v_isShared_1167_ = v_isSharedCheck_1194_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_snd_1164_);
lean_inc(v_fst_1163_);
lean_dec(v_b_1156_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1194_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1168_; lean_object* v_currMVarId_1169_; lean_object* v___x_1170_; 
v___x_1168_ = lean_array_uget_borrowed(v_as_1153_, v_i_1154_);
v_currMVarId_1169_ = l_Lean_Expr_mvarId_x21(v___x_1168_);
lean_inc(v___x_1168_);
v___x_1170_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(v___x_1168_, v_mvars_1152_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_);
if (lean_obj_tag(v___x_1170_) == 0)
{
lean_object* v_a_1171_; lean_object* v_a_1173_; uint8_t v___x_1177_; 
v_a_1171_ = lean_ctor_get(v___x_1170_, 0);
lean_inc(v_a_1171_);
lean_dec_ref_known(v___x_1170_, 1);
v___x_1177_ = lean_unbox(v_a_1171_);
lean_dec(v_a_1171_);
if (v___x_1177_ == 0)
{
lean_object* v___x_1178_; lean_object* v___x_1180_; 
v___x_1178_ = lean_array_push(v_fst_1163_, v_currMVarId_1169_);
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 0, v___x_1178_);
v___x_1180_ = v___x_1166_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1178_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v_snd_1164_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
v_a_1173_ = v___x_1180_;
goto v___jp_1172_;
}
}
else
{
lean_object* v___x_1182_; lean_object* v___x_1184_; 
v___x_1182_ = lean_array_push(v_snd_1164_, v_currMVarId_1169_);
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 1, v___x_1182_);
v___x_1184_ = v___x_1166_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_fst_1163_);
lean_ctor_set(v_reuseFailAlloc_1185_, 1, v___x_1182_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
v_a_1173_ = v___x_1184_;
goto v___jp_1172_;
}
}
v___jp_1172_:
{
size_t v___x_1174_; size_t v___x_1175_; 
v___x_1174_ = ((size_t)1ULL);
v___x_1175_ = lean_usize_add(v_i_1154_, v___x_1174_);
v_i_1154_ = v___x_1175_;
v_b_1156_ = v_a_1173_;
goto _start;
}
}
else
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1193_; 
lean_dec(v_currMVarId_1169_);
lean_del_object(v___x_1166_);
lean_dec(v_snd_1164_);
lean_dec(v_fst_1163_);
v_a_1186_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1188_ = v___x_1170_;
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1170_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1191_; 
if (v_isShared_1189_ == 0)
{
v___x_1191_ = v___x_1188_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_a_1186_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
}
}
else
{
lean_object* v___x_1195_; 
v___x_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1195_, 0, v_b_1156_);
return v___x_1195_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0___boxed(lean_object* v_mvars_1196_, lean_object* v_as_1197_, lean_object* v_i_1198_, lean_object* v_stop_1199_, lean_object* v_b_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
size_t v_i_boxed_1206_; size_t v_stop_boxed_1207_; lean_object* v_res_1208_; 
v_i_boxed_1206_ = lean_unbox_usize(v_i_1198_);
lean_dec(v_i_1198_);
v_stop_boxed_1207_ = lean_unbox_usize(v_stop_1199_);
lean_dec(v_stop_1199_);
v_res_1208_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(v_mvars_1196_, v_as_1197_, v_i_boxed_1206_, v_stop_boxed_1207_, v_b_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
lean_dec_ref(v_as_1197_);
lean_dec_ref(v_mvars_1196_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(lean_object* v_mvars_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_){
_start:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; uint8_t v___x_1222_; 
v___x_1219_ = lean_unsigned_to_nat(0u);
v___x_1220_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1));
v___x_1221_ = lean_array_get_size(v_mvars_1213_);
v___x_1222_ = lean_nat_dec_lt(v___x_1219_, v___x_1221_);
if (v___x_1222_ == 0)
{
lean_object* v___x_1223_; 
v___x_1223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1220_);
return v___x_1223_;
}
else
{
uint8_t v___x_1224_; 
v___x_1224_ = lean_nat_dec_le(v___x_1221_, v___x_1221_);
if (v___x_1224_ == 0)
{
if (v___x_1222_ == 0)
{
lean_object* v___x_1225_; 
v___x_1225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1220_);
return v___x_1225_;
}
else
{
size_t v___x_1226_; size_t v___x_1227_; lean_object* v___x_1228_; 
v___x_1226_ = ((size_t)0ULL);
v___x_1227_ = lean_usize_of_nat(v___x_1221_);
v___x_1228_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(v_mvars_1213_, v_mvars_1213_, v___x_1226_, v___x_1227_, v___x_1220_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_);
return v___x_1228_;
}
}
else
{
size_t v___x_1229_; size_t v___x_1230_; lean_object* v___x_1231_; 
v___x_1229_ = ((size_t)0ULL);
v___x_1230_ = lean_usize_of_nat(v___x_1221_);
v___x_1231_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(v_mvars_1213_, v_mvars_1213_, v___x_1229_, v___x_1230_, v___x_1220_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_);
return v___x_1231_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___boxed(lean_object* v_mvars_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(v_mvars_1232_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_);
lean_dec(v_a_1236_);
lean_dec_ref(v_a_1235_);
lean_dec(v_a_1234_);
lean_dec_ref(v_a_1233_);
lean_dec_ref(v_mvars_1232_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals_spec__0(lean_object* v_a_1239_, lean_object* v_a_1240_){
_start:
{
if (lean_obj_tag(v_a_1239_) == 0)
{
lean_object* v___x_1241_; 
v___x_1241_ = l_List_reverse___redArg(v_a_1240_);
return v___x_1241_;
}
else
{
lean_object* v_head_1242_; lean_object* v_tail_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1252_; 
v_head_1242_ = lean_ctor_get(v_a_1239_, 0);
v_tail_1243_ = lean_ctor_get(v_a_1239_, 1);
v_isSharedCheck_1252_ = !lean_is_exclusive(v_a_1239_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1245_ = v_a_1239_;
v_isShared_1246_ = v_isSharedCheck_1252_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_tail_1243_);
lean_inc(v_head_1242_);
lean_dec(v_a_1239_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1252_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1247_; lean_object* v___x_1249_; 
v___x_1247_ = l_Lean_Expr_mvarId_x21(v_head_1242_);
lean_dec(v_head_1242_);
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 1, v_a_1240_);
lean_ctor_set(v___x_1245_, 0, v___x_1247_);
v___x_1249_ = v___x_1245_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v___x_1247_);
lean_ctor_set(v_reuseFailAlloc_1251_, 1, v_a_1240_);
v___x_1249_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
v_a_1239_ = v_tail_1243_;
v_a_1240_ = v___x_1249_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(lean_object* v_mvars_1253_, uint8_t v_x_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_){
_start:
{
switch(v_x_1254_)
{
case 0:
{
lean_object* v___x_1260_; 
v___x_1260_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(v_mvars_1253_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
lean_dec_ref(v_mvars_1253_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1273_; 
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1263_ = v___x_1260_;
v_isShared_1264_ = v_isSharedCheck_1273_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v___x_1260_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1273_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v_fst_1265_; lean_object* v_snd_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1271_; 
v_fst_1265_ = lean_ctor_get(v_a_1261_, 0);
lean_inc(v_fst_1265_);
v_snd_1266_ = lean_ctor_get(v_a_1261_, 1);
lean_inc(v_snd_1266_);
lean_dec(v_a_1261_);
v___x_1267_ = lean_array_to_list(v_fst_1265_);
v___x_1268_ = lean_array_to_list(v_snd_1266_);
v___x_1269_ = l_List_appendTR___redArg(v___x_1267_, v___x_1268_);
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 0, v___x_1269_);
v___x_1271_ = v___x_1263_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v___x_1269_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
else
{
lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1281_; 
v_a_1274_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1276_ = v___x_1260_;
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_dec(v___x_1260_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1279_; 
if (v_isShared_1277_ == 0)
{
v___x_1279_ = v___x_1276_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_a_1274_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
}
}
case 1:
{
lean_object* v___x_1282_; 
v___x_1282_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(v_mvars_1253_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
lean_dec_ref(v_mvars_1253_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1292_; 
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1285_ = v___x_1282_;
v_isShared_1286_ = v_isSharedCheck_1292_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1282_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1292_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v_fst_1287_; lean_object* v___x_1288_; lean_object* v___x_1290_; 
v_fst_1287_ = lean_ctor_get(v_a_1283_, 0);
lean_inc(v_fst_1287_);
lean_dec(v_a_1283_);
v___x_1288_ = lean_array_to_list(v_fst_1287_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 0, v___x_1288_);
v___x_1290_ = v___x_1285_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v___x_1288_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
else
{
lean_object* v_a_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1300_; 
v_a_1293_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1295_ = v___x_1282_;
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_dec(v___x_1282_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1298_; 
if (v_isShared_1296_ == 0)
{
v___x_1298_ = v___x_1295_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_a_1293_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
}
default: 
{
lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1301_ = lean_array_to_list(v_mvars_1253_);
v___x_1302_ = lean_box(0);
v___x_1303_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals_spec__0(v___x_1301_, v___x_1302_);
v___x_1304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1303_);
return v___x_1304_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals___boxed(lean_object* v_mvars_1305_, lean_object* v_x_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_){
_start:
{
uint8_t v_x_814__boxed_1312_; lean_object* v_res_1313_; 
v_x_814__boxed_1312_ = lean_unbox(v_x_1306_);
v_res_1313_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(v_mvars_1305_, v_x_814__boxed_1312_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_);
lean_dec(v_a_1310_);
lean_dec_ref(v_a_1309_);
lean_dec(v_a_1308_);
lean_dec_ref(v_a_1307_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(uint8_t v_approx_1314_, lean_object* v_a_1315_, lean_object* v_b_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_){
_start:
{
if (v_approx_1314_ == 0)
{
lean_object* v___x_1322_; 
v___x_1322_ = l_Lean_Meta_isExprDefEqGuarded(v_a_1315_, v_b_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_);
return v___x_1322_;
}
else
{
lean_object* v___x_1323_; uint8_t v_constApprox_1324_; uint8_t v_isDefEqStuckEx_1325_; uint8_t v_unificationHints_1326_; uint8_t v_proofIrrelevance_1327_; uint8_t v_assignSyntheticOpaque_1328_; uint8_t v_offsetCnstrs_1329_; uint8_t v_transparency_1330_; uint8_t v_etaStruct_1331_; uint8_t v_univApprox_1332_; uint8_t v_iota_1333_; uint8_t v_beta_1334_; uint8_t v_proj_1335_; uint8_t v_zeta_1336_; uint8_t v_zetaDelta_1337_; uint8_t v_zetaUnused_1338_; uint8_t v_zetaHave_1339_; uint8_t v_canUnfoldPredicateConfig_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1361_; 
v___x_1323_ = l_Lean_Meta_Context_config(v_a_1317_);
v_constApprox_1324_ = lean_ctor_get_uint8(v___x_1323_, 3);
v_isDefEqStuckEx_1325_ = lean_ctor_get_uint8(v___x_1323_, 4);
v_unificationHints_1326_ = lean_ctor_get_uint8(v___x_1323_, 5);
v_proofIrrelevance_1327_ = lean_ctor_get_uint8(v___x_1323_, 6);
v_assignSyntheticOpaque_1328_ = lean_ctor_get_uint8(v___x_1323_, 7);
v_offsetCnstrs_1329_ = lean_ctor_get_uint8(v___x_1323_, 8);
v_transparency_1330_ = lean_ctor_get_uint8(v___x_1323_, 9);
v_etaStruct_1331_ = lean_ctor_get_uint8(v___x_1323_, 10);
v_univApprox_1332_ = lean_ctor_get_uint8(v___x_1323_, 11);
v_iota_1333_ = lean_ctor_get_uint8(v___x_1323_, 12);
v_beta_1334_ = lean_ctor_get_uint8(v___x_1323_, 13);
v_proj_1335_ = lean_ctor_get_uint8(v___x_1323_, 14);
v_zeta_1336_ = lean_ctor_get_uint8(v___x_1323_, 15);
v_zetaDelta_1337_ = lean_ctor_get_uint8(v___x_1323_, 16);
v_zetaUnused_1338_ = lean_ctor_get_uint8(v___x_1323_, 17);
v_zetaHave_1339_ = lean_ctor_get_uint8(v___x_1323_, 18);
v_canUnfoldPredicateConfig_1340_ = lean_ctor_get_uint8(v___x_1323_, 19);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1342_ = v___x_1323_;
v_isShared_1343_ = v_isSharedCheck_1361_;
goto v_resetjp_1341_;
}
else
{
lean_dec(v___x_1323_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1361_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___x_1345_; 
if (v_isShared_1343_ == 0)
{
v___x_1345_ = v___x_1342_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_1360_, 3, v_constApprox_1324_);
lean_ctor_set_uint8(v_reuseFailAlloc_1360_, 4, v_isDefEqStuckEx_1325_);
lean_ctor_set_uint8(v_reuseFailAlloc_1360_, 5, v_unificationHints_1326_);
lean_ctor_set_uint8(v_reuseFailAlloc_1360_, 6, v_proofIrrelevance_1327_);
lean_ctor_set_uint8(v_reuseFailAlloc_1360_, 7, v_assignSyntheticOpaque_1328_);
lean_ctor_set_uint8(v_reuseFailAlloc_1360_, 8, v_offsetCnstrs_1329_);
lean_ctor_set_uint8(v_reuseFailAlloc_1360_, 9, v_transparency_1330_);
lean_ctor_set_uint8(v_reuseFailAlloc_1360_, 10, v_etaStruct_1331_);
lean_ctor_set_uint8(v_reuseFailAlloc_1360_, 11, v_univApprox_1332_);
lean_ctor_set_uint8(v_reuseFailAlloc_1360_, 12, v_iota_1333_);
lean_ctor_set_uint8(v_reuseFailAlloc_1360_, 13, v_beta_1334_);
lean_ctor_set_uint8(v_reuseFailAlloc_1360_, 14, v_proj_1335_);
lean_ctor_set_uint8(v_reuseFailAlloc_1360_, 15, v_zeta_1336_);
lean_ctor_set_uint8(v_reuseFailAlloc_1360_, 16, v_zetaDelta_1337_);
lean_ctor_set_uint8(v_reuseFailAlloc_1360_, 17, v_zetaUnused_1338_);
lean_ctor_set_uint8(v_reuseFailAlloc_1360_, 18, v_zetaHave_1339_);
lean_ctor_set_uint8(v_reuseFailAlloc_1360_, 19, v_canUnfoldPredicateConfig_1340_);
v___x_1345_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
uint8_t v_trackZetaDelta_1346_; lean_object* v_zetaDeltaSet_1347_; lean_object* v_lctx_1348_; lean_object* v_localInstances_1349_; lean_object* v_defEqCtx_x3f_1350_; lean_object* v_synthPendingDepth_1351_; lean_object* v_customCanUnfoldPredicate_x3f_1352_; uint8_t v_univApprox_1353_; uint8_t v_inTypeClassResolution_1354_; uint8_t v_cacheInferType_1355_; uint64_t v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
lean_ctor_set_uint8(v___x_1345_, 0, v_approx_1314_);
lean_ctor_set_uint8(v___x_1345_, 1, v_approx_1314_);
lean_ctor_set_uint8(v___x_1345_, 2, v_approx_1314_);
v_trackZetaDelta_1346_ = lean_ctor_get_uint8(v_a_1317_, sizeof(void*)*7);
v_zetaDeltaSet_1347_ = lean_ctor_get(v_a_1317_, 1);
v_lctx_1348_ = lean_ctor_get(v_a_1317_, 2);
v_localInstances_1349_ = lean_ctor_get(v_a_1317_, 3);
v_defEqCtx_x3f_1350_ = lean_ctor_get(v_a_1317_, 4);
v_synthPendingDepth_1351_ = lean_ctor_get(v_a_1317_, 5);
v_customCanUnfoldPredicate_x3f_1352_ = lean_ctor_get(v_a_1317_, 6);
v_univApprox_1353_ = lean_ctor_get_uint8(v_a_1317_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1354_ = lean_ctor_get_uint8(v_a_1317_, sizeof(void*)*7 + 2);
v_cacheInferType_1355_ = lean_ctor_get_uint8(v_a_1317_, sizeof(void*)*7 + 3);
v___x_1356_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1345_);
v___x_1357_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1357_, 0, v___x_1345_);
lean_ctor_set_uint64(v___x_1357_, sizeof(void*)*1, v___x_1356_);
lean_inc(v_customCanUnfoldPredicate_x3f_1352_);
lean_inc(v_synthPendingDepth_1351_);
lean_inc(v_defEqCtx_x3f_1350_);
lean_inc_ref(v_localInstances_1349_);
lean_inc_ref(v_lctx_1348_);
lean_inc(v_zetaDeltaSet_1347_);
v___x_1358_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1358_, 0, v___x_1357_);
lean_ctor_set(v___x_1358_, 1, v_zetaDeltaSet_1347_);
lean_ctor_set(v___x_1358_, 2, v_lctx_1348_);
lean_ctor_set(v___x_1358_, 3, v_localInstances_1349_);
lean_ctor_set(v___x_1358_, 4, v_defEqCtx_x3f_1350_);
lean_ctor_set(v___x_1358_, 5, v_synthPendingDepth_1351_);
lean_ctor_set(v___x_1358_, 6, v_customCanUnfoldPredicate_x3f_1352_);
lean_ctor_set_uint8(v___x_1358_, sizeof(void*)*7, v_trackZetaDelta_1346_);
lean_ctor_set_uint8(v___x_1358_, sizeof(void*)*7 + 1, v_univApprox_1353_);
lean_ctor_set_uint8(v___x_1358_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1354_);
lean_ctor_set_uint8(v___x_1358_, sizeof(void*)*7 + 3, v_cacheInferType_1355_);
v___x_1359_ = l_Lean_Meta_isExprDefEqGuarded(v_a_1315_, v_b_1316_, v___x_1358_, v_a_1318_, v_a_1319_, v_a_1320_);
lean_dec_ref_known(v___x_1358_, 7);
return v___x_1359_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply___boxed(lean_object* v_approx_1362_, lean_object* v_a_1363_, lean_object* v_b_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_){
_start:
{
uint8_t v_approx_boxed_1370_; lean_object* v_res_1371_; 
v_approx_boxed_1370_ = lean_unbox(v_approx_1362_);
v_res_1371_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(v_approx_boxed_1370_, v_a_1363_, v_b_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
lean_dec(v_a_1368_);
lean_dec_ref(v_a_1367_);
lean_dec(v_a_1366_);
lean_dec_ref(v_a_1365_);
return v_res_1371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go(lean_object* v_mvarId_1372_, lean_object* v_cfg_1373_, lean_object* v_term_x3f_1374_, lean_object* v_targetType_1375_, lean_object* v_eType_1376_, lean_object* v_rangeNumArgs_1377_, lean_object* v_i_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_){
_start:
{
lean_object* v_lower_1384_; lean_object* v_upper_1385_; uint8_t v___x_1386_; 
v_lower_1384_ = lean_ctor_get(v_rangeNumArgs_1377_, 0);
v_upper_1385_ = lean_ctor_get(v_rangeNumArgs_1377_, 1);
v___x_1386_ = lean_nat_dec_lt(v_i_1378_, v_upper_1385_);
if (v___x_1386_ == 0)
{
lean_object* v___x_1387_; uint8_t v___x_1388_; 
lean_dec(v_i_1378_);
v___x_1387_ = lean_unsigned_to_nat(0u);
v___x_1388_ = lean_nat_dec_eq(v_lower_1384_, v___x_1387_);
if (v___x_1388_ == 0)
{
lean_object* v___x_1389_; uint8_t v___x_1390_; lean_object* v___x_1391_; 
lean_inc(v_lower_1384_);
v___x_1389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1389_, 0, v_lower_1384_);
v___x_1390_ = 0;
lean_inc_ref(v_eType_1376_);
v___x_1391_ = l_Lean_Meta_forallMetaTelescopeReducing(v_eType_1376_, v___x_1389_, v___x_1390_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_a_1392_; lean_object* v_snd_1393_; lean_object* v_snd_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
lean_inc(v_a_1392_);
lean_dec_ref_known(v___x_1391_, 1);
v_snd_1393_ = lean_ctor_get(v_a_1392_, 1);
lean_inc(v_snd_1393_);
lean_dec(v_a_1392_);
v_snd_1394_ = lean_ctor_get(v_snd_1393_, 1);
lean_inc(v_snd_1394_);
lean_dec(v_snd_1393_);
v___x_1395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1395_, 0, v_snd_1394_);
v___x_1396_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(v_mvarId_1372_, v_eType_1376_, v___x_1395_, v_targetType_1375_, v_term_x3f_1374_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_);
return v___x_1396_;
}
else
{
lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1404_; 
lean_dec_ref(v_eType_1376_);
lean_dec_ref(v_targetType_1375_);
lean_dec(v_term_x3f_1374_);
lean_dec(v_mvarId_1372_);
v_a_1397_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1399_ = v___x_1391_;
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1391_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1402_; 
if (v_isShared_1400_ == 0)
{
v___x_1402_ = v___x_1399_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_a_1397_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
}
else
{
lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1405_ = lean_box(0);
v___x_1406_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(v_mvarId_1372_, v_eType_1376_, v___x_1405_, v_targetType_1375_, v_term_x3f_1374_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_);
return v___x_1406_;
}
}
else
{
lean_object* v___x_1407_; 
v___x_1407_ = l_Lean_Meta_saveState___redArg(v_a_1380_, v_a_1382_);
if (lean_obj_tag(v___x_1407_) == 0)
{
lean_object* v_a_1408_; lean_object* v___x_1409_; uint8_t v___x_1410_; lean_object* v___x_1411_; 
v_a_1408_ = lean_ctor_get(v___x_1407_, 0);
lean_inc(v_a_1408_);
lean_dec_ref_known(v___x_1407_, 1);
lean_inc(v_i_1378_);
v___x_1409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1409_, 0, v_i_1378_);
v___x_1410_ = 0;
lean_inc_ref(v_eType_1376_);
v___x_1411_ = l_Lean_Meta_forallMetaTelescopeReducing(v_eType_1376_, v___x_1409_, v___x_1410_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_object* v_a_1412_; lean_object* v_snd_1413_; lean_object* v_fst_1414_; lean_object* v_fst_1415_; lean_object* v_snd_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1454_; 
v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
lean_inc(v_a_1412_);
lean_dec_ref_known(v___x_1411_, 1);
v_snd_1413_ = lean_ctor_get(v_a_1412_, 1);
lean_inc(v_snd_1413_);
v_fst_1414_ = lean_ctor_get(v_a_1412_, 0);
lean_inc(v_fst_1414_);
lean_dec(v_a_1412_);
v_fst_1415_ = lean_ctor_get(v_snd_1413_, 0);
v_snd_1416_ = lean_ctor_get(v_snd_1413_, 1);
v_isSharedCheck_1454_ = !lean_is_exclusive(v_snd_1413_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1418_ = v_snd_1413_;
v_isShared_1419_ = v_isSharedCheck_1454_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_snd_1416_);
lean_inc(v_fst_1415_);
lean_dec(v_snd_1413_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1454_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
uint8_t v_approx_1420_; lean_object* v___x_1421_; 
v_approx_1420_ = lean_ctor_get_uint8(v_cfg_1373_, 3);
lean_inc_ref(v_targetType_1375_);
v___x_1421_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(v_approx_1420_, v_snd_1416_, v_targetType_1375_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v_a_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1445_; 
v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1424_ = v___x_1421_;
v_isShared_1425_ = v_isSharedCheck_1445_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_a_1422_);
lean_dec(v___x_1421_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1445_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
uint8_t v___x_1426_; 
v___x_1426_ = lean_unbox(v_a_1422_);
lean_dec(v_a_1422_);
if (v___x_1426_ == 0)
{
lean_object* v___x_1427_; 
lean_del_object(v___x_1424_);
lean_del_object(v___x_1418_);
lean_dec(v_fst_1415_);
lean_dec(v_fst_1414_);
v___x_1427_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1408_, v_a_1380_, v_a_1382_);
lean_dec(v_a_1408_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v___x_1428_; lean_object* v___x_1429_; 
lean_dec_ref_known(v___x_1427_, 1);
v___x_1428_ = lean_unsigned_to_nat(1u);
v___x_1429_ = lean_nat_add(v_i_1378_, v___x_1428_);
lean_dec(v_i_1378_);
v_i_1378_ = v___x_1429_;
goto _start;
}
else
{
lean_object* v_a_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1438_; 
lean_dec(v_i_1378_);
lean_dec_ref(v_eType_1376_);
lean_dec_ref(v_targetType_1375_);
lean_dec(v_term_x3f_1374_);
lean_dec(v_mvarId_1372_);
v_a_1431_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1433_ = v___x_1427_;
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_a_1431_);
lean_dec(v___x_1427_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1436_; 
if (v_isShared_1434_ == 0)
{
v___x_1436_ = v___x_1433_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_a_1431_);
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
else
{
lean_object* v___x_1440_; 
lean_dec(v_a_1408_);
lean_dec(v_i_1378_);
lean_dec_ref(v_eType_1376_);
lean_dec_ref(v_targetType_1375_);
lean_dec(v_term_x3f_1374_);
lean_dec(v_mvarId_1372_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 1, v_fst_1415_);
lean_ctor_set(v___x_1418_, 0, v_fst_1414_);
v___x_1440_ = v___x_1418_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_fst_1414_);
lean_ctor_set(v_reuseFailAlloc_1444_, 1, v_fst_1415_);
v___x_1440_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
lean_object* v___x_1442_; 
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 0, v___x_1440_);
v___x_1442_ = v___x_1424_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v___x_1440_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
}
}
}
else
{
lean_object* v_a_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1453_; 
lean_del_object(v___x_1418_);
lean_dec(v_fst_1415_);
lean_dec(v_fst_1414_);
lean_dec(v_a_1408_);
lean_dec(v_i_1378_);
lean_dec_ref(v_eType_1376_);
lean_dec_ref(v_targetType_1375_);
lean_dec(v_term_x3f_1374_);
lean_dec(v_mvarId_1372_);
v_a_1446_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1448_ = v___x_1421_;
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_a_1446_);
lean_dec(v___x_1421_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1451_; 
if (v_isShared_1449_ == 0)
{
v___x_1451_ = v___x_1448_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_a_1446_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
}
}
else
{
lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1462_; 
lean_dec(v_a_1408_);
lean_dec(v_i_1378_);
lean_dec_ref(v_eType_1376_);
lean_dec_ref(v_targetType_1375_);
lean_dec(v_term_x3f_1374_);
lean_dec(v_mvarId_1372_);
v_a_1455_ = lean_ctor_get(v___x_1411_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1457_ = v___x_1411_;
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_dec(v___x_1411_);
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
lean_object* v_a_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1470_; 
lean_dec(v_i_1378_);
lean_dec_ref(v_eType_1376_);
lean_dec_ref(v_targetType_1375_);
lean_dec(v_term_x3f_1374_);
lean_dec(v_mvarId_1372_);
v_a_1463_ = lean_ctor_get(v___x_1407_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1465_ = v___x_1407_;
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_a_1463_);
lean_dec(v___x_1407_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go___boxed(lean_object* v_mvarId_1471_, lean_object* v_cfg_1472_, lean_object* v_term_x3f_1473_, lean_object* v_targetType_1474_, lean_object* v_eType_1475_, lean_object* v_rangeNumArgs_1476_, lean_object* v_i_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_){
_start:
{
lean_object* v_res_1483_; 
v_res_1483_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go(v_mvarId_1471_, v_cfg_1472_, v_term_x3f_1473_, v_targetType_1474_, v_eType_1475_, v_rangeNumArgs_1476_, v_i_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_);
lean_dec(v_a_1481_);
lean_dec_ref(v_a_1480_);
lean_dec(v_a_1479_);
lean_dec_ref(v_a_1478_);
lean_dec_ref(v_rangeNumArgs_1476_);
lean_dec_ref(v_cfg_1472_);
return v_res_1483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go_match__1_splitter___redArg(lean_object* v_x_1484_, lean_object* v_h__1_1485_){
_start:
{
lean_object* v_snd_1486_; lean_object* v_fst_1487_; lean_object* v_fst_1488_; lean_object* v_snd_1489_; lean_object* v___x_1490_; 
v_snd_1486_ = lean_ctor_get(v_x_1484_, 1);
lean_inc(v_snd_1486_);
v_fst_1487_ = lean_ctor_get(v_x_1484_, 0);
lean_inc(v_fst_1487_);
lean_dec_ref(v_x_1484_);
v_fst_1488_ = lean_ctor_get(v_snd_1486_, 0);
lean_inc(v_fst_1488_);
v_snd_1489_ = lean_ctor_get(v_snd_1486_, 1);
lean_inc(v_snd_1489_);
lean_dec(v_snd_1486_);
v___x_1490_ = lean_apply_3(v_h__1_1485_, v_fst_1487_, v_fst_1488_, v_snd_1489_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go_match__1_splitter(lean_object* v_motive_1491_, lean_object* v_x_1492_, lean_object* v_h__1_1493_){
_start:
{
lean_object* v_snd_1494_; lean_object* v_fst_1495_; lean_object* v_fst_1496_; lean_object* v_snd_1497_; lean_object* v___x_1498_; 
v_snd_1494_ = lean_ctor_get(v_x_1492_, 1);
lean_inc(v_snd_1494_);
v_fst_1495_ = lean_ctor_get(v_x_1492_, 0);
lean_inc(v_fst_1495_);
lean_dec_ref(v_x_1492_);
v_fst_1496_ = lean_ctor_get(v_snd_1494_, 0);
lean_inc(v_fst_1496_);
v_snd_1497_ = lean_ctor_get(v_snd_1494_, 1);
lean_inc(v_snd_1497_);
lean_dec(v_snd_1494_);
v___x_1498_ = lean_apply_3(v_h__1_1493_, v_fst_1495_, v_fst_1496_, v_snd_1497_);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(lean_object* v_e_1499_, lean_object* v___y_1500_){
_start:
{
uint8_t v___x_1502_; 
v___x_1502_ = l_Lean_Expr_hasMVar(v_e_1499_);
if (v___x_1502_ == 0)
{
lean_object* v___x_1503_; 
v___x_1503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1503_, 0, v_e_1499_);
return v___x_1503_;
}
else
{
lean_object* v___x_1504_; lean_object* v_mctx_1505_; lean_object* v___x_1506_; lean_object* v_fst_1507_; lean_object* v_snd_1508_; lean_object* v___x_1509_; lean_object* v_cache_1510_; lean_object* v_zetaDeltaFVarIds_1511_; lean_object* v_postponed_1512_; lean_object* v_diag_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1522_; 
v___x_1504_ = lean_st_ref_get(v___y_1500_);
v_mctx_1505_ = lean_ctor_get(v___x_1504_, 0);
lean_inc_ref(v_mctx_1505_);
lean_dec(v___x_1504_);
v___x_1506_ = l_Lean_instantiateMVarsCore(v_mctx_1505_, v_e_1499_);
v_fst_1507_ = lean_ctor_get(v___x_1506_, 0);
lean_inc(v_fst_1507_);
v_snd_1508_ = lean_ctor_get(v___x_1506_, 1);
lean_inc(v_snd_1508_);
lean_dec_ref(v___x_1506_);
v___x_1509_ = lean_st_ref_take(v___y_1500_);
v_cache_1510_ = lean_ctor_get(v___x_1509_, 1);
v_zetaDeltaFVarIds_1511_ = lean_ctor_get(v___x_1509_, 2);
v_postponed_1512_ = lean_ctor_get(v___x_1509_, 3);
v_diag_1513_ = lean_ctor_get(v___x_1509_, 4);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1522_ == 0)
{
lean_object* v_unused_1523_; 
v_unused_1523_ = lean_ctor_get(v___x_1509_, 0);
lean_dec(v_unused_1523_);
v___x_1515_ = v___x_1509_;
v_isShared_1516_ = v_isSharedCheck_1522_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_diag_1513_);
lean_inc(v_postponed_1512_);
lean_inc(v_zetaDeltaFVarIds_1511_);
lean_inc(v_cache_1510_);
lean_dec(v___x_1509_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1522_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1518_; 
if (v_isShared_1516_ == 0)
{
lean_ctor_set(v___x_1515_, 0, v_snd_1508_);
v___x_1518_ = v___x_1515_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v_snd_1508_);
lean_ctor_set(v_reuseFailAlloc_1521_, 1, v_cache_1510_);
lean_ctor_set(v_reuseFailAlloc_1521_, 2, v_zetaDeltaFVarIds_1511_);
lean_ctor_set(v_reuseFailAlloc_1521_, 3, v_postponed_1512_);
lean_ctor_set(v_reuseFailAlloc_1521_, 4, v_diag_1513_);
v___x_1518_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1519_ = lean_st_ref_put(v___y_1500_, v___x_1518_);
v___x_1520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1520_, 0, v_fst_1507_);
return v___x_1520_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg___boxed(lean_object* v_e_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_e_1524_, v___y_1525_);
lean_dec(v___y_1525_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0(lean_object* v_e_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
lean_object* v___x_1534_; 
v___x_1534_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_e_1528_, v___y_1530_);
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___boxed(lean_object* v_e_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0(v_e_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(lean_object* v_mvarId_1542_, lean_object* v_x_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_){
_start:
{
lean_object* v___x_1549_; 
v___x_1549_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1542_, v_x_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1557_; 
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1557_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1552_ = v___x_1549_;
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_a_1550_);
lean_dec(v___x_1549_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1555_; 
if (v_isShared_1553_ == 0)
{
v___x_1555_ = v___x_1552_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v_a_1550_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
}
else
{
lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1565_; 
v_a_1558_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1560_ = v___x_1549_;
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_dec(v___x_1549_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg___boxed(lean_object* v_mvarId_1566_, lean_object* v_x_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_1566_, v_x_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6(lean_object* v_00_u03b1_1574_, lean_object* v_mvarId_1575_, lean_object* v_x_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_){
_start:
{
lean_object* v___x_1582_; 
v___x_1582_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_1575_, v_x_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___boxed(lean_object* v_00_u03b1_1583_, lean_object* v_mvarId_1584_, lean_object* v_x_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
lean_object* v_res_1591_; 
v_res_1591_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6(v_00_u03b1_1583_, v_mvarId_1584_, v_x_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(lean_object* v_as_1592_, size_t v_i_1593_, size_t v_stop_1594_, lean_object* v_b_1595_, lean_object* v___y_1596_){
_start:
{
lean_object* v_a_1599_; uint8_t v___x_1603_; 
v___x_1603_ = lean_usize_dec_eq(v_i_1593_, v_stop_1594_);
if (v___x_1603_ == 0)
{
lean_object* v___x_1604_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1604_ = lean_array_uget_borrowed(v_as_1592_, v_i_1593_);
v___x_1607_ = l_Lean_Expr_mvarId_x21(v___x_1604_);
v___x_1608_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v___x_1607_, v___y_1596_);
lean_dec(v___x_1607_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v_a_1609_; uint8_t v___x_1610_; 
v_a_1609_ = lean_ctor_get(v___x_1608_, 0);
lean_inc(v_a_1609_);
lean_dec_ref_known(v___x_1608_, 1);
v___x_1610_ = lean_unbox(v_a_1609_);
lean_dec(v_a_1609_);
if (v___x_1610_ == 0)
{
goto v___jp_1605_;
}
else
{
v_a_1599_ = v_b_1595_;
goto v___jp_1598_;
}
}
else
{
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v_a_1611_; uint8_t v___x_1612_; 
v_a_1611_ = lean_ctor_get(v___x_1608_, 0);
lean_inc(v_a_1611_);
lean_dec_ref_known(v___x_1608_, 1);
v___x_1612_ = lean_unbox(v_a_1611_);
lean_dec(v_a_1611_);
if (v___x_1612_ == 0)
{
v_a_1599_ = v_b_1595_;
goto v___jp_1598_;
}
else
{
goto v___jp_1605_;
}
}
else
{
lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1620_; 
lean_dec_ref(v_b_1595_);
v_a_1613_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1615_ = v___x_1608_;
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v___x_1608_);
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
v___jp_1605_:
{
lean_object* v___x_1606_; 
lean_inc(v___x_1604_);
v___x_1606_ = lean_array_push(v_b_1595_, v___x_1604_);
v_a_1599_ = v___x_1606_;
goto v___jp_1598_;
}
}
else
{
lean_object* v___x_1621_; 
v___x_1621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1621_, 0, v_b_1595_);
return v___x_1621_;
}
v___jp_1598_:
{
size_t v___x_1600_; size_t v___x_1601_; 
v___x_1600_ = ((size_t)1ULL);
v___x_1601_ = lean_usize_add(v_i_1593_, v___x_1600_);
v_i_1593_ = v___x_1601_;
v_b_1595_ = v_a_1599_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg___boxed(lean_object* v_as_1622_, lean_object* v_i_1623_, lean_object* v_stop_1624_, lean_object* v_b_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_){
_start:
{
size_t v_i_boxed_1628_; size_t v_stop_boxed_1629_; lean_object* v_res_1630_; 
v_i_boxed_1628_ = lean_unbox_usize(v_i_1623_);
lean_dec(v_i_1623_);
v_stop_boxed_1629_ = lean_unbox_usize(v_stop_1624_);
lean_dec(v_stop_1624_);
v_res_1630_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_as_1622_, v_i_boxed_1628_, v_stop_boxed_1629_, v_b_1625_, v___y_1626_);
lean_dec(v___y_1626_);
lean_dec_ref(v_as_1622_);
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_apply_spec__3(lean_object* v_as_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_){
_start:
{
if (lean_obj_tag(v_as_1631_) == 0)
{
lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1637_ = lean_box(0);
v___x_1638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1637_);
return v___x_1638_;
}
else
{
lean_object* v_head_1639_; lean_object* v_tail_1640_; lean_object* v___x_1641_; 
v_head_1639_ = lean_ctor_get(v_as_1631_, 0);
lean_inc(v_head_1639_);
v_tail_1640_ = lean_ctor_get(v_as_1631_, 1);
lean_inc(v_tail_1640_);
lean_dec_ref_known(v_as_1631_, 2);
v___x_1641_ = l_Lean_MVarId_headBetaType(v_head_1639_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_dec_ref_known(v___x_1641_, 1);
v_as_1631_ = v_tail_1640_;
goto _start;
}
else
{
lean_dec(v_tail_1640_);
return v___x_1641_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_apply_spec__3___boxed(lean_object* v_as_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l_List_forM___at___00Lean_MVarId_apply_spec__3(v_as_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9___redArg(lean_object* v_x_1650_, lean_object* v_x_1651_, lean_object* v_x_1652_, lean_object* v_x_1653_){
_start:
{
lean_object* v_ks_1654_; lean_object* v_vs_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1679_; 
v_ks_1654_ = lean_ctor_get(v_x_1650_, 0);
v_vs_1655_ = lean_ctor_get(v_x_1650_, 1);
v_isSharedCheck_1679_ = !lean_is_exclusive(v_x_1650_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1657_ = v_x_1650_;
v_isShared_1658_ = v_isSharedCheck_1679_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_vs_1655_);
lean_inc(v_ks_1654_);
lean_dec(v_x_1650_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1679_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1659_; uint8_t v___x_1660_; 
v___x_1659_ = lean_array_get_size(v_ks_1654_);
v___x_1660_ = lean_nat_dec_lt(v_x_1651_, v___x_1659_);
if (v___x_1660_ == 0)
{
lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1664_; 
lean_dec(v_x_1651_);
v___x_1661_ = lean_array_push(v_ks_1654_, v_x_1652_);
v___x_1662_ = lean_array_push(v_vs_1655_, v_x_1653_);
if (v_isShared_1658_ == 0)
{
lean_ctor_set(v___x_1657_, 1, v___x_1662_);
lean_ctor_set(v___x_1657_, 0, v___x_1661_);
v___x_1664_ = v___x_1657_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v___x_1661_);
lean_ctor_set(v_reuseFailAlloc_1665_, 1, v___x_1662_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
else
{
lean_object* v_k_x27_1666_; uint8_t v___x_1667_; 
v_k_x27_1666_ = lean_array_fget_borrowed(v_ks_1654_, v_x_1651_);
v___x_1667_ = l_Lean_instBEqMVarId_beq(v_x_1652_, v_k_x27_1666_);
if (v___x_1667_ == 0)
{
lean_object* v___x_1669_; 
if (v_isShared_1658_ == 0)
{
v___x_1669_ = v___x_1657_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_ks_1654_);
lean_ctor_set(v_reuseFailAlloc_1673_, 1, v_vs_1655_);
v___x_1669_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1670_ = lean_unsigned_to_nat(1u);
v___x_1671_ = lean_nat_add(v_x_1651_, v___x_1670_);
lean_dec(v_x_1651_);
v_x_1650_ = v___x_1669_;
v_x_1651_ = v___x_1671_;
goto _start;
}
}
else
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1677_; 
v___x_1674_ = lean_array_fset(v_ks_1654_, v_x_1651_, v_x_1652_);
v___x_1675_ = lean_array_fset(v_vs_1655_, v_x_1651_, v_x_1653_);
lean_dec(v_x_1651_);
if (v_isShared_1658_ == 0)
{
lean_ctor_set(v___x_1657_, 1, v___x_1675_);
lean_ctor_set(v___x_1657_, 0, v___x_1674_);
v___x_1677_ = v___x_1657_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v___x_1674_);
lean_ctor_set(v_reuseFailAlloc_1678_, 1, v___x_1675_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8___redArg(lean_object* v_n_1680_, lean_object* v_k_1681_, lean_object* v_v_1682_){
_start:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1683_ = lean_unsigned_to_nat(0u);
v___x_1684_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9___redArg(v_n_1680_, v___x_1683_, v_k_1681_, v_v_1682_);
return v___x_1684_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1685_; 
v___x_1685_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(lean_object* v_x_1686_, size_t v_x_1687_, size_t v_x_1688_, lean_object* v_x_1689_, lean_object* v_x_1690_){
_start:
{
if (lean_obj_tag(v_x_1686_) == 0)
{
lean_object* v_es_1691_; size_t v___x_1692_; size_t v___x_1693_; lean_object* v_j_1694_; lean_object* v___x_1695_; uint8_t v___x_1696_; 
v_es_1691_ = lean_ctor_get(v_x_1686_, 0);
v___x_1692_ = ((size_t)31ULL);
v___x_1693_ = lean_usize_land(v_x_1687_, v___x_1692_);
v_j_1694_ = lean_usize_to_nat(v___x_1693_);
v___x_1695_ = lean_array_get_size(v_es_1691_);
v___x_1696_ = lean_nat_dec_lt(v_j_1694_, v___x_1695_);
if (v___x_1696_ == 0)
{
lean_dec(v_j_1694_);
lean_dec(v_x_1690_);
lean_dec(v_x_1689_);
return v_x_1686_;
}
else
{
lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1735_; 
lean_inc_ref(v_es_1691_);
v_isSharedCheck_1735_ = !lean_is_exclusive(v_x_1686_);
if (v_isSharedCheck_1735_ == 0)
{
lean_object* v_unused_1736_; 
v_unused_1736_ = lean_ctor_get(v_x_1686_, 0);
lean_dec(v_unused_1736_);
v___x_1698_ = v_x_1686_;
v_isShared_1699_ = v_isSharedCheck_1735_;
goto v_resetjp_1697_;
}
else
{
lean_dec(v_x_1686_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1735_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v_v_1700_; lean_object* v___x_1701_; lean_object* v_xs_x27_1702_; lean_object* v___y_1704_; 
v_v_1700_ = lean_array_fget(v_es_1691_, v_j_1694_);
v___x_1701_ = lean_box(0);
v_xs_x27_1702_ = lean_array_fset(v_es_1691_, v_j_1694_, v___x_1701_);
switch(lean_obj_tag(v_v_1700_))
{
case 0:
{
lean_object* v_key_1709_; lean_object* v_val_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1720_; 
v_key_1709_ = lean_ctor_get(v_v_1700_, 0);
v_val_1710_ = lean_ctor_get(v_v_1700_, 1);
v_isSharedCheck_1720_ = !lean_is_exclusive(v_v_1700_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1712_ = v_v_1700_;
v_isShared_1713_ = v_isSharedCheck_1720_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_val_1710_);
lean_inc(v_key_1709_);
lean_dec(v_v_1700_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1720_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
uint8_t v___x_1714_; 
v___x_1714_ = l_Lean_instBEqMVarId_beq(v_x_1689_, v_key_1709_);
if (v___x_1714_ == 0)
{
lean_object* v___x_1715_; lean_object* v___x_1716_; 
lean_del_object(v___x_1712_);
v___x_1715_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1709_, v_val_1710_, v_x_1689_, v_x_1690_);
v___x_1716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1716_, 0, v___x_1715_);
v___y_1704_ = v___x_1716_;
goto v___jp_1703_;
}
else
{
lean_object* v___x_1718_; 
lean_dec(v_val_1710_);
lean_dec(v_key_1709_);
if (v_isShared_1713_ == 0)
{
lean_ctor_set(v___x_1712_, 1, v_x_1690_);
lean_ctor_set(v___x_1712_, 0, v_x_1689_);
v___x_1718_ = v___x_1712_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_x_1689_);
lean_ctor_set(v_reuseFailAlloc_1719_, 1, v_x_1690_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
v___y_1704_ = v___x_1718_;
goto v___jp_1703_;
}
}
}
}
case 1:
{
lean_object* v_node_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1733_; 
v_node_1721_ = lean_ctor_get(v_v_1700_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v_v_1700_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1723_ = v_v_1700_;
v_isShared_1724_ = v_isSharedCheck_1733_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_node_1721_);
lean_dec(v_v_1700_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1733_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
size_t v___x_1725_; size_t v___x_1726_; size_t v___x_1727_; size_t v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1731_; 
v___x_1725_ = ((size_t)5ULL);
v___x_1726_ = lean_usize_shift_right(v_x_1687_, v___x_1725_);
v___x_1727_ = ((size_t)1ULL);
v___x_1728_ = lean_usize_add(v_x_1688_, v___x_1727_);
v___x_1729_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_node_1721_, v___x_1726_, v___x_1728_, v_x_1689_, v_x_1690_);
if (v_isShared_1724_ == 0)
{
lean_ctor_set(v___x_1723_, 0, v___x_1729_);
v___x_1731_ = v___x_1723_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v___x_1729_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
v___y_1704_ = v___x_1731_;
goto v___jp_1703_;
}
}
}
default: 
{
lean_object* v___x_1734_; 
v___x_1734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1734_, 0, v_x_1689_);
lean_ctor_set(v___x_1734_, 1, v_x_1690_);
v___y_1704_ = v___x_1734_;
goto v___jp_1703_;
}
}
v___jp_1703_:
{
lean_object* v___x_1705_; lean_object* v___x_1707_; 
v___x_1705_ = lean_array_fset(v_xs_x27_1702_, v_j_1694_, v___y_1704_);
lean_dec(v_j_1694_);
if (v_isShared_1699_ == 0)
{
lean_ctor_set(v___x_1698_, 0, v___x_1705_);
v___x_1707_ = v___x_1698_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v___x_1705_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
}
}
else
{
lean_object* v_ks_1737_; lean_object* v_vs_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1756_; 
v_ks_1737_ = lean_ctor_get(v_x_1686_, 0);
v_vs_1738_ = lean_ctor_get(v_x_1686_, 1);
v_isSharedCheck_1756_ = !lean_is_exclusive(v_x_1686_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1740_ = v_x_1686_;
v_isShared_1741_ = v_isSharedCheck_1756_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_vs_1738_);
lean_inc(v_ks_1737_);
lean_dec(v_x_1686_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1756_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1743_; 
if (v_isShared_1741_ == 0)
{
v___x_1743_ = v___x_1740_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v_ks_1737_);
lean_ctor_set(v_reuseFailAlloc_1755_, 1, v_vs_1738_);
v___x_1743_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
lean_object* v_newNode_1744_; size_t v___x_1745_; uint8_t v___x_1746_; 
v_newNode_1744_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8___redArg(v___x_1743_, v_x_1689_, v_x_1690_);
v___x_1745_ = ((size_t)7ULL);
v___x_1746_ = lean_usize_dec_le(v___x_1745_, v_x_1688_);
if (v___x_1746_ == 0)
{
lean_object* v___x_1747_; lean_object* v___x_1748_; uint8_t v___x_1749_; 
v___x_1747_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1744_);
v___x_1748_ = lean_unsigned_to_nat(4u);
v___x_1749_ = lean_nat_dec_lt(v___x_1747_, v___x_1748_);
lean_dec(v___x_1747_);
if (v___x_1749_ == 0)
{
lean_object* v_ks_1750_; lean_object* v_vs_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
v_ks_1750_ = lean_ctor_get(v_newNode_1744_, 0);
lean_inc_ref(v_ks_1750_);
v_vs_1751_ = lean_ctor_get(v_newNode_1744_, 1);
lean_inc_ref(v_vs_1751_);
lean_dec_ref(v_newNode_1744_);
v___x_1752_ = lean_unsigned_to_nat(0u);
v___x_1753_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0);
v___x_1754_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(v_x_1688_, v_ks_1750_, v_vs_1751_, v___x_1752_, v___x_1753_);
lean_dec_ref(v_vs_1751_);
lean_dec_ref(v_ks_1750_);
return v___x_1754_;
}
else
{
return v_newNode_1744_;
}
}
else
{
return v_newNode_1744_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(size_t v_depth_1757_, lean_object* v_keys_1758_, lean_object* v_vals_1759_, lean_object* v_i_1760_, lean_object* v_entries_1761_){
_start:
{
lean_object* v___x_1762_; uint8_t v___x_1763_; 
v___x_1762_ = lean_array_get_size(v_keys_1758_);
v___x_1763_ = lean_nat_dec_lt(v_i_1760_, v___x_1762_);
if (v___x_1763_ == 0)
{
lean_dec(v_i_1760_);
return v_entries_1761_;
}
else
{
lean_object* v_k_1764_; lean_object* v_v_1765_; uint64_t v___x_1766_; size_t v_h_1767_; size_t v___x_1768_; lean_object* v___x_1769_; size_t v___x_1770_; size_t v___x_1771_; size_t v___x_1772_; size_t v_h_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v_k_1764_ = lean_array_fget_borrowed(v_keys_1758_, v_i_1760_);
v_v_1765_ = lean_array_fget_borrowed(v_vals_1759_, v_i_1760_);
v___x_1766_ = l_Lean_instHashableMVarId_hash(v_k_1764_);
v_h_1767_ = lean_uint64_to_usize(v___x_1766_);
v___x_1768_ = ((size_t)5ULL);
v___x_1769_ = lean_unsigned_to_nat(1u);
v___x_1770_ = ((size_t)1ULL);
v___x_1771_ = lean_usize_sub(v_depth_1757_, v___x_1770_);
v___x_1772_ = lean_usize_mul(v___x_1768_, v___x_1771_);
v_h_1773_ = lean_usize_shift_right(v_h_1767_, v___x_1772_);
v___x_1774_ = lean_nat_add(v_i_1760_, v___x_1769_);
lean_dec(v_i_1760_);
lean_inc(v_v_1765_);
lean_inc(v_k_1764_);
v___x_1775_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_entries_1761_, v_h_1773_, v_depth_1757_, v_k_1764_, v_v_1765_);
v_i_1760_ = v___x_1774_;
v_entries_1761_ = v___x_1775_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg___boxed(lean_object* v_depth_1777_, lean_object* v_keys_1778_, lean_object* v_vals_1779_, lean_object* v_i_1780_, lean_object* v_entries_1781_){
_start:
{
size_t v_depth_boxed_1782_; lean_object* v_res_1783_; 
v_depth_boxed_1782_ = lean_unbox_usize(v_depth_1777_);
lean_dec(v_depth_1777_);
v_res_1783_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(v_depth_boxed_1782_, v_keys_1778_, v_vals_1779_, v_i_1780_, v_entries_1781_);
lean_dec_ref(v_vals_1779_);
lean_dec_ref(v_keys_1778_);
return v_res_1783_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_x_1784_, lean_object* v_x_1785_, lean_object* v_x_1786_, lean_object* v_x_1787_, lean_object* v_x_1788_){
_start:
{
size_t v_x_7081__boxed_1789_; size_t v_x_7082__boxed_1790_; lean_object* v_res_1791_; 
v_x_7081__boxed_1789_ = lean_unbox_usize(v_x_1785_);
lean_dec(v_x_1785_);
v_x_7082__boxed_1790_ = lean_unbox_usize(v_x_1786_);
lean_dec(v_x_1786_);
v_res_1791_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_x_1784_, v_x_7081__boxed_1789_, v_x_7082__boxed_1790_, v_x_1787_, v_x_1788_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1___redArg(lean_object* v_x_1792_, lean_object* v_x_1793_, lean_object* v_x_1794_){
_start:
{
uint64_t v___x_1795_; size_t v___x_1796_; size_t v___x_1797_; lean_object* v___x_1798_; 
v___x_1795_ = l_Lean_instHashableMVarId_hash(v_x_1793_);
v___x_1796_ = lean_uint64_to_usize(v___x_1795_);
v___x_1797_ = ((size_t)1ULL);
v___x_1798_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_x_1792_, v___x_1796_, v___x_1797_, v_x_1793_, v_x_1794_);
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(lean_object* v_mvarId_1799_, lean_object* v_val_1800_, lean_object* v___y_1801_){
_start:
{
lean_object* v___x_1803_; lean_object* v_mctx_1804_; lean_object* v_cache_1805_; lean_object* v_zetaDeltaFVarIds_1806_; lean_object* v_postponed_1807_; lean_object* v_diag_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1837_; 
v___x_1803_ = lean_st_ref_take(v___y_1801_);
v_mctx_1804_ = lean_ctor_get(v___x_1803_, 0);
v_cache_1805_ = lean_ctor_get(v___x_1803_, 1);
v_zetaDeltaFVarIds_1806_ = lean_ctor_get(v___x_1803_, 2);
v_postponed_1807_ = lean_ctor_get(v___x_1803_, 3);
v_diag_1808_ = lean_ctor_get(v___x_1803_, 4);
v_isSharedCheck_1837_ = !lean_is_exclusive(v___x_1803_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1810_ = v___x_1803_;
v_isShared_1811_ = v_isSharedCheck_1837_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_diag_1808_);
lean_inc(v_postponed_1807_);
lean_inc(v_zetaDeltaFVarIds_1806_);
lean_inc(v_cache_1805_);
lean_inc(v_mctx_1804_);
lean_dec(v___x_1803_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1837_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v_depth_1812_; lean_object* v_levelAssignDepth_1813_; lean_object* v_lmvarCounter_1814_; lean_object* v_mvarCounter_1815_; lean_object* v_lDecls_1816_; lean_object* v_decls_1817_; lean_object* v_userNames_1818_; lean_object* v_lAssignment_1819_; lean_object* v_eAssignment_1820_; lean_object* v_dAssignment_1821_; lean_object* v_instanceTypedMVars_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1836_; 
v_depth_1812_ = lean_ctor_get(v_mctx_1804_, 0);
v_levelAssignDepth_1813_ = lean_ctor_get(v_mctx_1804_, 1);
v_lmvarCounter_1814_ = lean_ctor_get(v_mctx_1804_, 2);
v_mvarCounter_1815_ = lean_ctor_get(v_mctx_1804_, 3);
v_lDecls_1816_ = lean_ctor_get(v_mctx_1804_, 4);
v_decls_1817_ = lean_ctor_get(v_mctx_1804_, 5);
v_userNames_1818_ = lean_ctor_get(v_mctx_1804_, 6);
v_lAssignment_1819_ = lean_ctor_get(v_mctx_1804_, 7);
v_eAssignment_1820_ = lean_ctor_get(v_mctx_1804_, 8);
v_dAssignment_1821_ = lean_ctor_get(v_mctx_1804_, 9);
v_instanceTypedMVars_1822_ = lean_ctor_get(v_mctx_1804_, 10);
v_isSharedCheck_1836_ = !lean_is_exclusive(v_mctx_1804_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1824_ = v_mctx_1804_;
v_isShared_1825_ = v_isSharedCheck_1836_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_instanceTypedMVars_1822_);
lean_inc(v_dAssignment_1821_);
lean_inc(v_eAssignment_1820_);
lean_inc(v_lAssignment_1819_);
lean_inc(v_userNames_1818_);
lean_inc(v_decls_1817_);
lean_inc(v_lDecls_1816_);
lean_inc(v_mvarCounter_1815_);
lean_inc(v_lmvarCounter_1814_);
lean_inc(v_levelAssignDepth_1813_);
lean_inc(v_depth_1812_);
lean_dec(v_mctx_1804_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1836_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1826_; lean_object* v___x_1828_; 
v___x_1826_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1___redArg(v_eAssignment_1820_, v_mvarId_1799_, v_val_1800_);
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 8, v___x_1826_);
v___x_1828_ = v___x_1824_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_depth_1812_);
lean_ctor_set(v_reuseFailAlloc_1835_, 1, v_levelAssignDepth_1813_);
lean_ctor_set(v_reuseFailAlloc_1835_, 2, v_lmvarCounter_1814_);
lean_ctor_set(v_reuseFailAlloc_1835_, 3, v_mvarCounter_1815_);
lean_ctor_set(v_reuseFailAlloc_1835_, 4, v_lDecls_1816_);
lean_ctor_set(v_reuseFailAlloc_1835_, 5, v_decls_1817_);
lean_ctor_set(v_reuseFailAlloc_1835_, 6, v_userNames_1818_);
lean_ctor_set(v_reuseFailAlloc_1835_, 7, v_lAssignment_1819_);
lean_ctor_set(v_reuseFailAlloc_1835_, 8, v___x_1826_);
lean_ctor_set(v_reuseFailAlloc_1835_, 9, v_dAssignment_1821_);
lean_ctor_set(v_reuseFailAlloc_1835_, 10, v_instanceTypedMVars_1822_);
v___x_1828_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
lean_object* v___x_1830_; 
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 0, v___x_1828_);
v___x_1830_ = v___x_1810_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v___x_1828_);
lean_ctor_set(v_reuseFailAlloc_1834_, 1, v_cache_1805_);
lean_ctor_set(v_reuseFailAlloc_1834_, 2, v_zetaDeltaFVarIds_1806_);
lean_ctor_set(v_reuseFailAlloc_1834_, 3, v_postponed_1807_);
lean_ctor_set(v_reuseFailAlloc_1834_, 4, v_diag_1808_);
v___x_1830_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; 
v___x_1831_ = lean_st_ref_put(v___y_1801_, v___x_1830_);
v___x_1832_ = lean_box(0);
v___x_1833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1832_);
return v___x_1833_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg___boxed(lean_object* v_mvarId_1838_, lean_object* v_val_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_){
_start:
{
lean_object* v_res_1842_; 
v_res_1842_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_1838_, v_val_1839_, v___y_1840_);
lean_dec(v___y_1840_);
return v_res_1842_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_MVarId_apply_spec__2(lean_object* v_a_1843_, lean_object* v_x_1844_){
_start:
{
if (lean_obj_tag(v_x_1844_) == 0)
{
uint8_t v___x_1845_; 
v___x_1845_ = 0;
return v___x_1845_;
}
else
{
lean_object* v_head_1846_; lean_object* v_tail_1847_; uint8_t v___x_1848_; 
v_head_1846_ = lean_ctor_get(v_x_1844_, 0);
v_tail_1847_ = lean_ctor_get(v_x_1844_, 1);
v___x_1848_ = l_Lean_instBEqMVarId_beq(v_a_1843_, v_head_1846_);
if (v___x_1848_ == 0)
{
v_x_1844_ = v_tail_1847_;
goto _start;
}
else
{
return v___x_1848_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_MVarId_apply_spec__2___boxed(lean_object* v_a_1850_, lean_object* v_x_1851_){
_start:
{
uint8_t v_res_1852_; lean_object* v_r_1853_; 
v_res_1852_ = l_List_elem___at___00Lean_MVarId_apply_spec__2(v_a_1850_, v_x_1851_);
lean_dec(v_x_1851_);
lean_dec(v_a_1850_);
v_r_1853_ = lean_box(v_res_1852_);
return v_r_1853_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(lean_object* v_a_1854_, lean_object* v_as_1855_, size_t v_i_1856_, size_t v_stop_1857_, lean_object* v_b_1858_){
_start:
{
lean_object* v___y_1860_; uint8_t v___x_1864_; 
v___x_1864_ = lean_usize_dec_eq(v_i_1856_, v_stop_1857_);
if (v___x_1864_ == 0)
{
lean_object* v___x_1865_; uint8_t v___x_1866_; 
v___x_1865_ = lean_array_uget_borrowed(v_as_1855_, v_i_1856_);
v___x_1866_ = l_List_elem___at___00Lean_MVarId_apply_spec__2(v___x_1865_, v_a_1854_);
if (v___x_1866_ == 0)
{
lean_object* v___x_1867_; 
lean_inc(v___x_1865_);
v___x_1867_ = lean_array_push(v_b_1858_, v___x_1865_);
v___y_1860_ = v___x_1867_;
goto v___jp_1859_;
}
else
{
v___y_1860_ = v_b_1858_;
goto v___jp_1859_;
}
}
else
{
return v_b_1858_;
}
v___jp_1859_:
{
size_t v___x_1861_; size_t v___x_1862_; 
v___x_1861_ = ((size_t)1ULL);
v___x_1862_ = lean_usize_add(v_i_1856_, v___x_1861_);
v_i_1856_ = v___x_1862_;
v_b_1858_ = v___y_1860_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4___boxed(lean_object* v_a_1868_, lean_object* v_as_1869_, lean_object* v_i_1870_, lean_object* v_stop_1871_, lean_object* v_b_1872_){
_start:
{
size_t v_i_boxed_1873_; size_t v_stop_boxed_1874_; lean_object* v_res_1875_; 
v_i_boxed_1873_ = lean_unbox_usize(v_i_1870_);
lean_dec(v_i_1870_);
v_stop_boxed_1874_ = lean_unbox_usize(v_stop_1871_);
lean_dec(v_stop_1871_);
v_res_1875_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(v_a_1868_, v_as_1869_, v_i_boxed_1873_, v_stop_boxed_1874_, v_b_1872_);
lean_dec_ref(v_as_1869_);
lean_dec(v_a_1868_);
return v_res_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___lam__0(lean_object* v_mvarId_1876_, lean_object* v___x_1877_, lean_object* v_e_1878_, lean_object* v_cfg_1879_, lean_object* v_term_x3f_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_){
_start:
{
lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1890_; lean_object* v___y_1891_; lean_object* v___y_1892_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v___y_1915_; lean_object* v___y_1916_; lean_object* v___y_1917_; uint8_t v___y_1918_; lean_object* v___y_1919_; lean_object* v___y_1920_; lean_object* v_a_1921_; lean_object* v___y_1954_; lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; uint8_t v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___x_1972_; 
lean_inc(v___x_1877_);
lean_inc(v_mvarId_1876_);
v___x_1972_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1876_, v___x_1877_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
if (lean_obj_tag(v___x_1972_) == 0)
{
lean_object* v___x_1973_; 
lean_dec_ref_known(v___x_1972_, 1);
lean_inc(v_mvarId_1876_);
v___x_1973_ = l_Lean_MVarId_getType(v_mvarId_1876_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_object* v_a_1974_; lean_object* v___x_1975_; 
v_a_1974_ = lean_ctor_get(v___x_1973_, 0);
lean_inc(v_a_1974_);
lean_dec_ref_known(v___x_1973_, 1);
lean_inc(v___y_1884_);
lean_inc_ref(v___y_1883_);
lean_inc(v___y_1882_);
lean_inc_ref(v___y_1881_);
lean_inc_ref(v_e_1878_);
v___x_1975_ = lean_infer_type(v_e_1878_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
if (lean_obj_tag(v___x_1975_) == 0)
{
lean_object* v_a_1976_; lean_object* v_rangeNumArgs_1978_; lean_object* v_lower_1979_; lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v___y_1982_; lean_object* v___y_1983_; lean_object* v___x_2023_; 
v_a_1976_ = lean_ctor_get(v___x_1975_, 0);
lean_inc_n(v_a_1976_, 2);
lean_dec_ref_known(v___x_1975_, 1);
v___x_2023_ = l_Lean_Meta_getExpectedNumArgsAux(v_a_1976_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v_a_2024_; lean_object* v_snd_2025_; uint8_t v___x_2026_; 
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
lean_inc(v_a_2024_);
lean_dec_ref_known(v___x_2023_, 1);
v_snd_2025_ = lean_ctor_get(v_a_2024_, 1);
v___x_2026_ = lean_unbox(v_snd_2025_);
if (v___x_2026_ == 0)
{
lean_object* v_fst_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2047_; 
v_fst_2027_ = lean_ctor_get(v_a_2024_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v_a_2024_);
if (v_isSharedCheck_2047_ == 0)
{
lean_object* v_unused_2048_; 
v_unused_2048_ = lean_ctor_get(v_a_2024_, 1);
lean_dec(v_unused_2048_);
v___x_2029_ = v_a_2024_;
v_isShared_2030_ = v_isSharedCheck_2047_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_fst_2027_);
lean_dec(v_a_2024_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2047_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2031_; 
lean_inc(v_a_1974_);
v___x_2031_ = l_Lean_Meta_getExpectedNumArgs(v_a_1974_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_object* v_a_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2037_; 
v_a_2032_ = lean_ctor_get(v___x_2031_, 0);
lean_inc(v_a_2032_);
lean_dec_ref_known(v___x_2031_, 1);
v___x_2033_ = lean_nat_sub(v_fst_2027_, v_a_2032_);
lean_dec(v_a_2032_);
v___x_2034_ = lean_unsigned_to_nat(1u);
v___x_2035_ = lean_nat_add(v_fst_2027_, v___x_2034_);
lean_dec(v_fst_2027_);
lean_inc(v___x_2033_);
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 1, v___x_2035_);
lean_ctor_set(v___x_2029_, 0, v___x_2033_);
v___x_2037_ = v___x_2029_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v___x_2033_);
lean_ctor_set(v_reuseFailAlloc_2038_, 1, v___x_2035_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
v_rangeNumArgs_1978_ = v___x_2037_;
v_lower_1979_ = v___x_2033_;
v___y_1980_ = v___y_1881_;
v___y_1981_ = v___y_1882_;
v___y_1982_ = v___y_1883_;
v___y_1983_ = v___y_1884_;
goto v___jp_1977_;
}
}
else
{
lean_object* v_a_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2046_; 
lean_del_object(v___x_2029_);
lean_dec(v_fst_2027_);
lean_dec(v_a_1976_);
lean_dec(v_a_1974_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v_term_x3f_1880_);
lean_dec_ref(v_e_1878_);
lean_dec(v___x_1877_);
lean_dec(v_mvarId_1876_);
v_a_2039_ = lean_ctor_get(v___x_2031_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2041_ = v___x_2031_;
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_a_2039_);
lean_dec(v___x_2031_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2044_; 
if (v_isShared_2042_ == 0)
{
v___x_2044_ = v___x_2041_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_a_2039_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
}
}
else
{
lean_object* v_fst_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2058_; 
v_fst_2049_ = lean_ctor_get(v_a_2024_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v_a_2024_);
if (v_isSharedCheck_2058_ == 0)
{
lean_object* v_unused_2059_; 
v_unused_2059_ = lean_ctor_get(v_a_2024_, 1);
lean_dec(v_unused_2059_);
v___x_2051_ = v_a_2024_;
v_isShared_2052_ = v_isSharedCheck_2058_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_fst_2049_);
lean_dec(v_a_2024_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2058_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2056_; 
v___x_2053_ = lean_unsigned_to_nat(1u);
v___x_2054_ = lean_nat_add(v_fst_2049_, v___x_2053_);
lean_inc(v_fst_2049_);
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 1, v___x_2054_);
v___x_2056_ = v___x_2051_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_fst_2049_);
lean_ctor_set(v_reuseFailAlloc_2057_, 1, v___x_2054_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
v_rangeNumArgs_1978_ = v___x_2056_;
v_lower_1979_ = v_fst_2049_;
v___y_1980_ = v___y_1881_;
v___y_1981_ = v___y_1882_;
v___y_1982_ = v___y_1883_;
v___y_1983_ = v___y_1884_;
goto v___jp_1977_;
}
}
}
}
else
{
lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2067_; 
lean_dec(v_a_1976_);
lean_dec(v_a_1974_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v_term_x3f_1880_);
lean_dec_ref(v_e_1878_);
lean_dec(v___x_1877_);
lean_dec(v_mvarId_1876_);
v_a_2060_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2062_ = v___x_2023_;
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_2023_);
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
v___jp_1977_:
{
lean_object* v___x_1984_; 
lean_inc(v_mvarId_1876_);
v___x_1984_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go(v_mvarId_1876_, v_cfg_1879_, v_term_x3f_1880_, v_a_1974_, v_a_1976_, v_rangeNumArgs_1978_, v_lower_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_);
lean_dec_ref(v_rangeNumArgs_1978_);
if (lean_obj_tag(v___x_1984_) == 0)
{
lean_object* v_a_1985_; lean_object* v_fst_1986_; lean_object* v_snd_1987_; uint8_t v_newGoals_1988_; uint8_t v_synthAssignedInstances_1989_; uint8_t v_allowSynthFailures_1990_; lean_object* v___x_1991_; 
v_a_1985_ = lean_ctor_get(v___x_1984_, 0);
lean_inc(v_a_1985_);
lean_dec_ref_known(v___x_1984_, 1);
v_fst_1986_ = lean_ctor_get(v_a_1985_, 0);
lean_inc(v_fst_1986_);
v_snd_1987_ = lean_ctor_get(v_a_1985_, 1);
lean_inc_n(v_snd_1987_, 2);
lean_dec(v_a_1985_);
v_newGoals_1988_ = lean_ctor_get_uint8(v_cfg_1879_, 0);
v_synthAssignedInstances_1989_ = lean_ctor_get_uint8(v_cfg_1879_, 1);
v_allowSynthFailures_1990_ = lean_ctor_get_uint8(v_cfg_1879_, 2);
lean_inc(v_mvarId_1876_);
v___x_1991_ = l_Lean_Meta_synthAppInstances(v___x_1877_, v_mvarId_1876_, v_fst_1986_, v_snd_1987_, v_synthAssignedInstances_1989_, v_allowSynthFailures_1990_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_object* v___x_1992_; lean_object* v_a_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; uint8_t v___x_1999_; 
lean_dec_ref_known(v___x_1991_, 1);
v___x_1992_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_e_1878_, v___y_1981_);
v_a_1993_ = lean_ctor_get(v___x_1992_, 0);
lean_inc_n(v_a_1993_, 2);
lean_dec_ref(v___x_1992_);
v___x_1994_ = l_Lean_mkAppN(v_a_1993_, v_fst_1986_);
lean_inc(v_mvarId_1876_);
v___x_1995_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_1876_, v___x_1994_, v___y_1981_);
lean_dec_ref(v___x_1995_);
v___x_1996_ = lean_unsigned_to_nat(0u);
v___x_1997_ = lean_array_get_size(v_fst_1986_);
v___x_1998_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0));
v___x_1999_ = lean_nat_dec_lt(v___x_1996_, v___x_1997_);
if (v___x_1999_ == 0)
{
lean_dec(v_fst_1986_);
v___y_1913_ = v___y_1980_;
v___y_1914_ = v_snd_1987_;
v___y_1915_ = v___y_1983_;
v___y_1916_ = v___x_1996_;
v___y_1917_ = v___y_1981_;
v___y_1918_ = v_newGoals_1988_;
v___y_1919_ = v_a_1993_;
v___y_1920_ = v___y_1982_;
v_a_1921_ = v___x_1998_;
goto v___jp_1912_;
}
else
{
uint8_t v___x_2000_; 
v___x_2000_ = lean_nat_dec_le(v___x_1997_, v___x_1997_);
if (v___x_2000_ == 0)
{
if (v___x_1999_ == 0)
{
lean_dec(v_fst_1986_);
v___y_1913_ = v___y_1980_;
v___y_1914_ = v_snd_1987_;
v___y_1915_ = v___y_1983_;
v___y_1916_ = v___x_1996_;
v___y_1917_ = v___y_1981_;
v___y_1918_ = v_newGoals_1988_;
v___y_1919_ = v_a_1993_;
v___y_1920_ = v___y_1982_;
v_a_1921_ = v___x_1998_;
goto v___jp_1912_;
}
else
{
size_t v___x_2001_; size_t v___x_2002_; lean_object* v___x_2003_; 
v___x_2001_ = ((size_t)0ULL);
v___x_2002_ = lean_usize_of_nat(v___x_1997_);
v___x_2003_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_fst_1986_, v___x_2001_, v___x_2002_, v___x_1998_, v___y_1981_);
lean_dec(v_fst_1986_);
v___y_1954_ = v___y_1980_;
v___y_1955_ = v_snd_1987_;
v___y_1956_ = v___y_1983_;
v___y_1957_ = v___y_1981_;
v___y_1958_ = v___x_1996_;
v___y_1959_ = v_a_1993_;
v___y_1960_ = v_newGoals_1988_;
v___y_1961_ = v___y_1982_;
v___y_1962_ = v___x_2003_;
goto v___jp_1953_;
}
}
else
{
size_t v___x_2004_; size_t v___x_2005_; lean_object* v___x_2006_; 
v___x_2004_ = ((size_t)0ULL);
v___x_2005_ = lean_usize_of_nat(v___x_1997_);
v___x_2006_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_fst_1986_, v___x_2004_, v___x_2005_, v___x_1998_, v___y_1981_);
lean_dec(v_fst_1986_);
v___y_1954_ = v___y_1980_;
v___y_1955_ = v_snd_1987_;
v___y_1956_ = v___y_1983_;
v___y_1957_ = v___y_1981_;
v___y_1958_ = v___x_1996_;
v___y_1959_ = v_a_1993_;
v___y_1960_ = v_newGoals_1988_;
v___y_1961_ = v___y_1982_;
v___y_1962_ = v___x_2006_;
goto v___jp_1953_;
}
}
}
else
{
lean_object* v_a_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2014_; 
lean_dec(v_snd_1987_);
lean_dec(v_fst_1986_);
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
lean_dec_ref(v_e_1878_);
lean_dec(v_mvarId_1876_);
v_a_2007_ = lean_ctor_get(v___x_1991_, 0);
v_isSharedCheck_2014_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_2009_ = v___x_1991_;
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_a_2007_);
lean_dec(v___x_1991_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2012_; 
if (v_isShared_2010_ == 0)
{
v___x_2012_ = v___x_2009_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_a_2007_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
}
else
{
lean_object* v_a_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2022_; 
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
lean_dec_ref(v_e_1878_);
lean_dec(v___x_1877_);
lean_dec(v_mvarId_1876_);
v_a_2015_ = lean_ctor_get(v___x_1984_, 0);
v_isSharedCheck_2022_ = !lean_is_exclusive(v___x_1984_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_2017_ = v___x_1984_;
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_a_2015_);
lean_dec(v___x_1984_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2020_; 
if (v_isShared_2018_ == 0)
{
v___x_2020_ = v___x_2017_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v_a_2015_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
}
}
}
}
}
else
{
lean_object* v_a_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2075_; 
lean_dec(v_a_1974_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v_term_x3f_1880_);
lean_dec_ref(v_e_1878_);
lean_dec(v___x_1877_);
lean_dec(v_mvarId_1876_);
v_a_2068_ = lean_ctor_get(v___x_1975_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2070_ = v___x_1975_;
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_a_2068_);
lean_dec(v___x_1975_);
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
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v_term_x3f_1880_);
lean_dec_ref(v_e_1878_);
lean_dec(v___x_1877_);
lean_dec(v_mvarId_1876_);
v_a_2076_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2078_ = v___x_1973_;
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_1973_);
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
else
{
lean_object* v_a_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2091_; 
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v_term_x3f_1880_);
lean_dec_ref(v_e_1878_);
lean_dec(v___x_1877_);
lean_dec(v_mvarId_1876_);
v_a_2084_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_2091_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2086_ = v___x_1972_;
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_a_2084_);
lean_dec(v___x_1972_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___x_2089_; 
if (v_isShared_2087_ == 0)
{
v___x_2089_ = v___x_2086_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_a_2084_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
return v___x_2089_;
}
}
}
v___jp_1886_:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1893_ = lean_array_to_list(v___y_1892_);
v___x_1894_ = l_List_appendTR___redArg(v___y_1890_, v___x_1893_);
lean_inc(v___x_1894_);
v___x_1895_ = l_List_forM___at___00Lean_MVarId_apply_spec__3(v___x_1894_, v___y_1887_, v___y_1889_, v___y_1891_, v___y_1888_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1891_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1887_);
if (lean_obj_tag(v___x_1895_) == 0)
{
lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1902_; 
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1902_ == 0)
{
lean_object* v_unused_1903_; 
v_unused_1903_ = lean_ctor_get(v___x_1895_, 0);
lean_dec(v_unused_1903_);
v___x_1897_ = v___x_1895_;
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
else
{
lean_dec(v___x_1895_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1900_; 
if (v_isShared_1898_ == 0)
{
lean_ctor_set(v___x_1897_, 0, v___x_1894_);
v___x_1900_ = v___x_1897_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v___x_1894_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
else
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1911_; 
lean_dec(v___x_1894_);
v_a_1904_ = lean_ctor_get(v___x_1895_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1906_ = v___x_1895_;
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v___x_1895_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1909_; 
if (v_isShared_1907_ == 0)
{
v___x_1909_ = v___x_1906_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_a_1904_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
}
v___jp_1912_:
{
lean_object* v___x_1922_; 
v___x_1922_ = l_Lean_Meta_appendParentTag(v_mvarId_1876_, v_a_1921_, v___y_1914_, v___y_1913_, v___y_1917_, v___y_1920_, v___y_1915_);
lean_dec_ref(v___y_1914_);
if (lean_obj_tag(v___x_1922_) == 0)
{
lean_object* v___x_1923_; 
lean_dec_ref_known(v___x_1922_, 1);
v___x_1923_ = l_Lean_Meta_getMVarsNoDelayed(v___y_1919_, v___y_1913_, v___y_1917_, v___y_1920_, v___y_1915_);
if (lean_obj_tag(v___x_1923_) == 0)
{
lean_object* v_a_1924_; lean_object* v___x_1925_; 
v_a_1924_ = lean_ctor_get(v___x_1923_, 0);
lean_inc(v_a_1924_);
lean_dec_ref_known(v___x_1923_, 1);
v___x_1925_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(v_a_1921_, v___y_1918_, v___y_1913_, v___y_1917_, v___y_1920_, v___y_1915_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v_a_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; uint8_t v___x_1929_; 
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
lean_inc(v_a_1926_);
lean_dec_ref_known(v___x_1925_, 1);
v___x_1927_ = lean_array_get_size(v_a_1924_);
v___x_1928_ = lean_mk_empty_array_with_capacity(v___y_1916_);
v___x_1929_ = lean_nat_dec_lt(v___y_1916_, v___x_1927_);
if (v___x_1929_ == 0)
{
lean_dec(v_a_1924_);
v___y_1887_ = v___y_1913_;
v___y_1888_ = v___y_1915_;
v___y_1889_ = v___y_1917_;
v___y_1890_ = v_a_1926_;
v___y_1891_ = v___y_1920_;
v___y_1892_ = v___x_1928_;
goto v___jp_1886_;
}
else
{
uint8_t v___x_1930_; 
v___x_1930_ = lean_nat_dec_le(v___x_1927_, v___x_1927_);
if (v___x_1930_ == 0)
{
if (v___x_1929_ == 0)
{
lean_dec(v_a_1924_);
v___y_1887_ = v___y_1913_;
v___y_1888_ = v___y_1915_;
v___y_1889_ = v___y_1917_;
v___y_1890_ = v_a_1926_;
v___y_1891_ = v___y_1920_;
v___y_1892_ = v___x_1928_;
goto v___jp_1886_;
}
else
{
size_t v___x_1931_; size_t v___x_1932_; lean_object* v___x_1933_; 
v___x_1931_ = ((size_t)0ULL);
v___x_1932_ = lean_usize_of_nat(v___x_1927_);
v___x_1933_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(v_a_1926_, v_a_1924_, v___x_1931_, v___x_1932_, v___x_1928_);
lean_dec(v_a_1924_);
v___y_1887_ = v___y_1913_;
v___y_1888_ = v___y_1915_;
v___y_1889_ = v___y_1917_;
v___y_1890_ = v_a_1926_;
v___y_1891_ = v___y_1920_;
v___y_1892_ = v___x_1933_;
goto v___jp_1886_;
}
}
else
{
size_t v___x_1934_; size_t v___x_1935_; lean_object* v___x_1936_; 
v___x_1934_ = ((size_t)0ULL);
v___x_1935_ = lean_usize_of_nat(v___x_1927_);
v___x_1936_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(v_a_1926_, v_a_1924_, v___x_1934_, v___x_1935_, v___x_1928_);
lean_dec(v_a_1924_);
v___y_1887_ = v___y_1913_;
v___y_1888_ = v___y_1915_;
v___y_1889_ = v___y_1917_;
v___y_1890_ = v_a_1926_;
v___y_1891_ = v___y_1920_;
v___y_1892_ = v___x_1936_;
goto v___jp_1886_;
}
}
}
else
{
lean_dec(v_a_1924_);
lean_dec_ref(v___y_1920_);
lean_dec(v___y_1917_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1913_);
return v___x_1925_;
}
}
else
{
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1944_; 
lean_dec_ref(v_a_1921_);
lean_dec_ref(v___y_1920_);
lean_dec(v___y_1917_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1913_);
v_a_1937_ = lean_ctor_get(v___x_1923_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1939_ = v___x_1923_;
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1923_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1942_; 
if (v_isShared_1940_ == 0)
{
v___x_1942_ = v___x_1939_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_a_1937_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
}
else
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1952_; 
lean_dec_ref(v_a_1921_);
lean_dec_ref(v___y_1920_);
lean_dec_ref(v___y_1919_);
lean_dec(v___y_1917_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1913_);
v_a_1945_ = lean_ctor_get(v___x_1922_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1922_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1947_ = v___x_1922_;
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1922_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1950_; 
if (v_isShared_1948_ == 0)
{
v___x_1950_ = v___x_1947_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_a_1945_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
}
v___jp_1953_:
{
if (lean_obj_tag(v___y_1962_) == 0)
{
lean_object* v_a_1963_; 
v_a_1963_ = lean_ctor_get(v___y_1962_, 0);
lean_inc(v_a_1963_);
lean_dec_ref_known(v___y_1962_, 1);
v___y_1913_ = v___y_1954_;
v___y_1914_ = v___y_1955_;
v___y_1915_ = v___y_1956_;
v___y_1916_ = v___y_1958_;
v___y_1917_ = v___y_1957_;
v___y_1918_ = v___y_1960_;
v___y_1919_ = v___y_1959_;
v___y_1920_ = v___y_1961_;
v_a_1921_ = v_a_1963_;
goto v___jp_1912_;
}
else
{
lean_object* v_a_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1971_; 
lean_dec_ref(v___y_1961_);
lean_dec_ref(v___y_1959_);
lean_dec(v___y_1957_);
lean_dec(v___y_1956_);
lean_dec_ref(v___y_1955_);
lean_dec_ref(v___y_1954_);
lean_dec(v_mvarId_1876_);
v_a_1964_ = lean_ctor_get(v___y_1962_, 0);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___y_1962_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1966_ = v___y_1962_;
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_a_1964_);
lean_dec(v___y_1962_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1969_; 
if (v_isShared_1967_ == 0)
{
v___x_1969_ = v___x_1966_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_a_1964_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
return v___x_1969_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___lam__0___boxed(lean_object* v_mvarId_2092_, lean_object* v___x_2093_, lean_object* v_e_2094_, lean_object* v_cfg_2095_, lean_object* v_term_x3f_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_){
_start:
{
lean_object* v_res_2102_; 
v_res_2102_ = l_Lean_MVarId_apply___lam__0(v_mvarId_2092_, v___x_2093_, v_e_2094_, v_cfg_2095_, v_term_x3f_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_);
lean_dec_ref(v_cfg_2095_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply(lean_object* v_mvarId_2103_, lean_object* v_e_2104_, lean_object* v_cfg_2105_, lean_object* v_term_x3f_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_){
_start:
{
lean_object* v___x_2112_; lean_object* v___f_2113_; lean_object* v___x_2114_; 
v___x_2112_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1));
lean_inc(v_mvarId_2103_);
v___f_2113_ = lean_alloc_closure((void*)(l_Lean_MVarId_apply___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2113_, 0, v_mvarId_2103_);
lean_closure_set(v___f_2113_, 1, v___x_2112_);
lean_closure_set(v___f_2113_, 2, v_e_2104_);
lean_closure_set(v___f_2113_, 3, v_cfg_2105_);
lean_closure_set(v___f_2113_, 4, v_term_x3f_2106_);
v___x_2114_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2103_, v___f_2113_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_);
return v___x_2114_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___boxed(lean_object* v_mvarId_2115_, lean_object* v_e_2116_, lean_object* v_cfg_2117_, lean_object* v_term_x3f_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_){
_start:
{
lean_object* v_res_2124_; 
v_res_2124_ = l_Lean_MVarId_apply(v_mvarId_2115_, v_e_2116_, v_cfg_2117_, v_term_x3f_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_);
lean_dec(v_a_2122_);
lean_dec_ref(v_a_2121_);
lean_dec(v_a_2120_);
lean_dec_ref(v_a_2119_);
return v_res_2124_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1(lean_object* v_mvarId_2125_, lean_object* v_val_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
lean_object* v___x_2132_; 
v___x_2132_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2125_, v_val_2126_, v___y_2128_);
return v___x_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___boxed(lean_object* v_mvarId_2133_, lean_object* v_val_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_){
_start:
{
lean_object* v_res_2140_; 
v_res_2140_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1(v_mvarId_2133_, v_val_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_);
lean_dec(v___y_2138_);
lean_dec_ref(v___y_2137_);
lean_dec(v___y_2136_);
lean_dec_ref(v___y_2135_);
return v_res_2140_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5(lean_object* v_as_2141_, size_t v_i_2142_, size_t v_stop_2143_, lean_object* v_b_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_){
_start:
{
lean_object* v___x_2150_; 
v___x_2150_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_as_2141_, v_i_2142_, v_stop_2143_, v_b_2144_, v___y_2146_);
return v___x_2150_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___boxed(lean_object* v_as_2151_, lean_object* v_i_2152_, lean_object* v_stop_2153_, lean_object* v_b_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_){
_start:
{
size_t v_i_boxed_2160_; size_t v_stop_boxed_2161_; lean_object* v_res_2162_; 
v_i_boxed_2160_ = lean_unbox_usize(v_i_2152_);
lean_dec(v_i_2152_);
v_stop_boxed_2161_ = lean_unbox_usize(v_stop_2153_);
lean_dec(v_stop_2153_);
v_res_2162_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5(v_as_2151_, v_i_boxed_2160_, v_stop_boxed_2161_, v_b_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
lean_dec_ref(v_as_2151_);
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1(lean_object* v_00_u03b2_2163_, lean_object* v_x_2164_, lean_object* v_x_2165_, lean_object* v_x_2166_){
_start:
{
lean_object* v___x_2167_; 
v___x_2167_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1___redArg(v_x_2164_, v_x_2165_, v_x_2166_);
return v___x_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_2168_, lean_object* v_x_2169_, size_t v_x_2170_, size_t v_x_2171_, lean_object* v_x_2172_, lean_object* v_x_2173_){
_start:
{
lean_object* v___x_2174_; 
v___x_2174_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_x_2169_, v_x_2170_, v_x_2171_, v_x_2172_, v_x_2173_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2175_, lean_object* v_x_2176_, lean_object* v_x_2177_, lean_object* v_x_2178_, lean_object* v_x_2179_, lean_object* v_x_2180_){
_start:
{
size_t v_x_7810__boxed_2181_; size_t v_x_7811__boxed_2182_; lean_object* v_res_2183_; 
v_x_7810__boxed_2181_ = lean_unbox_usize(v_x_2177_);
lean_dec(v_x_2177_);
v_x_7811__boxed_2182_ = lean_unbox_usize(v_x_2178_);
lean_dec(v_x_2178_);
v_res_2183_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3(v_00_u03b2_2175_, v_x_2176_, v_x_7810__boxed_2181_, v_x_7811__boxed_2182_, v_x_2179_, v_x_2180_);
return v_res_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_2184_, lean_object* v_n_2185_, lean_object* v_k_2186_, lean_object* v_v_2187_){
_start:
{
lean_object* v___x_2188_; 
v___x_2188_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8___redArg(v_n_2185_, v_k_2186_, v_v_2187_);
return v___x_2188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9(lean_object* v_00_u03b2_2189_, size_t v_depth_2190_, lean_object* v_keys_2191_, lean_object* v_vals_2192_, lean_object* v_heq_2193_, lean_object* v_i_2194_, lean_object* v_entries_2195_){
_start:
{
lean_object* v___x_2196_; 
v___x_2196_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(v_depth_2190_, v_keys_2191_, v_vals_2192_, v_i_2194_, v_entries_2195_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___boxed(lean_object* v_00_u03b2_2197_, lean_object* v_depth_2198_, lean_object* v_keys_2199_, lean_object* v_vals_2200_, lean_object* v_heq_2201_, lean_object* v_i_2202_, lean_object* v_entries_2203_){
_start:
{
size_t v_depth_boxed_2204_; lean_object* v_res_2205_; 
v_depth_boxed_2204_ = lean_unbox_usize(v_depth_2198_);
lean_dec(v_depth_2198_);
v_res_2205_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9(v_00_u03b2_2197_, v_depth_boxed_2204_, v_keys_2199_, v_vals_2200_, v_heq_2201_, v_i_2202_, v_entries_2203_);
lean_dec_ref(v_vals_2200_);
lean_dec_ref(v_keys_2199_);
return v_res_2205_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9(lean_object* v_00_u03b2_2206_, lean_object* v_x_2207_, lean_object* v_x_2208_, lean_object* v_x_2209_, lean_object* v_x_2210_){
_start:
{
lean_object* v___x_2211_; 
v___x_2211_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9___redArg(v_x_2207_, v_x_2208_, v_x_2209_, v_x_2210_);
return v___x_2211_;
}
}
static lean_object* _init_l_Lean_MVarId_applyConst___closed__1(void){
_start:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2213_ = ((lean_object*)(l_Lean_MVarId_applyConst___closed__0));
v___x_2214_ = l_Lean_stringToMessageData(v___x_2213_);
return v___x_2214_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyConst(lean_object* v_mvar_2215_, lean_object* v_c_2216_, lean_object* v_cfg_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_){
_start:
{
lean_object* v___x_2223_; 
lean_inc(v_c_2216_);
v___x_2223_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_c_2216_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
if (lean_obj_tag(v___x_2223_) == 0)
{
lean_object* v_a_2224_; lean_object* v___x_2225_; uint8_t v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; 
v_a_2224_ = lean_ctor_get(v___x_2223_, 0);
lean_inc(v_a_2224_);
lean_dec_ref_known(v___x_2223_, 1);
v___x_2225_ = lean_obj_once(&l_Lean_MVarId_applyConst___closed__1, &l_Lean_MVarId_applyConst___closed__1_once, _init_l_Lean_MVarId_applyConst___closed__1);
v___x_2226_ = 0;
v___x_2227_ = l_Lean_MessageData_ofConstName(v_c_2216_, v___x_2226_);
v___x_2228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2225_);
lean_ctor_set(v___x_2228_, 1, v___x_2227_);
v___x_2229_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2229_, 0, v___x_2228_);
lean_ctor_set(v___x_2229_, 1, v___x_2225_);
v___x_2230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2229_);
v___x_2231_ = l_Lean_MVarId_apply(v_mvar_2215_, v_a_2224_, v_cfg_2217_, v___x_2230_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
return v___x_2231_;
}
else
{
lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2239_; 
lean_dec_ref(v_cfg_2217_);
lean_dec(v_c_2216_);
lean_dec(v_mvar_2215_);
v_a_2232_ = lean_ctor_get(v___x_2223_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2223_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2234_ = v___x_2223_;
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___x_2223_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2237_; 
if (v_isShared_2235_ == 0)
{
v___x_2237_ = v___x_2234_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_a_2232_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyConst___boxed(lean_object* v_mvar_2240_, lean_object* v_c_2241_, lean_object* v_cfg_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_){
_start:
{
lean_object* v_res_2248_; 
v_res_2248_ = l_Lean_MVarId_applyConst(v_mvar_2240_, v_c_2241_, v_cfg_2242_, v_a_2243_, v_a_2244_, v_a_2245_, v_a_2246_);
lean_dec(v_a_2246_);
lean_dec_ref(v_a_2245_);
lean_dec(v_a_2244_);
lean_dec_ref(v_a_2243_);
return v_res_2248_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1(lean_object* v_msgData_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_){
_start:
{
lean_object* v___x_2255_; lean_object* v_env_2256_; lean_object* v___x_2257_; lean_object* v_toCold_2258_; lean_object* v_mctx_2259_; lean_object* v_lctx_2260_; lean_object* v_options_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; 
v___x_2255_ = lean_st_ref_get(v___y_2253_);
v_env_2256_ = lean_ctor_get(v___x_2255_, 0);
lean_inc_ref(v_env_2256_);
lean_dec(v___x_2255_);
v___x_2257_ = lean_st_ref_get(v___y_2251_);
v_toCold_2258_ = lean_ctor_get(v___y_2252_, 0);
v_mctx_2259_ = lean_ctor_get(v___x_2257_, 0);
lean_inc_ref(v_mctx_2259_);
lean_dec(v___x_2257_);
v_lctx_2260_ = lean_ctor_get(v___y_2250_, 2);
v_options_2261_ = lean_ctor_get(v_toCold_2258_, 2);
lean_inc_ref(v_options_2261_);
lean_inc_ref(v_lctx_2260_);
v___x_2262_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2262_, 0, v_env_2256_);
lean_ctor_set(v___x_2262_, 1, v_mctx_2259_);
lean_ctor_set(v___x_2262_, 2, v_lctx_2260_);
lean_ctor_set(v___x_2262_, 3, v_options_2261_);
v___x_2263_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2262_);
lean_ctor_set(v___x_2263_, 1, v_msgData_2249_);
v___x_2264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2263_);
return v___x_2264_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1___boxed(lean_object* v_msgData_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_){
_start:
{
lean_object* v_res_2271_; 
v_res_2271_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1(v_msgData_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
return v_res_2271_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(lean_object* v_msg_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_){
_start:
{
lean_object* v_ref_2278_; lean_object* v___x_2279_; lean_object* v_a_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2288_; 
v_ref_2278_ = lean_ctor_get(v___y_2275_, 2);
v___x_2279_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1(v_msg_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
v_a_2280_ = lean_ctor_get(v___x_2279_, 0);
v_isSharedCheck_2288_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2282_ = v___x_2279_;
v_isShared_2283_ = v_isSharedCheck_2288_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_a_2280_);
lean_dec(v___x_2279_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2288_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v___x_2284_; lean_object* v___x_2286_; 
lean_inc(v_ref_2278_);
v___x_2284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2284_, 0, v_ref_2278_);
lean_ctor_set(v___x_2284_, 1, v_a_2280_);
if (v_isShared_2283_ == 0)
{
lean_ctor_set_tag(v___x_2282_, 1);
lean_ctor_set(v___x_2282_, 0, v___x_2284_);
v___x_2286_ = v___x_2282_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v___x_2284_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
return v___x_2286_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg___boxed(lean_object* v_msg_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_){
_start:
{
lean_object* v_res_2295_; 
v_res_2295_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v_msg_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_);
lean_dec(v___y_2293_);
lean_dec_ref(v___y_2292_);
lean_dec(v___y_2291_);
lean_dec_ref(v___y_2290_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0(size_t v_sz_2296_, size_t v_i_2297_, lean_object* v_bs_2298_){
_start:
{
uint8_t v___x_2299_; 
v___x_2299_ = lean_usize_dec_lt(v_i_2297_, v_sz_2296_);
if (v___x_2299_ == 0)
{
return v_bs_2298_;
}
else
{
lean_object* v_v_2300_; lean_object* v___x_2301_; lean_object* v_bs_x27_2302_; lean_object* v___x_2303_; size_t v___x_2304_; size_t v___x_2305_; lean_object* v___x_2306_; 
v_v_2300_ = lean_array_uget(v_bs_2298_, v_i_2297_);
v___x_2301_ = lean_unsigned_to_nat(0u);
v_bs_x27_2302_ = lean_array_uset(v_bs_2298_, v_i_2297_, v___x_2301_);
v___x_2303_ = l_Lean_Expr_mvarId_x21(v_v_2300_);
lean_dec(v_v_2300_);
v___x_2304_ = ((size_t)1ULL);
v___x_2305_ = lean_usize_add(v_i_2297_, v___x_2304_);
v___x_2306_ = lean_array_uset(v_bs_x27_2302_, v_i_2297_, v___x_2303_);
v_i_2297_ = v___x_2305_;
v_bs_2298_ = v___x_2306_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0___boxed(lean_object* v_sz_2308_, lean_object* v_i_2309_, lean_object* v_bs_2310_){
_start:
{
size_t v_sz_boxed_2311_; size_t v_i_boxed_2312_; lean_object* v_res_2313_; 
v_sz_boxed_2311_ = lean_unbox_usize(v_sz_2308_);
lean_dec(v_sz_2308_);
v_i_boxed_2312_ = lean_unbox_usize(v_i_2309_);
lean_dec(v_i_2309_);
v_res_2313_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0(v_sz_boxed_2311_, v_i_boxed_2312_, v_bs_2310_);
return v_res_2313_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2315_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__0));
v___x_2316_ = l_Lean_stringToMessageData(v___x_2315_);
return v___x_2316_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2318_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__2));
v___x_2319_ = l_Lean_stringToMessageData(v___x_2318_);
return v___x_2319_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2321_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__4));
v___x_2322_ = l_Lean_stringToMessageData(v___x_2321_);
return v___x_2322_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__7(void){
_start:
{
lean_object* v___x_2324_; lean_object* v___x_2325_; 
v___x_2324_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__6));
v___x_2325_ = l_Lean_stringToMessageData(v___x_2324_);
return v___x_2325_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__9(void){
_start:
{
lean_object* v___x_2327_; lean_object* v___x_2328_; 
v___x_2327_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__8));
v___x_2328_ = l_Lean_stringToMessageData(v___x_2327_);
return v___x_2328_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__11(void){
_start:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; 
v___x_2330_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__10));
v___x_2331_ = l_Lean_stringToMessageData(v___x_2330_);
return v___x_2331_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN___lam__0(lean_object* v_mvarId_2332_, lean_object* v___x_2333_, lean_object* v_e_2334_, lean_object* v_n_2335_, uint8_t v_useApproxDefEq_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_){
_start:
{
lean_object* v___x_2342_; 
lean_inc(v_mvarId_2332_);
v___x_2342_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2332_, v___x_2333_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_object* v___x_2343_; 
lean_dec_ref_known(v___x_2342_, 1);
lean_inc(v_mvarId_2332_);
v___x_2343_ = l_Lean_MVarId_getType(v_mvarId_2332_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
if (lean_obj_tag(v___x_2343_) == 0)
{
lean_object* v_a_2344_; lean_object* v___x_2345_; 
v_a_2344_ = lean_ctor_get(v___x_2343_, 0);
lean_inc(v_a_2344_);
lean_dec_ref_known(v___x_2343_, 1);
lean_inc(v___y_2340_);
lean_inc_ref(v___y_2339_);
lean_inc(v___y_2338_);
lean_inc_ref(v___y_2337_);
lean_inc_ref(v_e_2334_);
v___x_2345_ = lean_infer_type(v_e_2334_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_object* v_a_2346_; uint8_t v___x_2347_; lean_object* v___x_2348_; 
v_a_2346_ = lean_ctor_get(v___x_2345_, 0);
lean_inc(v_a_2346_);
lean_dec_ref_known(v___x_2345_, 1);
v___x_2347_ = 0;
lean_inc(v_n_2335_);
v___x_2348_ = l_Lean_Meta_forallMetaBoundedTelescope(v_a_2346_, v_n_2335_, v___x_2347_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v_a_2349_; lean_object* v_fst_2350_; lean_object* v_snd_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2441_; 
v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
lean_inc(v_a_2349_);
lean_dec_ref_known(v___x_2348_, 1);
v_fst_2350_ = lean_ctor_get(v_a_2349_, 0);
v_snd_2351_ = lean_ctor_get(v_a_2349_, 1);
v_isSharedCheck_2441_ = !lean_is_exclusive(v_a_2349_);
if (v_isSharedCheck_2441_ == 0)
{
v___x_2353_ = v_a_2349_;
v_isShared_2354_ = v_isSharedCheck_2441_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_snd_2351_);
lean_inc(v_fst_2350_);
lean_dec(v_a_2349_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2441_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___y_2356_; lean_object* v_snd_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2439_; 
v_snd_2371_ = lean_ctor_get(v_snd_2351_, 1);
v_isSharedCheck_2439_ = !lean_is_exclusive(v_snd_2351_);
if (v_isSharedCheck_2439_ == 0)
{
lean_object* v_unused_2440_; 
v_unused_2440_ = lean_ctor_get(v_snd_2351_, 0);
lean_dec(v_unused_2440_);
v___x_2373_ = v_snd_2351_;
v_isShared_2374_ = v_isSharedCheck_2439_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_snd_2371_);
lean_dec(v_snd_2351_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2439_;
goto v_resetjp_2372_;
}
v___jp_2355_:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2369_; 
lean_inc(v_fst_2350_);
v___x_2357_ = l_Lean_Expr_beta(v_e_2334_, v_fst_2350_);
v___x_2358_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2332_, v___x_2357_, v___y_2356_);
lean_dec(v___y_2356_);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2358_);
if (v_isSharedCheck_2369_ == 0)
{
lean_object* v_unused_2370_; 
v_unused_2370_ = lean_ctor_get(v___x_2358_, 0);
lean_dec(v_unused_2370_);
v___x_2360_ = v___x_2358_;
v_isShared_2361_ = v_isSharedCheck_2369_;
goto v_resetjp_2359_;
}
else
{
lean_dec(v___x_2358_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2369_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
size_t v_sz_2362_; size_t v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2367_; 
v_sz_2362_ = lean_array_size(v_fst_2350_);
v___x_2363_ = ((size_t)0ULL);
v___x_2364_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0(v_sz_2362_, v___x_2363_, v_fst_2350_);
v___x_2365_ = lean_array_to_list(v___x_2364_);
if (v_isShared_2361_ == 0)
{
lean_ctor_set(v___x_2360_, 0, v___x_2365_);
v___x_2367_ = v___x_2360_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v___x_2365_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
}
}
}
v_resetjp_2372_:
{
lean_object* v___y_2376_; lean_object* v___y_2377_; lean_object* v___y_2378_; lean_object* v___y_2379_; lean_object* v___x_2419_; uint8_t v___x_2420_; 
v___x_2419_ = lean_array_get_size(v_fst_2350_);
v___x_2420_ = lean_nat_dec_eq(v___x_2419_, v_n_2335_);
if (v___x_2420_ == 0)
{
lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v_a_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2438_; 
lean_del_object(v___x_2373_);
lean_del_object(v___x_2353_);
lean_dec(v_fst_2350_);
lean_dec(v_a_2344_);
lean_dec_ref(v_e_2334_);
lean_dec(v_mvarId_2332_);
v___x_2421_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__9, &l_Lean_MVarId_applyN___lam__0___closed__9_once, _init_l_Lean_MVarId_applyN___lam__0___closed__9);
v___x_2422_ = l_Nat_reprFast(v_n_2335_);
v___x_2423_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2422_);
v___x_2424_ = l_Lean_MessageData_ofFormat(v___x_2423_);
v___x_2425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2421_);
lean_ctor_set(v___x_2425_, 1, v___x_2424_);
v___x_2426_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__11, &l_Lean_MVarId_applyN___lam__0___closed__11_once, _init_l_Lean_MVarId_applyN___lam__0___closed__11);
v___x_2427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2427_, 0, v___x_2425_);
lean_ctor_set(v___x_2427_, 1, v___x_2426_);
v___x_2428_ = l_Lean_indentExpr(v_snd_2371_);
v___x_2429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2429_, 0, v___x_2427_);
lean_ctor_set(v___x_2429_, 1, v___x_2428_);
v___x_2430_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_2429_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
lean_dec(v___y_2340_);
lean_dec_ref(v___y_2339_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2337_);
v_a_2431_ = lean_ctor_get(v___x_2430_, 0);
v_isSharedCheck_2438_ = !lean_is_exclusive(v___x_2430_);
if (v_isSharedCheck_2438_ == 0)
{
v___x_2433_ = v___x_2430_;
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_a_2431_);
lean_dec(v___x_2430_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
lean_object* v___x_2436_; 
if (v_isShared_2434_ == 0)
{
v___x_2436_ = v___x_2433_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v_a_2431_);
v___x_2436_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
return v___x_2436_;
}
}
}
else
{
v___y_2376_ = v___y_2337_;
v___y_2377_ = v___y_2338_;
v___y_2378_ = v___y_2339_;
v___y_2379_ = v___y_2340_;
goto v___jp_2375_;
}
v___jp_2375_:
{
lean_object* v___x_2380_; 
lean_inc(v_a_2344_);
lean_inc(v_snd_2371_);
v___x_2380_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(v_useApproxDefEq_2336_, v_snd_2371_, v_a_2344_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_);
if (lean_obj_tag(v___x_2380_) == 0)
{
lean_object* v_a_2381_; uint8_t v___x_2382_; 
v_a_2381_ = lean_ctor_get(v___x_2380_, 0);
lean_inc(v_a_2381_);
lean_dec_ref_known(v___x_2380_, 1);
v___x_2382_ = lean_unbox(v_a_2381_);
lean_dec(v_a_2381_);
if (v___x_2382_ == 0)
{
lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2386_; 
lean_dec(v_fst_2350_);
lean_dec_ref(v_e_2334_);
lean_dec(v_mvarId_2332_);
v___x_2383_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__1, &l_Lean_MVarId_applyN___lam__0___closed__1_once, _init_l_Lean_MVarId_applyN___lam__0___closed__1);
v___x_2384_ = l_Lean_indentExpr(v_a_2344_);
if (v_isShared_2374_ == 0)
{
lean_ctor_set_tag(v___x_2373_, 7);
lean_ctor_set(v___x_2373_, 1, v___x_2384_);
lean_ctor_set(v___x_2373_, 0, v___x_2383_);
v___x_2386_ = v___x_2373_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v___x_2383_);
lean_ctor_set(v_reuseFailAlloc_2410_, 1, v___x_2384_);
v___x_2386_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
lean_object* v___x_2387_; lean_object* v___x_2389_; 
v___x_2387_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__3, &l_Lean_MVarId_applyN___lam__0___closed__3_once, _init_l_Lean_MVarId_applyN___lam__0___closed__3);
if (v_isShared_2354_ == 0)
{
lean_ctor_set_tag(v___x_2353_, 7);
lean_ctor_set(v___x_2353_, 1, v___x_2387_);
lean_ctor_set(v___x_2353_, 0, v___x_2386_);
v___x_2389_ = v___x_2353_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v___x_2386_);
lean_ctor_set(v_reuseFailAlloc_2409_, 1, v___x_2387_);
v___x_2389_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v_a_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2408_; 
v___x_2390_ = l_Lean_indentExpr(v_snd_2371_);
v___x_2391_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2389_);
lean_ctor_set(v___x_2391_, 1, v___x_2390_);
v___x_2392_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__5, &l_Lean_MVarId_applyN___lam__0___closed__5_once, _init_l_Lean_MVarId_applyN___lam__0___closed__5);
v___x_2393_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2391_);
lean_ctor_set(v___x_2393_, 1, v___x_2392_);
v___x_2394_ = l_Nat_reprFast(v_n_2335_);
v___x_2395_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2395_, 0, v___x_2394_);
v___x_2396_ = l_Lean_MessageData_ofFormat(v___x_2395_);
v___x_2397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2397_, 0, v___x_2393_);
lean_ctor_set(v___x_2397_, 1, v___x_2396_);
v___x_2398_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__7, &l_Lean_MVarId_applyN___lam__0___closed__7_once, _init_l_Lean_MVarId_applyN___lam__0___closed__7);
v___x_2399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2397_);
lean_ctor_set(v___x_2399_, 1, v___x_2398_);
v___x_2400_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_2399_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
v_a_2401_ = lean_ctor_get(v___x_2400_, 0);
v_isSharedCheck_2408_ = !lean_is_exclusive(v___x_2400_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2403_ = v___x_2400_;
v_isShared_2404_ = v_isSharedCheck_2408_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_a_2401_);
lean_dec(v___x_2400_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2408_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v___x_2406_; 
if (v_isShared_2404_ == 0)
{
v___x_2406_ = v___x_2403_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v_a_2401_);
v___x_2406_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
return v___x_2406_;
}
}
}
}
}
else
{
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
lean_dec_ref(v___y_2376_);
lean_del_object(v___x_2373_);
lean_dec(v_snd_2371_);
lean_del_object(v___x_2353_);
lean_dec(v_a_2344_);
lean_dec(v_n_2335_);
v___y_2356_ = v___y_2377_;
goto v___jp_2355_;
}
}
else
{
lean_object* v_a_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2418_; 
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
lean_del_object(v___x_2373_);
lean_dec(v_snd_2371_);
lean_del_object(v___x_2353_);
lean_dec(v_fst_2350_);
lean_dec(v_a_2344_);
lean_dec(v_n_2335_);
lean_dec_ref(v_e_2334_);
lean_dec(v_mvarId_2332_);
v_a_2411_ = lean_ctor_get(v___x_2380_, 0);
v_isSharedCheck_2418_ = !lean_is_exclusive(v___x_2380_);
if (v_isSharedCheck_2418_ == 0)
{
v___x_2413_ = v___x_2380_;
v_isShared_2414_ = v_isSharedCheck_2418_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_a_2411_);
lean_dec(v___x_2380_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2418_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2416_; 
if (v_isShared_2414_ == 0)
{
v___x_2416_ = v___x_2413_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v_a_2411_);
v___x_2416_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
return v___x_2416_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2449_; 
lean_dec(v_a_2344_);
lean_dec(v___y_2340_);
lean_dec_ref(v___y_2339_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2337_);
lean_dec(v_n_2335_);
lean_dec_ref(v_e_2334_);
lean_dec(v_mvarId_2332_);
v_a_2442_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2449_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2444_ = v___x_2348_;
v_isShared_2445_ = v_isSharedCheck_2449_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_a_2442_);
lean_dec(v___x_2348_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2449_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
lean_object* v___x_2447_; 
if (v_isShared_2445_ == 0)
{
v___x_2447_ = v___x_2444_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v_a_2442_);
v___x_2447_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
return v___x_2447_;
}
}
}
}
else
{
lean_object* v_a_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2457_; 
lean_dec(v_a_2344_);
lean_dec(v___y_2340_);
lean_dec_ref(v___y_2339_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2337_);
lean_dec(v_n_2335_);
lean_dec_ref(v_e_2334_);
lean_dec(v_mvarId_2332_);
v_a_2450_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2457_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2452_ = v___x_2345_;
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_a_2450_);
lean_dec(v___x_2345_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___x_2455_; 
if (v_isShared_2453_ == 0)
{
v___x_2455_ = v___x_2452_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_a_2450_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
}
}
else
{
lean_object* v_a_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2465_; 
lean_dec(v___y_2340_);
lean_dec_ref(v___y_2339_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2337_);
lean_dec(v_n_2335_);
lean_dec_ref(v_e_2334_);
lean_dec(v_mvarId_2332_);
v_a_2458_ = lean_ctor_get(v___x_2343_, 0);
v_isSharedCheck_2465_ = !lean_is_exclusive(v___x_2343_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2460_ = v___x_2343_;
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_a_2458_);
lean_dec(v___x_2343_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___x_2463_; 
if (v_isShared_2461_ == 0)
{
v___x_2463_ = v___x_2460_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v_a_2458_);
v___x_2463_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
return v___x_2463_;
}
}
}
}
else
{
lean_object* v_a_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2473_; 
lean_dec(v___y_2340_);
lean_dec_ref(v___y_2339_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2337_);
lean_dec(v_n_2335_);
lean_dec_ref(v_e_2334_);
lean_dec(v_mvarId_2332_);
v_a_2466_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2468_ = v___x_2342_;
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_a_2466_);
lean_dec(v___x_2342_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v___x_2471_; 
if (v_isShared_2469_ == 0)
{
v___x_2471_ = v___x_2468_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_a_2466_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN___lam__0___boxed(lean_object* v_mvarId_2474_, lean_object* v___x_2475_, lean_object* v_e_2476_, lean_object* v_n_2477_, lean_object* v_useApproxDefEq_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_){
_start:
{
uint8_t v_useApproxDefEq_boxed_2484_; lean_object* v_res_2485_; 
v_useApproxDefEq_boxed_2484_ = lean_unbox(v_useApproxDefEq_2478_);
v_res_2485_ = l_Lean_MVarId_applyN___lam__0(v_mvarId_2474_, v___x_2475_, v_e_2476_, v_n_2477_, v_useApproxDefEq_boxed_2484_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
return v_res_2485_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN(lean_object* v_mvarId_2486_, lean_object* v_e_2487_, lean_object* v_n_2488_, uint8_t v_useApproxDefEq_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_){
_start:
{
lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___f_2497_; lean_object* v___x_2498_; 
v___x_2495_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1));
v___x_2496_ = lean_box(v_useApproxDefEq_2489_);
lean_inc(v_mvarId_2486_);
v___f_2497_ = lean_alloc_closure((void*)(l_Lean_MVarId_applyN___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2497_, 0, v_mvarId_2486_);
lean_closure_set(v___f_2497_, 1, v___x_2495_);
lean_closure_set(v___f_2497_, 2, v_e_2487_);
lean_closure_set(v___f_2497_, 3, v_n_2488_);
lean_closure_set(v___f_2497_, 4, v___x_2496_);
v___x_2498_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2486_, v___f_2497_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_);
return v___x_2498_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN___boxed(lean_object* v_mvarId_2499_, lean_object* v_e_2500_, lean_object* v_n_2501_, lean_object* v_useApproxDefEq_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_){
_start:
{
uint8_t v_useApproxDefEq_boxed_2508_; lean_object* v_res_2509_; 
v_useApproxDefEq_boxed_2508_ = lean_unbox(v_useApproxDefEq_2502_);
v_res_2509_ = l_Lean_MVarId_applyN(v_mvarId_2499_, v_e_2500_, v_n_2501_, v_useApproxDefEq_boxed_2508_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_);
lean_dec(v_a_2506_);
lean_dec_ref(v_a_2505_);
lean_dec(v_a_2504_);
lean_dec_ref(v_a_2503_);
return v_res_2509_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1(lean_object* v_00_u03b1_2510_, lean_object* v_msg_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_){
_start:
{
lean_object* v___x_2517_; 
v___x_2517_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v_msg_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_);
return v___x_2517_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___boxed(lean_object* v_00_u03b1_2518_, lean_object* v_msg_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_){
_start:
{
lean_object* v_res_2525_; 
v_res_2525_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1(v_00_u03b1_2518_, v_msg_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
lean_dec(v___y_2523_);
lean_dec_ref(v___y_2522_);
lean_dec(v___y_2521_);
lean_dec_ref(v___y_2520_);
return v_res_2525_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6(void){
_start:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; 
v___x_2536_ = lean_box(0);
v___x_2537_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__5));
v___x_2538_ = l_Lean_mkConst(v___x_2537_, v___x_2536_);
return v___x_2538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(lean_object* v_tag_2539_, lean_object* v_type_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_){
_start:
{
lean_object* v___x_2547_; 
lean_inc(v_a_2545_);
lean_inc_ref(v_a_2544_);
lean_inc(v_a_2543_);
lean_inc_ref(v_a_2542_);
v___x_2547_ = lean_whnf(v_type_2540_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_);
if (lean_obj_tag(v___x_2547_) == 0)
{
lean_object* v_a_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; uint8_t v___x_2551_; 
v_a_2548_ = lean_ctor_get(v___x_2547_, 0);
lean_inc(v_a_2548_);
lean_dec_ref_known(v___x_2547_, 1);
v___x_2549_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__1));
v___x_2550_ = lean_unsigned_to_nat(2u);
v___x_2551_ = l_Lean_Expr_isAppOfArity(v_a_2548_, v___x_2549_, v___x_2550_);
if (v___x_2551_ == 0)
{
lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2552_ = lean_st_ref_get(v_a_2541_);
v___x_2553_ = lean_array_get_size(v___x_2552_);
lean_dec(v___x_2552_);
v___x_2554_ = lean_unsigned_to_nat(1u);
v___x_2555_ = lean_nat_add(v___x_2553_, v___x_2554_);
v___x_2556_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__3));
v___x_2557_ = lean_name_append_index_after(v___x_2556_, v___x_2555_);
v___x_2558_ = l_Lean_Name_append(v_tag_2539_, v___x_2557_);
v___x_2559_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_2548_, v___x_2558_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_object* v_a_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2571_; 
v_a_2560_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2571_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2562_ = v___x_2559_;
v_isShared_2563_ = v_isSharedCheck_2571_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_dec(v___x_2559_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2571_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2569_; 
v___x_2564_ = lean_st_ref_take(v_a_2541_);
v___x_2565_ = l_Lean_Expr_mvarId_x21(v_a_2560_);
v___x_2566_ = lean_array_push(v___x_2564_, v___x_2565_);
v___x_2567_ = lean_st_ref_put(v_a_2541_, v___x_2566_);
if (v_isShared_2563_ == 0)
{
v___x_2569_ = v___x_2562_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v_a_2560_);
v___x_2569_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
return v___x_2569_;
}
}
}
else
{
return v___x_2559_;
}
}
else
{
lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2572_ = l_Lean_Expr_appFn_x21(v_a_2548_);
v___x_2573_ = l_Lean_Expr_appArg_x21(v___x_2572_);
lean_dec_ref(v___x_2572_);
lean_inc_ref(v___x_2573_);
lean_inc(v_tag_2539_);
v___x_2574_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_tag_2539_, v___x_2573_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_);
if (lean_obj_tag(v___x_2574_) == 0)
{
lean_object* v_a_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
v_a_2575_ = lean_ctor_get(v___x_2574_, 0);
lean_inc(v_a_2575_);
lean_dec_ref_known(v___x_2574_, 1);
v___x_2576_ = l_Lean_Expr_appArg_x21(v_a_2548_);
lean_dec(v_a_2548_);
lean_inc_ref(v___x_2576_);
v___x_2577_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_tag_2539_, v___x_2576_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_);
if (lean_obj_tag(v___x_2577_) == 0)
{
lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2587_; 
v_a_2578_ = lean_ctor_get(v___x_2577_, 0);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2580_ = v___x_2577_;
v_isShared_2581_ = v_isSharedCheck_2587_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v___x_2577_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2587_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2585_; 
v___x_2582_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6, &l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6);
v___x_2583_ = l_Lean_mkApp4(v___x_2582_, v___x_2573_, v___x_2576_, v_a_2575_, v_a_2578_);
if (v_isShared_2581_ == 0)
{
lean_ctor_set(v___x_2580_, 0, v___x_2583_);
v___x_2585_ = v___x_2580_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v___x_2583_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
}
else
{
lean_dec_ref(v___x_2576_);
lean_dec(v_a_2575_);
lean_dec_ref(v___x_2573_);
return v___x_2577_;
}
}
else
{
lean_dec_ref(v___x_2573_);
lean_dec(v_a_2548_);
lean_dec(v_tag_2539_);
return v___x_2574_;
}
}
}
else
{
lean_dec(v_tag_2539_);
return v___x_2547_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___boxed(lean_object* v_tag_2588_, lean_object* v_type_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_){
_start:
{
lean_object* v_res_2596_; 
v_res_2596_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_tag_2588_, v_type_2589_, v_a_2590_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_);
lean_dec(v_a_2594_);
lean_dec_ref(v_a_2593_);
lean_dec(v_a_2592_);
lean_dec_ref(v_a_2591_);
lean_dec(v_a_2590_);
return v_res_2596_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore___lam__0(lean_object* v_mvarId_2597_, lean_object* v___x_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_){
_start:
{
lean_object* v___x_2604_; 
lean_inc(v_mvarId_2597_);
v___x_2604_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2597_, v___x_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
if (lean_obj_tag(v___x_2604_) == 0)
{
lean_object* v___x_2605_; 
lean_dec_ref_known(v___x_2604_, 1);
lean_inc(v_mvarId_2597_);
v___x_2605_ = l_Lean_MVarId_getType_x27(v_mvarId_2597_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
if (lean_obj_tag(v___x_2605_) == 0)
{
lean_object* v_a_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2651_; 
v_a_2606_ = lean_ctor_get(v___x_2605_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2605_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2608_ = v___x_2605_;
v_isShared_2609_ = v_isSharedCheck_2651_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_dec(v___x_2605_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2651_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___x_2610_; lean_object* v___x_2611_; uint8_t v___x_2612_; 
v___x_2610_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__1));
v___x_2611_ = lean_unsigned_to_nat(2u);
v___x_2612_ = l_Lean_Expr_isAppOfArity(v_a_2606_, v___x_2610_, v___x_2611_);
if (v___x_2612_ == 0)
{
lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2616_; 
lean_dec(v_a_2606_);
v___x_2613_ = lean_box(0);
v___x_2614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2614_, 0, v_mvarId_2597_);
lean_ctor_set(v___x_2614_, 1, v___x_2613_);
if (v_isShared_2609_ == 0)
{
lean_ctor_set(v___x_2608_, 0, v___x_2614_);
v___x_2616_ = v___x_2608_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v___x_2614_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
else
{
lean_object* v___x_2618_; 
lean_del_object(v___x_2608_);
lean_inc(v_mvarId_2597_);
v___x_2618_ = l_Lean_MVarId_getTag(v_mvarId_2597_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
if (lean_obj_tag(v___x_2618_) == 0)
{
lean_object* v_a_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; 
v_a_2619_ = lean_ctor_get(v___x_2618_, 0);
lean_inc(v_a_2619_);
lean_dec_ref_known(v___x_2618_, 1);
v___x_2620_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__0));
v___x_2621_ = lean_st_mk_ref(v___x_2620_);
v___x_2622_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_a_2619_, v_a_2606_, v___x_2621_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
if (lean_obj_tag(v___x_2622_) == 0)
{
lean_object* v_a_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2633_; 
v_a_2623_ = lean_ctor_get(v___x_2622_, 0);
lean_inc(v_a_2623_);
lean_dec_ref_known(v___x_2622_, 1);
v___x_2624_ = lean_st_ref_get(v___x_2621_);
lean_dec(v___x_2621_);
v___x_2625_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2597_, v_a_2623_, v___y_2600_);
v_isSharedCheck_2633_ = !lean_is_exclusive(v___x_2625_);
if (v_isSharedCheck_2633_ == 0)
{
lean_object* v_unused_2634_; 
v_unused_2634_ = lean_ctor_get(v___x_2625_, 0);
lean_dec(v_unused_2634_);
v___x_2627_ = v___x_2625_;
v_isShared_2628_ = v_isSharedCheck_2633_;
goto v_resetjp_2626_;
}
else
{
lean_dec(v___x_2625_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2633_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2629_; lean_object* v___x_2631_; 
v___x_2629_ = lean_array_to_list(v___x_2624_);
if (v_isShared_2628_ == 0)
{
lean_ctor_set(v___x_2627_, 0, v___x_2629_);
v___x_2631_ = v___x_2627_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v___x_2629_);
v___x_2631_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
return v___x_2631_;
}
}
}
else
{
lean_object* v_a_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2642_; 
lean_dec(v___x_2621_);
lean_dec(v_mvarId_2597_);
v_a_2635_ = lean_ctor_get(v___x_2622_, 0);
v_isSharedCheck_2642_ = !lean_is_exclusive(v___x_2622_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2637_ = v___x_2622_;
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_a_2635_);
lean_dec(v___x_2622_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v___x_2640_; 
if (v_isShared_2638_ == 0)
{
v___x_2640_ = v___x_2637_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_a_2635_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
return v___x_2640_;
}
}
}
}
else
{
lean_object* v_a_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2650_; 
lean_dec(v_a_2606_);
lean_dec(v_mvarId_2597_);
v_a_2643_ = lean_ctor_get(v___x_2618_, 0);
v_isSharedCheck_2650_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2645_ = v___x_2618_;
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_a_2643_);
lean_dec(v___x_2618_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v___x_2648_; 
if (v_isShared_2646_ == 0)
{
v___x_2648_ = v___x_2645_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_a_2643_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
}
}
}
}
}
}
else
{
lean_object* v_a_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2659_; 
lean_dec(v_mvarId_2597_);
v_a_2652_ = lean_ctor_get(v___x_2605_, 0);
v_isSharedCheck_2659_ = !lean_is_exclusive(v___x_2605_);
if (v_isSharedCheck_2659_ == 0)
{
v___x_2654_ = v___x_2605_;
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_a_2652_);
lean_dec(v___x_2605_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2657_; 
if (v_isShared_2655_ == 0)
{
v___x_2657_ = v___x_2654_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v_a_2652_);
v___x_2657_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
return v___x_2657_;
}
}
}
}
else
{
lean_object* v_a_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2667_; 
lean_dec(v_mvarId_2597_);
v_a_2660_ = lean_ctor_get(v___x_2604_, 0);
v_isSharedCheck_2667_ = !lean_is_exclusive(v___x_2604_);
if (v_isSharedCheck_2667_ == 0)
{
v___x_2662_ = v___x_2604_;
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_a_2660_);
lean_dec(v___x_2604_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
lean_object* v___x_2665_; 
if (v_isShared_2663_ == 0)
{
v___x_2665_ = v___x_2662_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v_a_2660_);
v___x_2665_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
return v___x_2665_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore___lam__0___boxed(lean_object* v_mvarId_2668_, lean_object* v___x_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_){
_start:
{
lean_object* v_res_2675_; 
v_res_2675_ = l_Lean_MVarId_splitAndCore___lam__0(v_mvarId_2668_, v___x_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_);
lean_dec(v___y_2673_);
lean_dec_ref(v___y_2672_);
lean_dec(v___y_2671_);
lean_dec_ref(v___y_2670_);
return v_res_2675_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore(lean_object* v_mvarId_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_){
_start:
{
lean_object* v___x_2685_; lean_object* v___f_2686_; lean_object* v___x_2687_; 
v___x_2685_ = ((lean_object*)(l_Lean_MVarId_splitAndCore___closed__1));
lean_inc(v_mvarId_2679_);
v___f_2686_ = lean_alloc_closure((void*)(l_Lean_MVarId_splitAndCore___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2686_, 0, v_mvarId_2679_);
lean_closure_set(v___f_2686_, 1, v___x_2685_);
v___x_2687_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2679_, v___f_2686_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_);
return v___x_2687_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore___boxed(lean_object* v_mvarId_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_){
_start:
{
lean_object* v_res_2694_; 
v_res_2694_ = l_Lean_MVarId_splitAndCore(v_mvarId_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_);
lean_dec(v_a_2692_);
lean_dec_ref(v_a_2691_);
lean_dec(v_a_2690_);
lean_dec_ref(v_a_2689_);
return v_res_2694_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAnd(lean_object* v_mvarId_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_){
_start:
{
lean_object* v___x_2701_; 
v___x_2701_ = l_Lean_MVarId_splitAndCore(v_mvarId_2695_, v_a_2696_, v_a_2697_, v_a_2698_, v_a_2699_);
return v___x_2701_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAnd___boxed(lean_object* v_mvarId_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_){
_start:
{
lean_object* v_res_2708_; 
v_res_2708_ = l_Lean_MVarId_splitAnd(v_mvarId_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_);
lean_dec(v_a_2706_);
lean_dec_ref(v_a_2705_);
lean_dec(v_a_2704_);
lean_dec_ref(v_a_2703_);
return v_res_2708_;
}
}
static lean_object* _init_l_Lean_MVarId_exfalso___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; 
v___x_2712_ = lean_box(0);
v___x_2713_ = ((lean_object*)(l_Lean_MVarId_exfalso___lam__0___closed__1));
v___x_2714_ = l_Lean_mkConst(v___x_2713_, v___x_2712_);
return v___x_2714_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso___lam__0(lean_object* v_mvarId_2719_, lean_object* v___x_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_){
_start:
{
lean_object* v___x_2726_; 
lean_inc(v_mvarId_2719_);
v___x_2726_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2719_, v___x_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_);
if (lean_obj_tag(v___x_2726_) == 0)
{
lean_object* v___x_2727_; 
lean_dec_ref_known(v___x_2726_, 1);
lean_inc(v_mvarId_2719_);
v___x_2727_ = l_Lean_MVarId_getType(v_mvarId_2719_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_);
if (lean_obj_tag(v___x_2727_) == 0)
{
lean_object* v_a_2728_; lean_object* v___x_2729_; lean_object* v_a_2730_; lean_object* v___x_2731_; 
v_a_2728_ = lean_ctor_get(v___x_2727_, 0);
lean_inc(v_a_2728_);
lean_dec_ref_known(v___x_2727_, 1);
v___x_2729_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_a_2728_, v___y_2722_);
v_a_2730_ = lean_ctor_get(v___x_2729_, 0);
lean_inc_n(v_a_2730_, 2);
lean_dec_ref(v___x_2729_);
v___x_2731_ = l_Lean_Meta_getLevel(v_a_2730_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_);
if (lean_obj_tag(v___x_2731_) == 0)
{
lean_object* v_a_2732_; lean_object* v___x_2733_; 
v_a_2732_ = lean_ctor_get(v___x_2731_, 0);
lean_inc(v_a_2732_);
lean_dec_ref_known(v___x_2731_, 1);
lean_inc(v_mvarId_2719_);
v___x_2733_ = l_Lean_MVarId_getTag(v_mvarId_2719_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_);
if (lean_obj_tag(v___x_2733_) == 0)
{
lean_object* v_a_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; 
v_a_2734_ = lean_ctor_get(v___x_2733_, 0);
lean_inc(v_a_2734_);
lean_dec_ref_known(v___x_2733_, 1);
v___x_2735_ = lean_box(0);
v___x_2736_ = lean_obj_once(&l_Lean_MVarId_exfalso___lam__0___closed__2, &l_Lean_MVarId_exfalso___lam__0___closed__2_once, _init_l_Lean_MVarId_exfalso___lam__0___closed__2);
v___x_2737_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_2736_, v_a_2734_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_);
if (lean_obj_tag(v___x_2737_) == 0)
{
lean_object* v_a_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2751_; 
v_a_2738_ = lean_ctor_get(v___x_2737_, 0);
lean_inc_n(v_a_2738_, 2);
lean_dec_ref_known(v___x_2737_, 1);
v___x_2739_ = ((lean_object*)(l_Lean_MVarId_exfalso___lam__0___closed__4));
v___x_2740_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2740_, 0, v_a_2732_);
lean_ctor_set(v___x_2740_, 1, v___x_2735_);
v___x_2741_ = l_Lean_mkConst(v___x_2739_, v___x_2740_);
v___x_2742_ = l_Lean_mkAppB(v___x_2741_, v_a_2730_, v_a_2738_);
v___x_2743_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2719_, v___x_2742_, v___y_2722_);
v_isSharedCheck_2751_ = !lean_is_exclusive(v___x_2743_);
if (v_isSharedCheck_2751_ == 0)
{
lean_object* v_unused_2752_; 
v_unused_2752_ = lean_ctor_get(v___x_2743_, 0);
lean_dec(v_unused_2752_);
v___x_2745_ = v___x_2743_;
v_isShared_2746_ = v_isSharedCheck_2751_;
goto v_resetjp_2744_;
}
else
{
lean_dec(v___x_2743_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2751_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2747_; lean_object* v___x_2749_; 
v___x_2747_ = l_Lean_Expr_mvarId_x21(v_a_2738_);
lean_dec(v_a_2738_);
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 0, v___x_2747_);
v___x_2749_ = v___x_2745_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v___x_2747_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
return v___x_2749_;
}
}
}
else
{
lean_object* v_a_2753_; lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2760_; 
lean_dec(v_a_2732_);
lean_dec(v_a_2730_);
lean_dec(v_mvarId_2719_);
v_a_2753_ = lean_ctor_get(v___x_2737_, 0);
v_isSharedCheck_2760_ = !lean_is_exclusive(v___x_2737_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2755_ = v___x_2737_;
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
else
{
lean_inc(v_a_2753_);
lean_dec(v___x_2737_);
v___x_2755_ = lean_box(0);
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
v_resetjp_2754_:
{
lean_object* v___x_2758_; 
if (v_isShared_2756_ == 0)
{
v___x_2758_ = v___x_2755_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v_a_2753_);
v___x_2758_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
return v___x_2758_;
}
}
}
}
else
{
lean_object* v_a_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2768_; 
lean_dec(v_a_2732_);
lean_dec(v_a_2730_);
lean_dec(v_mvarId_2719_);
v_a_2761_ = lean_ctor_get(v___x_2733_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2763_ = v___x_2733_;
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_a_2761_);
lean_dec(v___x_2733_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v___x_2766_; 
if (v_isShared_2764_ == 0)
{
v___x_2766_ = v___x_2763_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v_a_2761_);
v___x_2766_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
return v___x_2766_;
}
}
}
}
else
{
lean_object* v_a_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2776_; 
lean_dec(v_a_2730_);
lean_dec(v_mvarId_2719_);
v_a_2769_ = lean_ctor_get(v___x_2731_, 0);
v_isSharedCheck_2776_ = !lean_is_exclusive(v___x_2731_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2771_ = v___x_2731_;
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_a_2769_);
lean_dec(v___x_2731_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v___x_2774_; 
if (v_isShared_2772_ == 0)
{
v___x_2774_ = v___x_2771_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_a_2769_);
v___x_2774_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
return v___x_2774_;
}
}
}
}
else
{
lean_object* v_a_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2784_; 
lean_dec(v_mvarId_2719_);
v_a_2777_ = lean_ctor_get(v___x_2727_, 0);
v_isSharedCheck_2784_ = !lean_is_exclusive(v___x_2727_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2779_ = v___x_2727_;
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_a_2777_);
lean_dec(v___x_2727_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v___x_2782_; 
if (v_isShared_2780_ == 0)
{
v___x_2782_ = v___x_2779_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_a_2777_);
v___x_2782_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
return v___x_2782_;
}
}
}
}
else
{
lean_object* v_a_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2792_; 
lean_dec(v_mvarId_2719_);
v_a_2785_ = lean_ctor_get(v___x_2726_, 0);
v_isSharedCheck_2792_ = !lean_is_exclusive(v___x_2726_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2787_ = v___x_2726_;
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_a_2785_);
lean_dec(v___x_2726_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v___x_2790_; 
if (v_isShared_2788_ == 0)
{
v___x_2790_ = v___x_2787_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v_a_2785_);
v___x_2790_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
return v___x_2790_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso___lam__0___boxed(lean_object* v_mvarId_2793_, lean_object* v___x_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_){
_start:
{
lean_object* v_res_2800_; 
v_res_2800_ = l_Lean_MVarId_exfalso___lam__0(v_mvarId_2793_, v___x_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
return v_res_2800_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso(lean_object* v_mvarId_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_){
_start:
{
lean_object* v___x_2810_; lean_object* v___f_2811_; lean_object* v___x_2812_; 
v___x_2810_ = ((lean_object*)(l_Lean_MVarId_exfalso___closed__1));
lean_inc(v_mvarId_2804_);
v___f_2811_ = lean_alloc_closure((void*)(l_Lean_MVarId_exfalso___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2811_, 0, v_mvarId_2804_);
lean_closure_set(v___f_2811_, 1, v___x_2810_);
v___x_2812_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2804_, v___f_2811_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_);
return v___x_2812_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso___boxed(lean_object* v_mvarId_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_){
_start:
{
lean_object* v_res_2819_; 
v_res_2819_ = l_Lean_MVarId_exfalso(v_mvarId_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_);
lean_dec(v_a_2817_);
lean_dec_ref(v_a_2816_);
lean_dec(v_a_2815_);
lean_dec_ref(v_a_2814_);
return v_res_2819_;
}
}
static lean_object* _init_l_Lean_MVarId_nthConstructor___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2823_; lean_object* v___x_2824_; 
v___x_2823_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__1));
v___x_2824_ = l_Lean_MessageData_ofFormat(v___x_2823_);
return v___x_2824_;
}
}
static lean_object* _init_l_Lean_MVarId_nthConstructor___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2825_; lean_object* v___x_2826_; 
v___x_2825_ = lean_obj_once(&l_Lean_MVarId_nthConstructor___lam__0___closed__2, &l_Lean_MVarId_nthConstructor___lam__0___closed__2_once, _init_l_Lean_MVarId_nthConstructor___lam__0___closed__2);
v___x_2826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2826_, 0, v___x_2825_);
return v___x_2826_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___lam__0(lean_object* v_goal_2831_, lean_object* v_name_2832_, lean_object* v_idx_2833_, lean_object* v_expected_x3f_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_){
_start:
{
lean_object* v___y_2841_; lean_object* v___y_2842_; lean_object* v___y_2843_; lean_object* v___y_2844_; lean_object* v___x_2847_; 
lean_inc(v_name_2832_);
lean_inc(v_goal_2831_);
v___x_2847_ = l_Lean_MVarId_checkNotAssigned(v_goal_2831_, v_name_2832_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_);
if (lean_obj_tag(v___x_2847_) == 0)
{
lean_object* v___x_2848_; 
lean_dec_ref_known(v___x_2847_, 1);
lean_inc(v_goal_2831_);
v___x_2848_ = l_Lean_MVarId_getType_x27(v_goal_2831_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_);
if (lean_obj_tag(v___x_2848_) == 0)
{
lean_object* v_a_2849_; lean_object* v___x_2850_; 
v_a_2849_ = lean_ctor_get(v___x_2848_, 0);
lean_inc(v_a_2849_);
lean_dec_ref_known(v___x_2848_, 1);
v___x_2850_ = l_Lean_Expr_getAppFn(v_a_2849_);
lean_dec(v_a_2849_);
if (lean_obj_tag(v___x_2850_) == 4)
{
lean_object* v_declName_2851_; lean_object* v_us_2852_; lean_object* v___x_2853_; lean_object* v_env_2854_; uint8_t v___x_2855_; lean_object* v___x_2856_; 
v_declName_2851_ = lean_ctor_get(v___x_2850_, 0);
lean_inc(v_declName_2851_);
v_us_2852_ = lean_ctor_get(v___x_2850_, 1);
lean_inc(v_us_2852_);
lean_dec_ref_known(v___x_2850_, 2);
v___x_2853_ = lean_st_ref_get(v___y_2838_);
v_env_2854_ = lean_ctor_get(v___x_2853_, 0);
lean_inc_ref(v_env_2854_);
lean_dec(v___x_2853_);
v___x_2855_ = 0;
v___x_2856_ = l_Lean_Environment_find_x3f(v_env_2854_, v_declName_2851_, v___x_2855_);
if (lean_obj_tag(v___x_2856_) == 0)
{
lean_dec(v_us_2852_);
lean_dec(v_expected_x3f_2834_);
lean_dec(v_idx_2833_);
v___y_2841_ = v___y_2835_;
v___y_2842_ = v___y_2836_;
v___y_2843_ = v___y_2837_;
v___y_2844_ = v___y_2838_;
goto v___jp_2840_;
}
else
{
lean_object* v_val_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2927_; 
v_val_2857_ = lean_ctor_get(v___x_2856_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2856_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2859_ = v___x_2856_;
v_isShared_2860_ = v_isSharedCheck_2927_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_val_2857_);
lean_dec(v___x_2856_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2927_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
if (lean_obj_tag(v_val_2857_) == 5)
{
lean_object* v_val_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2926_; 
v_val_2861_ = lean_ctor_get(v_val_2857_, 0);
v_isSharedCheck_2926_ = !lean_is_exclusive(v_val_2857_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2863_ = v_val_2857_;
v_isShared_2864_ = v_isSharedCheck_2926_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_val_2861_);
lean_dec(v_val_2857_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2926_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
lean_object* v___y_2866_; lean_object* v___y_2867_; lean_object* v___y_2868_; lean_object* v___y_2869_; 
if (lean_obj_tag(v_expected_x3f_2834_) == 1)
{
lean_object* v_val_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2925_; 
v_val_2896_ = lean_ctor_get(v_expected_x3f_2834_, 0);
v_isSharedCheck_2925_ = !lean_is_exclusive(v_expected_x3f_2834_);
if (v_isSharedCheck_2925_ == 0)
{
v___x_2898_ = v_expected_x3f_2834_;
v_isShared_2899_ = v_isSharedCheck_2925_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_val_2896_);
lean_dec(v_expected_x3f_2834_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2925_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v_ctors_2900_; lean_object* v___x_2901_; uint8_t v___x_2902_; 
v_ctors_2900_ = lean_ctor_get(v_val_2861_, 4);
v___x_2901_ = l_List_lengthTR___redArg(v_ctors_2900_);
v___x_2902_ = lean_nat_dec_eq(v___x_2901_, v_val_2896_);
lean_dec(v___x_2901_);
if (v___x_2902_ == 0)
{
uint8_t v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2914_; 
v___x_2903_ = 1;
lean_inc(v_name_2832_);
v___x_2904_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2832_, v___x_2903_);
v___x_2905_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__7));
v___x_2906_ = lean_string_append(v___x_2904_, v___x_2905_);
v___x_2907_ = l_Nat_reprFast(v_val_2896_);
v___x_2908_ = lean_string_append(v___x_2906_, v___x_2907_);
lean_dec_ref(v___x_2907_);
v___x_2909_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__6));
v___x_2910_ = lean_string_append(v___x_2908_, v___x_2909_);
v___x_2911_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2911_, 0, v___x_2910_);
v___x_2912_ = l_Lean_MessageData_ofFormat(v___x_2911_);
if (v_isShared_2899_ == 0)
{
lean_ctor_set(v___x_2898_, 0, v___x_2912_);
v___x_2914_ = v___x_2898_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v___x_2912_);
v___x_2914_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
lean_object* v___x_2915_; 
lean_inc(v_goal_2831_);
lean_inc(v_name_2832_);
v___x_2915_ = l_Lean_Meta_throwTacticEx___redArg(v_name_2832_, v_goal_2831_, v___x_2914_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_);
if (lean_obj_tag(v___x_2915_) == 0)
{
lean_dec_ref_known(v___x_2915_, 1);
v___y_2866_ = v___y_2835_;
v___y_2867_ = v___y_2836_;
v___y_2868_ = v___y_2837_;
v___y_2869_ = v___y_2838_;
goto v___jp_2865_;
}
else
{
lean_object* v_a_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2923_; 
lean_del_object(v___x_2863_);
lean_dec_ref(v_val_2861_);
lean_del_object(v___x_2859_);
lean_dec(v_us_2852_);
lean_dec(v_idx_2833_);
lean_dec(v_name_2832_);
lean_dec(v_goal_2831_);
v_a_2916_ = lean_ctor_get(v___x_2915_, 0);
v_isSharedCheck_2923_ = !lean_is_exclusive(v___x_2915_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2918_ = v___x_2915_;
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_a_2916_);
lean_dec(v___x_2915_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v___x_2921_; 
if (v_isShared_2919_ == 0)
{
v___x_2921_ = v___x_2918_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v_a_2916_);
v___x_2921_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
return v___x_2921_;
}
}
}
}
}
else
{
lean_del_object(v___x_2898_);
lean_dec(v_val_2896_);
v___y_2866_ = v___y_2835_;
v___y_2867_ = v___y_2836_;
v___y_2868_ = v___y_2837_;
v___y_2869_ = v___y_2838_;
goto v___jp_2865_;
}
}
}
else
{
lean_dec(v_expected_x3f_2834_);
v___y_2866_ = v___y_2835_;
v___y_2867_ = v___y_2836_;
v___y_2868_ = v___y_2837_;
v___y_2869_ = v___y_2838_;
goto v___jp_2865_;
}
v___jp_2865_:
{
lean_object* v_ctors_2870_; lean_object* v___x_2871_; uint8_t v___x_2872_; 
v_ctors_2870_ = lean_ctor_get(v_val_2861_, 4);
lean_inc(v_ctors_2870_);
lean_dec_ref(v_val_2861_);
v___x_2871_ = l_List_lengthTR___redArg(v_ctors_2870_);
v___x_2872_ = lean_nat_dec_lt(v_idx_2833_, v___x_2871_);
if (v___x_2872_ == 0)
{
lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2883_; 
lean_dec(v_ctors_2870_);
lean_dec(v_us_2852_);
v___x_2873_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__4));
v___x_2874_ = l_Nat_reprFast(v_idx_2833_);
v___x_2875_ = lean_string_append(v___x_2873_, v___x_2874_);
lean_dec_ref(v___x_2874_);
v___x_2876_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__5));
v___x_2877_ = lean_string_append(v___x_2875_, v___x_2876_);
v___x_2878_ = l_Nat_reprFast(v___x_2871_);
v___x_2879_ = lean_string_append(v___x_2877_, v___x_2878_);
lean_dec_ref(v___x_2878_);
v___x_2880_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__6));
v___x_2881_ = lean_string_append(v___x_2879_, v___x_2880_);
if (v_isShared_2864_ == 0)
{
lean_ctor_set_tag(v___x_2863_, 3);
lean_ctor_set(v___x_2863_, 0, v___x_2881_);
v___x_2883_ = v___x_2863_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v___x_2881_);
v___x_2883_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
lean_object* v___x_2884_; lean_object* v___x_2886_; 
v___x_2884_ = l_Lean_MessageData_ofFormat(v___x_2883_);
if (v_isShared_2860_ == 0)
{
lean_ctor_set(v___x_2859_, 0, v___x_2884_);
v___x_2886_ = v___x_2859_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v___x_2884_);
v___x_2886_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
lean_object* v___x_2887_; 
v___x_2887_ = l_Lean_Meta_throwTacticEx___redArg(v_name_2832_, v_goal_2831_, v___x_2886_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_);
return v___x_2887_;
}
}
}
else
{
lean_object* v___x_2890_; lean_object* v___x_2891_; uint8_t v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; 
lean_dec(v___x_2871_);
lean_del_object(v___x_2863_);
lean_del_object(v___x_2859_);
lean_dec(v_name_2832_);
v___x_2890_ = l_List_get___redArg(v_ctors_2870_, v_idx_2833_);
lean_dec(v_ctors_2870_);
v___x_2891_ = l_Lean_mkConst(v___x_2890_, v_us_2852_);
v___x_2892_ = 0;
v___x_2893_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_2893_, 0, v___x_2892_);
lean_ctor_set_uint8(v___x_2893_, 1, v___x_2872_);
lean_ctor_set_uint8(v___x_2893_, 2, v___x_2855_);
lean_ctor_set_uint8(v___x_2893_, 3, v___x_2872_);
v___x_2894_ = lean_box(0);
v___x_2895_ = l_Lean_MVarId_apply(v_goal_2831_, v___x_2891_, v___x_2893_, v___x_2894_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_);
return v___x_2895_;
}
}
}
}
else
{
lean_del_object(v___x_2859_);
lean_dec(v_val_2857_);
lean_dec(v_us_2852_);
lean_dec(v_expected_x3f_2834_);
lean_dec(v_idx_2833_);
v___y_2841_ = v___y_2835_;
v___y_2842_ = v___y_2836_;
v___y_2843_ = v___y_2837_;
v___y_2844_ = v___y_2838_;
goto v___jp_2840_;
}
}
}
}
else
{
lean_dec_ref(v___x_2850_);
lean_dec(v_expected_x3f_2834_);
lean_dec(v_idx_2833_);
v___y_2841_ = v___y_2835_;
v___y_2842_ = v___y_2836_;
v___y_2843_ = v___y_2837_;
v___y_2844_ = v___y_2838_;
goto v___jp_2840_;
}
}
else
{
lean_object* v_a_2928_; lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_2935_; 
lean_dec(v_expected_x3f_2834_);
lean_dec(v_idx_2833_);
lean_dec(v_name_2832_);
lean_dec(v_goal_2831_);
v_a_2928_ = lean_ctor_get(v___x_2848_, 0);
v_isSharedCheck_2935_ = !lean_is_exclusive(v___x_2848_);
if (v_isSharedCheck_2935_ == 0)
{
v___x_2930_ = v___x_2848_;
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
else
{
lean_inc(v_a_2928_);
lean_dec(v___x_2848_);
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
lean_dec(v_expected_x3f_2834_);
lean_dec(v_idx_2833_);
lean_dec(v_name_2832_);
lean_dec(v_goal_2831_);
v_a_2936_ = lean_ctor_get(v___x_2847_, 0);
v_isSharedCheck_2943_ = !lean_is_exclusive(v___x_2847_);
if (v_isSharedCheck_2943_ == 0)
{
v___x_2938_ = v___x_2847_;
v_isShared_2939_ = v_isSharedCheck_2943_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_a_2936_);
lean_dec(v___x_2847_);
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
v___jp_2840_:
{
lean_object* v___x_2845_; lean_object* v___x_2846_; 
v___x_2845_ = lean_obj_once(&l_Lean_MVarId_nthConstructor___lam__0___closed__3, &l_Lean_MVarId_nthConstructor___lam__0___closed__3_once, _init_l_Lean_MVarId_nthConstructor___lam__0___closed__3);
v___x_2846_ = l_Lean_Meta_throwTacticEx___redArg(v_name_2832_, v_goal_2831_, v___x_2845_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
return v___x_2846_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___lam__0___boxed(lean_object* v_goal_2944_, lean_object* v_name_2945_, lean_object* v_idx_2946_, lean_object* v_expected_x3f_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_){
_start:
{
lean_object* v_res_2953_; 
v_res_2953_ = l_Lean_MVarId_nthConstructor___lam__0(v_goal_2944_, v_name_2945_, v_idx_2946_, v_expected_x3f_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_);
lean_dec(v___y_2951_);
lean_dec_ref(v___y_2950_);
lean_dec(v___y_2949_);
lean_dec_ref(v___y_2948_);
return v_res_2953_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor(lean_object* v_name_2954_, lean_object* v_idx_2955_, lean_object* v_expected_x3f_2956_, lean_object* v_goal_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_){
_start:
{
lean_object* v___f_2963_; lean_object* v___x_2964_; 
lean_inc(v_goal_2957_);
v___f_2963_ = lean_alloc_closure((void*)(l_Lean_MVarId_nthConstructor___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2963_, 0, v_goal_2957_);
lean_closure_set(v___f_2963_, 1, v_name_2954_);
lean_closure_set(v___f_2963_, 2, v_idx_2955_);
lean_closure_set(v___f_2963_, 3, v_expected_x3f_2956_);
v___x_2964_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_goal_2957_, v___f_2963_, v_a_2958_, v_a_2959_, v_a_2960_, v_a_2961_);
return v___x_2964_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___boxed(lean_object* v_name_2965_, lean_object* v_idx_2966_, lean_object* v_expected_x3f_2967_, lean_object* v_goal_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_){
_start:
{
lean_object* v_res_2974_; 
v_res_2974_ = l_Lean_MVarId_nthConstructor(v_name_2965_, v_idx_2966_, v_expected_x3f_2967_, v_goal_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
lean_dec(v_a_2972_);
lean_dec_ref(v_a_2971_);
lean_dec(v_a_2970_);
lean_dec_ref(v_a_2969_);
return v_res_2974_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(lean_object* v_x_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_){
_start:
{
lean_object* v___x_2981_; 
v___x_2981_ = l_Lean_Meta_saveState___redArg(v___y_2977_, v___y_2979_);
if (lean_obj_tag(v___x_2981_) == 0)
{
lean_object* v_a_2982_; lean_object* v___x_2983_; 
v_a_2982_ = lean_ctor_get(v___x_2981_, 0);
lean_inc(v_a_2982_);
lean_dec_ref_known(v___x_2981_, 1);
lean_inc(v___y_2979_);
lean_inc_ref(v___y_2978_);
lean_inc(v___y_2977_);
lean_inc_ref(v___y_2976_);
v___x_2983_ = lean_apply_5(v_x_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_, lean_box(0));
if (lean_obj_tag(v___x_2983_) == 0)
{
lean_object* v_a_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_2992_; 
lean_dec(v_a_2982_);
v_a_2984_ = lean_ctor_get(v___x_2983_, 0);
v_isSharedCheck_2992_ = !lean_is_exclusive(v___x_2983_);
if (v_isSharedCheck_2992_ == 0)
{
v___x_2986_ = v___x_2983_;
v_isShared_2987_ = v_isSharedCheck_2992_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_a_2984_);
lean_dec(v___x_2983_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_2992_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v___x_2988_; lean_object* v___x_2990_; 
v___x_2988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2988_, 0, v_a_2984_);
if (v_isShared_2987_ == 0)
{
lean_ctor_set(v___x_2986_, 0, v___x_2988_);
v___x_2990_ = v___x_2986_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v___x_2988_);
v___x_2990_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
return v___x_2990_;
}
}
}
else
{
lean_object* v_a_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3022_; 
v_a_2993_ = lean_ctor_get(v___x_2983_, 0);
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_2983_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_2995_ = v___x_2983_;
v_isShared_2996_ = v_isSharedCheck_3022_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_a_2993_);
lean_dec(v___x_2983_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3022_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
uint8_t v___y_2998_; uint8_t v___x_3020_; 
v___x_3020_ = l_Lean_Exception_isInterrupt(v_a_2993_);
if (v___x_3020_ == 0)
{
uint8_t v___x_3021_; 
lean_inc(v_a_2993_);
v___x_3021_ = l_Lean_Exception_isRuntime(v_a_2993_);
v___y_2998_ = v___x_3021_;
goto v___jp_2997_;
}
else
{
v___y_2998_ = v___x_3020_;
goto v___jp_2997_;
}
v___jp_2997_:
{
if (v___y_2998_ == 0)
{
lean_object* v___x_2999_; 
lean_del_object(v___x_2995_);
lean_dec(v_a_2993_);
v___x_2999_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2982_, v___y_2977_, v___y_2979_);
lean_dec(v_a_2982_);
if (lean_obj_tag(v___x_2999_) == 0)
{
lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3007_; 
v_isSharedCheck_3007_ = !lean_is_exclusive(v___x_2999_);
if (v_isSharedCheck_3007_ == 0)
{
lean_object* v_unused_3008_; 
v_unused_3008_ = lean_ctor_get(v___x_2999_, 0);
lean_dec(v_unused_3008_);
v___x_3001_ = v___x_2999_;
v_isShared_3002_ = v_isSharedCheck_3007_;
goto v_resetjp_3000_;
}
else
{
lean_dec(v___x_2999_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3007_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3003_; lean_object* v___x_3005_; 
v___x_3003_ = lean_box(0);
if (v_isShared_3002_ == 0)
{
lean_ctor_set(v___x_3001_, 0, v___x_3003_);
v___x_3005_ = v___x_3001_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v___x_3003_);
v___x_3005_ = v_reuseFailAlloc_3006_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
return v___x_3005_;
}
}
}
else
{
lean_object* v_a_3009_; lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3016_; 
v_a_3009_ = lean_ctor_get(v___x_2999_, 0);
v_isSharedCheck_3016_ = !lean_is_exclusive(v___x_2999_);
if (v_isSharedCheck_3016_ == 0)
{
v___x_3011_ = v___x_2999_;
v_isShared_3012_ = v_isSharedCheck_3016_;
goto v_resetjp_3010_;
}
else
{
lean_inc(v_a_3009_);
lean_dec(v___x_2999_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3016_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
lean_object* v___x_3014_; 
if (v_isShared_3012_ == 0)
{
v___x_3014_ = v___x_3011_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3015_, 0, v_a_3009_);
v___x_3014_ = v_reuseFailAlloc_3015_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
return v___x_3014_;
}
}
}
}
else
{
lean_object* v___x_3018_; 
lean_dec(v_a_2982_);
if (v_isShared_2996_ == 0)
{
v___x_3018_ = v___x_2995_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v_a_2993_);
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
}
else
{
lean_object* v_a_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3030_; 
lean_dec_ref(v_x_2975_);
v_a_3023_ = lean_ctor_get(v___x_2981_, 0);
v_isSharedCheck_3030_ = !lean_is_exclusive(v___x_2981_);
if (v_isSharedCheck_3030_ == 0)
{
v___x_3025_ = v___x_2981_;
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_a_3023_);
lean_dec(v___x_2981_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v___x_3028_; 
if (v_isShared_3026_ == 0)
{
v___x_3028_ = v___x_3025_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_a_3023_);
v___x_3028_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
return v___x_3028_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg___boxed(lean_object* v_x_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_){
_start:
{
lean_object* v_res_3037_; 
v_res_3037_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v_x_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_);
lean_dec(v___y_3035_);
lean_dec_ref(v___y_3034_);
lean_dec(v___y_3033_);
lean_dec_ref(v___y_3032_);
return v_res_3037_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0(lean_object* v_00_u03b1_3038_, lean_object* v_x_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_){
_start:
{
lean_object* v___x_3045_; 
v___x_3045_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v_x_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_);
return v___x_3045_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___boxed(lean_object* v_00_u03b1_3046_, lean_object* v_x_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_){
_start:
{
lean_object* v_res_3053_; 
v_res_3053_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0(v_00_u03b1_3046_, v_x_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_);
lean_dec(v___y_3051_);
lean_dec_ref(v___y_3050_);
lean_dec(v___y_3049_);
lean_dec_ref(v___y_3048_);
return v_res_3053_;
}
}
static lean_object* _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3055_ = ((lean_object*)(l_Lean_MVarId_iffOfEq___lam__0___closed__0));
v___x_3056_ = l_Lean_stringToMessageData(v___x_3055_);
return v___x_3056_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq___lam__0(lean_object* v_mvarId_3057_, lean_object* v___x_3058_, lean_object* v___x_3059_, lean_object* v___x_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_){
_start:
{
lean_object* v___x_3066_; 
v___x_3066_ = l_Lean_MVarId_apply(v_mvarId_3057_, v___x_3058_, v___x_3059_, v___x_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_);
if (lean_obj_tag(v___x_3066_) == 0)
{
lean_object* v_a_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3083_; 
v_a_3067_ = lean_ctor_get(v___x_3066_, 0);
v_isSharedCheck_3083_ = !lean_is_exclusive(v___x_3066_);
if (v_isSharedCheck_3083_ == 0)
{
v___x_3069_ = v___x_3066_;
v_isShared_3070_ = v_isSharedCheck_3083_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_a_3067_);
lean_dec(v___x_3066_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3083_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; 
if (lean_obj_tag(v_a_3067_) == 1)
{
lean_object* v_tail_3078_; 
v_tail_3078_ = lean_ctor_get(v_a_3067_, 1);
if (lean_obj_tag(v_tail_3078_) == 0)
{
lean_object* v_head_3079_; lean_object* v___x_3081_; 
v_head_3079_ = lean_ctor_get(v_a_3067_, 0);
lean_inc(v_head_3079_);
lean_dec_ref_known(v_a_3067_, 2);
if (v_isShared_3070_ == 0)
{
lean_ctor_set(v___x_3069_, 0, v_head_3079_);
v___x_3081_ = v___x_3069_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3082_; 
v_reuseFailAlloc_3082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3082_, 0, v_head_3079_);
v___x_3081_ = v_reuseFailAlloc_3082_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
return v___x_3081_;
}
}
else
{
lean_dec_ref_known(v_a_3067_, 2);
lean_del_object(v___x_3069_);
v___y_3072_ = v___y_3061_;
v___y_3073_ = v___y_3062_;
v___y_3074_ = v___y_3063_;
v___y_3075_ = v___y_3064_;
goto v___jp_3071_;
}
}
else
{
lean_del_object(v___x_3069_);
lean_dec(v_a_3067_);
v___y_3072_ = v___y_3061_;
v___y_3073_ = v___y_3062_;
v___y_3074_ = v___y_3063_;
v___y_3075_ = v___y_3064_;
goto v___jp_3071_;
}
v___jp_3071_:
{
lean_object* v___x_3076_; lean_object* v___x_3077_; 
v___x_3076_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3077_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3076_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_);
return v___x_3077_;
}
}
}
else
{
lean_object* v_a_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3091_; 
v_a_3084_ = lean_ctor_get(v___x_3066_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v___x_3066_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3086_ = v___x_3066_;
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_a_3084_);
lean_dec(v___x_3066_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v___x_3089_; 
if (v_isShared_3087_ == 0)
{
v___x_3089_ = v___x_3086_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_a_3084_);
v___x_3089_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
return v___x_3089_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq___lam__0___boxed(lean_object* v_mvarId_3092_, lean_object* v___x_3093_, lean_object* v___x_3094_, lean_object* v___x_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_){
_start:
{
lean_object* v_res_3101_; 
v_res_3101_ = l_Lean_MVarId_iffOfEq___lam__0(v_mvarId_3092_, v___x_3093_, v___x_3094_, v___x_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_);
lean_dec(v___y_3099_);
lean_dec_ref(v___y_3098_);
lean_dec(v___y_3097_);
lean_dec_ref(v___y_3096_);
return v_res_3101_;
}
}
static lean_object* _init_l_Lean_MVarId_iffOfEq___closed__2(void){
_start:
{
lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; 
v___x_3105_ = lean_box(0);
v___x_3106_ = ((lean_object*)(l_Lean_MVarId_iffOfEq___closed__1));
v___x_3107_ = l_Lean_mkConst(v___x_3106_, v___x_3105_);
return v___x_3107_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq(lean_object* v_mvarId_3112_, lean_object* v_a_3113_, lean_object* v_a_3114_, lean_object* v_a_3115_, lean_object* v_a_3116_){
_start:
{
lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___f_3121_; lean_object* v___x_3122_; 
v___x_3118_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___closed__2, &l_Lean_MVarId_iffOfEq___closed__2_once, _init_l_Lean_MVarId_iffOfEq___closed__2);
v___x_3119_ = ((lean_object*)(l_Lean_MVarId_iffOfEq___closed__3));
v___x_3120_ = lean_box(0);
lean_inc(v_mvarId_3112_);
v___f_3121_ = lean_alloc_closure((void*)(l_Lean_MVarId_iffOfEq___lam__0___boxed), 9, 4);
lean_closure_set(v___f_3121_, 0, v_mvarId_3112_);
lean_closure_set(v___f_3121_, 1, v___x_3118_);
lean_closure_set(v___f_3121_, 2, v___x_3119_);
lean_closure_set(v___f_3121_, 3, v___x_3120_);
v___x_3122_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v___f_3121_, v_a_3113_, v_a_3114_, v_a_3115_, v_a_3116_);
if (lean_obj_tag(v___x_3122_) == 0)
{
lean_object* v_a_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3134_; 
v_a_3123_ = lean_ctor_get(v___x_3122_, 0);
v_isSharedCheck_3134_ = !lean_is_exclusive(v___x_3122_);
if (v_isSharedCheck_3134_ == 0)
{
v___x_3125_ = v___x_3122_;
v_isShared_3126_ = v_isSharedCheck_3134_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_a_3123_);
lean_dec(v___x_3122_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3134_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
if (lean_obj_tag(v_a_3123_) == 0)
{
lean_object* v___x_3128_; 
if (v_isShared_3126_ == 0)
{
lean_ctor_set(v___x_3125_, 0, v_mvarId_3112_);
v___x_3128_ = v___x_3125_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v_mvarId_3112_);
v___x_3128_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
return v___x_3128_;
}
}
else
{
lean_object* v_val_3130_; lean_object* v___x_3132_; 
lean_dec(v_mvarId_3112_);
v_val_3130_ = lean_ctor_get(v_a_3123_, 0);
lean_inc(v_val_3130_);
lean_dec_ref_known(v_a_3123_, 1);
if (v_isShared_3126_ == 0)
{
lean_ctor_set(v___x_3125_, 0, v_val_3130_);
v___x_3132_ = v___x_3125_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v_val_3130_);
v___x_3132_ = v_reuseFailAlloc_3133_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
return v___x_3132_;
}
}
}
}
else
{
lean_object* v_a_3135_; lean_object* v___x_3137_; uint8_t v_isShared_3138_; uint8_t v_isSharedCheck_3142_; 
lean_dec(v_mvarId_3112_);
v_a_3135_ = lean_ctor_get(v___x_3122_, 0);
v_isSharedCheck_3142_ = !lean_is_exclusive(v___x_3122_);
if (v_isSharedCheck_3142_ == 0)
{
v___x_3137_ = v___x_3122_;
v_isShared_3138_ = v_isSharedCheck_3142_;
goto v_resetjp_3136_;
}
else
{
lean_inc(v_a_3135_);
lean_dec(v___x_3122_);
v___x_3137_ = lean_box(0);
v_isShared_3138_ = v_isSharedCheck_3142_;
goto v_resetjp_3136_;
}
v_resetjp_3136_:
{
lean_object* v___x_3140_; 
if (v_isShared_3138_ == 0)
{
v___x_3140_ = v___x_3137_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v_a_3135_);
v___x_3140_ = v_reuseFailAlloc_3141_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
return v___x_3140_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq___boxed(lean_object* v_mvarId_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_){
_start:
{
lean_object* v_res_3149_; 
v_res_3149_ = l_Lean_MVarId_iffOfEq(v_mvarId_3143_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_);
lean_dec(v_a_3147_);
lean_dec_ref(v_a_3146_);
lean_dec(v_a_3145_);
lean_dec_ref(v_a_3144_);
return v_res_3149_;
}
}
static lean_object* _init_l_Lean_MVarId_propext___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; 
v___x_3153_ = lean_box(0);
v___x_3154_ = ((lean_object*)(l_Lean_MVarId_propext___lam__0___closed__1));
v___x_3155_ = l_Lean_mkConst(v___x_3154_, v___x_3153_);
return v___x_3155_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___lam__0(lean_object* v_mvarId_3159_, uint8_t v___x_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_){
_start:
{
lean_object* v___y_3167_; lean_object* v___y_3168_; lean_object* v___y_3169_; lean_object* v___y_3170_; uint8_t v___y_3174_; lean_object* v___y_3200_; lean_object* v___x_3238_; uint8_t v_transparency_3239_; uint8_t v___x_3240_; 
v___x_3238_ = l_Lean_Meta_Context_config(v___y_3161_);
v_transparency_3239_ = lean_ctor_get_uint8(v___x_3238_, 9);
lean_dec_ref(v___x_3238_);
v___x_3240_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3239_, v___x_3160_);
if (v___x_3240_ == 0)
{
lean_object* v_keyedConfig_3241_; uint8_t v_trackZetaDelta_3242_; lean_object* v_zetaDeltaSet_3243_; lean_object* v_lctx_3244_; lean_object* v_localInstances_3245_; lean_object* v_defEqCtx_x3f_3246_; lean_object* v_synthPendingDepth_3247_; lean_object* v_customCanUnfoldPredicate_x3f_3248_; uint8_t v_univApprox_3249_; uint8_t v_inTypeClassResolution_3250_; uint8_t v_cacheInferType_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; 
v_keyedConfig_3241_ = lean_ctor_get(v___y_3161_, 0);
v_trackZetaDelta_3242_ = lean_ctor_get_uint8(v___y_3161_, sizeof(void*)*7);
v_zetaDeltaSet_3243_ = lean_ctor_get(v___y_3161_, 1);
v_lctx_3244_ = lean_ctor_get(v___y_3161_, 2);
v_localInstances_3245_ = lean_ctor_get(v___y_3161_, 3);
v_defEqCtx_x3f_3246_ = lean_ctor_get(v___y_3161_, 4);
v_synthPendingDepth_3247_ = lean_ctor_get(v___y_3161_, 5);
v_customCanUnfoldPredicate_x3f_3248_ = lean_ctor_get(v___y_3161_, 6);
v_univApprox_3249_ = lean_ctor_get_uint8(v___y_3161_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3250_ = lean_ctor_get_uint8(v___y_3161_, sizeof(void*)*7 + 2);
v_cacheInferType_3251_ = lean_ctor_get_uint8(v___y_3161_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3241_);
v___x_3252_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3160_, v_keyedConfig_3241_);
lean_inc(v_customCanUnfoldPredicate_x3f_3248_);
lean_inc(v_synthPendingDepth_3247_);
lean_inc(v_defEqCtx_x3f_3246_);
lean_inc_ref(v_localInstances_3245_);
lean_inc_ref(v_lctx_3244_);
lean_inc(v_zetaDeltaSet_3243_);
v___x_3253_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3253_, 0, v___x_3252_);
lean_ctor_set(v___x_3253_, 1, v_zetaDeltaSet_3243_);
lean_ctor_set(v___x_3253_, 2, v_lctx_3244_);
lean_ctor_set(v___x_3253_, 3, v_localInstances_3245_);
lean_ctor_set(v___x_3253_, 4, v_defEqCtx_x3f_3246_);
lean_ctor_set(v___x_3253_, 5, v_synthPendingDepth_3247_);
lean_ctor_set(v___x_3253_, 6, v_customCanUnfoldPredicate_x3f_3248_);
lean_ctor_set_uint8(v___x_3253_, sizeof(void*)*7, v_trackZetaDelta_3242_);
lean_ctor_set_uint8(v___x_3253_, sizeof(void*)*7 + 1, v_univApprox_3249_);
lean_ctor_set_uint8(v___x_3253_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3250_);
lean_ctor_set_uint8(v___x_3253_, sizeof(void*)*7 + 3, v_cacheInferType_3251_);
lean_inc(v_mvarId_3159_);
v___x_3254_ = l_Lean_MVarId_getType_x27(v_mvarId_3159_, v___x_3253_, v___y_3162_, v___y_3163_, v___y_3164_);
lean_dec_ref_known(v___x_3253_, 7);
v___y_3200_ = v___x_3254_;
goto v___jp_3199_;
}
else
{
lean_object* v___x_3255_; 
lean_inc(v_mvarId_3159_);
v___x_3255_ = l_Lean_MVarId_getType_x27(v_mvarId_3159_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_);
v___y_3200_ = v___x_3255_;
goto v___jp_3199_;
}
v___jp_3166_:
{
lean_object* v___x_3171_; lean_object* v___x_3172_; 
v___x_3171_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3172_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3171_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
lean_dec_ref(v___y_3167_);
return v___x_3172_;
}
v___jp_3173_:
{
lean_object* v___x_3175_; uint8_t v___x_3176_; uint8_t v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; 
v___x_3175_ = lean_obj_once(&l_Lean_MVarId_propext___lam__0___closed__2, &l_Lean_MVarId_propext___lam__0___closed__2_once, _init_l_Lean_MVarId_propext___lam__0___closed__2);
v___x_3176_ = 0;
v___x_3177_ = 0;
v___x_3178_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3178_, 0, v___x_3176_);
lean_ctor_set_uint8(v___x_3178_, 1, v___y_3174_);
lean_ctor_set_uint8(v___x_3178_, 2, v___x_3177_);
lean_ctor_set_uint8(v___x_3178_, 3, v___y_3174_);
v___x_3179_ = lean_box(0);
v___x_3180_ = l_Lean_MVarId_apply(v_mvarId_3159_, v___x_3175_, v___x_3178_, v___x_3179_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_);
if (lean_obj_tag(v___x_3180_) == 0)
{
lean_object* v_a_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3190_; 
v_a_3181_ = lean_ctor_get(v___x_3180_, 0);
v_isSharedCheck_3190_ = !lean_is_exclusive(v___x_3180_);
if (v_isSharedCheck_3190_ == 0)
{
v___x_3183_ = v___x_3180_;
v_isShared_3184_ = v_isSharedCheck_3190_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_a_3181_);
lean_dec(v___x_3180_);
v___x_3183_ = lean_box(0);
v_isShared_3184_ = v_isSharedCheck_3190_;
goto v_resetjp_3182_;
}
v_resetjp_3182_:
{
if (lean_obj_tag(v_a_3181_) == 1)
{
lean_object* v_tail_3185_; 
v_tail_3185_ = lean_ctor_get(v_a_3181_, 1);
if (lean_obj_tag(v_tail_3185_) == 0)
{
lean_object* v_head_3186_; lean_object* v___x_3188_; 
lean_dec_ref(v___y_3161_);
v_head_3186_ = lean_ctor_get(v_a_3181_, 0);
lean_inc(v_head_3186_);
lean_dec_ref_known(v_a_3181_, 2);
if (v_isShared_3184_ == 0)
{
lean_ctor_set(v___x_3183_, 0, v_head_3186_);
v___x_3188_ = v___x_3183_;
goto v_reusejp_3187_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v_head_3186_);
v___x_3188_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3187_;
}
v_reusejp_3187_:
{
return v___x_3188_;
}
}
else
{
lean_dec_ref_known(v_a_3181_, 2);
lean_del_object(v___x_3183_);
v___y_3167_ = v___y_3161_;
v___y_3168_ = v___y_3162_;
v___y_3169_ = v___y_3163_;
v___y_3170_ = v___y_3164_;
goto v___jp_3166_;
}
}
else
{
lean_del_object(v___x_3183_);
lean_dec(v_a_3181_);
v___y_3167_ = v___y_3161_;
v___y_3168_ = v___y_3162_;
v___y_3169_ = v___y_3163_;
v___y_3170_ = v___y_3164_;
goto v___jp_3166_;
}
}
}
else
{
lean_object* v_a_3191_; lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3198_; 
lean_dec_ref(v___y_3161_);
v_a_3191_ = lean_ctor_get(v___x_3180_, 0);
v_isSharedCheck_3198_ = !lean_is_exclusive(v___x_3180_);
if (v_isSharedCheck_3198_ == 0)
{
v___x_3193_ = v___x_3180_;
v_isShared_3194_ = v_isSharedCheck_3198_;
goto v_resetjp_3192_;
}
else
{
lean_inc(v_a_3191_);
lean_dec(v___x_3180_);
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
v___jp_3199_:
{
if (lean_obj_tag(v___y_3200_) == 0)
{
lean_object* v_a_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; uint8_t v___x_3204_; 
v_a_3201_ = lean_ctor_get(v___y_3200_, 0);
lean_inc(v_a_3201_);
lean_dec_ref_known(v___y_3200_, 1);
v___x_3202_ = ((lean_object*)(l_Lean_MVarId_propext___lam__0___closed__4));
v___x_3203_ = lean_unsigned_to_nat(3u);
v___x_3204_ = l_Lean_Expr_isAppOfArity(v_a_3201_, v___x_3202_, v___x_3203_);
if (v___x_3204_ == 0)
{
lean_object* v___x_3205_; lean_object* v___x_3206_; 
lean_dec(v_a_3201_);
lean_dec(v_mvarId_3159_);
v___x_3205_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3206_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3205_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_);
lean_dec_ref(v___y_3161_);
return v___x_3206_;
}
else
{
lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; 
v___x_3207_ = l_Lean_Expr_appFn_x21(v_a_3201_);
lean_dec(v_a_3201_);
v___x_3208_ = l_Lean_Expr_appArg_x21(v___x_3207_);
lean_dec_ref(v___x_3207_);
v___x_3209_ = l_Lean_Meta_isProp(v___x_3208_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_);
if (lean_obj_tag(v___x_3209_) == 0)
{
lean_object* v_a_3210_; uint8_t v___x_3211_; 
v_a_3210_ = lean_ctor_get(v___x_3209_, 0);
lean_inc(v_a_3210_);
lean_dec_ref_known(v___x_3209_, 1);
v___x_3211_ = lean_unbox(v_a_3210_);
lean_dec(v_a_3210_);
if (v___x_3211_ == 0)
{
lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v_a_3214_; lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3221_; 
lean_dec(v_mvarId_3159_);
v___x_3212_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3213_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3212_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_);
lean_dec_ref(v___y_3161_);
v_a_3214_ = lean_ctor_get(v___x_3213_, 0);
v_isSharedCheck_3221_ = !lean_is_exclusive(v___x_3213_);
if (v_isSharedCheck_3221_ == 0)
{
v___x_3216_ = v___x_3213_;
v_isShared_3217_ = v_isSharedCheck_3221_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_a_3214_);
lean_dec(v___x_3213_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3221_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
lean_object* v___x_3219_; 
if (v_isShared_3217_ == 0)
{
v___x_3219_ = v___x_3216_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v_a_3214_);
v___x_3219_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
return v___x_3219_;
}
}
}
else
{
v___y_3174_ = v___x_3204_;
goto v___jp_3173_;
}
}
else
{
lean_object* v_a_3222_; lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3229_; 
lean_dec_ref(v___y_3161_);
lean_dec(v_mvarId_3159_);
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
else
{
lean_object* v_a_3230_; lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3237_; 
lean_dec_ref(v___y_3161_);
lean_dec(v_mvarId_3159_);
v_a_3230_ = lean_ctor_get(v___y_3200_, 0);
v_isSharedCheck_3237_ = !lean_is_exclusive(v___y_3200_);
if (v_isSharedCheck_3237_ == 0)
{
v___x_3232_ = v___y_3200_;
v_isShared_3233_ = v_isSharedCheck_3237_;
goto v_resetjp_3231_;
}
else
{
lean_inc(v_a_3230_);
lean_dec(v___y_3200_);
v___x_3232_ = lean_box(0);
v_isShared_3233_ = v_isSharedCheck_3237_;
goto v_resetjp_3231_;
}
v_resetjp_3231_:
{
lean_object* v___x_3235_; 
if (v_isShared_3233_ == 0)
{
v___x_3235_ = v___x_3232_;
goto v_reusejp_3234_;
}
else
{
lean_object* v_reuseFailAlloc_3236_; 
v_reuseFailAlloc_3236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3236_, 0, v_a_3230_);
v___x_3235_ = v_reuseFailAlloc_3236_;
goto v_reusejp_3234_;
}
v_reusejp_3234_:
{
return v___x_3235_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___lam__0___boxed(lean_object* v_mvarId_3256_, lean_object* v___x_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_){
_start:
{
uint8_t v___x_2521__boxed_3263_; lean_object* v_res_3264_; 
v___x_2521__boxed_3263_ = lean_unbox(v___x_3257_);
v_res_3264_ = l_Lean_MVarId_propext___lam__0(v_mvarId_3256_, v___x_2521__boxed_3263_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_);
lean_dec(v___y_3261_);
lean_dec_ref(v___y_3260_);
lean_dec(v___y_3259_);
return v_res_3264_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext(lean_object* v_mvarId_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_){
_start:
{
uint8_t v___x_3271_; lean_object* v___x_3272_; lean_object* v___f_3273_; lean_object* v___x_3274_; 
v___x_3271_ = 2;
v___x_3272_ = lean_box(v___x_3271_);
lean_inc(v_mvarId_3265_);
v___f_3273_ = lean_alloc_closure((void*)(l_Lean_MVarId_propext___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3273_, 0, v_mvarId_3265_);
lean_closure_set(v___f_3273_, 1, v___x_3272_);
v___x_3274_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v___f_3273_, v_a_3266_, v_a_3267_, v_a_3268_, v_a_3269_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_object* v_a_3275_; lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3286_; 
v_a_3275_ = lean_ctor_get(v___x_3274_, 0);
v_isSharedCheck_3286_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3286_ == 0)
{
v___x_3277_ = v___x_3274_;
v_isShared_3278_ = v_isSharedCheck_3286_;
goto v_resetjp_3276_;
}
else
{
lean_inc(v_a_3275_);
lean_dec(v___x_3274_);
v___x_3277_ = lean_box(0);
v_isShared_3278_ = v_isSharedCheck_3286_;
goto v_resetjp_3276_;
}
v_resetjp_3276_:
{
if (lean_obj_tag(v_a_3275_) == 0)
{
lean_object* v___x_3280_; 
if (v_isShared_3278_ == 0)
{
lean_ctor_set(v___x_3277_, 0, v_mvarId_3265_);
v___x_3280_ = v___x_3277_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v_mvarId_3265_);
v___x_3280_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3279_;
}
v_reusejp_3279_:
{
return v___x_3280_;
}
}
else
{
lean_object* v_val_3282_; lean_object* v___x_3284_; 
lean_dec(v_mvarId_3265_);
v_val_3282_ = lean_ctor_get(v_a_3275_, 0);
lean_inc(v_val_3282_);
lean_dec_ref_known(v_a_3275_, 1);
if (v_isShared_3278_ == 0)
{
lean_ctor_set(v___x_3277_, 0, v_val_3282_);
v___x_3284_ = v___x_3277_;
goto v_reusejp_3283_;
}
else
{
lean_object* v_reuseFailAlloc_3285_; 
v_reuseFailAlloc_3285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3285_, 0, v_val_3282_);
v___x_3284_ = v_reuseFailAlloc_3285_;
goto v_reusejp_3283_;
}
v_reusejp_3283_:
{
return v___x_3284_;
}
}
}
}
else
{
lean_object* v_a_3287_; lean_object* v___x_3289_; uint8_t v_isShared_3290_; uint8_t v_isSharedCheck_3294_; 
lean_dec(v_mvarId_3265_);
v_a_3287_ = lean_ctor_get(v___x_3274_, 0);
v_isSharedCheck_3294_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3294_ == 0)
{
v___x_3289_ = v___x_3274_;
v_isShared_3290_ = v_isSharedCheck_3294_;
goto v_resetjp_3288_;
}
else
{
lean_inc(v_a_3287_);
lean_dec(v___x_3274_);
v___x_3289_ = lean_box(0);
v_isShared_3290_ = v_isSharedCheck_3294_;
goto v_resetjp_3288_;
}
v_resetjp_3288_:
{
lean_object* v___x_3292_; 
if (v_isShared_3290_ == 0)
{
v___x_3292_ = v___x_3289_;
goto v_reusejp_3291_;
}
else
{
lean_object* v_reuseFailAlloc_3293_; 
v_reuseFailAlloc_3293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3293_, 0, v_a_3287_);
v___x_3292_ = v_reuseFailAlloc_3293_;
goto v_reusejp_3291_;
}
v_reusejp_3291_:
{
return v___x_3292_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___boxed(lean_object* v_mvarId_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_){
_start:
{
lean_object* v_res_3301_; 
v_res_3301_ = l_Lean_MVarId_propext(v_mvarId_3295_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_);
lean_dec(v_a_3299_);
lean_dec_ref(v_a_3298_);
lean_dec(v_a_3297_);
lean_dec_ref(v_a_3296_);
return v_res_3301_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__0(lean_object* v_mvarId_3308_, lean_object* v___x_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_){
_start:
{
lean_object* v___y_3316_; lean_object* v___x_3360_; 
lean_inc(v_mvarId_3308_);
v___x_3360_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3308_, v___x_3309_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_);
if (lean_obj_tag(v___x_3360_) == 0)
{
lean_object* v___x_3361_; uint8_t v_transparency_3362_; uint8_t v___x_3363_; uint8_t v___x_3364_; 
lean_dec_ref_known(v___x_3360_, 1);
v___x_3361_ = l_Lean_Meta_Context_config(v___y_3310_);
v_transparency_3362_ = lean_ctor_get_uint8(v___x_3361_, 9);
lean_dec_ref(v___x_3361_);
v___x_3363_ = 2;
v___x_3364_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3362_, v___x_3363_);
if (v___x_3364_ == 0)
{
lean_object* v_keyedConfig_3365_; uint8_t v_trackZetaDelta_3366_; lean_object* v_zetaDeltaSet_3367_; lean_object* v_lctx_3368_; lean_object* v_localInstances_3369_; lean_object* v_defEqCtx_x3f_3370_; lean_object* v_synthPendingDepth_3371_; lean_object* v_customCanUnfoldPredicate_x3f_3372_; uint8_t v_univApprox_3373_; uint8_t v_inTypeClassResolution_3374_; uint8_t v_cacheInferType_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
v_keyedConfig_3365_ = lean_ctor_get(v___y_3310_, 0);
v_trackZetaDelta_3366_ = lean_ctor_get_uint8(v___y_3310_, sizeof(void*)*7);
v_zetaDeltaSet_3367_ = lean_ctor_get(v___y_3310_, 1);
v_lctx_3368_ = lean_ctor_get(v___y_3310_, 2);
v_localInstances_3369_ = lean_ctor_get(v___y_3310_, 3);
v_defEqCtx_x3f_3370_ = lean_ctor_get(v___y_3310_, 4);
v_synthPendingDepth_3371_ = lean_ctor_get(v___y_3310_, 5);
v_customCanUnfoldPredicate_x3f_3372_ = lean_ctor_get(v___y_3310_, 6);
v_univApprox_3373_ = lean_ctor_get_uint8(v___y_3310_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3374_ = lean_ctor_get_uint8(v___y_3310_, sizeof(void*)*7 + 2);
v_cacheInferType_3375_ = lean_ctor_get_uint8(v___y_3310_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3365_);
v___x_3376_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3363_, v_keyedConfig_3365_);
lean_inc(v_customCanUnfoldPredicate_x3f_3372_);
lean_inc(v_synthPendingDepth_3371_);
lean_inc(v_defEqCtx_x3f_3370_);
lean_inc_ref(v_localInstances_3369_);
lean_inc_ref(v_lctx_3368_);
lean_inc(v_zetaDeltaSet_3367_);
v___x_3377_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3377_, 0, v___x_3376_);
lean_ctor_set(v___x_3377_, 1, v_zetaDeltaSet_3367_);
lean_ctor_set(v___x_3377_, 2, v_lctx_3368_);
lean_ctor_set(v___x_3377_, 3, v_localInstances_3369_);
lean_ctor_set(v___x_3377_, 4, v_defEqCtx_x3f_3370_);
lean_ctor_set(v___x_3377_, 5, v_synthPendingDepth_3371_);
lean_ctor_set(v___x_3377_, 6, v_customCanUnfoldPredicate_x3f_3372_);
lean_ctor_set_uint8(v___x_3377_, sizeof(void*)*7, v_trackZetaDelta_3366_);
lean_ctor_set_uint8(v___x_3377_, sizeof(void*)*7 + 1, v_univApprox_3373_);
lean_ctor_set_uint8(v___x_3377_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3374_);
lean_ctor_set_uint8(v___x_3377_, sizeof(void*)*7 + 3, v_cacheInferType_3375_);
lean_inc(v_mvarId_3308_);
v___x_3378_ = l_Lean_MVarId_getType_x27(v_mvarId_3308_, v___x_3377_, v___y_3311_, v___y_3312_, v___y_3313_);
lean_dec_ref_known(v___x_3377_, 7);
v___y_3316_ = v___x_3378_;
goto v___jp_3315_;
}
else
{
lean_object* v___x_3379_; 
lean_inc(v_mvarId_3308_);
v___x_3379_ = l_Lean_MVarId_getType_x27(v_mvarId_3308_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_);
v___y_3316_ = v___x_3379_;
goto v___jp_3315_;
}
}
else
{
lean_object* v_a_3380_; lean_object* v___x_3382_; uint8_t v_isShared_3383_; uint8_t v_isSharedCheck_3387_; 
lean_dec_ref(v___y_3310_);
lean_dec(v_mvarId_3308_);
v_a_3380_ = lean_ctor_get(v___x_3360_, 0);
v_isSharedCheck_3387_ = !lean_is_exclusive(v___x_3360_);
if (v_isSharedCheck_3387_ == 0)
{
v___x_3382_ = v___x_3360_;
v_isShared_3383_ = v_isSharedCheck_3387_;
goto v_resetjp_3381_;
}
else
{
lean_inc(v_a_3380_);
lean_dec(v___x_3360_);
v___x_3382_ = lean_box(0);
v_isShared_3383_ = v_isSharedCheck_3387_;
goto v_resetjp_3381_;
}
v_resetjp_3381_:
{
lean_object* v___x_3385_; 
if (v_isShared_3383_ == 0)
{
v___x_3385_ = v___x_3382_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v_a_3380_);
v___x_3385_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
return v___x_3385_;
}
}
}
v___jp_3315_:
{
if (lean_obj_tag(v___y_3316_) == 0)
{
lean_object* v_a_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; uint8_t v___x_3320_; 
v_a_3317_ = lean_ctor_get(v___y_3316_, 0);
lean_inc(v_a_3317_);
lean_dec_ref_known(v___y_3316_, 1);
v___x_3318_ = ((lean_object*)(l_Lean_MVarId_proofIrrelHeq___lam__0___closed__1));
v___x_3319_ = lean_unsigned_to_nat(4u);
v___x_3320_ = l_Lean_Expr_isAppOfArity(v_a_3317_, v___x_3318_, v___x_3319_);
if (v___x_3320_ == 0)
{
lean_object* v___x_3321_; lean_object* v___x_3322_; 
lean_dec(v_a_3317_);
lean_dec(v_mvarId_3308_);
v___x_3321_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3322_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3321_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_);
lean_dec_ref(v___y_3310_);
return v___x_3322_;
}
else
{
lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; 
v___x_3323_ = l_Lean_Expr_appFn_x21(v_a_3317_);
v___x_3324_ = l_Lean_Expr_appFn_x21(v___x_3323_);
lean_dec_ref(v___x_3323_);
v___x_3325_ = l_Lean_Expr_appArg_x21(v___x_3324_);
lean_dec_ref(v___x_3324_);
v___x_3326_ = l_Lean_Expr_appArg_x21(v_a_3317_);
lean_dec(v_a_3317_);
v___x_3327_ = ((lean_object*)(l_Lean_MVarId_proofIrrelHeq___lam__0___closed__3));
v___x_3328_ = lean_unsigned_to_nat(2u);
v___x_3329_ = lean_mk_empty_array_with_capacity(v___x_3328_);
v___x_3330_ = lean_array_push(v___x_3329_, v___x_3325_);
v___x_3331_ = lean_array_push(v___x_3330_, v___x_3326_);
v___x_3332_ = l_Lean_Meta_mkAppM(v___x_3327_, v___x_3331_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_);
lean_dec_ref(v___y_3310_);
if (lean_obj_tag(v___x_3332_) == 0)
{
lean_object* v_a_3333_; lean_object* v___x_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3342_; 
v_a_3333_ = lean_ctor_get(v___x_3332_, 0);
lean_inc(v_a_3333_);
lean_dec_ref_known(v___x_3332_, 1);
v___x_3334_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_3308_, v_a_3333_, v___y_3311_);
v_isSharedCheck_3342_ = !lean_is_exclusive(v___x_3334_);
if (v_isSharedCheck_3342_ == 0)
{
lean_object* v_unused_3343_; 
v_unused_3343_ = lean_ctor_get(v___x_3334_, 0);
lean_dec(v_unused_3343_);
v___x_3336_ = v___x_3334_;
v_isShared_3337_ = v_isSharedCheck_3342_;
goto v_resetjp_3335_;
}
else
{
lean_dec(v___x_3334_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3342_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
lean_object* v___x_3338_; lean_object* v___x_3340_; 
v___x_3338_ = lean_box(v___x_3320_);
if (v_isShared_3337_ == 0)
{
lean_ctor_set(v___x_3336_, 0, v___x_3338_);
v___x_3340_ = v___x_3336_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v___x_3338_);
v___x_3340_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
return v___x_3340_;
}
}
}
else
{
lean_object* v_a_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3351_; 
lean_dec(v_mvarId_3308_);
v_a_3344_ = lean_ctor_get(v___x_3332_, 0);
v_isSharedCheck_3351_ = !lean_is_exclusive(v___x_3332_);
if (v_isSharedCheck_3351_ == 0)
{
v___x_3346_ = v___x_3332_;
v_isShared_3347_ = v_isSharedCheck_3351_;
goto v_resetjp_3345_;
}
else
{
lean_inc(v_a_3344_);
lean_dec(v___x_3332_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3351_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
lean_object* v___x_3349_; 
if (v_isShared_3347_ == 0)
{
v___x_3349_ = v___x_3346_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v_a_3344_);
v___x_3349_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3348_;
}
v_reusejp_3348_:
{
return v___x_3349_;
}
}
}
}
}
else
{
lean_object* v_a_3352_; lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3359_; 
lean_dec_ref(v___y_3310_);
lean_dec(v_mvarId_3308_);
v_a_3352_ = lean_ctor_get(v___y_3316_, 0);
v_isSharedCheck_3359_ = !lean_is_exclusive(v___y_3316_);
if (v_isSharedCheck_3359_ == 0)
{
v___x_3354_ = v___y_3316_;
v_isShared_3355_ = v_isSharedCheck_3359_;
goto v_resetjp_3353_;
}
else
{
lean_inc(v_a_3352_);
lean_dec(v___y_3316_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3359_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
lean_object* v___x_3357_; 
if (v_isShared_3355_ == 0)
{
v___x_3357_ = v___x_3354_;
goto v_reusejp_3356_;
}
else
{
lean_object* v_reuseFailAlloc_3358_; 
v_reuseFailAlloc_3358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3358_, 0, v_a_3352_);
v___x_3357_ = v_reuseFailAlloc_3358_;
goto v_reusejp_3356_;
}
v_reusejp_3356_:
{
return v___x_3357_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__0___boxed(lean_object* v_mvarId_3388_, lean_object* v___x_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_){
_start:
{
lean_object* v_res_3395_; 
v_res_3395_ = l_Lean_MVarId_proofIrrelHeq___lam__0(v_mvarId_3388_, v___x_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_);
lean_dec(v___y_3393_);
lean_dec_ref(v___y_3392_);
lean_dec(v___y_3391_);
return v_res_3395_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__1(lean_object* v___f_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_){
_start:
{
lean_object* v___x_3402_; 
v___x_3402_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v___f_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
if (lean_obj_tag(v___x_3402_) == 0)
{
lean_object* v_a_3403_; lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3416_; 
v_a_3403_ = lean_ctor_get(v___x_3402_, 0);
v_isSharedCheck_3416_ = !lean_is_exclusive(v___x_3402_);
if (v_isSharedCheck_3416_ == 0)
{
v___x_3405_ = v___x_3402_;
v_isShared_3406_ = v_isSharedCheck_3416_;
goto v_resetjp_3404_;
}
else
{
lean_inc(v_a_3403_);
lean_dec(v___x_3402_);
v___x_3405_ = lean_box(0);
v_isShared_3406_ = v_isSharedCheck_3416_;
goto v_resetjp_3404_;
}
v_resetjp_3404_:
{
if (lean_obj_tag(v_a_3403_) == 0)
{
uint8_t v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3410_; 
v___x_3407_ = 0;
v___x_3408_ = lean_box(v___x_3407_);
if (v_isShared_3406_ == 0)
{
lean_ctor_set(v___x_3405_, 0, v___x_3408_);
v___x_3410_ = v___x_3405_;
goto v_reusejp_3409_;
}
else
{
lean_object* v_reuseFailAlloc_3411_; 
v_reuseFailAlloc_3411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3411_, 0, v___x_3408_);
v___x_3410_ = v_reuseFailAlloc_3411_;
goto v_reusejp_3409_;
}
v_reusejp_3409_:
{
return v___x_3410_;
}
}
else
{
lean_object* v_val_3412_; lean_object* v___x_3414_; 
v_val_3412_ = lean_ctor_get(v_a_3403_, 0);
lean_inc(v_val_3412_);
lean_dec_ref_known(v_a_3403_, 1);
if (v_isShared_3406_ == 0)
{
lean_ctor_set(v___x_3405_, 0, v_val_3412_);
v___x_3414_ = v___x_3405_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v_val_3412_);
v___x_3414_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
return v___x_3414_;
}
}
}
}
else
{
lean_object* v_a_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3424_; 
v_a_3417_ = lean_ctor_get(v___x_3402_, 0);
v_isSharedCheck_3424_ = !lean_is_exclusive(v___x_3402_);
if (v_isSharedCheck_3424_ == 0)
{
v___x_3419_ = v___x_3402_;
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_a_3417_);
lean_dec(v___x_3402_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
lean_object* v___x_3422_; 
if (v_isShared_3420_ == 0)
{
v___x_3422_ = v___x_3419_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_a_3417_);
v___x_3422_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
return v___x_3422_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__1___boxed(lean_object* v___f_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_){
_start:
{
lean_object* v_res_3431_; 
v_res_3431_ = l_Lean_MVarId_proofIrrelHeq___lam__1(v___f_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec(v___y_3427_);
lean_dec_ref(v___y_3426_);
return v_res_3431_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq(lean_object* v_mvarId_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_){
_start:
{
lean_object* v___x_3441_; lean_object* v___f_3442_; lean_object* v___f_3443_; lean_object* v___x_3444_; 
v___x_3441_ = ((lean_object*)(l_Lean_MVarId_proofIrrelHeq___closed__1));
lean_inc(v_mvarId_3435_);
v___f_3442_ = lean_alloc_closure((void*)(l_Lean_MVarId_proofIrrelHeq___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3442_, 0, v_mvarId_3435_);
lean_closure_set(v___f_3442_, 1, v___x_3441_);
v___f_3443_ = lean_alloc_closure((void*)(l_Lean_MVarId_proofIrrelHeq___lam__1___boxed), 6, 1);
lean_closure_set(v___f_3443_, 0, v___f_3442_);
v___x_3444_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_3435_, v___f_3443_, v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_);
return v___x_3444_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___boxed(lean_object* v_mvarId_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_, lean_object* v_a_3450_){
_start:
{
lean_object* v_res_3451_; 
v_res_3451_ = l_Lean_MVarId_proofIrrelHeq(v_mvarId_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
lean_dec(v_a_3449_);
lean_dec_ref(v_a_3448_);
lean_dec(v_a_3447_);
lean_dec_ref(v_a_3446_);
return v_res_3451_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim___lam__0(lean_object* v_mvarId_3456_, lean_object* v___x_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_){
_start:
{
lean_object* v___y_3464_; lean_object* v___x_3507_; 
lean_inc(v_mvarId_3456_);
v___x_3507_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3456_, v___x_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_);
if (lean_obj_tag(v___x_3507_) == 0)
{
lean_object* v___x_3508_; uint8_t v_transparency_3509_; uint8_t v___x_3510_; uint8_t v___x_3511_; 
lean_dec_ref_known(v___x_3507_, 1);
v___x_3508_ = l_Lean_Meta_Context_config(v___y_3458_);
v_transparency_3509_ = lean_ctor_get_uint8(v___x_3508_, 9);
lean_dec_ref(v___x_3508_);
v___x_3510_ = 2;
v___x_3511_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3509_, v___x_3510_);
if (v___x_3511_ == 0)
{
lean_object* v_keyedConfig_3512_; uint8_t v_trackZetaDelta_3513_; lean_object* v_zetaDeltaSet_3514_; lean_object* v_lctx_3515_; lean_object* v_localInstances_3516_; lean_object* v_defEqCtx_x3f_3517_; lean_object* v_synthPendingDepth_3518_; lean_object* v_customCanUnfoldPredicate_x3f_3519_; uint8_t v_univApprox_3520_; uint8_t v_inTypeClassResolution_3521_; uint8_t v_cacheInferType_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; 
v_keyedConfig_3512_ = lean_ctor_get(v___y_3458_, 0);
v_trackZetaDelta_3513_ = lean_ctor_get_uint8(v___y_3458_, sizeof(void*)*7);
v_zetaDeltaSet_3514_ = lean_ctor_get(v___y_3458_, 1);
v_lctx_3515_ = lean_ctor_get(v___y_3458_, 2);
v_localInstances_3516_ = lean_ctor_get(v___y_3458_, 3);
v_defEqCtx_x3f_3517_ = lean_ctor_get(v___y_3458_, 4);
v_synthPendingDepth_3518_ = lean_ctor_get(v___y_3458_, 5);
v_customCanUnfoldPredicate_x3f_3519_ = lean_ctor_get(v___y_3458_, 6);
v_univApprox_3520_ = lean_ctor_get_uint8(v___y_3458_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3521_ = lean_ctor_get_uint8(v___y_3458_, sizeof(void*)*7 + 2);
v_cacheInferType_3522_ = lean_ctor_get_uint8(v___y_3458_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3512_);
v___x_3523_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3510_, v_keyedConfig_3512_);
lean_inc(v_customCanUnfoldPredicate_x3f_3519_);
lean_inc(v_synthPendingDepth_3518_);
lean_inc(v_defEqCtx_x3f_3517_);
lean_inc_ref(v_localInstances_3516_);
lean_inc_ref(v_lctx_3515_);
lean_inc(v_zetaDeltaSet_3514_);
v___x_3524_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3524_, 0, v___x_3523_);
lean_ctor_set(v___x_3524_, 1, v_zetaDeltaSet_3514_);
lean_ctor_set(v___x_3524_, 2, v_lctx_3515_);
lean_ctor_set(v___x_3524_, 3, v_localInstances_3516_);
lean_ctor_set(v___x_3524_, 4, v_defEqCtx_x3f_3517_);
lean_ctor_set(v___x_3524_, 5, v_synthPendingDepth_3518_);
lean_ctor_set(v___x_3524_, 6, v_customCanUnfoldPredicate_x3f_3519_);
lean_ctor_set_uint8(v___x_3524_, sizeof(void*)*7, v_trackZetaDelta_3513_);
lean_ctor_set_uint8(v___x_3524_, sizeof(void*)*7 + 1, v_univApprox_3520_);
lean_ctor_set_uint8(v___x_3524_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3521_);
lean_ctor_set_uint8(v___x_3524_, sizeof(void*)*7 + 3, v_cacheInferType_3522_);
lean_inc(v_mvarId_3456_);
v___x_3525_ = l_Lean_MVarId_getType_x27(v_mvarId_3456_, v___x_3524_, v___y_3459_, v___y_3460_, v___y_3461_);
lean_dec_ref_known(v___x_3524_, 7);
v___y_3464_ = v___x_3525_;
goto v___jp_3463_;
}
else
{
lean_object* v___x_3526_; 
lean_inc(v_mvarId_3456_);
v___x_3526_ = l_Lean_MVarId_getType_x27(v_mvarId_3456_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_);
v___y_3464_ = v___x_3526_;
goto v___jp_3463_;
}
}
else
{
lean_object* v_a_3527_; lean_object* v___x_3529_; uint8_t v_isShared_3530_; uint8_t v_isSharedCheck_3534_; 
lean_dec_ref(v___y_3458_);
lean_dec(v_mvarId_3456_);
v_a_3527_ = lean_ctor_get(v___x_3507_, 0);
v_isSharedCheck_3534_ = !lean_is_exclusive(v___x_3507_);
if (v_isSharedCheck_3534_ == 0)
{
v___x_3529_ = v___x_3507_;
v_isShared_3530_ = v_isSharedCheck_3534_;
goto v_resetjp_3528_;
}
else
{
lean_inc(v_a_3527_);
lean_dec(v___x_3507_);
v___x_3529_ = lean_box(0);
v_isShared_3530_ = v_isSharedCheck_3534_;
goto v_resetjp_3528_;
}
v_resetjp_3528_:
{
lean_object* v___x_3532_; 
if (v_isShared_3530_ == 0)
{
v___x_3532_ = v___x_3529_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v_a_3527_);
v___x_3532_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
return v___x_3532_;
}
}
}
v___jp_3463_:
{
if (lean_obj_tag(v___y_3464_) == 0)
{
lean_object* v_a_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; uint8_t v___x_3468_; 
v_a_3465_ = lean_ctor_get(v___y_3464_, 0);
lean_inc(v_a_3465_);
lean_dec_ref_known(v___y_3464_, 1);
v___x_3466_ = ((lean_object*)(l_Lean_MVarId_propext___lam__0___closed__4));
v___x_3467_ = lean_unsigned_to_nat(3u);
v___x_3468_ = l_Lean_Expr_isAppOfArity(v_a_3465_, v___x_3466_, v___x_3467_);
if (v___x_3468_ == 0)
{
lean_object* v___x_3469_; lean_object* v___x_3470_; 
lean_dec(v_a_3465_);
lean_dec(v_mvarId_3456_);
v___x_3469_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3470_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3469_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_);
lean_dec_ref(v___y_3458_);
return v___x_3470_;
}
else
{
lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; 
v___x_3471_ = l_Lean_Expr_appFn_x21(v_a_3465_);
v___x_3472_ = l_Lean_Expr_appArg_x21(v___x_3471_);
lean_dec_ref(v___x_3471_);
v___x_3473_ = l_Lean_Expr_appArg_x21(v_a_3465_);
lean_dec(v_a_3465_);
v___x_3474_ = ((lean_object*)(l_Lean_MVarId_subsingletonElim___lam__0___closed__1));
v___x_3475_ = lean_unsigned_to_nat(2u);
v___x_3476_ = lean_mk_empty_array_with_capacity(v___x_3475_);
v___x_3477_ = lean_array_push(v___x_3476_, v___x_3472_);
v___x_3478_ = lean_array_push(v___x_3477_, v___x_3473_);
v___x_3479_ = l_Lean_Meta_mkAppM(v___x_3474_, v___x_3478_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_);
lean_dec_ref(v___y_3458_);
if (lean_obj_tag(v___x_3479_) == 0)
{
lean_object* v_a_3480_; lean_object* v___x_3481_; lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3489_; 
v_a_3480_ = lean_ctor_get(v___x_3479_, 0);
lean_inc(v_a_3480_);
lean_dec_ref_known(v___x_3479_, 1);
v___x_3481_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_3456_, v_a_3480_, v___y_3459_);
v_isSharedCheck_3489_ = !lean_is_exclusive(v___x_3481_);
if (v_isSharedCheck_3489_ == 0)
{
lean_object* v_unused_3490_; 
v_unused_3490_ = lean_ctor_get(v___x_3481_, 0);
lean_dec(v_unused_3490_);
v___x_3483_ = v___x_3481_;
v_isShared_3484_ = v_isSharedCheck_3489_;
goto v_resetjp_3482_;
}
else
{
lean_dec(v___x_3481_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3489_;
goto v_resetjp_3482_;
}
v_resetjp_3482_:
{
lean_object* v___x_3485_; lean_object* v___x_3487_; 
v___x_3485_ = lean_box(v___x_3468_);
if (v_isShared_3484_ == 0)
{
lean_ctor_set(v___x_3483_, 0, v___x_3485_);
v___x_3487_ = v___x_3483_;
goto v_reusejp_3486_;
}
else
{
lean_object* v_reuseFailAlloc_3488_; 
v_reuseFailAlloc_3488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3488_, 0, v___x_3485_);
v___x_3487_ = v_reuseFailAlloc_3488_;
goto v_reusejp_3486_;
}
v_reusejp_3486_:
{
return v___x_3487_;
}
}
}
else
{
lean_object* v_a_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3498_; 
lean_dec(v_mvarId_3456_);
v_a_3491_ = lean_ctor_get(v___x_3479_, 0);
v_isSharedCheck_3498_ = !lean_is_exclusive(v___x_3479_);
if (v_isSharedCheck_3498_ == 0)
{
v___x_3493_ = v___x_3479_;
v_isShared_3494_ = v_isSharedCheck_3498_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_a_3491_);
lean_dec(v___x_3479_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3498_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v___x_3496_; 
if (v_isShared_3494_ == 0)
{
v___x_3496_ = v___x_3493_;
goto v_reusejp_3495_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v_a_3491_);
v___x_3496_ = v_reuseFailAlloc_3497_;
goto v_reusejp_3495_;
}
v_reusejp_3495_:
{
return v___x_3496_;
}
}
}
}
}
else
{
lean_object* v_a_3499_; lean_object* v___x_3501_; uint8_t v_isShared_3502_; uint8_t v_isSharedCheck_3506_; 
lean_dec_ref(v___y_3458_);
lean_dec(v_mvarId_3456_);
v_a_3499_ = lean_ctor_get(v___y_3464_, 0);
v_isSharedCheck_3506_ = !lean_is_exclusive(v___y_3464_);
if (v_isSharedCheck_3506_ == 0)
{
v___x_3501_ = v___y_3464_;
v_isShared_3502_ = v_isSharedCheck_3506_;
goto v_resetjp_3500_;
}
else
{
lean_inc(v_a_3499_);
lean_dec(v___y_3464_);
v___x_3501_ = lean_box(0);
v_isShared_3502_ = v_isSharedCheck_3506_;
goto v_resetjp_3500_;
}
v_resetjp_3500_:
{
lean_object* v___x_3504_; 
if (v_isShared_3502_ == 0)
{
v___x_3504_ = v___x_3501_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v_a_3499_);
v___x_3504_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
return v___x_3504_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim___lam__0___boxed(lean_object* v_mvarId_3535_, lean_object* v___x_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_){
_start:
{
lean_object* v_res_3542_; 
v_res_3542_ = l_Lean_MVarId_subsingletonElim___lam__0(v_mvarId_3535_, v___x_3536_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_);
lean_dec(v___y_3540_);
lean_dec_ref(v___y_3539_);
lean_dec(v___y_3538_);
return v_res_3542_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim(lean_object* v_mvarId_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_){
_start:
{
lean_object* v___x_3552_; lean_object* v___f_3553_; lean_object* v___f_3554_; lean_object* v___x_3555_; 
v___x_3552_ = ((lean_object*)(l_Lean_MVarId_subsingletonElim___closed__1));
lean_inc(v_mvarId_3546_);
v___f_3553_ = lean_alloc_closure((void*)(l_Lean_MVarId_subsingletonElim___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3553_, 0, v_mvarId_3546_);
lean_closure_set(v___f_3553_, 1, v___x_3552_);
v___f_3554_ = lean_alloc_closure((void*)(l_Lean_MVarId_proofIrrelHeq___lam__1___boxed), 6, 1);
lean_closure_set(v___f_3554_, 0, v___f_3553_);
v___x_3555_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_3546_, v___f_3554_, v_a_3547_, v_a_3548_, v_a_3549_, v_a_3550_);
return v___x_3555_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim___boxed(lean_object* v_mvarId_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_){
_start:
{
lean_object* v_res_3562_; 
v_res_3562_ = l_Lean_MVarId_subsingletonElim(v_mvarId_3556_, v_a_3557_, v_a_3558_, v_a_3559_, v_a_3560_);
lean_dec(v_a_3560_);
lean_dec_ref(v_a_3559_);
lean_dec(v_a_3558_);
lean_dec_ref(v_a_3557_);
return v_res_3562_;
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
