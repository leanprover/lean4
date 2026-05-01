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
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l_Lean_MVarId_getType_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Meta_getExpectedNumArgsAux___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Meta_getExpectedNumArgsAux___closed__1;
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
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_synthAppInstances_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_synthAppInstances_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_synthAppInstances(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_synthAppInstances___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_MVarId_propext___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_MVarId_propext___lam__0___closed__0 = (const lean_object*)&l_Lean_MVarId_propext___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_propext___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_propext___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_MVarId_propext___lam__0___closed__1 = (const lean_object*)&l_Lean_MVarId_propext___lam__0___closed__1_value;
static const lean_string_object l_Lean_MVarId_propext___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "propext"};
static const lean_object* l_Lean_MVarId_propext___lam__0___closed__2 = (const lean_object*)&l_Lean_MVarId_propext___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_MVarId_propext___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_propext___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(53, 150, 49, 30, 125, 3, 39, 172)}};
static const lean_object* l_Lean_MVarId_propext___lam__0___closed__3 = (const lean_object*)&l_Lean_MVarId_propext___lam__0___closed__3_value;
static lean_once_cell_t l_Lean_MVarId_propext___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_propext___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_propext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0;
static const lean_string_object l_Lean_MVarId_proofIrrelHeq___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "HEq"};
static const lean_object* l_Lean_MVarId_proofIrrelHeq___lam__0___closed__1 = (const lean_object*)&l_Lean_MVarId_proofIrrelHeq___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_MVarId_proofIrrelHeq___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_proofIrrelHeq___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(67, 180, 169, 191, 74, 196, 152, 188)}};
static const lean_object* l_Lean_MVarId_proofIrrelHeq___lam__0___closed__2 = (const lean_object*)&l_Lean_MVarId_proofIrrelHeq___lam__0___closed__2_value;
static const lean_string_object l_Lean_MVarId_proofIrrelHeq___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "proof_irrel_heq"};
static const lean_object* l_Lean_MVarId_proofIrrelHeq___lam__0___closed__3 = (const lean_object*)&l_Lean_MVarId_proofIrrelHeq___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_MVarId_proofIrrelHeq___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_proofIrrelHeq___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(180, 105, 248, 247, 187, 48, 190, 226)}};
static const lean_object* l_Lean_MVarId_proofIrrelHeq___lam__0___closed__4 = (const lean_object*)&l_Lean_MVarId_proofIrrelHeq___lam__0___closed__4_value;
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
static uint64_t _init_l_Lean_Meta_getExpectedNumArgsAux___closed__1(void){
_start:
{
uint8_t v___x_104_; uint64_t v___x_105_; 
v___x_104_ = 1;
v___x_105_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getExpectedNumArgsAux(lean_object* v_e_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_){
_start:
{
lean_object* v___x_112_; uint8_t v_foApprox_113_; uint8_t v_ctxApprox_114_; uint8_t v_quasiPatternApprox_115_; uint8_t v_constApprox_116_; uint8_t v_isDefEqStuckEx_117_; uint8_t v_unificationHints_118_; uint8_t v_proofIrrelevance_119_; uint8_t v_assignSyntheticOpaque_120_; uint8_t v_offsetCnstrs_121_; uint8_t v_etaStruct_122_; uint8_t v_univApprox_123_; uint8_t v_iota_124_; uint8_t v_beta_125_; uint8_t v_proj_126_; uint8_t v_zeta_127_; uint8_t v_zetaDelta_128_; uint8_t v_zetaUnused_129_; uint8_t v_zetaHave_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_159_; 
v___x_112_ = l_Lean_Meta_Context_config(v_a_107_);
v_foApprox_113_ = lean_ctor_get_uint8(v___x_112_, 0);
v_ctxApprox_114_ = lean_ctor_get_uint8(v___x_112_, 1);
v_quasiPatternApprox_115_ = lean_ctor_get_uint8(v___x_112_, 2);
v_constApprox_116_ = lean_ctor_get_uint8(v___x_112_, 3);
v_isDefEqStuckEx_117_ = lean_ctor_get_uint8(v___x_112_, 4);
v_unificationHints_118_ = lean_ctor_get_uint8(v___x_112_, 5);
v_proofIrrelevance_119_ = lean_ctor_get_uint8(v___x_112_, 6);
v_assignSyntheticOpaque_120_ = lean_ctor_get_uint8(v___x_112_, 7);
v_offsetCnstrs_121_ = lean_ctor_get_uint8(v___x_112_, 8);
v_etaStruct_122_ = lean_ctor_get_uint8(v___x_112_, 10);
v_univApprox_123_ = lean_ctor_get_uint8(v___x_112_, 11);
v_iota_124_ = lean_ctor_get_uint8(v___x_112_, 12);
v_beta_125_ = lean_ctor_get_uint8(v___x_112_, 13);
v_proj_126_ = lean_ctor_get_uint8(v___x_112_, 14);
v_zeta_127_ = lean_ctor_get_uint8(v___x_112_, 15);
v_zetaDelta_128_ = lean_ctor_get_uint8(v___x_112_, 16);
v_zetaUnused_129_ = lean_ctor_get_uint8(v___x_112_, 17);
v_zetaHave_130_ = lean_ctor_get_uint8(v___x_112_, 18);
v_isSharedCheck_159_ = !lean_is_exclusive(v___x_112_);
if (v_isSharedCheck_159_ == 0)
{
v___x_132_ = v___x_112_;
v_isShared_133_ = v_isSharedCheck_159_;
goto v_resetjp_131_;
}
else
{
lean_dec(v___x_112_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_159_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
uint8_t v_trackZetaDelta_134_; lean_object* v_zetaDeltaSet_135_; lean_object* v_lctx_136_; lean_object* v_localInstances_137_; lean_object* v_defEqCtx_x3f_138_; lean_object* v_synthPendingDepth_139_; lean_object* v_canUnfold_x3f_140_; uint8_t v_univApprox_141_; uint8_t v_inTypeClassResolution_142_; uint8_t v_cacheInferType_143_; uint8_t v___x_144_; lean_object* v_config_146_; 
v_trackZetaDelta_134_ = lean_ctor_get_uint8(v_a_107_, sizeof(void*)*7);
v_zetaDeltaSet_135_ = lean_ctor_get(v_a_107_, 1);
v_lctx_136_ = lean_ctor_get(v_a_107_, 2);
v_localInstances_137_ = lean_ctor_get(v_a_107_, 3);
v_defEqCtx_x3f_138_ = lean_ctor_get(v_a_107_, 4);
v_synthPendingDepth_139_ = lean_ctor_get(v_a_107_, 5);
v_canUnfold_x3f_140_ = lean_ctor_get(v_a_107_, 6);
v_univApprox_141_ = lean_ctor_get_uint8(v_a_107_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_142_ = lean_ctor_get_uint8(v_a_107_, sizeof(void*)*7 + 2);
v_cacheInferType_143_ = lean_ctor_get_uint8(v_a_107_, sizeof(void*)*7 + 3);
v___x_144_ = 1;
if (v_isShared_133_ == 0)
{
v_config_146_ = v___x_132_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_158_, 0, v_foApprox_113_);
lean_ctor_set_uint8(v_reuseFailAlloc_158_, 1, v_ctxApprox_114_);
lean_ctor_set_uint8(v_reuseFailAlloc_158_, 2, v_quasiPatternApprox_115_);
lean_ctor_set_uint8(v_reuseFailAlloc_158_, 3, v_constApprox_116_);
lean_ctor_set_uint8(v_reuseFailAlloc_158_, 4, v_isDefEqStuckEx_117_);
lean_ctor_set_uint8(v_reuseFailAlloc_158_, 5, v_unificationHints_118_);
lean_ctor_set_uint8(v_reuseFailAlloc_158_, 6, v_proofIrrelevance_119_);
lean_ctor_set_uint8(v_reuseFailAlloc_158_, 7, v_assignSyntheticOpaque_120_);
lean_ctor_set_uint8(v_reuseFailAlloc_158_, 8, v_offsetCnstrs_121_);
lean_ctor_set_uint8(v_reuseFailAlloc_158_, 10, v_etaStruct_122_);
lean_ctor_set_uint8(v_reuseFailAlloc_158_, 11, v_univApprox_123_);
lean_ctor_set_uint8(v_reuseFailAlloc_158_, 12, v_iota_124_);
lean_ctor_set_uint8(v_reuseFailAlloc_158_, 13, v_beta_125_);
lean_ctor_set_uint8(v_reuseFailAlloc_158_, 14, v_proj_126_);
lean_ctor_set_uint8(v_reuseFailAlloc_158_, 15, v_zeta_127_);
lean_ctor_set_uint8(v_reuseFailAlloc_158_, 16, v_zetaDelta_128_);
lean_ctor_set_uint8(v_reuseFailAlloc_158_, 17, v_zetaUnused_129_);
lean_ctor_set_uint8(v_reuseFailAlloc_158_, 18, v_zetaHave_130_);
v_config_146_ = v_reuseFailAlloc_158_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
uint64_t v___x_147_; uint64_t v___x_148_; uint64_t v___x_149_; lean_object* v___f_150_; uint8_t v___x_151_; uint64_t v___x_152_; uint64_t v___x_153_; uint64_t v_key_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
lean_ctor_set_uint8(v_config_146_, 9, v___x_144_);
v___x_147_ = l_Lean_Meta_Context_configKey(v_a_107_);
v___x_148_ = 2ULL;
v___x_149_ = lean_uint64_shift_right(v___x_147_, v___x_148_);
v___f_150_ = ((lean_object*)(l_Lean_Meta_getExpectedNumArgsAux___closed__0));
v___x_151_ = 0;
v___x_152_ = lean_uint64_shift_left(v___x_149_, v___x_148_);
v___x_153_ = lean_uint64_once(&l_Lean_Meta_getExpectedNumArgsAux___closed__1, &l_Lean_Meta_getExpectedNumArgsAux___closed__1_once, _init_l_Lean_Meta_getExpectedNumArgsAux___closed__1);
v_key_154_ = lean_uint64_lor(v___x_152_, v___x_153_);
v___x_155_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_155_, 0, v_config_146_);
lean_ctor_set_uint64(v___x_155_, sizeof(void*)*1, v_key_154_);
lean_inc(v_canUnfold_x3f_140_);
lean_inc(v_synthPendingDepth_139_);
lean_inc(v_defEqCtx_x3f_138_);
lean_inc_ref(v_localInstances_137_);
lean_inc_ref(v_lctx_136_);
lean_inc(v_zetaDeltaSet_135_);
v___x_156_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_156_, 0, v___x_155_);
lean_ctor_set(v___x_156_, 1, v_zetaDeltaSet_135_);
lean_ctor_set(v___x_156_, 2, v_lctx_136_);
lean_ctor_set(v___x_156_, 3, v_localInstances_137_);
lean_ctor_set(v___x_156_, 4, v_defEqCtx_x3f_138_);
lean_ctor_set(v___x_156_, 5, v_synthPendingDepth_139_);
lean_ctor_set(v___x_156_, 6, v_canUnfold_x3f_140_);
lean_ctor_set_uint8(v___x_156_, sizeof(void*)*7, v_trackZetaDelta_134_);
lean_ctor_set_uint8(v___x_156_, sizeof(void*)*7 + 1, v_univApprox_141_);
lean_ctor_set_uint8(v___x_156_, sizeof(void*)*7 + 2, v_inTypeClassResolution_142_);
lean_ctor_set_uint8(v___x_156_, sizeof(void*)*7 + 3, v_cacheInferType_143_);
v___x_157_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg(v_e_106_, v___f_150_, v___x_151_, v___x_151_, v___x_156_, v_a_108_, v_a_109_, v_a_110_);
lean_dec_ref(v___x_156_);
return v___x_157_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getExpectedNumArgsAux___boxed(lean_object* v_e_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Lean_Meta_getExpectedNumArgsAux(v_e_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_);
lean_dec(v_a_164_);
lean_dec_ref(v_a_163_);
lean_dec(v_a_162_);
lean_dec_ref(v_a_161_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getExpectedNumArgs(lean_object* v_e_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = l_Lean_Meta_getExpectedNumArgsAux(v_e_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_);
if (lean_obj_tag(v___x_173_) == 0)
{
lean_object* v_a_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_182_; 
v_a_174_ = lean_ctor_get(v___x_173_, 0);
v_isSharedCheck_182_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_182_ == 0)
{
v___x_176_ = v___x_173_;
v_isShared_177_ = v_isSharedCheck_182_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_a_174_);
lean_dec(v___x_173_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_182_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v_fst_178_; lean_object* v___x_180_; 
v_fst_178_ = lean_ctor_get(v_a_174_, 0);
lean_inc(v_fst_178_);
lean_dec(v_a_174_);
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 0, v_fst_178_);
v___x_180_ = v___x_176_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_fst_178_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
return v___x_180_;
}
}
}
else
{
lean_object* v_a_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_190_; 
v_a_183_ = lean_ctor_get(v___x_173_, 0);
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_190_ == 0)
{
v___x_185_ = v___x_173_;
v_isShared_186_ = v_isSharedCheck_190_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_a_183_);
lean_dec(v___x_173_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_190_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_188_; 
if (v_isShared_186_ == 0)
{
v___x_188_ = v___x_185_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_a_183_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getExpectedNumArgs___boxed(lean_object* v_e_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean_Meta_getExpectedNumArgs(v_e_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_);
lean_dec(v_a_195_);
lean_dec_ref(v_a_194_);
lean_dec(v_a_193_);
lean_dec_ref(v_a_192_);
return v_res_197_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__0));
v___x_200_ = l_Lean_stringToMessageData(v___x_199_);
return v___x_200_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__2));
v___x_203_ = l_Lean_stringToMessageData(v___x_202_);
return v___x_203_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_205_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__4));
v___x_206_ = l_Lean_stringToMessageData(v___x_205_);
return v___x_206_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__7));
v___x_211_ = l_Lean_MessageData_ofFormat(v___x_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0(lean_object* v___y_214_, lean_object* v_targetType_215_, lean_object* v___y_216_, lean_object* v_term_x3f_217_, lean_object* v_conclusionType_x3f_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l_Lean_Meta_addPPExplicitToExposeDiff(v___y_214_, v_targetType_215_, v___y_219_, v___y_220_, v___y_221_, v___y_222_);
if (lean_obj_tag(v___x_224_) == 0)
{
lean_object* v_a_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_266_; 
v_a_225_ = lean_ctor_get(v___x_224_, 0);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_224_);
if (v_isSharedCheck_266_ == 0)
{
v___x_227_ = v___x_224_;
v_isShared_228_ = v_isSharedCheck_266_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_a_225_);
lean_dec(v___x_224_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_266_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v_fst_229_; lean_object* v_snd_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_265_; 
v_fst_229_ = lean_ctor_get(v_a_225_, 0);
v_snd_230_ = lean_ctor_get(v_a_225_, 1);
v_isSharedCheck_265_ = !lean_is_exclusive(v_a_225_);
if (v_isSharedCheck_265_ == 0)
{
v___x_232_ = v_a_225_;
v_isShared_233_ = v_isSharedCheck_265_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_snd_230_);
lean_inc(v_fst_229_);
lean_dec(v_a_225_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_265_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___y_235_; lean_object* v___y_236_; lean_object* v___y_237_; lean_object* v___y_253_; 
if (lean_obj_tag(v_conclusionType_x3f_218_) == 0)
{
lean_object* v___x_263_; 
v___x_263_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__9));
v___y_253_ = v___x_263_;
goto v___jp_252_;
}
else
{
lean_object* v___x_264_; 
v___x_264_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__10));
v___y_253_ = v___x_264_;
goto v___jp_252_;
}
v___jp_234_:
{
lean_object* v___x_239_; 
if (v_isShared_233_ == 0)
{
lean_ctor_set_tag(v___x_232_, 7);
lean_ctor_set(v___x_232_, 1, v___y_237_);
lean_ctor_set(v___x_232_, 0, v___y_235_);
v___x_239_ = v___x_232_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v___y_235_);
lean_ctor_set(v_reuseFailAlloc_251_, 1, v___y_237_);
v___x_239_ = v_reuseFailAlloc_251_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_249_; 
v___x_240_ = l_Lean_indentExpr(v_fst_229_);
v___x_241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_241_, 0, v___x_239_);
lean_ctor_set(v___x_241_, 1, v___x_240_);
v___x_242_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__1);
v___x_243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_241_);
lean_ctor_set(v___x_243_, 1, v___x_242_);
v___x_244_ = l_Lean_indentExpr(v_snd_230_);
v___x_245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_245_, 0, v___x_243_);
lean_ctor_set(v___x_245_, 1, v___x_244_);
v___x_246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
lean_ctor_set(v___x_246_, 1, v___y_216_);
v___x_247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
lean_ctor_set(v___x_247_, 1, v___y_236_);
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 0, v___x_247_);
v___x_249_ = v___x_227_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v___x_247_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
v___jp_252_:
{
lean_object* v___x_254_; 
lean_inc(v_snd_230_);
lean_inc(v_fst_229_);
v___x_254_ = l_Lean_Meta_mkUnfoldAxiomsNote(v_fst_229_, v_snd_230_, v___y_219_, v___y_220_, v___y_221_, v___y_222_);
if (lean_obj_tag(v___x_254_) == 0)
{
lean_object* v_a_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v_a_255_ = lean_ctor_get(v___x_254_, 0);
lean_inc(v_a_255_);
lean_dec_ref(v___x_254_);
v___x_256_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__3);
lean_inc_ref(v___y_253_);
v___x_257_ = l_Lean_stringToMessageData(v___y_253_);
v___x_258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_256_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
v___x_259_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__5, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__5_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__5);
v___x_260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_258_);
lean_ctor_set(v___x_260_, 1, v___x_259_);
if (lean_obj_tag(v_term_x3f_217_) == 0)
{
lean_object* v___x_261_; 
v___x_261_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8);
v___y_235_ = v___x_260_;
v___y_236_ = v_a_255_;
v___y_237_ = v___x_261_;
goto v___jp_234_;
}
else
{
lean_object* v_val_262_; 
v_val_262_ = lean_ctor_get(v_term_x3f_217_, 0);
lean_inc(v_val_262_);
lean_dec_ref(v_term_x3f_217_);
v___y_235_ = v___x_260_;
v___y_236_ = v_a_255_;
v___y_237_ = v_val_262_;
goto v___jp_234_;
}
}
else
{
lean_del_object(v___x_232_);
lean_dec(v_snd_230_);
lean_dec(v_fst_229_);
lean_del_object(v___x_227_);
lean_dec(v_term_x3f_217_);
lean_dec_ref(v___y_216_);
return v___x_254_;
}
}
}
}
}
else
{
lean_object* v_a_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_274_; 
lean_dec(v_term_x3f_217_);
lean_dec_ref(v___y_216_);
v_a_267_ = lean_ctor_get(v___x_224_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_224_);
if (v_isSharedCheck_274_ == 0)
{
v___x_269_ = v___x_224_;
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_a_267_);
lean_dec(v___x_224_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_272_; 
if (v_isShared_270_ == 0)
{
v___x_272_ = v___x_269_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_a_267_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___boxed(lean_object* v___y_275_, lean_object* v_targetType_276_, lean_object* v___y_277_, lean_object* v_term_x3f_278_, lean_object* v_conclusionType_x3f_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0(v___y_275_, v_targetType_276_, v___y_277_, v_term_x3f_278_, v_conclusionType_x3f_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
lean_dec(v___y_281_);
lean_dec_ref(v___y_280_);
lean_dec(v_conclusionType_x3f_279_);
return v_res_285_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__3(void){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_290_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__2));
v___x_291_ = l_Lean_stringToMessageData(v___x_290_);
return v___x_291_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__5(void){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_293_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__4));
v___x_294_ = l_Lean_stringToMessageData(v___x_293_);
return v___x_294_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__7(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_296_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__6));
v___x_297_ = l_Lean_stringToMessageData(v___x_296_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(lean_object* v_mvarId_298_, lean_object* v_eType_299_, lean_object* v_conclusionType_x3f_300_, lean_object* v_targetType_301_, lean_object* v_term_x3f_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_){
_start:
{
lean_object* v___x_308_; lean_object* v___y_310_; lean_object* v___y_311_; lean_object* v___y_321_; lean_object* v___y_322_; lean_object* v___y_323_; lean_object* v___y_331_; 
v___x_308_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1));
if (lean_obj_tag(v_conclusionType_x3f_300_) == 0)
{
lean_inc_ref(v_eType_299_);
v___y_331_ = v_eType_299_;
goto v___jp_330_;
}
else
{
lean_object* v_val_336_; 
v_val_336_ = lean_ctor_get(v_conclusionType_x3f_300_, 0);
lean_inc(v_val_336_);
v___y_331_ = v_val_336_;
goto v___jp_330_;
}
v___jp_309_:
{
lean_object* v___f_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
lean_inc_ref(v_targetType_301_);
v___f_312_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_312_, 0, v___y_310_);
lean_closure_set(v___f_312_, 1, v_targetType_301_);
lean_closure_set(v___f_312_, 2, v___y_311_);
lean_closure_set(v___f_312_, 3, v_term_x3f_302_);
lean_closure_set(v___f_312_, 4, v_conclusionType_x3f_300_);
v___x_313_ = lean_unsigned_to_nat(2u);
v___x_314_ = lean_mk_empty_array_with_capacity(v___x_313_);
v___x_315_ = lean_array_push(v___x_314_, v_eType_299_);
v___x_316_ = lean_array_push(v___x_315_, v_targetType_301_);
v___x_317_ = l_Lean_MessageData_ofLazyM(v___f_312_, v___x_316_);
v___x_318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
v___x_319_ = l_Lean_Meta_throwTacticEx___redArg(v___x_308_, v_mvarId_298_, v___x_318_, v_a_303_, v_a_304_, v_a_305_, v_a_306_);
return v___x_319_;
}
v___jp_320_:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
lean_inc_ref(v___y_322_);
v___x_324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_324_, 0, v___y_322_);
lean_ctor_set(v___x_324_, 1, v___y_323_);
v___x_325_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__3, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__3);
v___x_326_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_326_, 0, v___x_324_);
lean_ctor_set(v___x_326_, 1, v___x_325_);
lean_inc_ref(v_eType_299_);
v___x_327_ = l_Lean_indentExpr(v_eType_299_);
v___x_328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_328_, 0, v___x_326_);
lean_ctor_set(v___x_328_, 1, v___x_327_);
v___x_329_ = l_Lean_MessageData_note(v___x_328_);
v___y_310_ = v___y_321_;
v___y_311_ = v___x_329_;
goto v___jp_309_;
}
v___jp_330_:
{
if (lean_obj_tag(v_conclusionType_x3f_300_) == 0)
{
lean_object* v___x_332_; 
v___x_332_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__5, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__5_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__5);
v___y_310_ = v___y_331_;
v___y_311_ = v___x_332_;
goto v___jp_309_;
}
else
{
lean_object* v___x_333_; 
v___x_333_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__7, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__7);
if (lean_obj_tag(v_term_x3f_302_) == 0)
{
lean_object* v___x_334_; 
v___x_334_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8, &l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8);
v___y_321_ = v___y_331_;
v___y_322_ = v___x_333_;
v___y_323_ = v___x_334_;
goto v___jp_320_;
}
else
{
lean_object* v_val_335_; 
v_val_335_ = lean_ctor_get(v_term_x3f_302_, 0);
lean_inc(v_val_335_);
v___y_321_ = v___y_331_;
v___y_322_ = v___x_333_;
v___y_323_ = v_val_335_;
goto v___jp_320_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___boxed(lean_object* v_mvarId_337_, lean_object* v_eType_338_, lean_object* v_conclusionType_x3f_339_, lean_object* v_targetType_340_, lean_object* v_term_x3f_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(v_mvarId_337_, v_eType_338_, v_conclusionType_x3f_339_, v_targetType_340_, v_term_x3f_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_);
lean_dec(v_a_345_);
lean_dec_ref(v_a_344_);
lean_dec(v_a_343_);
lean_dec_ref(v_a_342_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError(lean_object* v_00_u03b1_348_, lean_object* v_mvarId_349_, lean_object* v_eType_350_, lean_object* v_conclusionType_x3f_351_, lean_object* v_targetType_352_, lean_object* v_term_x3f_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(v_mvarId_349_, v_eType_350_, v_conclusionType_x3f_351_, v_targetType_352_, v_term_x3f_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___boxed(lean_object* v_00_u03b1_360_, lean_object* v_mvarId_361_, lean_object* v_eType_362_, lean_object* v_conclusionType_x3f_363_, lean_object* v_targetType_364_, lean_object* v_term_x3f_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError(v_00_u03b1_360_, v_mvarId_361_, v_eType_362_, v_conclusionType_x3f_363_, v_targetType_364_, v_term_x3f_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_);
lean_dec(v_a_369_);
lean_dec_ref(v_a_368_);
lean_dec(v_a_367_);
lean_dec_ref(v_a_366_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0(lean_object* v_a_372_, lean_object* v_snd_373_, lean_object* v_fst_374_, lean_object* v_____r_375_, uint8_t v_progressAfterEx_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_382_, 0, v_a_372_);
v___x_383_ = lean_box(v_progressAfterEx_376_);
v___x_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_384_, 0, v___x_383_);
lean_ctor_set(v___x_384_, 1, v_snd_373_);
v___x_385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_385_, 0, v_fst_374_);
lean_ctor_set(v___x_385_, 1, v___x_384_);
v___x_386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_382_);
lean_ctor_set(v___x_386_, 1, v___x_385_);
v___x_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0___boxed(lean_object* v_a_388_, lean_object* v_snd_389_, lean_object* v_fst_390_, lean_object* v_____r_391_, lean_object* v_progressAfterEx_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
uint8_t v_progressAfterEx_boxed_398_; lean_object* v_res_399_; 
v_progressAfterEx_boxed_398_ = lean_unbox(v_progressAfterEx_392_);
v_res_399_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0(v_a_388_, v_snd_389_, v_fst_390_, v_____r_391_, v_progressAfterEx_boxed_398_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
return v_res_399_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__2(void){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_403_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__1));
v___x_404_ = l_Lean_MessageData_ofFormat(v___x_403_);
return v___x_404_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__2);
v___x_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0(uint8_t v_allowSynthFailures_407_, lean_object* v_tacticName_408_, lean_object* v_mvarId_409_, lean_object* v_as_410_, size_t v_sz_411_, size_t v_i_412_, lean_object* v_b_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
lean_object* v_a_420_; lean_object* v_fst_425_; lean_object* v_fst_426_; lean_object* v_snd_427_; uint8_t v___x_430_; 
v___x_430_ = lean_usize_dec_lt(v_i_412_, v_sz_411_);
if (v___x_430_ == 0)
{
lean_object* v___x_431_; 
lean_dec(v_mvarId_409_);
lean_dec(v_tacticName_408_);
v___x_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_431_, 0, v_b_413_);
return v___x_431_;
}
else
{
lean_object* v_a_432_; lean_object* v___x_433_; 
v_a_432_ = lean_array_uget_borrowed(v_as_410_, v_i_412_);
lean_inc(v___y_417_);
lean_inc_ref(v___y_416_);
lean_inc(v___y_415_);
lean_inc_ref(v___y_414_);
lean_inc(v_a_432_);
v___x_433_ = lean_infer_type(v_a_432_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v_snd_434_; lean_object* v_a_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_528_; 
v_snd_434_ = lean_ctor_get(v_b_413_, 1);
lean_inc(v_snd_434_);
v_a_435_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_528_ == 0)
{
v___x_437_ = v___x_433_;
v_isShared_438_ = v_isSharedCheck_528_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_a_435_);
lean_dec(v___x_433_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_528_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v_fst_439_; lean_object* v_fst_440_; lean_object* v_snd_441_; lean_object* v___y_443_; uint8_t v___y_444_; lean_object* v_a_451_; lean_object* v___y_455_; lean_object* v___x_516_; lean_object* v___x_517_; 
v_fst_439_ = lean_ctor_get(v_b_413_, 0);
lean_inc(v_fst_439_);
lean_dec_ref(v_b_413_);
v_fst_440_ = lean_ctor_get(v_snd_434_, 0);
lean_inc(v_fst_440_);
v_snd_441_ = lean_ctor_get(v_snd_434_, 1);
lean_inc(v_snd_441_);
lean_dec(v_snd_434_);
v___x_516_ = lean_box(0);
v___x_517_ = l_Lean_Meta_synthInstance(v_a_435_, v___x_516_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v_a_518_; lean_object* v___x_519_; lean_object* v___x_520_; uint8_t v___x_521_; 
v_a_518_ = lean_ctor_get(v___x_517_, 0);
lean_inc(v_a_518_);
lean_dec_ref(v___x_517_);
v___x_519_ = lean_array_get_size(v_snd_441_);
v___x_520_ = lean_unsigned_to_nat(0u);
v___x_521_ = lean_nat_dec_eq(v___x_519_, v___x_520_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = lean_box(0);
lean_inc(v_snd_441_);
v___x_523_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0(v_a_518_, v_snd_441_, v_fst_439_, v___x_522_, v___x_430_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
v___y_455_ = v___x_523_;
goto v___jp_454_;
}
else
{
lean_object* v___x_524_; uint8_t v___x_525_; lean_object* v___x_526_; 
v___x_524_ = lean_box(0);
v___x_525_ = lean_unbox(v_fst_440_);
lean_inc(v_snd_441_);
v___x_526_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0(v_a_518_, v_snd_441_, v_fst_439_, v___x_524_, v___x_525_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
v___y_455_ = v___x_526_;
goto v___jp_454_;
}
}
else
{
lean_object* v_a_527_; 
lean_dec(v_fst_439_);
v_a_527_ = lean_ctor_get(v___x_517_, 0);
lean_inc(v_a_527_);
lean_dec_ref(v___x_517_);
v_a_451_ = v_a_527_;
goto v___jp_450_;
}
v___jp_442_:
{
if (v___y_444_ == 0)
{
lean_object* v___x_445_; lean_object* v___x_446_; 
lean_del_object(v___x_437_);
v___x_445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_445_, 0, v___y_443_);
lean_inc(v_a_432_);
v___x_446_ = lean_array_push(v_snd_441_, v_a_432_);
v_fst_425_ = v___x_445_;
v_fst_426_ = v_fst_440_;
v_snd_427_ = v___x_446_;
goto v___jp_424_;
}
else
{
lean_object* v___x_448_; 
lean_dec(v_snd_441_);
lean_dec(v_fst_440_);
lean_dec(v_mvarId_409_);
lean_dec(v_tacticName_408_);
if (v_isShared_438_ == 0)
{
lean_ctor_set_tag(v___x_437_, 1);
lean_ctor_set(v___x_437_, 0, v___y_443_);
v___x_448_ = v___x_437_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v___y_443_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
v___jp_450_:
{
uint8_t v___x_452_; 
v___x_452_ = l_Lean_Exception_isInterrupt(v_a_451_);
if (v___x_452_ == 0)
{
uint8_t v___x_453_; 
lean_inc_ref(v_a_451_);
v___x_453_ = l_Lean_Exception_isRuntime(v_a_451_);
v___y_443_ = v_a_451_;
v___y_444_ = v___x_453_;
goto v___jp_442_;
}
else
{
v___y_443_ = v_a_451_;
v___y_444_ = v___x_452_;
goto v___jp_442_;
}
}
v___jp_454_:
{
if (lean_obj_tag(v___y_455_) == 0)
{
lean_object* v_a_456_; lean_object* v_snd_457_; lean_object* v_snd_458_; lean_object* v_fst_459_; 
lean_dec(v_snd_441_);
lean_dec(v_fst_440_);
lean_del_object(v___x_437_);
v_a_456_ = lean_ctor_get(v___y_455_, 0);
lean_inc(v_a_456_);
lean_dec_ref(v___y_455_);
v_snd_457_ = lean_ctor_get(v_a_456_, 1);
lean_inc(v_snd_457_);
v_snd_458_ = lean_ctor_get(v_snd_457_, 1);
lean_inc(v_snd_458_);
v_fst_459_ = lean_ctor_get(v_a_456_, 0);
lean_inc(v_fst_459_);
lean_dec(v_a_456_);
if (lean_obj_tag(v_fst_459_) == 1)
{
lean_object* v_fst_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_510_; 
v_fst_460_ = lean_ctor_get(v_snd_457_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v_snd_457_);
if (v_isSharedCheck_510_ == 0)
{
lean_object* v_unused_511_; 
v_unused_511_ = lean_ctor_get(v_snd_457_, 1);
lean_dec(v_unused_511_);
v___x_462_ = v_snd_457_;
v_isShared_463_ = v_isSharedCheck_510_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_fst_460_);
lean_dec(v_snd_457_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_510_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v_fst_464_; lean_object* v_snd_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_509_; 
v_fst_464_ = lean_ctor_get(v_snd_458_, 0);
v_snd_465_ = lean_ctor_get(v_snd_458_, 1);
v_isSharedCheck_509_ = !lean_is_exclusive(v_snd_458_);
if (v_isSharedCheck_509_ == 0)
{
v___x_467_ = v_snd_458_;
v_isShared_468_ = v_isSharedCheck_509_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_snd_465_);
lean_inc(v_fst_464_);
lean_dec(v_snd_458_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_509_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v_val_469_; lean_object* v___x_470_; 
v_val_469_ = lean_ctor_get(v_fst_459_, 0);
lean_inc(v_val_469_);
lean_dec_ref(v_fst_459_);
lean_inc(v_a_432_);
v___x_470_ = l_Lean_Meta_isExprDefEq(v_a_432_, v_val_469_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
if (lean_obj_tag(v___x_470_) == 0)
{
lean_object* v_a_471_; uint8_t v___x_472_; 
v_a_471_ = lean_ctor_get(v___x_470_, 0);
lean_inc(v_a_471_);
lean_dec_ref(v___x_470_);
v___x_472_ = lean_unbox(v_a_471_);
lean_dec(v_a_471_);
if (v___x_472_ == 0)
{
if (v_allowSynthFailures_407_ == 0)
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3);
lean_inc(v_mvarId_409_);
lean_inc(v_tacticName_408_);
v___x_474_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_408_, v_mvarId_409_, v___x_473_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
if (lean_obj_tag(v___x_474_) == 0)
{
lean_object* v___x_476_; 
lean_dec_ref(v___x_474_);
if (v_isShared_468_ == 0)
{
v___x_476_ = v___x_467_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_fst_464_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v_snd_465_);
v___x_476_ = v_reuseFailAlloc_480_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
lean_object* v___x_478_; 
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 1, v___x_476_);
v___x_478_ = v___x_462_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_fst_460_);
lean_ctor_set(v_reuseFailAlloc_479_, 1, v___x_476_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
v_a_420_ = v___x_478_;
goto v___jp_419_;
}
}
}
else
{
lean_object* v_a_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_488_; 
lean_del_object(v___x_467_);
lean_dec(v_snd_465_);
lean_dec(v_fst_464_);
lean_del_object(v___x_462_);
lean_dec(v_fst_460_);
lean_dec(v_mvarId_409_);
lean_dec(v_tacticName_408_);
v_a_481_ = lean_ctor_get(v___x_474_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_488_ == 0)
{
v___x_483_ = v___x_474_;
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_a_481_);
lean_dec(v___x_474_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_486_; 
if (v_isShared_484_ == 0)
{
v___x_486_ = v___x_483_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_a_481_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
else
{
lean_object* v___x_490_; 
if (v_isShared_468_ == 0)
{
v___x_490_ = v___x_467_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_fst_464_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v_snd_465_);
v___x_490_ = v_reuseFailAlloc_494_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
lean_object* v___x_492_; 
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 1, v___x_490_);
v___x_492_ = v___x_462_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_fst_460_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v___x_490_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
v_a_420_ = v___x_492_;
goto v___jp_419_;
}
}
}
}
else
{
lean_object* v___x_496_; 
if (v_isShared_468_ == 0)
{
v___x_496_ = v___x_467_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_fst_464_);
lean_ctor_set(v_reuseFailAlloc_500_, 1, v_snd_465_);
v___x_496_ = v_reuseFailAlloc_500_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
lean_object* v___x_498_; 
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 1, v___x_496_);
v___x_498_ = v___x_462_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_fst_460_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v___x_496_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
v_a_420_ = v___x_498_;
goto v___jp_419_;
}
}
}
}
else
{
lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_508_; 
lean_del_object(v___x_467_);
lean_dec(v_snd_465_);
lean_dec(v_fst_464_);
lean_del_object(v___x_462_);
lean_dec(v_fst_460_);
lean_dec(v_mvarId_409_);
lean_dec(v_tacticName_408_);
v_a_501_ = lean_ctor_get(v___x_470_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_470_);
if (v_isSharedCheck_508_ == 0)
{
v___x_503_ = v___x_470_;
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v___x_470_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_506_; 
if (v_isShared_504_ == 0)
{
v___x_506_ = v___x_503_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_a_501_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
}
}
else
{
lean_object* v_fst_512_; lean_object* v_fst_513_; lean_object* v_snd_514_; 
lean_dec(v_fst_459_);
v_fst_512_ = lean_ctor_get(v_snd_457_, 0);
lean_inc(v_fst_512_);
lean_dec(v_snd_457_);
v_fst_513_ = lean_ctor_get(v_snd_458_, 0);
lean_inc(v_fst_513_);
v_snd_514_ = lean_ctor_get(v_snd_458_, 1);
lean_inc(v_snd_514_);
lean_dec(v_snd_458_);
v_fst_425_ = v_fst_512_;
v_fst_426_ = v_fst_513_;
v_snd_427_ = v_snd_514_;
goto v___jp_424_;
}
}
else
{
lean_object* v_a_515_; 
v_a_515_ = lean_ctor_get(v___y_455_, 0);
lean_inc(v_a_515_);
lean_dec_ref(v___y_455_);
v_a_451_ = v_a_515_;
goto v___jp_450_;
}
}
}
}
else
{
lean_object* v_a_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_536_; 
lean_dec_ref(v_b_413_);
lean_dec(v_mvarId_409_);
lean_dec(v_tacticName_408_);
v_a_529_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_536_ == 0)
{
v___x_531_ = v___x_433_;
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_a_529_);
lean_dec(v___x_433_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_534_; 
if (v_isShared_532_ == 0)
{
v___x_534_ = v___x_531_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_a_529_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
v___jp_419_:
{
size_t v___x_421_; size_t v___x_422_; 
v___x_421_ = ((size_t)1ULL);
v___x_422_ = lean_usize_add(v_i_412_, v___x_421_);
v_i_412_ = v___x_422_;
v_b_413_ = v_a_420_;
goto _start;
}
v___jp_424_:
{
lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_428_, 0, v_fst_426_);
lean_ctor_set(v___x_428_, 1, v_snd_427_);
v___x_429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_429_, 0, v_fst_425_);
lean_ctor_set(v___x_429_, 1, v___x_428_);
v_a_420_ = v___x_429_;
goto v___jp_419_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___boxed(lean_object* v_allowSynthFailures_537_, lean_object* v_tacticName_538_, lean_object* v_mvarId_539_, lean_object* v_as_540_, lean_object* v_sz_541_, lean_object* v_i_542_, lean_object* v_b_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
uint8_t v_allowSynthFailures_boxed_549_; size_t v_sz_boxed_550_; size_t v_i_boxed_551_; lean_object* v_res_552_; 
v_allowSynthFailures_boxed_549_ = lean_unbox(v_allowSynthFailures_537_);
v_sz_boxed_550_ = lean_unbox_usize(v_sz_541_);
lean_dec(v_sz_541_);
v_i_boxed_551_ = lean_unbox_usize(v_i_542_);
lean_dec(v_i_542_);
v_res_552_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0(v_allowSynthFailures_boxed_549_, v_tacticName_538_, v_mvarId_539_, v_as_540_, v_sz_boxed_550_, v_i_boxed_551_, v_b_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_);
lean_dec(v___y_547_);
lean_dec_ref(v___y_546_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
lean_dec_ref(v_as_540_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step(lean_object* v_tacticName_562_, lean_object* v_mvarId_563_, uint8_t v_allowSynthFailures_564_, lean_object* v_mvars_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_){
_start:
{
lean_object* v_postponed_571_; lean_object* v___x_572_; size_t v_sz_573_; size_t v___x_574_; lean_object* v___x_575_; 
v_postponed_571_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0));
v___x_572_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__2));
v_sz_573_ = lean_array_size(v_mvars_565_);
v___x_574_ = ((size_t)0ULL);
v___x_575_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0(v_allowSynthFailures_564_, v_tacticName_562_, v_mvarId_563_, v_mvars_565_, v_sz_573_, v___x_574_, v___x_572_, v_a_566_, v_a_567_, v_a_568_, v_a_569_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v_a_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_598_; 
v_a_576_ = lean_ctor_get(v___x_575_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_598_ == 0)
{
v___x_578_ = v___x_575_;
v_isShared_579_ = v_isSharedCheck_598_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_a_576_);
lean_dec(v___x_575_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_598_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v_fst_580_; 
v_fst_580_ = lean_ctor_get(v_a_576_, 0);
lean_inc(v_fst_580_);
if (lean_obj_tag(v_fst_580_) == 1)
{
lean_object* v_snd_581_; lean_object* v_fst_582_; uint8_t v___x_583_; 
v_snd_581_ = lean_ctor_get(v_a_576_, 1);
lean_inc(v_snd_581_);
lean_dec(v_a_576_);
v_fst_582_ = lean_ctor_get(v_snd_581_, 0);
v___x_583_ = lean_unbox(v_fst_582_);
if (v___x_583_ == 0)
{
lean_dec(v_snd_581_);
if (v_allowSynthFailures_564_ == 0)
{
lean_object* v_val_584_; lean_object* v___x_586_; 
v_val_584_ = lean_ctor_get(v_fst_580_, 0);
lean_inc(v_val_584_);
lean_dec_ref(v_fst_580_);
if (v_isShared_579_ == 0)
{
lean_ctor_set_tag(v___x_578_, 1);
lean_ctor_set(v___x_578_, 0, v_val_584_);
v___x_586_ = v___x_578_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_val_584_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
else
{
lean_object* v___x_589_; 
lean_dec_ref(v_fst_580_);
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 0, v_postponed_571_);
v___x_589_ = v___x_578_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_postponed_571_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
else
{
lean_object* v_snd_591_; lean_object* v___x_593_; 
lean_dec_ref(v_fst_580_);
v_snd_591_ = lean_ctor_get(v_snd_581_, 1);
lean_inc(v_snd_591_);
lean_dec(v_snd_581_);
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 0, v_snd_591_);
v___x_593_ = v___x_578_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_snd_591_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
else
{
lean_object* v___x_596_; 
lean_dec(v_fst_580_);
lean_dec(v_a_576_);
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 0, v_postponed_571_);
v___x_596_ = v___x_578_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_postponed_571_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
}
else
{
lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_606_; 
v_a_599_ = lean_ctor_get(v___x_575_, 0);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_606_ == 0)
{
v___x_601_ = v___x_575_;
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_dec(v___x_575_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_604_; 
if (v_isShared_602_ == 0)
{
v___x_604_ = v___x_601_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_a_599_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___boxed(lean_object* v_tacticName_607_, lean_object* v_mvarId_608_, lean_object* v_allowSynthFailures_609_, lean_object* v_mvars_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_){
_start:
{
uint8_t v_allowSynthFailures_boxed_616_; lean_object* v_res_617_; 
v_allowSynthFailures_boxed_616_ = lean_unbox(v_allowSynthFailures_609_);
v_res_617_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step(v_tacticName_607_, v_mvarId_608_, v_allowSynthFailures_boxed_616_, v_mvars_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_);
lean_dec(v_a_614_);
lean_dec_ref(v_a_613_);
lean_dec(v_a_612_);
lean_dec_ref(v_a_611_);
lean_dec_ref(v_mvars_610_);
return v_res_617_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_keys_618_, lean_object* v_i_619_, lean_object* v_k_620_){
_start:
{
lean_object* v___x_621_; uint8_t v___x_622_; 
v___x_621_ = lean_array_get_size(v_keys_618_);
v___x_622_ = lean_nat_dec_lt(v_i_619_, v___x_621_);
if (v___x_622_ == 0)
{
lean_dec(v_i_619_);
return v___x_622_;
}
else
{
lean_object* v_k_x27_623_; uint8_t v___x_624_; 
v_k_x27_623_ = lean_array_fget_borrowed(v_keys_618_, v_i_619_);
v___x_624_ = l_Lean_instBEqMVarId_beq(v_k_620_, v_k_x27_623_);
if (v___x_624_ == 0)
{
lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_625_ = lean_unsigned_to_nat(1u);
v___x_626_ = lean_nat_add(v_i_619_, v___x_625_);
lean_dec(v_i_619_);
v_i_619_ = v___x_626_;
goto _start;
}
else
{
lean_dec(v_i_619_);
return v___x_624_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_keys_628_, lean_object* v_i_629_, lean_object* v_k_630_){
_start:
{
uint8_t v_res_631_; lean_object* v_r_632_; 
v_res_631_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_628_, v_i_629_, v_k_630_);
lean_dec(v_k_630_);
lean_dec_ref(v_keys_628_);
v_r_632_ = lean_box(v_res_631_);
return v_r_632_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_633_; size_t v___x_634_; size_t v___x_635_; 
v___x_633_ = ((size_t)5ULL);
v___x_634_ = ((size_t)1ULL);
v___x_635_ = lean_usize_shift_left(v___x_634_, v___x_633_);
return v___x_635_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_636_; size_t v___x_637_; size_t v___x_638_; 
v___x_636_ = ((size_t)1ULL);
v___x_637_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_638_ = lean_usize_sub(v___x_637_, v___x_636_);
return v___x_638_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(lean_object* v_x_639_, size_t v_x_640_, lean_object* v_x_641_){
_start:
{
if (lean_obj_tag(v_x_639_) == 0)
{
lean_object* v_es_642_; lean_object* v___x_643_; size_t v___x_644_; size_t v___x_645_; size_t v___x_646_; lean_object* v_j_647_; lean_object* v___x_648_; 
v_es_642_ = lean_ctor_get(v_x_639_, 0);
v___x_643_ = lean_box(2);
v___x_644_ = ((size_t)5ULL);
v___x_645_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_646_ = lean_usize_land(v_x_640_, v___x_645_);
v_j_647_ = lean_usize_to_nat(v___x_646_);
v___x_648_ = lean_array_get_borrowed(v___x_643_, v_es_642_, v_j_647_);
lean_dec(v_j_647_);
switch(lean_obj_tag(v___x_648_))
{
case 0:
{
lean_object* v_key_649_; uint8_t v___x_650_; 
v_key_649_ = lean_ctor_get(v___x_648_, 0);
v___x_650_ = l_Lean_instBEqMVarId_beq(v_x_641_, v_key_649_);
return v___x_650_;
}
case 1:
{
lean_object* v_node_651_; size_t v___x_652_; 
v_node_651_ = lean_ctor_get(v___x_648_, 0);
v___x_652_ = lean_usize_shift_right(v_x_640_, v___x_644_);
v_x_639_ = v_node_651_;
v_x_640_ = v___x_652_;
goto _start;
}
default: 
{
uint8_t v___x_654_; 
v___x_654_ = 0;
return v___x_654_;
}
}
}
else
{
lean_object* v_ks_655_; lean_object* v___x_656_; uint8_t v___x_657_; 
v_ks_655_ = lean_ctor_get(v_x_639_, 0);
v___x_656_ = lean_unsigned_to_nat(0u);
v___x_657_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(v_ks_655_, v___x_656_, v_x_641_);
return v___x_657_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_658_, lean_object* v_x_659_, lean_object* v_x_660_){
_start:
{
size_t v_x_2678__boxed_661_; uint8_t v_res_662_; lean_object* v_r_663_; 
v_x_2678__boxed_661_ = lean_unbox_usize(v_x_659_);
lean_dec(v_x_659_);
v_res_662_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(v_x_658_, v_x_2678__boxed_661_, v_x_660_);
lean_dec(v_x_660_);
lean_dec_ref(v_x_658_);
v_r_663_ = lean_box(v_res_662_);
return v_r_663_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(lean_object* v_x_664_, lean_object* v_x_665_){
_start:
{
uint64_t v___x_666_; size_t v___x_667_; uint8_t v___x_668_; 
v___x_666_ = l_Lean_instHashableMVarId_hash(v_x_665_);
v___x_667_ = lean_uint64_to_usize(v___x_666_);
v___x_668_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(v_x_664_, v___x_667_, v_x_665_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg___boxed(lean_object* v_x_669_, lean_object* v_x_670_){
_start:
{
uint8_t v_res_671_; lean_object* v_r_672_; 
v_res_671_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(v_x_669_, v_x_670_);
lean_dec(v_x_670_);
lean_dec_ref(v_x_669_);
v_r_672_ = lean_box(v_res_671_);
return v_r_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(lean_object* v_mvarId_673_, lean_object* v___y_674_){
_start:
{
lean_object* v___x_676_; lean_object* v_mctx_677_; lean_object* v_eAssignment_678_; uint8_t v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_676_ = lean_st_ref_get(v___y_674_);
v_mctx_677_ = lean_ctor_get(v___x_676_, 0);
lean_inc_ref(v_mctx_677_);
lean_dec(v___x_676_);
v_eAssignment_678_ = lean_ctor_get(v_mctx_677_, 8);
lean_inc_ref(v_eAssignment_678_);
lean_dec_ref(v_mctx_677_);
v___x_679_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(v_eAssignment_678_, v_mvarId_673_);
lean_dec_ref(v_eAssignment_678_);
v___x_680_ = lean_box(v___x_679_);
v___x_681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_681_, 0, v___x_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg___boxed(lean_object* v_mvarId_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v_mvarId_682_, v___y_683_);
lean_dec(v___y_683_);
lean_dec(v_mvarId_682_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1(uint8_t v_synthAssignedInstances_686_, lean_object* v_as_687_, size_t v_sz_688_, size_t v_i_689_, lean_object* v_b_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_){
_start:
{
lean_object* v_a_697_; uint8_t v___x_701_; 
v___x_701_ = lean_usize_dec_lt(v_i_689_, v_sz_688_);
if (v___x_701_ == 0)
{
lean_object* v___x_702_; 
v___x_702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_702_, 0, v_b_690_);
return v___x_702_;
}
else
{
lean_object* v_snd_703_; lean_object* v_fst_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_754_; 
v_snd_703_ = lean_ctor_get(v_b_690_, 1);
v_fst_704_ = lean_ctor_get(v_b_690_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v_b_690_);
if (v_isSharedCheck_754_ == 0)
{
v___x_706_ = v_b_690_;
v_isShared_707_ = v_isSharedCheck_754_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_snd_703_);
lean_inc(v_fst_704_);
lean_dec(v_b_690_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_754_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v_array_708_; lean_object* v_start_709_; lean_object* v_stop_710_; uint8_t v___x_711_; 
v_array_708_ = lean_ctor_get(v_snd_703_, 0);
v_start_709_ = lean_ctor_get(v_snd_703_, 1);
v_stop_710_ = lean_ctor_get(v_snd_703_, 2);
v___x_711_ = lean_nat_dec_lt(v_start_709_, v_stop_710_);
if (v___x_711_ == 0)
{
lean_object* v___x_713_; 
if (v_isShared_707_ == 0)
{
v___x_713_ = v___x_706_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_fst_704_);
lean_ctor_set(v_reuseFailAlloc_715_, 1, v_snd_703_);
v___x_713_ = v_reuseFailAlloc_715_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
lean_object* v___x_714_; 
v___x_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
return v___x_714_;
}
}
else
{
lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_750_; 
lean_inc(v_stop_710_);
lean_inc(v_start_709_);
lean_inc_ref(v_array_708_);
v_isSharedCheck_750_ = !lean_is_exclusive(v_snd_703_);
if (v_isSharedCheck_750_ == 0)
{
lean_object* v_unused_751_; lean_object* v_unused_752_; lean_object* v_unused_753_; 
v_unused_751_ = lean_ctor_get(v_snd_703_, 2);
lean_dec(v_unused_751_);
v_unused_752_ = lean_ctor_get(v_snd_703_, 1);
lean_dec(v_unused_752_);
v_unused_753_ = lean_ctor_get(v_snd_703_, 0);
lean_dec(v_unused_753_);
v___x_717_ = v_snd_703_;
v_isShared_718_ = v_isSharedCheck_750_;
goto v_resetjp_716_;
}
else
{
lean_dec(v_snd_703_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_750_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_723_; 
v___x_719_ = lean_array_fget(v_array_708_, v_start_709_);
v___x_720_ = lean_unsigned_to_nat(1u);
v___x_721_ = lean_nat_add(v_start_709_, v___x_720_);
lean_dec(v_start_709_);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 1, v___x_721_);
v___x_723_ = v___x_717_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_array_708_);
lean_ctor_set(v_reuseFailAlloc_749_, 1, v___x_721_);
lean_ctor_set(v_reuseFailAlloc_749_, 2, v_stop_710_);
v___x_723_ = v_reuseFailAlloc_749_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
uint8_t v___x_724_; uint8_t v___x_725_; 
v___x_724_ = lean_unbox(v___x_719_);
lean_dec(v___x_719_);
v___x_725_ = l_Lean_BinderInfo_isInstImplicit(v___x_724_);
if (v___x_725_ == 0)
{
lean_object* v___x_727_; 
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 1, v___x_723_);
v___x_727_ = v___x_706_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_fst_704_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v___x_723_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
v_a_697_ = v___x_727_;
goto v___jp_696_;
}
}
else
{
lean_object* v_a_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v_a_729_ = lean_array_uget_borrowed(v_as_687_, v_i_689_);
v___x_730_ = l_Lean_Expr_mvarId_x21(v_a_729_);
v___x_731_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v___x_730_, v___y_692_);
lean_dec(v___x_730_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v_a_732_; 
v_a_732_ = lean_ctor_get(v___x_731_, 0);
lean_inc(v_a_732_);
lean_dec_ref(v___x_731_);
if (v_synthAssignedInstances_686_ == 0)
{
uint8_t v___x_740_; 
v___x_740_ = lean_unbox(v_a_732_);
lean_dec(v_a_732_);
if (v___x_740_ == 0)
{
if (v___x_725_ == 0)
{
goto v___jp_733_;
}
else
{
lean_del_object(v___x_706_);
goto v___jp_737_;
}
}
else
{
goto v___jp_733_;
}
}
else
{
lean_dec(v_a_732_);
lean_del_object(v___x_706_);
goto v___jp_737_;
}
v___jp_733_:
{
lean_object* v___x_735_; 
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 1, v___x_723_);
v___x_735_ = v___x_706_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_fst_704_);
lean_ctor_set(v_reuseFailAlloc_736_, 1, v___x_723_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
v_a_697_ = v___x_735_;
goto v___jp_696_;
}
}
v___jp_737_:
{
lean_object* v___x_738_; lean_object* v___x_739_; 
lean_inc(v_a_729_);
v___x_738_ = lean_array_push(v_fst_704_, v_a_729_);
v___x_739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_739_, 0, v___x_738_);
lean_ctor_set(v___x_739_, 1, v___x_723_);
v_a_697_ = v___x_739_;
goto v___jp_696_;
}
}
else
{
lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_748_; 
lean_dec_ref(v___x_723_);
lean_del_object(v___x_706_);
lean_dec(v_fst_704_);
v_a_741_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_748_ == 0)
{
v___x_743_ = v___x_731_;
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v___x_731_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_746_; 
if (v_isShared_744_ == 0)
{
v___x_746_ = v___x_743_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_a_741_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
}
}
}
}
}
v___jp_696_:
{
size_t v___x_698_; size_t v___x_699_; 
v___x_698_ = ((size_t)1ULL);
v___x_699_ = lean_usize_add(v_i_689_, v___x_698_);
v_i_689_ = v___x_699_;
v_b_690_ = v_a_697_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1___boxed(lean_object* v_synthAssignedInstances_755_, lean_object* v_as_756_, lean_object* v_sz_757_, lean_object* v_i_758_, lean_object* v_b_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
uint8_t v_synthAssignedInstances_boxed_765_; size_t v_sz_boxed_766_; size_t v_i_boxed_767_; lean_object* v_res_768_; 
v_synthAssignedInstances_boxed_765_ = lean_unbox(v_synthAssignedInstances_755_);
v_sz_boxed_766_ = lean_unbox_usize(v_sz_757_);
lean_dec(v_sz_757_);
v_i_boxed_767_ = lean_unbox_usize(v_i_758_);
lean_dec(v_i_758_);
v_res_768_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1(v_synthAssignedInstances_boxed_765_, v_as_756_, v_sz_boxed_766_, v_i_boxed_767_, v_b_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec_ref(v_as_756_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_synthAppInstances_spec__2(lean_object* v_tacticName_769_, lean_object* v_mvarId_770_, uint8_t v_allowSynthFailures_771_, lean_object* v_b_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; uint8_t v___x_780_; 
v___x_778_ = lean_array_get_size(v_b_772_);
v___x_779_ = lean_unsigned_to_nat(0u);
v___x_780_ = lean_nat_dec_eq(v___x_778_, v___x_779_);
if (v___x_780_ == 0)
{
lean_object* v___x_781_; 
lean_inc(v_mvarId_770_);
lean_inc(v_tacticName_769_);
v___x_781_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step(v_tacticName_769_, v_mvarId_770_, v_allowSynthFailures_771_, v_b_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
lean_dec_ref(v_b_772_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_object* v_a_782_; 
v_a_782_ = lean_ctor_get(v___x_781_, 0);
lean_inc(v_a_782_);
lean_dec_ref(v___x_781_);
v_b_772_ = v_a_782_;
goto _start;
}
else
{
lean_dec(v_mvarId_770_);
lean_dec(v_tacticName_769_);
return v___x_781_;
}
}
else
{
lean_object* v___x_784_; 
lean_dec(v_mvarId_770_);
lean_dec(v_tacticName_769_);
v___x_784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_784_, 0, v_b_772_);
return v___x_784_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_synthAppInstances_spec__2___boxed(lean_object* v_tacticName_785_, lean_object* v_mvarId_786_, lean_object* v_allowSynthFailures_787_, lean_object* v_b_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
uint8_t v_allowSynthFailures_boxed_794_; lean_object* v_res_795_; 
v_allowSynthFailures_boxed_794_ = lean_unbox(v_allowSynthFailures_787_);
v_res_795_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_synthAppInstances_spec__2(v_tacticName_785_, v_mvarId_786_, v_allowSynthFailures_boxed_794_, v_b_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_synthAppInstances(lean_object* v_tacticName_796_, lean_object* v_mvarId_797_, lean_object* v_mvarsNew_798_, lean_object* v_binderInfos_799_, uint8_t v_synthAssignedInstances_800_, uint8_t v_allowSynthFailures_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_){
_start:
{
lean_object* v___x_807_; lean_object* v_todo_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; size_t v_sz_812_; size_t v___x_813_; lean_object* v___x_814_; 
v___x_807_ = lean_unsigned_to_nat(0u);
v_todo_808_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0));
v___x_809_ = lean_array_get_size(v_binderInfos_799_);
v___x_810_ = l_Array_toSubarray___redArg(v_binderInfos_799_, v___x_807_, v___x_809_);
v___x_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_811_, 0, v_todo_808_);
lean_ctor_set(v___x_811_, 1, v___x_810_);
v_sz_812_ = lean_array_size(v_mvarsNew_798_);
v___x_813_ = ((size_t)0ULL);
v___x_814_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1(v_synthAssignedInstances_800_, v_mvarsNew_798_, v_sz_812_, v___x_813_, v___x_811_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
if (lean_obj_tag(v___x_814_) == 0)
{
lean_object* v_a_815_; lean_object* v_fst_816_; lean_object* v___x_817_; 
v_a_815_ = lean_ctor_get(v___x_814_, 0);
lean_inc(v_a_815_);
lean_dec_ref(v___x_814_);
v_fst_816_ = lean_ctor_get(v_a_815_, 0);
lean_inc(v_fst_816_);
lean_dec(v_a_815_);
v___x_817_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_synthAppInstances_spec__2(v_tacticName_796_, v_mvarId_797_, v_allowSynthFailures_801_, v_fst_816_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_825_; 
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_825_ == 0)
{
lean_object* v_unused_826_; 
v_unused_826_ = lean_ctor_get(v___x_817_, 0);
lean_dec(v_unused_826_);
v___x_819_ = v___x_817_;
v_isShared_820_ = v_isSharedCheck_825_;
goto v_resetjp_818_;
}
else
{
lean_dec(v___x_817_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_825_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_821_; lean_object* v___x_823_; 
v___x_821_ = lean_box(0);
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 0, v___x_821_);
v___x_823_ = v___x_819_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_821_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
else
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
v_a_827_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___x_817_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_817_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_832_; 
if (v_isShared_830_ == 0)
{
v___x_832_ = v___x_829_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_a_827_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
else
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_842_; 
lean_dec(v_mvarId_797_);
lean_dec(v_tacticName_796_);
v_a_835_ = lean_ctor_get(v___x_814_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_842_ == 0)
{
v___x_837_ = v___x_814_;
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___x_814_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_a_835_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_synthAppInstances___boxed(lean_object* v_tacticName_843_, lean_object* v_mvarId_844_, lean_object* v_mvarsNew_845_, lean_object* v_binderInfos_846_, lean_object* v_synthAssignedInstances_847_, lean_object* v_allowSynthFailures_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_){
_start:
{
uint8_t v_synthAssignedInstances_boxed_854_; uint8_t v_allowSynthFailures_boxed_855_; lean_object* v_res_856_; 
v_synthAssignedInstances_boxed_854_ = lean_unbox(v_synthAssignedInstances_847_);
v_allowSynthFailures_boxed_855_ = lean_unbox(v_allowSynthFailures_848_);
v_res_856_ = l_Lean_Meta_synthAppInstances(v_tacticName_843_, v_mvarId_844_, v_mvarsNew_845_, v_binderInfos_846_, v_synthAssignedInstances_boxed_854_, v_allowSynthFailures_boxed_855_, v_a_849_, v_a_850_, v_a_851_, v_a_852_);
lean_dec(v_a_852_);
lean_dec_ref(v_a_851_);
lean_dec(v_a_850_);
lean_dec_ref(v_a_849_);
lean_dec_ref(v_mvarsNew_845_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0(lean_object* v_mvarId_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
lean_object* v___x_863_; 
v___x_863_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v_mvarId_857_, v___y_859_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___boxed(lean_object* v_mvarId_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0(v_mvarId_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec(v___y_866_);
lean_dec_ref(v___y_865_);
lean_dec(v_mvarId_864_);
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
size_t v_x_2998__boxed_889_; uint8_t v_res_890_; lean_object* v_r_891_; 
v_x_2998__boxed_889_ = lean_unbox_usize(v_x_887_);
lean_dec(v_x_887_);
v_res_890_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1(v_00_u03b2_885_, v_x_886_, v_x_2998__boxed_889_, v_x_888_);
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
lean_object* v_one_921_; lean_object* v_n_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v_a_928_; uint8_t v___x_929_; 
v_one_921_ = lean_unsigned_to_nat(1u);
v_n_922_ = lean_nat_sub(v_i_911_, v_one_921_);
lean_dec(v_i_911_);
v___x_923_ = lean_nat_sub(v_n_910_, v_n_922_);
v___x_924_ = lean_nat_sub(v___x_923_, v_one_921_);
lean_dec(v___x_923_);
v___x_925_ = lean_array_fget_borrowed(v_newMVars_907_, v___x_924_);
v___x_926_ = l_Lean_Expr_mvarId_x21(v___x_925_);
v___x_927_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v___x_926_, v___y_913_);
v_a_928_ = lean_ctor_get(v___x_927_, 0);
lean_inc(v_a_928_);
lean_dec_ref(v___x_927_);
v___x_929_ = lean_unbox(v_a_928_);
lean_dec(v_a_928_);
if (v___x_929_ == 0)
{
uint8_t v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; uint8_t v___x_933_; uint8_t v___x_934_; 
v___x_930_ = 0;
v___x_931_ = lean_box(v___x_930_);
v___x_932_ = lean_array_get(v___x_931_, v_binderInfos_908_, v___x_924_);
lean_dec(v___x_924_);
lean_dec(v___x_931_);
v___x_933_ = lean_unbox(v___x_932_);
lean_dec(v___x_932_);
v___x_934_ = l_Lean_BinderInfo_isInstImplicit(v___x_933_);
if (v___x_934_ == 0)
{
lean_object* v___x_935_; 
lean_inc(v___x_926_);
v___x_935_ = l_Lean_MVarId_getTag(v___x_926_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
if (lean_obj_tag(v___x_935_) == 0)
{
lean_object* v_a_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v_a_936_ = lean_ctor_get(v___x_935_, 0);
lean_inc(v_a_936_);
lean_dec_ref(v___x_935_);
lean_inc(v_a_909_);
v___x_937_ = l_Lean_Meta_appendTag(v_a_909_, v_a_936_);
v___x_938_ = l_Lean_MVarId_setTag___redArg(v___x_926_, v___x_937_, v___y_913_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_dec_ref(v___x_938_);
v_i_911_ = v_n_922_;
goto _start;
}
else
{
lean_dec(v_n_922_);
lean_dec(v_a_909_);
return v___x_938_;
}
}
else
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
lean_dec(v___x_926_);
lean_dec(v_n_922_);
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
lean_dec(v___x_926_);
v_i_911_ = v_n_922_;
goto _start;
}
}
else
{
lean_dec(v___x_926_);
lean_dec(v___x_924_);
v_i_911_ = v_n_922_;
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
lean_object* v___x_969_; 
v___x_969_ = l_Lean_MVarId_getTag(v_mvarId_961_, v_a_964_, v_a_965_, v_a_966_, v_a_967_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_988_; 
v_a_970_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_988_ == 0)
{
v___x_972_ = v___x_969_;
v_isShared_973_ = v_isSharedCheck_988_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_969_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_988_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_974_; lean_object* v___x_975_; uint8_t v___x_976_; 
v___x_974_ = lean_array_get_size(v_newMVars_962_);
v___x_975_ = lean_unsigned_to_nat(1u);
v___x_976_ = lean_nat_dec_eq(v___x_974_, v___x_975_);
if (v___x_976_ == 0)
{
uint8_t v___x_977_; 
v___x_977_ = l_Lean_Name_isAnonymous(v_a_970_);
if (v___x_977_ == 0)
{
lean_object* v___x_978_; 
lean_del_object(v___x_972_);
v___x_978_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(v_newMVars_962_, v_binderInfos_963_, v_a_970_, v___x_974_, v___x_974_, v_a_964_, v_a_965_, v_a_966_, v_a_967_);
return v___x_978_;
}
else
{
lean_object* v___x_979_; lean_object* v___x_981_; 
lean_dec(v_a_970_);
v___x_979_ = lean_box(0);
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 0, v___x_979_);
v___x_981_ = v___x_972_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v___x_979_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
}
else
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
lean_del_object(v___x_972_);
v___x_983_ = l_Lean_instInhabitedExpr;
v___x_984_ = lean_unsigned_to_nat(0u);
v___x_985_ = lean_array_get_borrowed(v___x_983_, v_newMVars_962_, v___x_984_);
v___x_986_ = l_Lean_Expr_mvarId_x21(v___x_985_);
v___x_987_ = l_Lean_MVarId_setTag___redArg(v___x_986_, v_a_970_, v_a_965_);
return v___x_987_;
}
}
}
else
{
lean_object* v_a_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_996_; 
v_a_989_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_996_ == 0)
{
v___x_991_ = v___x_969_;
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_a_989_);
lean_dec(v___x_969_);
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
uint8_t v___x_1073_; 
v___x_1073_ = lean_usize_dec_eq(v_i_1066_, v_stop_1067_);
if (v___x_1073_ == 0)
{
uint8_t v___x_1074_; uint8_t v_a_1076_; lean_object* v___x_1082_; uint8_t v___x_1083_; 
v___x_1074_ = 1;
v___x_1082_ = lean_array_uget_borrowed(v_as_1065_, v_i_1066_);
v___x_1083_ = lean_expr_eqv(v_mvar_1064_, v___x_1082_);
if (v___x_1083_ == 0)
{
lean_object* v___x_1084_; 
lean_inc(v___y_1071_);
lean_inc_ref(v___y_1070_);
lean_inc(v___y_1069_);
lean_inc_ref(v___y_1068_);
lean_inc(v___x_1082_);
v___x_1084_ = lean_infer_type(v___x_1082_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1096_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1087_ = v___x_1084_;
v_isShared_1088_ = v_isSharedCheck_1096_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1084_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1096_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___f_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
lean_inc_ref(v_mvar_1064_);
v___f_1089_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1089_, 0, v_mvar_1064_);
v___x_1090_ = lean_box(0);
v___x_1091_ = l_Lean_FindMVar_main(v___f_1089_, v_a_1085_, v___x_1090_);
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_del_object(v___x_1087_);
v_a_1076_ = v___x_1083_;
goto v___jp_1075_;
}
else
{
lean_object* v___x_1092_; lean_object* v___x_1094_; 
lean_dec_ref(v___x_1091_);
lean_dec_ref(v_mvar_1064_);
v___x_1092_ = lean_box(v___x_1074_);
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 0, v___x_1092_);
v___x_1094_ = v___x_1087_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1092_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
}
else
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1104_; 
lean_dec_ref(v_mvar_1064_);
v_a_1097_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1099_ = v___x_1084_;
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___x_1084_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1102_; 
if (v_isShared_1100_ == 0)
{
v___x_1102_ = v___x_1099_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_a_1097_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
}
else
{
v_a_1076_ = v___x_1073_;
goto v___jp_1075_;
}
v___jp_1075_:
{
if (v_a_1076_ == 0)
{
size_t v___x_1077_; size_t v___x_1078_; 
v___x_1077_ = ((size_t)1ULL);
v___x_1078_ = lean_usize_add(v_i_1066_, v___x_1077_);
v_i_1066_ = v___x_1078_;
goto _start;
}
else
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
lean_dec_ref(v_mvar_1064_);
v___x_1080_ = lean_box(v___x_1074_);
v___x_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1080_);
return v___x_1081_;
}
}
}
else
{
uint8_t v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
lean_dec_ref(v_mvar_1064_);
v___x_1105_ = 0;
v___x_1106_ = lean_box(v___x_1105_);
v___x_1107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1106_);
return v___x_1107_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___boxed(lean_object* v_mvar_1108_, lean_object* v_as_1109_, lean_object* v_i_1110_, lean_object* v_stop_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
size_t v_i_boxed_1117_; size_t v_stop_boxed_1118_; lean_object* v_res_1119_; 
v_i_boxed_1117_ = lean_unbox_usize(v_i_1110_);
lean_dec(v_i_1110_);
v_stop_boxed_1118_ = lean_unbox_usize(v_stop_1111_);
lean_dec(v_stop_1111_);
v_res_1119_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0(v_mvar_1108_, v_as_1109_, v_i_boxed_1117_, v_stop_boxed_1118_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
lean_dec_ref(v_as_1109_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(lean_object* v_mvar_1120_, lean_object* v_otherMVars_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_){
_start:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; uint8_t v___x_1129_; 
v___x_1127_ = lean_unsigned_to_nat(0u);
v___x_1128_ = lean_array_get_size(v_otherMVars_1121_);
v___x_1129_ = lean_nat_dec_lt(v___x_1127_, v___x_1128_);
if (v___x_1129_ == 0)
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
lean_dec_ref(v_mvar_1120_);
v___x_1130_ = lean_box(v___x_1129_);
v___x_1131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1130_);
return v___x_1131_;
}
else
{
if (v___x_1129_ == 0)
{
lean_object* v___x_1132_; lean_object* v___x_1133_; 
lean_dec_ref(v_mvar_1120_);
v___x_1132_ = lean_box(v___x_1129_);
v___x_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1132_);
return v___x_1133_;
}
else
{
size_t v___x_1134_; size_t v___x_1135_; lean_object* v___x_1136_; 
v___x_1134_ = ((size_t)0ULL);
v___x_1135_ = lean_usize_of_nat(v___x_1128_);
v___x_1136_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0(v_mvar_1120_, v_otherMVars_1121_, v___x_1134_, v___x_1135_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_);
return v___x_1136_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___boxed(lean_object* v_mvar_1137_, lean_object* v_otherMVars_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(v_mvar_1137_, v_otherMVars_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_);
lean_dec(v_a_1142_);
lean_dec_ref(v_a_1141_);
lean_dec(v_a_1140_);
lean_dec_ref(v_a_1139_);
lean_dec_ref(v_otherMVars_1138_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(lean_object* v_mvars_1145_, lean_object* v_as_1146_, size_t v_i_1147_, size_t v_stop_1148_, lean_object* v_b_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
uint8_t v___x_1155_; 
v___x_1155_ = lean_usize_dec_eq(v_i_1147_, v_stop_1148_);
if (v___x_1155_ == 0)
{
lean_object* v_fst_1156_; lean_object* v_snd_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1187_; 
v_fst_1156_ = lean_ctor_get(v_b_1149_, 0);
v_snd_1157_ = lean_ctor_get(v_b_1149_, 1);
v_isSharedCheck_1187_ = !lean_is_exclusive(v_b_1149_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1159_ = v_b_1149_;
v_isShared_1160_ = v_isSharedCheck_1187_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_snd_1157_);
lean_inc(v_fst_1156_);
lean_dec(v_b_1149_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1187_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1161_; lean_object* v_currMVarId_1162_; lean_object* v___x_1163_; 
v___x_1161_ = lean_array_uget_borrowed(v_as_1146_, v_i_1147_);
v_currMVarId_1162_ = l_Lean_Expr_mvarId_x21(v___x_1161_);
lean_inc(v___x_1161_);
v___x_1163_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(v___x_1161_, v_mvars_1145_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
if (lean_obj_tag(v___x_1163_) == 0)
{
lean_object* v_a_1164_; lean_object* v_a_1166_; uint8_t v___x_1170_; 
v_a_1164_ = lean_ctor_get(v___x_1163_, 0);
lean_inc(v_a_1164_);
lean_dec_ref(v___x_1163_);
v___x_1170_ = lean_unbox(v_a_1164_);
lean_dec(v_a_1164_);
if (v___x_1170_ == 0)
{
lean_object* v___x_1171_; lean_object* v___x_1173_; 
v___x_1171_ = lean_array_push(v_fst_1156_, v_currMVarId_1162_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 0, v___x_1171_);
v___x_1173_ = v___x_1159_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v___x_1171_);
lean_ctor_set(v_reuseFailAlloc_1174_, 1, v_snd_1157_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
v_a_1166_ = v___x_1173_;
goto v___jp_1165_;
}
}
else
{
lean_object* v___x_1175_; lean_object* v___x_1177_; 
v___x_1175_ = lean_array_push(v_snd_1157_, v_currMVarId_1162_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 1, v___x_1175_);
v___x_1177_ = v___x_1159_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_fst_1156_);
lean_ctor_set(v_reuseFailAlloc_1178_, 1, v___x_1175_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
v_a_1166_ = v___x_1177_;
goto v___jp_1165_;
}
}
v___jp_1165_:
{
size_t v___x_1167_; size_t v___x_1168_; 
v___x_1167_ = ((size_t)1ULL);
v___x_1168_ = lean_usize_add(v_i_1147_, v___x_1167_);
v_i_1147_ = v___x_1168_;
v_b_1149_ = v_a_1166_;
goto _start;
}
}
else
{
lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1186_; 
lean_dec(v_currMVarId_1162_);
lean_del_object(v___x_1159_);
lean_dec(v_snd_1157_);
lean_dec(v_fst_1156_);
v_a_1179_ = lean_ctor_get(v___x_1163_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1181_ = v___x_1163_;
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_dec(v___x_1163_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1184_; 
if (v_isShared_1182_ == 0)
{
v___x_1184_ = v___x_1181_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_a_1179_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
}
}
else
{
lean_object* v___x_1188_; 
v___x_1188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1188_, 0, v_b_1149_);
return v___x_1188_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0___boxed(lean_object* v_mvars_1189_, lean_object* v_as_1190_, lean_object* v_i_1191_, lean_object* v_stop_1192_, lean_object* v_b_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
size_t v_i_boxed_1199_; size_t v_stop_boxed_1200_; lean_object* v_res_1201_; 
v_i_boxed_1199_ = lean_unbox_usize(v_i_1191_);
lean_dec(v_i_1191_);
v_stop_boxed_1200_ = lean_unbox_usize(v_stop_1192_);
lean_dec(v_stop_1192_);
v_res_1201_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(v_mvars_1189_, v_as_1190_, v_i_boxed_1199_, v_stop_boxed_1200_, v_b_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec_ref(v_as_1190_);
lean_dec_ref(v_mvars_1189_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(lean_object* v_mvars_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; uint8_t v___x_1215_; 
v___x_1212_ = lean_unsigned_to_nat(0u);
v___x_1213_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1));
v___x_1214_ = lean_array_get_size(v_mvars_1206_);
v___x_1215_ = lean_nat_dec_lt(v___x_1212_, v___x_1214_);
if (v___x_1215_ == 0)
{
lean_object* v___x_1216_; 
v___x_1216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1213_);
return v___x_1216_;
}
else
{
uint8_t v___x_1217_; 
v___x_1217_ = lean_nat_dec_le(v___x_1214_, v___x_1214_);
if (v___x_1217_ == 0)
{
if (v___x_1215_ == 0)
{
lean_object* v___x_1218_; 
v___x_1218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1213_);
return v___x_1218_;
}
else
{
size_t v___x_1219_; size_t v___x_1220_; lean_object* v___x_1221_; 
v___x_1219_ = ((size_t)0ULL);
v___x_1220_ = lean_usize_of_nat(v___x_1214_);
v___x_1221_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(v_mvars_1206_, v_mvars_1206_, v___x_1219_, v___x_1220_, v___x_1213_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_);
return v___x_1221_;
}
}
else
{
size_t v___x_1222_; size_t v___x_1223_; lean_object* v___x_1224_; 
v___x_1222_ = ((size_t)0ULL);
v___x_1223_ = lean_usize_of_nat(v___x_1214_);
v___x_1224_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(v_mvars_1206_, v_mvars_1206_, v___x_1222_, v___x_1223_, v___x_1213_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_);
return v___x_1224_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___boxed(lean_object* v_mvars_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(v_mvars_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_);
lean_dec(v_a_1229_);
lean_dec_ref(v_a_1228_);
lean_dec(v_a_1227_);
lean_dec_ref(v_a_1226_);
lean_dec_ref(v_mvars_1225_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals_spec__0(lean_object* v_a_1232_, lean_object* v_a_1233_){
_start:
{
if (lean_obj_tag(v_a_1232_) == 0)
{
lean_object* v___x_1234_; 
v___x_1234_ = l_List_reverse___redArg(v_a_1233_);
return v___x_1234_;
}
else
{
lean_object* v_head_1235_; lean_object* v_tail_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1245_; 
v_head_1235_ = lean_ctor_get(v_a_1232_, 0);
v_tail_1236_ = lean_ctor_get(v_a_1232_, 1);
v_isSharedCheck_1245_ = !lean_is_exclusive(v_a_1232_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1238_ = v_a_1232_;
v_isShared_1239_ = v_isSharedCheck_1245_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_tail_1236_);
lean_inc(v_head_1235_);
lean_dec(v_a_1232_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1245_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1240_; lean_object* v___x_1242_; 
v___x_1240_ = l_Lean_Expr_mvarId_x21(v_head_1235_);
lean_dec(v_head_1235_);
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 1, v_a_1233_);
lean_ctor_set(v___x_1238_, 0, v___x_1240_);
v___x_1242_ = v___x_1238_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v___x_1240_);
lean_ctor_set(v_reuseFailAlloc_1244_, 1, v_a_1233_);
v___x_1242_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
v_a_1232_ = v_tail_1236_;
v_a_1233_ = v___x_1242_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(lean_object* v_mvars_1246_, uint8_t v_x_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_){
_start:
{
switch(v_x_1247_)
{
case 0:
{
lean_object* v___x_1253_; 
v___x_1253_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(v_mvars_1246_, v_a_1248_, v_a_1249_, v_a_1250_, v_a_1251_);
lean_dec_ref(v_mvars_1246_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1266_; 
v_a_1254_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1256_ = v___x_1253_;
v_isShared_1257_ = v_isSharedCheck_1266_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_dec(v___x_1253_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1266_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v_fst_1258_; lean_object* v_snd_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1264_; 
v_fst_1258_ = lean_ctor_get(v_a_1254_, 0);
lean_inc(v_fst_1258_);
v_snd_1259_ = lean_ctor_get(v_a_1254_, 1);
lean_inc(v_snd_1259_);
lean_dec(v_a_1254_);
v___x_1260_ = lean_array_to_list(v_fst_1258_);
v___x_1261_ = lean_array_to_list(v_snd_1259_);
v___x_1262_ = l_List_appendTR___redArg(v___x_1260_, v___x_1261_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 0, v___x_1262_);
v___x_1264_ = v___x_1256_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v___x_1262_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
else
{
lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1274_; 
v_a_1267_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1269_ = v___x_1253_;
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_dec(v___x_1253_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
if (v_isShared_1270_ == 0)
{
v___x_1272_ = v___x_1269_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_a_1267_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
}
case 1:
{
lean_object* v___x_1275_; 
v___x_1275_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(v_mvars_1246_, v_a_1248_, v_a_1249_, v_a_1250_, v_a_1251_);
lean_dec_ref(v_mvars_1246_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1285_; 
v_a_1276_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1278_ = v___x_1275_;
v_isShared_1279_ = v_isSharedCheck_1285_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1275_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1285_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v_fst_1280_; lean_object* v___x_1281_; lean_object* v___x_1283_; 
v_fst_1280_ = lean_ctor_get(v_a_1276_, 0);
lean_inc(v_fst_1280_);
lean_dec(v_a_1276_);
v___x_1281_ = lean_array_to_list(v_fst_1280_);
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 0, v___x_1281_);
v___x_1283_ = v___x_1278_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v___x_1281_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
else
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
v_a_1286_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1288_ = v___x_1275_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1275_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1289_ == 0)
{
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_a_1286_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
default: 
{
lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1294_ = lean_array_to_list(v_mvars_1246_);
v___x_1295_ = lean_box(0);
v___x_1296_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals_spec__0(v___x_1294_, v___x_1295_);
v___x_1297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1297_, 0, v___x_1296_);
return v___x_1297_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals___boxed(lean_object* v_mvars_1298_, lean_object* v_x_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_){
_start:
{
uint8_t v_x_820__boxed_1305_; lean_object* v_res_1306_; 
v_x_820__boxed_1305_ = lean_unbox(v_x_1299_);
v_res_1306_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(v_mvars_1298_, v_x_820__boxed_1305_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_);
lean_dec(v_a_1303_);
lean_dec_ref(v_a_1302_);
lean_dec(v_a_1301_);
lean_dec_ref(v_a_1300_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(uint8_t v_approx_1307_, lean_object* v_a_1308_, lean_object* v_b_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_){
_start:
{
if (v_approx_1307_ == 0)
{
lean_object* v___x_1315_; 
v___x_1315_ = l_Lean_Meta_isExprDefEqGuarded(v_a_1308_, v_b_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_);
return v___x_1315_;
}
else
{
lean_object* v___x_1316_; uint8_t v_constApprox_1317_; uint8_t v_isDefEqStuckEx_1318_; uint8_t v_unificationHints_1319_; uint8_t v_proofIrrelevance_1320_; uint8_t v_assignSyntheticOpaque_1321_; uint8_t v_offsetCnstrs_1322_; uint8_t v_transparency_1323_; uint8_t v_etaStruct_1324_; uint8_t v_univApprox_1325_; uint8_t v_iota_1326_; uint8_t v_beta_1327_; uint8_t v_proj_1328_; uint8_t v_zeta_1329_; uint8_t v_zetaDelta_1330_; uint8_t v_zetaUnused_1331_; uint8_t v_zetaHave_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1353_; 
v___x_1316_ = l_Lean_Meta_Context_config(v_a_1310_);
v_constApprox_1317_ = lean_ctor_get_uint8(v___x_1316_, 3);
v_isDefEqStuckEx_1318_ = lean_ctor_get_uint8(v___x_1316_, 4);
v_unificationHints_1319_ = lean_ctor_get_uint8(v___x_1316_, 5);
v_proofIrrelevance_1320_ = lean_ctor_get_uint8(v___x_1316_, 6);
v_assignSyntheticOpaque_1321_ = lean_ctor_get_uint8(v___x_1316_, 7);
v_offsetCnstrs_1322_ = lean_ctor_get_uint8(v___x_1316_, 8);
v_transparency_1323_ = lean_ctor_get_uint8(v___x_1316_, 9);
v_etaStruct_1324_ = lean_ctor_get_uint8(v___x_1316_, 10);
v_univApprox_1325_ = lean_ctor_get_uint8(v___x_1316_, 11);
v_iota_1326_ = lean_ctor_get_uint8(v___x_1316_, 12);
v_beta_1327_ = lean_ctor_get_uint8(v___x_1316_, 13);
v_proj_1328_ = lean_ctor_get_uint8(v___x_1316_, 14);
v_zeta_1329_ = lean_ctor_get_uint8(v___x_1316_, 15);
v_zetaDelta_1330_ = lean_ctor_get_uint8(v___x_1316_, 16);
v_zetaUnused_1331_ = lean_ctor_get_uint8(v___x_1316_, 17);
v_zetaHave_1332_ = lean_ctor_get_uint8(v___x_1316_, 18);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1334_ = v___x_1316_;
v_isShared_1335_ = v_isSharedCheck_1353_;
goto v_resetjp_1333_;
}
else
{
lean_dec(v___x_1316_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1353_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1337_; 
if (v_isShared_1335_ == 0)
{
v___x_1337_ = v___x_1334_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1352_, 3, v_constApprox_1317_);
lean_ctor_set_uint8(v_reuseFailAlloc_1352_, 4, v_isDefEqStuckEx_1318_);
lean_ctor_set_uint8(v_reuseFailAlloc_1352_, 5, v_unificationHints_1319_);
lean_ctor_set_uint8(v_reuseFailAlloc_1352_, 6, v_proofIrrelevance_1320_);
lean_ctor_set_uint8(v_reuseFailAlloc_1352_, 7, v_assignSyntheticOpaque_1321_);
lean_ctor_set_uint8(v_reuseFailAlloc_1352_, 8, v_offsetCnstrs_1322_);
lean_ctor_set_uint8(v_reuseFailAlloc_1352_, 9, v_transparency_1323_);
lean_ctor_set_uint8(v_reuseFailAlloc_1352_, 10, v_etaStruct_1324_);
lean_ctor_set_uint8(v_reuseFailAlloc_1352_, 11, v_univApprox_1325_);
lean_ctor_set_uint8(v_reuseFailAlloc_1352_, 12, v_iota_1326_);
lean_ctor_set_uint8(v_reuseFailAlloc_1352_, 13, v_beta_1327_);
lean_ctor_set_uint8(v_reuseFailAlloc_1352_, 14, v_proj_1328_);
lean_ctor_set_uint8(v_reuseFailAlloc_1352_, 15, v_zeta_1329_);
lean_ctor_set_uint8(v_reuseFailAlloc_1352_, 16, v_zetaDelta_1330_);
lean_ctor_set_uint8(v_reuseFailAlloc_1352_, 17, v_zetaUnused_1331_);
lean_ctor_set_uint8(v_reuseFailAlloc_1352_, 18, v_zetaHave_1332_);
v___x_1337_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
uint8_t v_trackZetaDelta_1338_; lean_object* v_zetaDeltaSet_1339_; lean_object* v_lctx_1340_; lean_object* v_localInstances_1341_; lean_object* v_defEqCtx_x3f_1342_; lean_object* v_synthPendingDepth_1343_; lean_object* v_canUnfold_x3f_1344_; uint8_t v_univApprox_1345_; uint8_t v_inTypeClassResolution_1346_; uint8_t v_cacheInferType_1347_; uint64_t v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; 
lean_ctor_set_uint8(v___x_1337_, 0, v_approx_1307_);
lean_ctor_set_uint8(v___x_1337_, 1, v_approx_1307_);
lean_ctor_set_uint8(v___x_1337_, 2, v_approx_1307_);
v_trackZetaDelta_1338_ = lean_ctor_get_uint8(v_a_1310_, sizeof(void*)*7);
v_zetaDeltaSet_1339_ = lean_ctor_get(v_a_1310_, 1);
v_lctx_1340_ = lean_ctor_get(v_a_1310_, 2);
v_localInstances_1341_ = lean_ctor_get(v_a_1310_, 3);
v_defEqCtx_x3f_1342_ = lean_ctor_get(v_a_1310_, 4);
v_synthPendingDepth_1343_ = lean_ctor_get(v_a_1310_, 5);
v_canUnfold_x3f_1344_ = lean_ctor_get(v_a_1310_, 6);
v_univApprox_1345_ = lean_ctor_get_uint8(v_a_1310_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1346_ = lean_ctor_get_uint8(v_a_1310_, sizeof(void*)*7 + 2);
v_cacheInferType_1347_ = lean_ctor_get_uint8(v_a_1310_, sizeof(void*)*7 + 3);
v___x_1348_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1337_);
v___x_1349_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1349_, 0, v___x_1337_);
lean_ctor_set_uint64(v___x_1349_, sizeof(void*)*1, v___x_1348_);
lean_inc(v_canUnfold_x3f_1344_);
lean_inc(v_synthPendingDepth_1343_);
lean_inc(v_defEqCtx_x3f_1342_);
lean_inc_ref(v_localInstances_1341_);
lean_inc_ref(v_lctx_1340_);
lean_inc(v_zetaDeltaSet_1339_);
v___x_1350_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1350_, 0, v___x_1349_);
lean_ctor_set(v___x_1350_, 1, v_zetaDeltaSet_1339_);
lean_ctor_set(v___x_1350_, 2, v_lctx_1340_);
lean_ctor_set(v___x_1350_, 3, v_localInstances_1341_);
lean_ctor_set(v___x_1350_, 4, v_defEqCtx_x3f_1342_);
lean_ctor_set(v___x_1350_, 5, v_synthPendingDepth_1343_);
lean_ctor_set(v___x_1350_, 6, v_canUnfold_x3f_1344_);
lean_ctor_set_uint8(v___x_1350_, sizeof(void*)*7, v_trackZetaDelta_1338_);
lean_ctor_set_uint8(v___x_1350_, sizeof(void*)*7 + 1, v_univApprox_1345_);
lean_ctor_set_uint8(v___x_1350_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1346_);
lean_ctor_set_uint8(v___x_1350_, sizeof(void*)*7 + 3, v_cacheInferType_1347_);
v___x_1351_ = l_Lean_Meta_isExprDefEqGuarded(v_a_1308_, v_b_1309_, v___x_1350_, v_a_1311_, v_a_1312_, v_a_1313_);
lean_dec_ref(v___x_1350_);
return v___x_1351_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply___boxed(lean_object* v_approx_1354_, lean_object* v_a_1355_, lean_object* v_b_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_){
_start:
{
uint8_t v_approx_boxed_1362_; lean_object* v_res_1363_; 
v_approx_boxed_1362_ = lean_unbox(v_approx_1354_);
v_res_1363_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(v_approx_boxed_1362_, v_a_1355_, v_b_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_);
lean_dec(v_a_1360_);
lean_dec_ref(v_a_1359_);
lean_dec(v_a_1358_);
lean_dec_ref(v_a_1357_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go(lean_object* v_mvarId_1364_, lean_object* v_cfg_1365_, lean_object* v_term_x3f_1366_, lean_object* v_targetType_1367_, lean_object* v_eType_1368_, lean_object* v_rangeNumArgs_1369_, lean_object* v_i_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_){
_start:
{
lean_object* v_lower_1376_; lean_object* v_upper_1377_; uint8_t v___x_1378_; 
v_lower_1376_ = lean_ctor_get(v_rangeNumArgs_1369_, 0);
v_upper_1377_ = lean_ctor_get(v_rangeNumArgs_1369_, 1);
v___x_1378_ = lean_nat_dec_lt(v_i_1370_, v_upper_1377_);
if (v___x_1378_ == 0)
{
lean_object* v___x_1379_; uint8_t v___x_1380_; 
lean_dec(v_i_1370_);
v___x_1379_ = lean_unsigned_to_nat(0u);
v___x_1380_ = lean_nat_dec_eq(v_lower_1376_, v___x_1379_);
if (v___x_1380_ == 0)
{
lean_object* v___x_1381_; uint8_t v___x_1382_; lean_object* v___x_1383_; 
lean_inc(v_lower_1376_);
v___x_1381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1381_, 0, v_lower_1376_);
v___x_1382_ = 0;
lean_inc_ref(v_eType_1368_);
v___x_1383_ = l_Lean_Meta_forallMetaTelescopeReducing(v_eType_1368_, v___x_1381_, v___x_1382_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_a_1384_; lean_object* v_snd_1385_; lean_object* v_snd_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; 
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_a_1384_);
lean_dec_ref(v___x_1383_);
v_snd_1385_ = lean_ctor_get(v_a_1384_, 1);
lean_inc(v_snd_1385_);
lean_dec(v_a_1384_);
v_snd_1386_ = lean_ctor_get(v_snd_1385_, 1);
lean_inc(v_snd_1386_);
lean_dec(v_snd_1385_);
v___x_1387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1387_, 0, v_snd_1386_);
v___x_1388_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(v_mvarId_1364_, v_eType_1368_, v___x_1387_, v_targetType_1367_, v_term_x3f_1366_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
return v___x_1388_;
}
else
{
lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1396_; 
lean_dec_ref(v_eType_1368_);
lean_dec_ref(v_targetType_1367_);
lean_dec(v_term_x3f_1366_);
lean_dec(v_mvarId_1364_);
v_a_1389_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1391_ = v___x_1383_;
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1383_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1394_; 
if (v_isShared_1392_ == 0)
{
v___x_1394_ = v___x_1391_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_a_1389_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
}
else
{
lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1397_ = lean_box(0);
v___x_1398_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(v_mvarId_1364_, v_eType_1368_, v___x_1397_, v_targetType_1367_, v_term_x3f_1366_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
return v___x_1398_;
}
}
else
{
lean_object* v___x_1399_; 
v___x_1399_ = l_Lean_Meta_saveState___redArg(v_a_1372_, v_a_1374_);
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_object* v_a_1400_; lean_object* v___x_1401_; uint8_t v___x_1402_; lean_object* v___x_1403_; 
v_a_1400_ = lean_ctor_get(v___x_1399_, 0);
lean_inc(v_a_1400_);
lean_dec_ref(v___x_1399_);
lean_inc(v_i_1370_);
v___x_1401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1401_, 0, v_i_1370_);
v___x_1402_ = 0;
lean_inc_ref(v_eType_1368_);
v___x_1403_ = l_Lean_Meta_forallMetaTelescopeReducing(v_eType_1368_, v___x_1401_, v___x_1402_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
if (lean_obj_tag(v___x_1403_) == 0)
{
lean_object* v_a_1404_; lean_object* v_snd_1405_; lean_object* v_fst_1406_; lean_object* v_fst_1407_; lean_object* v_snd_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1446_; 
v_a_1404_ = lean_ctor_get(v___x_1403_, 0);
lean_inc(v_a_1404_);
lean_dec_ref(v___x_1403_);
v_snd_1405_ = lean_ctor_get(v_a_1404_, 1);
lean_inc(v_snd_1405_);
v_fst_1406_ = lean_ctor_get(v_a_1404_, 0);
lean_inc(v_fst_1406_);
lean_dec(v_a_1404_);
v_fst_1407_ = lean_ctor_get(v_snd_1405_, 0);
v_snd_1408_ = lean_ctor_get(v_snd_1405_, 1);
v_isSharedCheck_1446_ = !lean_is_exclusive(v_snd_1405_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1410_ = v_snd_1405_;
v_isShared_1411_ = v_isSharedCheck_1446_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_snd_1408_);
lean_inc(v_fst_1407_);
lean_dec(v_snd_1405_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1446_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
uint8_t v_approx_1412_; lean_object* v___x_1413_; 
v_approx_1412_ = lean_ctor_get_uint8(v_cfg_1365_, 3);
lean_inc_ref(v_targetType_1367_);
v___x_1413_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(v_approx_1412_, v_snd_1408_, v_targetType_1367_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1437_; 
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1416_ = v___x_1413_;
v_isShared_1417_ = v_isSharedCheck_1437_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1413_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1437_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
uint8_t v___x_1418_; 
v___x_1418_ = lean_unbox(v_a_1414_);
lean_dec(v_a_1414_);
if (v___x_1418_ == 0)
{
lean_object* v___x_1419_; 
lean_del_object(v___x_1416_);
lean_del_object(v___x_1410_);
lean_dec(v_fst_1407_);
lean_dec(v_fst_1406_);
v___x_1419_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1400_, v_a_1372_, v_a_1374_);
lean_dec(v_a_1400_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v___x_1420_; lean_object* v___x_1421_; 
lean_dec_ref(v___x_1419_);
v___x_1420_ = lean_unsigned_to_nat(1u);
v___x_1421_ = lean_nat_add(v_i_1370_, v___x_1420_);
lean_dec(v_i_1370_);
v_i_1370_ = v___x_1421_;
goto _start;
}
else
{
lean_object* v_a_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1430_; 
lean_dec(v_i_1370_);
lean_dec_ref(v_eType_1368_);
lean_dec_ref(v_targetType_1367_);
lean_dec(v_term_x3f_1366_);
lean_dec(v_mvarId_1364_);
v_a_1423_ = lean_ctor_get(v___x_1419_, 0);
v_isSharedCheck_1430_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1425_ = v___x_1419_;
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_a_1423_);
lean_dec(v___x_1419_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v___x_1428_; 
if (v_isShared_1426_ == 0)
{
v___x_1428_ = v___x_1425_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v_a_1423_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
}
}
else
{
lean_object* v___x_1432_; 
lean_dec(v_a_1400_);
lean_dec(v_i_1370_);
lean_dec_ref(v_eType_1368_);
lean_dec_ref(v_targetType_1367_);
lean_dec(v_term_x3f_1366_);
lean_dec(v_mvarId_1364_);
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 1, v_fst_1407_);
lean_ctor_set(v___x_1410_, 0, v_fst_1406_);
v___x_1432_ = v___x_1410_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_fst_1406_);
lean_ctor_set(v_reuseFailAlloc_1436_, 1, v_fst_1407_);
v___x_1432_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
lean_object* v___x_1434_; 
if (v_isShared_1417_ == 0)
{
lean_ctor_set(v___x_1416_, 0, v___x_1432_);
v___x_1434_ = v___x_1416_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1432_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
}
}
else
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1445_; 
lean_del_object(v___x_1410_);
lean_dec(v_fst_1407_);
lean_dec(v_fst_1406_);
lean_dec(v_a_1400_);
lean_dec(v_i_1370_);
lean_dec_ref(v_eType_1368_);
lean_dec_ref(v_targetType_1367_);
lean_dec(v_term_x3f_1366_);
lean_dec(v_mvarId_1364_);
v_a_1438_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1440_ = v___x_1413_;
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1413_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1443_; 
if (v_isShared_1441_ == 0)
{
v___x_1443_ = v___x_1440_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_a_1438_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
}
else
{
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1454_; 
lean_dec(v_a_1400_);
lean_dec(v_i_1370_);
lean_dec_ref(v_eType_1368_);
lean_dec_ref(v_targetType_1367_);
lean_dec(v_term_x3f_1366_);
lean_dec(v_mvarId_1364_);
v_a_1447_ = lean_ctor_get(v___x_1403_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1403_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1449_ = v___x_1403_;
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1403_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1452_; 
if (v_isShared_1450_ == 0)
{
v___x_1452_ = v___x_1449_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_a_1447_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
else
{
lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1462_; 
lean_dec(v_i_1370_);
lean_dec_ref(v_eType_1368_);
lean_dec_ref(v_targetType_1367_);
lean_dec(v_term_x3f_1366_);
lean_dec(v_mvarId_1364_);
v_a_1455_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1457_ = v___x_1399_;
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_dec(v___x_1399_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go___boxed(lean_object* v_mvarId_1463_, lean_object* v_cfg_1464_, lean_object* v_term_x3f_1465_, lean_object* v_targetType_1466_, lean_object* v_eType_1467_, lean_object* v_rangeNumArgs_1468_, lean_object* v_i_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go(v_mvarId_1463_, v_cfg_1464_, v_term_x3f_1465_, v_targetType_1466_, v_eType_1467_, v_rangeNumArgs_1468_, v_i_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_);
lean_dec(v_a_1473_);
lean_dec_ref(v_a_1472_);
lean_dec(v_a_1471_);
lean_dec_ref(v_a_1470_);
lean_dec_ref(v_rangeNumArgs_1468_);
lean_dec_ref(v_cfg_1464_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go_match__1_splitter___redArg(lean_object* v_x_1476_, lean_object* v_h__1_1477_){
_start:
{
lean_object* v_snd_1478_; lean_object* v_fst_1479_; lean_object* v_fst_1480_; lean_object* v_snd_1481_; lean_object* v___x_1482_; 
v_snd_1478_ = lean_ctor_get(v_x_1476_, 1);
lean_inc(v_snd_1478_);
v_fst_1479_ = lean_ctor_get(v_x_1476_, 0);
lean_inc(v_fst_1479_);
lean_dec_ref(v_x_1476_);
v_fst_1480_ = lean_ctor_get(v_snd_1478_, 0);
lean_inc(v_fst_1480_);
v_snd_1481_ = lean_ctor_get(v_snd_1478_, 1);
lean_inc(v_snd_1481_);
lean_dec(v_snd_1478_);
v___x_1482_ = lean_apply_3(v_h__1_1477_, v_fst_1479_, v_fst_1480_, v_snd_1481_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go_match__1_splitter(lean_object* v_motive_1483_, lean_object* v_x_1484_, lean_object* v_h__1_1485_){
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(lean_object* v_e_1491_, lean_object* v___y_1492_){
_start:
{
uint8_t v___x_1494_; 
v___x_1494_ = l_Lean_Expr_hasMVar(v_e_1491_);
if (v___x_1494_ == 0)
{
lean_object* v___x_1495_; 
v___x_1495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1495_, 0, v_e_1491_);
return v___x_1495_;
}
else
{
lean_object* v___x_1496_; lean_object* v_mctx_1497_; lean_object* v___x_1498_; lean_object* v_fst_1499_; lean_object* v_snd_1500_; lean_object* v___x_1501_; lean_object* v_cache_1502_; lean_object* v_zetaDeltaFVarIds_1503_; lean_object* v_postponed_1504_; lean_object* v_diag_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1514_; 
v___x_1496_ = lean_st_ref_get(v___y_1492_);
v_mctx_1497_ = lean_ctor_get(v___x_1496_, 0);
lean_inc_ref(v_mctx_1497_);
lean_dec(v___x_1496_);
v___x_1498_ = l_Lean_instantiateMVarsCore(v_mctx_1497_, v_e_1491_);
v_fst_1499_ = lean_ctor_get(v___x_1498_, 0);
lean_inc(v_fst_1499_);
v_snd_1500_ = lean_ctor_get(v___x_1498_, 1);
lean_inc(v_snd_1500_);
lean_dec_ref(v___x_1498_);
v___x_1501_ = lean_st_ref_take(v___y_1492_);
v_cache_1502_ = lean_ctor_get(v___x_1501_, 1);
v_zetaDeltaFVarIds_1503_ = lean_ctor_get(v___x_1501_, 2);
v_postponed_1504_ = lean_ctor_get(v___x_1501_, 3);
v_diag_1505_ = lean_ctor_get(v___x_1501_, 4);
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1501_);
if (v_isSharedCheck_1514_ == 0)
{
lean_object* v_unused_1515_; 
v_unused_1515_ = lean_ctor_get(v___x_1501_, 0);
lean_dec(v_unused_1515_);
v___x_1507_ = v___x_1501_;
v_isShared_1508_ = v_isSharedCheck_1514_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_diag_1505_);
lean_inc(v_postponed_1504_);
lean_inc(v_zetaDeltaFVarIds_1503_);
lean_inc(v_cache_1502_);
lean_dec(v___x_1501_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1514_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1510_; 
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 0, v_snd_1500_);
v___x_1510_ = v___x_1507_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v_snd_1500_);
lean_ctor_set(v_reuseFailAlloc_1513_, 1, v_cache_1502_);
lean_ctor_set(v_reuseFailAlloc_1513_, 2, v_zetaDeltaFVarIds_1503_);
lean_ctor_set(v_reuseFailAlloc_1513_, 3, v_postponed_1504_);
lean_ctor_set(v_reuseFailAlloc_1513_, 4, v_diag_1505_);
v___x_1510_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1511_ = lean_st_ref_set(v___y_1492_, v___x_1510_);
v___x_1512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1512_, 0, v_fst_1499_);
return v___x_1512_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg___boxed(lean_object* v_e_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_e_1516_, v___y_1517_);
lean_dec(v___y_1517_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0(lean_object* v_e_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_){
_start:
{
lean_object* v___x_1526_; 
v___x_1526_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_e_1520_, v___y_1522_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___boxed(lean_object* v_e_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0(v_e_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(lean_object* v_mvarId_1534_, lean_object* v_x_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_){
_start:
{
lean_object* v___x_1541_; 
v___x_1541_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1534_, v_x_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v_a_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1549_; 
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
v_isSharedCheck_1549_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1544_ = v___x_1541_;
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_a_1542_);
lean_dec(v___x_1541_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___x_1547_; 
if (v_isShared_1545_ == 0)
{
v___x_1547_ = v___x_1544_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_a_1542_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
}
}
}
else
{
lean_object* v_a_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1557_; 
v_a_1550_ = lean_ctor_get(v___x_1541_, 0);
v_isSharedCheck_1557_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1552_ = v___x_1541_;
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_a_1550_);
lean_dec(v___x_1541_);
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
v_reuseFailAlloc_1556_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg___boxed(lean_object* v_mvarId_1558_, lean_object* v_x_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_){
_start:
{
lean_object* v_res_1565_; 
v_res_1565_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_1558_, v_x_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
lean_dec(v___y_1563_);
lean_dec_ref(v___y_1562_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6(lean_object* v_00_u03b1_1566_, lean_object* v_mvarId_1567_, lean_object* v_x_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
lean_object* v___x_1574_; 
v___x_1574_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_1567_, v_x_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___boxed(lean_object* v_00_u03b1_1575_, lean_object* v_mvarId_1576_, lean_object* v_x_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6(v_00_u03b1_1575_, v_mvarId_1576_, v_x_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_);
lean_dec(v___y_1581_);
lean_dec_ref(v___y_1580_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(lean_object* v_as_1584_, size_t v_i_1585_, size_t v_stop_1586_, lean_object* v_b_1587_, lean_object* v___y_1588_){
_start:
{
lean_object* v_a_1591_; uint8_t v___x_1595_; 
v___x_1595_ = lean_usize_dec_eq(v_i_1585_, v_stop_1586_);
if (v___x_1595_ == 0)
{
lean_object* v___x_1596_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1596_ = lean_array_uget_borrowed(v_as_1584_, v_i_1585_);
v___x_1599_ = l_Lean_Expr_mvarId_x21(v___x_1596_);
v___x_1600_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v___x_1599_, v___y_1588_);
lean_dec(v___x_1599_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v_a_1601_; uint8_t v___x_1602_; 
v_a_1601_ = lean_ctor_get(v___x_1600_, 0);
lean_inc(v_a_1601_);
lean_dec_ref(v___x_1600_);
v___x_1602_ = lean_unbox(v_a_1601_);
lean_dec(v_a_1601_);
if (v___x_1602_ == 0)
{
goto v___jp_1597_;
}
else
{
v_a_1591_ = v_b_1587_;
goto v___jp_1590_;
}
}
else
{
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v_a_1603_; uint8_t v___x_1604_; 
v_a_1603_ = lean_ctor_get(v___x_1600_, 0);
lean_inc(v_a_1603_);
lean_dec_ref(v___x_1600_);
v___x_1604_ = lean_unbox(v_a_1603_);
lean_dec(v_a_1603_);
if (v___x_1604_ == 0)
{
v_a_1591_ = v_b_1587_;
goto v___jp_1590_;
}
else
{
goto v___jp_1597_;
}
}
else
{
lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1612_; 
lean_dec_ref(v_b_1587_);
v_a_1605_ = lean_ctor_get(v___x_1600_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1607_ = v___x_1600_;
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_dec(v___x_1600_);
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
v___jp_1597_:
{
lean_object* v___x_1598_; 
lean_inc(v___x_1596_);
v___x_1598_ = lean_array_push(v_b_1587_, v___x_1596_);
v_a_1591_ = v___x_1598_;
goto v___jp_1590_;
}
}
else
{
lean_object* v___x_1613_; 
v___x_1613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1613_, 0, v_b_1587_);
return v___x_1613_;
}
v___jp_1590_:
{
size_t v___x_1592_; size_t v___x_1593_; 
v___x_1592_ = ((size_t)1ULL);
v___x_1593_ = lean_usize_add(v_i_1585_, v___x_1592_);
v_i_1585_ = v___x_1593_;
v_b_1587_ = v_a_1591_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg___boxed(lean_object* v_as_1614_, lean_object* v_i_1615_, lean_object* v_stop_1616_, lean_object* v_b_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_){
_start:
{
size_t v_i_boxed_1620_; size_t v_stop_boxed_1621_; lean_object* v_res_1622_; 
v_i_boxed_1620_ = lean_unbox_usize(v_i_1615_);
lean_dec(v_i_1615_);
v_stop_boxed_1621_ = lean_unbox_usize(v_stop_1616_);
lean_dec(v_stop_1616_);
v_res_1622_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_as_1614_, v_i_boxed_1620_, v_stop_boxed_1621_, v_b_1617_, v___y_1618_);
lean_dec(v___y_1618_);
lean_dec_ref(v_as_1614_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_apply_spec__3(lean_object* v_as_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_){
_start:
{
if (lean_obj_tag(v_as_1623_) == 0)
{
lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1629_ = lean_box(0);
v___x_1630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1629_);
return v___x_1630_;
}
else
{
lean_object* v_head_1631_; lean_object* v_tail_1632_; lean_object* v___x_1633_; 
v_head_1631_ = lean_ctor_get(v_as_1623_, 0);
lean_inc(v_head_1631_);
v_tail_1632_ = lean_ctor_get(v_as_1623_, 1);
lean_inc(v_tail_1632_);
lean_dec_ref(v_as_1623_);
v___x_1633_ = l_Lean_MVarId_headBetaType(v_head_1631_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_dec_ref(v___x_1633_);
v_as_1623_ = v_tail_1632_;
goto _start;
}
else
{
lean_dec(v_tail_1632_);
return v___x_1633_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_apply_spec__3___boxed(lean_object* v_as_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l_List_forM___at___00Lean_MVarId_apply_spec__3(v_as_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_);
lean_dec(v___y_1639_);
lean_dec_ref(v___y_1638_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9___redArg(lean_object* v_x_1642_, lean_object* v_x_1643_, lean_object* v_x_1644_, lean_object* v_x_1645_){
_start:
{
lean_object* v_ks_1646_; lean_object* v_vs_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1671_; 
v_ks_1646_ = lean_ctor_get(v_x_1642_, 0);
v_vs_1647_ = lean_ctor_get(v_x_1642_, 1);
v_isSharedCheck_1671_ = !lean_is_exclusive(v_x_1642_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1649_ = v_x_1642_;
v_isShared_1650_ = v_isSharedCheck_1671_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_vs_1647_);
lean_inc(v_ks_1646_);
lean_dec(v_x_1642_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1671_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1651_; uint8_t v___x_1652_; 
v___x_1651_ = lean_array_get_size(v_ks_1646_);
v___x_1652_ = lean_nat_dec_lt(v_x_1643_, v___x_1651_);
if (v___x_1652_ == 0)
{
lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1656_; 
lean_dec(v_x_1643_);
v___x_1653_ = lean_array_push(v_ks_1646_, v_x_1644_);
v___x_1654_ = lean_array_push(v_vs_1647_, v_x_1645_);
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 1, v___x_1654_);
lean_ctor_set(v___x_1649_, 0, v___x_1653_);
v___x_1656_ = v___x_1649_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1653_);
lean_ctor_set(v_reuseFailAlloc_1657_, 1, v___x_1654_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
else
{
lean_object* v_k_x27_1658_; uint8_t v___x_1659_; 
v_k_x27_1658_ = lean_array_fget_borrowed(v_ks_1646_, v_x_1643_);
v___x_1659_ = l_Lean_instBEqMVarId_beq(v_x_1644_, v_k_x27_1658_);
if (v___x_1659_ == 0)
{
lean_object* v___x_1661_; 
if (v_isShared_1650_ == 0)
{
v___x_1661_ = v___x_1649_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_ks_1646_);
lean_ctor_set(v_reuseFailAlloc_1665_, 1, v_vs_1647_);
v___x_1661_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1662_ = lean_unsigned_to_nat(1u);
v___x_1663_ = lean_nat_add(v_x_1643_, v___x_1662_);
lean_dec(v_x_1643_);
v_x_1642_ = v___x_1661_;
v_x_1643_ = v___x_1663_;
goto _start;
}
}
else
{
lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1669_; 
v___x_1666_ = lean_array_fset(v_ks_1646_, v_x_1643_, v_x_1644_);
v___x_1667_ = lean_array_fset(v_vs_1647_, v_x_1643_, v_x_1645_);
lean_dec(v_x_1643_);
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 1, v___x_1667_);
lean_ctor_set(v___x_1649_, 0, v___x_1666_);
v___x_1669_ = v___x_1649_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v___x_1666_);
lean_ctor_set(v_reuseFailAlloc_1670_, 1, v___x_1667_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8___redArg(lean_object* v_n_1672_, lean_object* v_k_1673_, lean_object* v_v_1674_){
_start:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1675_ = lean_unsigned_to_nat(0u);
v___x_1676_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9___redArg(v_n_1672_, v___x_1675_, v_k_1673_, v_v_1674_);
return v___x_1676_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(lean_object* v_x_1678_, size_t v_x_1679_, size_t v_x_1680_, lean_object* v_x_1681_, lean_object* v_x_1682_){
_start:
{
if (lean_obj_tag(v_x_1678_) == 0)
{
lean_object* v_es_1683_; size_t v___x_1684_; size_t v___x_1685_; size_t v___x_1686_; size_t v___x_1687_; lean_object* v_j_1688_; lean_object* v___x_1689_; uint8_t v___x_1690_; 
v_es_1683_ = lean_ctor_get(v_x_1678_, 0);
v___x_1684_ = ((size_t)5ULL);
v___x_1685_ = ((size_t)1ULL);
v___x_1686_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1687_ = lean_usize_land(v_x_1679_, v___x_1686_);
v_j_1688_ = lean_usize_to_nat(v___x_1687_);
v___x_1689_ = lean_array_get_size(v_es_1683_);
v___x_1690_ = lean_nat_dec_lt(v_j_1688_, v___x_1689_);
if (v___x_1690_ == 0)
{
lean_dec(v_j_1688_);
lean_dec(v_x_1682_);
lean_dec(v_x_1681_);
return v_x_1678_;
}
else
{
lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1727_; 
lean_inc_ref(v_es_1683_);
v_isSharedCheck_1727_ = !lean_is_exclusive(v_x_1678_);
if (v_isSharedCheck_1727_ == 0)
{
lean_object* v_unused_1728_; 
v_unused_1728_ = lean_ctor_get(v_x_1678_, 0);
lean_dec(v_unused_1728_);
v___x_1692_ = v_x_1678_;
v_isShared_1693_ = v_isSharedCheck_1727_;
goto v_resetjp_1691_;
}
else
{
lean_dec(v_x_1678_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1727_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v_v_1694_; lean_object* v___x_1695_; lean_object* v_xs_x27_1696_; lean_object* v___y_1698_; 
v_v_1694_ = lean_array_fget(v_es_1683_, v_j_1688_);
v___x_1695_ = lean_box(0);
v_xs_x27_1696_ = lean_array_fset(v_es_1683_, v_j_1688_, v___x_1695_);
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
v___x_1708_ = l_Lean_instBEqMVarId_beq(v_x_1681_, v_key_1703_);
if (v___x_1708_ == 0)
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
lean_del_object(v___x_1706_);
v___x_1709_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1703_, v_val_1704_, v_x_1681_, v_x_1682_);
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
lean_ctor_set(v___x_1706_, 1, v_x_1682_);
lean_ctor_set(v___x_1706_, 0, v_x_1681_);
v___x_1712_ = v___x_1706_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_x_1681_);
lean_ctor_set(v_reuseFailAlloc_1713_, 1, v_x_1682_);
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
lean_object* v_node_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1725_; 
v_node_1715_ = lean_ctor_get(v_v_1694_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v_v_1694_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1717_ = v_v_1694_;
v_isShared_1718_ = v_isSharedCheck_1725_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_node_1715_);
lean_dec(v_v_1694_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1725_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
size_t v___x_1719_; size_t v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1723_; 
v___x_1719_ = lean_usize_shift_right(v_x_1679_, v___x_1684_);
v___x_1720_ = lean_usize_add(v_x_1680_, v___x_1685_);
v___x_1721_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_node_1715_, v___x_1719_, v___x_1720_, v_x_1681_, v_x_1682_);
if (v_isShared_1718_ == 0)
{
lean_ctor_set(v___x_1717_, 0, v___x_1721_);
v___x_1723_ = v___x_1717_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v___x_1721_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
v___y_1698_ = v___x_1723_;
goto v___jp_1697_;
}
}
}
default: 
{
lean_object* v___x_1726_; 
v___x_1726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1726_, 0, v_x_1681_);
lean_ctor_set(v___x_1726_, 1, v_x_1682_);
v___y_1698_ = v___x_1726_;
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
lean_object* v_ks_1729_; lean_object* v_vs_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1750_; 
v_ks_1729_ = lean_ctor_get(v_x_1678_, 0);
v_vs_1730_ = lean_ctor_get(v_x_1678_, 1);
v_isSharedCheck_1750_ = !lean_is_exclusive(v_x_1678_);
if (v_isSharedCheck_1750_ == 0)
{
v___x_1732_ = v_x_1678_;
v_isShared_1733_ = v_isSharedCheck_1750_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_vs_1730_);
lean_inc(v_ks_1729_);
lean_dec(v_x_1678_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1750_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v___x_1735_; 
if (v_isShared_1733_ == 0)
{
v___x_1735_ = v___x_1732_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_ks_1729_);
lean_ctor_set(v_reuseFailAlloc_1749_, 1, v_vs_1730_);
v___x_1735_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
lean_object* v_newNode_1736_; uint8_t v___y_1738_; size_t v___x_1744_; uint8_t v___x_1745_; 
v_newNode_1736_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8___redArg(v___x_1735_, v_x_1681_, v_x_1682_);
v___x_1744_ = ((size_t)7ULL);
v___x_1745_ = lean_usize_dec_le(v___x_1744_, v_x_1680_);
if (v___x_1745_ == 0)
{
lean_object* v___x_1746_; lean_object* v___x_1747_; uint8_t v___x_1748_; 
v___x_1746_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1736_);
v___x_1747_ = lean_unsigned_to_nat(4u);
v___x_1748_ = lean_nat_dec_lt(v___x_1746_, v___x_1747_);
lean_dec(v___x_1746_);
v___y_1738_ = v___x_1748_;
goto v___jp_1737_;
}
else
{
v___y_1738_ = v___x_1745_;
goto v___jp_1737_;
}
v___jp_1737_:
{
if (v___y_1738_ == 0)
{
lean_object* v_ks_1739_; lean_object* v_vs_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
v_ks_1739_ = lean_ctor_get(v_newNode_1736_, 0);
lean_inc_ref(v_ks_1739_);
v_vs_1740_ = lean_ctor_get(v_newNode_1736_, 1);
lean_inc_ref(v_vs_1740_);
lean_dec_ref(v_newNode_1736_);
v___x_1741_ = lean_unsigned_to_nat(0u);
v___x_1742_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0);
v___x_1743_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(v_x_1680_, v_ks_1739_, v_vs_1740_, v___x_1741_, v___x_1742_);
lean_dec_ref(v_vs_1740_);
lean_dec_ref(v_ks_1739_);
return v___x_1743_;
}
else
{
return v_newNode_1736_;
}
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
size_t v_x_7242__boxed_1783_; size_t v_x_7243__boxed_1784_; lean_object* v_res_1785_; 
v_x_7242__boxed_1783_ = lean_unbox_usize(v_x_1779_);
lean_dec(v_x_1779_);
v_x_7243__boxed_1784_ = lean_unbox_usize(v_x_1780_);
lean_dec(v_x_1780_);
v_res_1785_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_x_1778_, v_x_7242__boxed_1783_, v_x_7243__boxed_1784_, v_x_1781_, v_x_1782_);
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
lean_object* v___x_1797_; lean_object* v_mctx_1798_; lean_object* v_cache_1799_; lean_object* v_zetaDeltaFVarIds_1800_; lean_object* v_postponed_1801_; lean_object* v_diag_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1830_; 
v___x_1797_ = lean_st_ref_take(v___y_1795_);
v_mctx_1798_ = lean_ctor_get(v___x_1797_, 0);
v_cache_1799_ = lean_ctor_get(v___x_1797_, 1);
v_zetaDeltaFVarIds_1800_ = lean_ctor_get(v___x_1797_, 2);
v_postponed_1801_ = lean_ctor_get(v___x_1797_, 3);
v_diag_1802_ = lean_ctor_get(v___x_1797_, 4);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1804_ = v___x_1797_;
v_isShared_1805_ = v_isSharedCheck_1830_;
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
v_isShared_1805_ = v_isSharedCheck_1830_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v_depth_1806_; lean_object* v_levelAssignDepth_1807_; lean_object* v_lmvarCounter_1808_; lean_object* v_mvarCounter_1809_; lean_object* v_lDecls_1810_; lean_object* v_decls_1811_; lean_object* v_userNames_1812_; lean_object* v_lAssignment_1813_; lean_object* v_eAssignment_1814_; lean_object* v_dAssignment_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1829_; 
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
v_isSharedCheck_1829_ = !lean_is_exclusive(v_mctx_1798_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1817_ = v_mctx_1798_;
v_isShared_1818_ = v_isSharedCheck_1829_;
goto v_resetjp_1816_;
}
else
{
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
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1829_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1819_; lean_object* v___x_1821_; 
v___x_1819_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1___redArg(v_eAssignment_1814_, v_mvarId_1793_, v_val_1794_);
if (v_isShared_1818_ == 0)
{
lean_ctor_set(v___x_1817_, 8, v___x_1819_);
v___x_1821_ = v___x_1817_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_depth_1806_);
lean_ctor_set(v_reuseFailAlloc_1828_, 1, v_levelAssignDepth_1807_);
lean_ctor_set(v_reuseFailAlloc_1828_, 2, v_lmvarCounter_1808_);
lean_ctor_set(v_reuseFailAlloc_1828_, 3, v_mvarCounter_1809_);
lean_ctor_set(v_reuseFailAlloc_1828_, 4, v_lDecls_1810_);
lean_ctor_set(v_reuseFailAlloc_1828_, 5, v_decls_1811_);
lean_ctor_set(v_reuseFailAlloc_1828_, 6, v_userNames_1812_);
lean_ctor_set(v_reuseFailAlloc_1828_, 7, v_lAssignment_1813_);
lean_ctor_set(v_reuseFailAlloc_1828_, 8, v___x_1819_);
lean_ctor_set(v_reuseFailAlloc_1828_, 9, v_dAssignment_1815_);
v___x_1821_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
lean_object* v___x_1823_; 
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 0, v___x_1821_);
v___x_1823_ = v___x_1804_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v___x_1821_);
lean_ctor_set(v_reuseFailAlloc_1827_, 1, v_cache_1799_);
lean_ctor_set(v_reuseFailAlloc_1827_, 2, v_zetaDeltaFVarIds_1800_);
lean_ctor_set(v_reuseFailAlloc_1827_, 3, v_postponed_1801_);
lean_ctor_set(v_reuseFailAlloc_1827_, 4, v_diag_1802_);
v___x_1823_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1824_ = lean_st_ref_set(v___y_1795_, v___x_1823_);
v___x_1825_ = lean_box(0);
v___x_1826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1825_);
return v___x_1826_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg___boxed(lean_object* v_mvarId_1831_, lean_object* v_val_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_){
_start:
{
lean_object* v_res_1835_; 
v_res_1835_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_1831_, v_val_1832_, v___y_1833_);
lean_dec(v___y_1833_);
return v_res_1835_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_MVarId_apply_spec__2(lean_object* v_a_1836_, lean_object* v_x_1837_){
_start:
{
if (lean_obj_tag(v_x_1837_) == 0)
{
uint8_t v___x_1838_; 
v___x_1838_ = 0;
return v___x_1838_;
}
else
{
lean_object* v_head_1839_; lean_object* v_tail_1840_; uint8_t v___x_1841_; 
v_head_1839_ = lean_ctor_get(v_x_1837_, 0);
v_tail_1840_ = lean_ctor_get(v_x_1837_, 1);
v___x_1841_ = l_Lean_instBEqMVarId_beq(v_a_1836_, v_head_1839_);
if (v___x_1841_ == 0)
{
v_x_1837_ = v_tail_1840_;
goto _start;
}
else
{
return v___x_1841_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_MVarId_apply_spec__2___boxed(lean_object* v_a_1843_, lean_object* v_x_1844_){
_start:
{
uint8_t v_res_1845_; lean_object* v_r_1846_; 
v_res_1845_ = l_List_elem___at___00Lean_MVarId_apply_spec__2(v_a_1843_, v_x_1844_);
lean_dec(v_x_1844_);
lean_dec(v_a_1843_);
v_r_1846_ = lean_box(v_res_1845_);
return v_r_1846_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(lean_object* v_a_1847_, lean_object* v_as_1848_, size_t v_i_1849_, size_t v_stop_1850_, lean_object* v_b_1851_){
_start:
{
lean_object* v___y_1853_; uint8_t v___x_1857_; 
v___x_1857_ = lean_usize_dec_eq(v_i_1849_, v_stop_1850_);
if (v___x_1857_ == 0)
{
lean_object* v___x_1858_; uint8_t v___x_1859_; 
v___x_1858_ = lean_array_uget_borrowed(v_as_1848_, v_i_1849_);
v___x_1859_ = l_List_elem___at___00Lean_MVarId_apply_spec__2(v___x_1858_, v_a_1847_);
if (v___x_1859_ == 0)
{
lean_object* v___x_1860_; 
lean_inc(v___x_1858_);
v___x_1860_ = lean_array_push(v_b_1851_, v___x_1858_);
v___y_1853_ = v___x_1860_;
goto v___jp_1852_;
}
else
{
v___y_1853_ = v_b_1851_;
goto v___jp_1852_;
}
}
else
{
return v_b_1851_;
}
v___jp_1852_:
{
size_t v___x_1854_; size_t v___x_1855_; 
v___x_1854_ = ((size_t)1ULL);
v___x_1855_ = lean_usize_add(v_i_1849_, v___x_1854_);
v_i_1849_ = v___x_1855_;
v_b_1851_ = v___y_1853_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4___boxed(lean_object* v_a_1861_, lean_object* v_as_1862_, lean_object* v_i_1863_, lean_object* v_stop_1864_, lean_object* v_b_1865_){
_start:
{
size_t v_i_boxed_1866_; size_t v_stop_boxed_1867_; lean_object* v_res_1868_; 
v_i_boxed_1866_ = lean_unbox_usize(v_i_1863_);
lean_dec(v_i_1863_);
v_stop_boxed_1867_ = lean_unbox_usize(v_stop_1864_);
lean_dec(v_stop_1864_);
v_res_1868_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(v_a_1861_, v_as_1862_, v_i_boxed_1866_, v_stop_boxed_1867_, v_b_1865_);
lean_dec_ref(v_as_1862_);
lean_dec(v_a_1861_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___lam__0(lean_object* v_mvarId_1869_, lean_object* v___x_1870_, lean_object* v_e_1871_, lean_object* v_cfg_1872_, lean_object* v_term_x3f_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v___y_1880_; lean_object* v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v___y_1885_; lean_object* v___y_1906_; lean_object* v___y_1907_; uint8_t v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v___y_1911_; lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v_a_1914_; lean_object* v___y_1947_; lean_object* v___y_1948_; uint8_t v___y_1949_; lean_object* v___y_1950_; lean_object* v___y_1951_; lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v___y_1955_; lean_object* v___x_1965_; 
lean_inc(v___x_1870_);
lean_inc(v_mvarId_1869_);
v___x_1965_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1869_, v___x_1870_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_object* v___x_1966_; 
lean_dec_ref(v___x_1965_);
lean_inc(v_mvarId_1869_);
v___x_1966_ = l_Lean_MVarId_getType(v_mvarId_1869_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v_a_1967_; lean_object* v___x_1968_; 
v_a_1967_ = lean_ctor_get(v___x_1966_, 0);
lean_inc(v_a_1967_);
lean_dec_ref(v___x_1966_);
lean_inc(v___y_1877_);
lean_inc_ref(v___y_1876_);
lean_inc(v___y_1875_);
lean_inc_ref(v___y_1874_);
lean_inc_ref(v_e_1871_);
v___x_1968_ = lean_infer_type(v_e_1871_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v_a_1969_; lean_object* v_rangeNumArgs_1971_; lean_object* v_lower_1972_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v___y_1975_; lean_object* v___y_1976_; lean_object* v___x_2016_; 
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
lean_inc_n(v_a_1969_, 2);
lean_dec_ref(v___x_1968_);
v___x_2016_ = l_Lean_Meta_getExpectedNumArgsAux(v_a_1969_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v_a_2017_; lean_object* v_snd_2018_; uint8_t v___x_2019_; 
v_a_2017_ = lean_ctor_get(v___x_2016_, 0);
lean_inc(v_a_2017_);
lean_dec_ref(v___x_2016_);
v_snd_2018_ = lean_ctor_get(v_a_2017_, 1);
v___x_2019_ = lean_unbox(v_snd_2018_);
if (v___x_2019_ == 0)
{
lean_object* v_fst_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2040_; 
v_fst_2020_ = lean_ctor_get(v_a_2017_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v_a_2017_);
if (v_isSharedCheck_2040_ == 0)
{
lean_object* v_unused_2041_; 
v_unused_2041_ = lean_ctor_get(v_a_2017_, 1);
lean_dec(v_unused_2041_);
v___x_2022_ = v_a_2017_;
v_isShared_2023_ = v_isSharedCheck_2040_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_fst_2020_);
lean_dec(v_a_2017_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2040_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2024_; 
lean_inc(v_a_1967_);
v___x_2024_ = l_Lean_Meta_getExpectedNumArgs(v_a_1967_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v_a_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2030_; 
v_a_2025_ = lean_ctor_get(v___x_2024_, 0);
lean_inc(v_a_2025_);
lean_dec_ref(v___x_2024_);
v___x_2026_ = lean_nat_sub(v_fst_2020_, v_a_2025_);
lean_dec(v_a_2025_);
v___x_2027_ = lean_unsigned_to_nat(1u);
v___x_2028_ = lean_nat_add(v_fst_2020_, v___x_2027_);
lean_dec(v_fst_2020_);
lean_inc(v___x_2026_);
if (v_isShared_2023_ == 0)
{
lean_ctor_set(v___x_2022_, 1, v___x_2028_);
lean_ctor_set(v___x_2022_, 0, v___x_2026_);
v___x_2030_ = v___x_2022_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v___x_2026_);
lean_ctor_set(v_reuseFailAlloc_2031_, 1, v___x_2028_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
v_rangeNumArgs_1971_ = v___x_2030_;
v_lower_1972_ = v___x_2026_;
v___y_1973_ = v___y_1874_;
v___y_1974_ = v___y_1875_;
v___y_1975_ = v___y_1876_;
v___y_1976_ = v___y_1877_;
goto v___jp_1970_;
}
}
else
{
lean_object* v_a_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2039_; 
lean_del_object(v___x_2022_);
lean_dec(v_fst_2020_);
lean_dec(v_a_1969_);
lean_dec(v_a_1967_);
lean_dec(v___y_1877_);
lean_dec_ref(v___y_1876_);
lean_dec(v___y_1875_);
lean_dec_ref(v___y_1874_);
lean_dec(v_term_x3f_1873_);
lean_dec_ref(v_e_1871_);
lean_dec(v___x_1870_);
lean_dec(v_mvarId_1869_);
v_a_2032_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2034_ = v___x_2024_;
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_a_2032_);
lean_dec(v___x_2024_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2037_; 
if (v_isShared_2035_ == 0)
{
v___x_2037_ = v___x_2034_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_a_2032_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
}
}
else
{
lean_object* v_fst_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2051_; 
v_fst_2042_ = lean_ctor_get(v_a_2017_, 0);
v_isSharedCheck_2051_ = !lean_is_exclusive(v_a_2017_);
if (v_isSharedCheck_2051_ == 0)
{
lean_object* v_unused_2052_; 
v_unused_2052_ = lean_ctor_get(v_a_2017_, 1);
lean_dec(v_unused_2052_);
v___x_2044_ = v_a_2017_;
v_isShared_2045_ = v_isSharedCheck_2051_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_fst_2042_);
lean_dec(v_a_2017_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2051_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2049_; 
v___x_2046_ = lean_unsigned_to_nat(1u);
v___x_2047_ = lean_nat_add(v_fst_2042_, v___x_2046_);
lean_inc(v_fst_2042_);
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 1, v___x_2047_);
v___x_2049_ = v___x_2044_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_fst_2042_);
lean_ctor_set(v_reuseFailAlloc_2050_, 1, v___x_2047_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
v_rangeNumArgs_1971_ = v___x_2049_;
v_lower_1972_ = v_fst_2042_;
v___y_1973_ = v___y_1874_;
v___y_1974_ = v___y_1875_;
v___y_1975_ = v___y_1876_;
v___y_1976_ = v___y_1877_;
goto v___jp_1970_;
}
}
}
}
else
{
lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2060_; 
lean_dec(v_a_1969_);
lean_dec(v_a_1967_);
lean_dec(v___y_1877_);
lean_dec_ref(v___y_1876_);
lean_dec(v___y_1875_);
lean_dec_ref(v___y_1874_);
lean_dec(v_term_x3f_1873_);
lean_dec_ref(v_e_1871_);
lean_dec(v___x_1870_);
lean_dec(v_mvarId_1869_);
v_a_2053_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2055_ = v___x_2016_;
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_dec(v___x_2016_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2058_; 
if (v_isShared_2056_ == 0)
{
v___x_2058_ = v___x_2055_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_a_2053_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
v___jp_1970_:
{
lean_object* v___x_1977_; 
lean_inc(v_mvarId_1869_);
v___x_1977_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go(v_mvarId_1869_, v_cfg_1872_, v_term_x3f_1873_, v_a_1967_, v_a_1969_, v_rangeNumArgs_1971_, v_lower_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_);
lean_dec_ref(v_rangeNumArgs_1971_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_object* v_a_1978_; lean_object* v_fst_1979_; lean_object* v_snd_1980_; uint8_t v_newGoals_1981_; uint8_t v_synthAssignedInstances_1982_; uint8_t v_allowSynthFailures_1983_; lean_object* v___x_1984_; 
v_a_1978_ = lean_ctor_get(v___x_1977_, 0);
lean_inc(v_a_1978_);
lean_dec_ref(v___x_1977_);
v_fst_1979_ = lean_ctor_get(v_a_1978_, 0);
lean_inc(v_fst_1979_);
v_snd_1980_ = lean_ctor_get(v_a_1978_, 1);
lean_inc_n(v_snd_1980_, 2);
lean_dec(v_a_1978_);
v_newGoals_1981_ = lean_ctor_get_uint8(v_cfg_1872_, 0);
v_synthAssignedInstances_1982_ = lean_ctor_get_uint8(v_cfg_1872_, 1);
v_allowSynthFailures_1983_ = lean_ctor_get_uint8(v_cfg_1872_, 2);
lean_inc(v_mvarId_1869_);
v___x_1984_ = l_Lean_Meta_synthAppInstances(v___x_1870_, v_mvarId_1869_, v_fst_1979_, v_snd_1980_, v_synthAssignedInstances_1982_, v_allowSynthFailures_1983_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_);
if (lean_obj_tag(v___x_1984_) == 0)
{
lean_object* v___x_1985_; lean_object* v_a_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; uint8_t v___x_1992_; 
lean_dec_ref(v___x_1984_);
v___x_1985_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_e_1871_, v___y_1974_);
v_a_1986_ = lean_ctor_get(v___x_1985_, 0);
lean_inc_n(v_a_1986_, 2);
lean_dec_ref(v___x_1985_);
v___x_1987_ = l_Lean_mkAppN(v_a_1986_, v_fst_1979_);
lean_inc(v_mvarId_1869_);
v___x_1988_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_1869_, v___x_1987_, v___y_1974_);
lean_dec_ref(v___x_1988_);
v___x_1989_ = lean_unsigned_to_nat(0u);
v___x_1990_ = lean_array_get_size(v_fst_1979_);
v___x_1991_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0));
v___x_1992_ = lean_nat_dec_lt(v___x_1989_, v___x_1990_);
if (v___x_1992_ == 0)
{
lean_dec(v_fst_1979_);
v___y_1906_ = v___x_1989_;
v___y_1907_ = v___y_1975_;
v___y_1908_ = v_newGoals_1981_;
v___y_1909_ = v_a_1986_;
v___y_1910_ = v_snd_1980_;
v___y_1911_ = v___y_1974_;
v___y_1912_ = v___y_1973_;
v___y_1913_ = v___y_1976_;
v_a_1914_ = v___x_1991_;
goto v___jp_1905_;
}
else
{
uint8_t v___x_1993_; 
v___x_1993_ = lean_nat_dec_le(v___x_1990_, v___x_1990_);
if (v___x_1993_ == 0)
{
if (v___x_1992_ == 0)
{
lean_dec(v_fst_1979_);
v___y_1906_ = v___x_1989_;
v___y_1907_ = v___y_1975_;
v___y_1908_ = v_newGoals_1981_;
v___y_1909_ = v_a_1986_;
v___y_1910_ = v_snd_1980_;
v___y_1911_ = v___y_1974_;
v___y_1912_ = v___y_1973_;
v___y_1913_ = v___y_1976_;
v_a_1914_ = v___x_1991_;
goto v___jp_1905_;
}
else
{
size_t v___x_1994_; size_t v___x_1995_; lean_object* v___x_1996_; 
v___x_1994_ = ((size_t)0ULL);
v___x_1995_ = lean_usize_of_nat(v___x_1990_);
v___x_1996_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_fst_1979_, v___x_1994_, v___x_1995_, v___x_1991_, v___y_1974_);
lean_dec(v_fst_1979_);
v___y_1947_ = v___x_1989_;
v___y_1948_ = v___y_1975_;
v___y_1949_ = v_newGoals_1981_;
v___y_1950_ = v_snd_1980_;
v___y_1951_ = v_a_1986_;
v___y_1952_ = v___y_1973_;
v___y_1953_ = v___y_1974_;
v___y_1954_ = v___y_1976_;
v___y_1955_ = v___x_1996_;
goto v___jp_1946_;
}
}
else
{
size_t v___x_1997_; size_t v___x_1998_; lean_object* v___x_1999_; 
v___x_1997_ = ((size_t)0ULL);
v___x_1998_ = lean_usize_of_nat(v___x_1990_);
v___x_1999_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_fst_1979_, v___x_1997_, v___x_1998_, v___x_1991_, v___y_1974_);
lean_dec(v_fst_1979_);
v___y_1947_ = v___x_1989_;
v___y_1948_ = v___y_1975_;
v___y_1949_ = v_newGoals_1981_;
v___y_1950_ = v_snd_1980_;
v___y_1951_ = v_a_1986_;
v___y_1952_ = v___y_1973_;
v___y_1953_ = v___y_1974_;
v___y_1954_ = v___y_1976_;
v___y_1955_ = v___x_1999_;
goto v___jp_1946_;
}
}
}
else
{
lean_object* v_a_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2007_; 
lean_dec(v_snd_1980_);
lean_dec(v_fst_1979_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
lean_dec_ref(v_e_1871_);
lean_dec(v_mvarId_1869_);
v_a_2000_ = lean_ctor_get(v___x_1984_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1984_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_2002_ = v___x_1984_;
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_a_2000_);
lean_dec(v___x_1984_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2005_; 
if (v_isShared_2003_ == 0)
{
v___x_2005_ = v___x_2002_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_a_2000_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
}
}
else
{
lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2015_; 
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
lean_dec_ref(v_e_1871_);
lean_dec(v___x_1870_);
lean_dec(v_mvarId_1869_);
v_a_2008_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2010_ = v___x_1977_;
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v___x_1977_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2013_; 
if (v_isShared_2011_ == 0)
{
v___x_2013_ = v___x_2010_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_a_2008_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
}
}
else
{
lean_object* v_a_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2068_; 
lean_dec(v_a_1967_);
lean_dec(v___y_1877_);
lean_dec_ref(v___y_1876_);
lean_dec(v___y_1875_);
lean_dec_ref(v___y_1874_);
lean_dec(v_term_x3f_1873_);
lean_dec_ref(v_e_1871_);
lean_dec(v___x_1870_);
lean_dec(v_mvarId_1869_);
v_a_2061_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2063_ = v___x_1968_;
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_a_2061_);
lean_dec(v___x_1968_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2066_; 
if (v_isShared_2064_ == 0)
{
v___x_2066_ = v___x_2063_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_a_2061_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
}
else
{
lean_object* v_a_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2076_; 
lean_dec(v___y_1877_);
lean_dec_ref(v___y_1876_);
lean_dec(v___y_1875_);
lean_dec_ref(v___y_1874_);
lean_dec(v_term_x3f_1873_);
lean_dec_ref(v_e_1871_);
lean_dec(v___x_1870_);
lean_dec(v_mvarId_1869_);
v_a_2069_ = lean_ctor_get(v___x_1966_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2071_ = v___x_1966_;
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_a_2069_);
lean_dec(v___x_1966_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2074_; 
if (v_isShared_2072_ == 0)
{
v___x_2074_ = v___x_2071_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_a_2069_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
}
}
else
{
lean_object* v_a_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2084_; 
lean_dec(v___y_1877_);
lean_dec_ref(v___y_1876_);
lean_dec(v___y_1875_);
lean_dec_ref(v___y_1874_);
lean_dec(v_term_x3f_1873_);
lean_dec_ref(v_e_1871_);
lean_dec(v___x_1870_);
lean_dec(v_mvarId_1869_);
v_a_2077_ = lean_ctor_get(v___x_1965_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2079_ = v___x_1965_;
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_a_2077_);
lean_dec(v___x_1965_);
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
v___jp_1879_:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1886_ = lean_array_to_list(v___y_1885_);
v___x_1887_ = l_List_appendTR___redArg(v___y_1881_, v___x_1886_);
lean_inc(v___x_1887_);
v___x_1888_ = l_List_forM___at___00Lean_MVarId_apply_spec__3(v___x_1887_, v___y_1883_, v___y_1882_, v___y_1880_, v___y_1884_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1880_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1883_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1895_; 
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1895_ == 0)
{
lean_object* v_unused_1896_; 
v_unused_1896_ = lean_ctor_get(v___x_1888_, 0);
lean_dec(v_unused_1896_);
v___x_1890_ = v___x_1888_;
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
else
{
lean_dec(v___x_1888_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1893_; 
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 0, v___x_1887_);
v___x_1893_ = v___x_1890_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1887_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
else
{
lean_object* v_a_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1904_; 
lean_dec(v___x_1887_);
v_a_1897_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1899_ = v___x_1888_;
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_a_1897_);
lean_dec(v___x_1888_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1902_; 
if (v_isShared_1900_ == 0)
{
v___x_1902_ = v___x_1899_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_a_1897_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
return v___x_1902_;
}
}
}
}
v___jp_1905_:
{
lean_object* v___x_1915_; 
v___x_1915_ = l_Lean_Meta_appendParentTag(v_mvarId_1869_, v_a_1914_, v___y_1910_, v___y_1912_, v___y_1911_, v___y_1907_, v___y_1913_);
lean_dec_ref(v___y_1910_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v___x_1916_; 
lean_dec_ref(v___x_1915_);
v___x_1916_ = l_Lean_Meta_getMVarsNoDelayed(v___y_1909_, v___y_1912_, v___y_1911_, v___y_1907_, v___y_1913_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v_a_1917_; lean_object* v___x_1918_; 
v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
lean_inc(v_a_1917_);
lean_dec_ref(v___x_1916_);
v___x_1918_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(v_a_1914_, v___y_1908_, v___y_1912_, v___y_1911_, v___y_1907_, v___y_1913_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v_a_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; uint8_t v___x_1922_; 
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
lean_inc(v_a_1919_);
lean_dec_ref(v___x_1918_);
v___x_1920_ = lean_array_get_size(v_a_1917_);
v___x_1921_ = lean_mk_empty_array_with_capacity(v___y_1906_);
v___x_1922_ = lean_nat_dec_lt(v___y_1906_, v___x_1920_);
if (v___x_1922_ == 0)
{
lean_dec(v_a_1917_);
v___y_1880_ = v___y_1907_;
v___y_1881_ = v_a_1919_;
v___y_1882_ = v___y_1911_;
v___y_1883_ = v___y_1912_;
v___y_1884_ = v___y_1913_;
v___y_1885_ = v___x_1921_;
goto v___jp_1879_;
}
else
{
uint8_t v___x_1923_; 
v___x_1923_ = lean_nat_dec_le(v___x_1920_, v___x_1920_);
if (v___x_1923_ == 0)
{
if (v___x_1922_ == 0)
{
lean_dec(v_a_1917_);
v___y_1880_ = v___y_1907_;
v___y_1881_ = v_a_1919_;
v___y_1882_ = v___y_1911_;
v___y_1883_ = v___y_1912_;
v___y_1884_ = v___y_1913_;
v___y_1885_ = v___x_1921_;
goto v___jp_1879_;
}
else
{
size_t v___x_1924_; size_t v___x_1925_; lean_object* v___x_1926_; 
v___x_1924_ = ((size_t)0ULL);
v___x_1925_ = lean_usize_of_nat(v___x_1920_);
v___x_1926_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(v_a_1919_, v_a_1917_, v___x_1924_, v___x_1925_, v___x_1921_);
lean_dec(v_a_1917_);
v___y_1880_ = v___y_1907_;
v___y_1881_ = v_a_1919_;
v___y_1882_ = v___y_1911_;
v___y_1883_ = v___y_1912_;
v___y_1884_ = v___y_1913_;
v___y_1885_ = v___x_1926_;
goto v___jp_1879_;
}
}
else
{
size_t v___x_1927_; size_t v___x_1928_; lean_object* v___x_1929_; 
v___x_1927_ = ((size_t)0ULL);
v___x_1928_ = lean_usize_of_nat(v___x_1920_);
v___x_1929_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(v_a_1919_, v_a_1917_, v___x_1927_, v___x_1928_, v___x_1921_);
lean_dec(v_a_1917_);
v___y_1880_ = v___y_1907_;
v___y_1881_ = v_a_1919_;
v___y_1882_ = v___y_1911_;
v___y_1883_ = v___y_1912_;
v___y_1884_ = v___y_1913_;
v___y_1885_ = v___x_1929_;
goto v___jp_1879_;
}
}
}
else
{
lean_dec(v_a_1917_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1907_);
return v___x_1918_;
}
}
else
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1937_; 
lean_dec_ref(v_a_1914_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1907_);
v_a_1930_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1932_ = v___x_1916_;
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1916_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1935_; 
if (v_isShared_1933_ == 0)
{
v___x_1935_ = v___x_1932_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_a_1930_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
}
else
{
lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1945_; 
lean_dec_ref(v_a_1914_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1909_);
lean_dec_ref(v___y_1907_);
v_a_1938_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1940_ = v___x_1915_;
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___x_1915_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1943_; 
if (v_isShared_1941_ == 0)
{
v___x_1943_ = v___x_1940_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_a_1938_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
}
v___jp_1946_:
{
if (lean_obj_tag(v___y_1955_) == 0)
{
lean_object* v_a_1956_; 
v_a_1956_ = lean_ctor_get(v___y_1955_, 0);
lean_inc(v_a_1956_);
lean_dec_ref(v___y_1955_);
v___y_1906_ = v___y_1947_;
v___y_1907_ = v___y_1948_;
v___y_1908_ = v___y_1949_;
v___y_1909_ = v___y_1951_;
v___y_1910_ = v___y_1950_;
v___y_1911_ = v___y_1953_;
v___y_1912_ = v___y_1952_;
v___y_1913_ = v___y_1954_;
v_a_1914_ = v_a_1956_;
goto v___jp_1905_;
}
else
{
lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1964_; 
lean_dec(v___y_1954_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec_ref(v___y_1950_);
lean_dec_ref(v___y_1948_);
lean_dec(v_mvarId_1869_);
v_a_1957_ = lean_ctor_get(v___y_1955_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___y_1955_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1959_ = v___y_1955_;
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v___y_1955_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1962_; 
if (v_isShared_1960_ == 0)
{
v___x_1962_ = v___x_1959_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_a_1957_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___lam__0___boxed(lean_object* v_mvarId_2085_, lean_object* v___x_2086_, lean_object* v_e_2087_, lean_object* v_cfg_2088_, lean_object* v_term_x3f_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_){
_start:
{
lean_object* v_res_2095_; 
v_res_2095_ = l_Lean_MVarId_apply___lam__0(v_mvarId_2085_, v___x_2086_, v_e_2087_, v_cfg_2088_, v_term_x3f_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_);
lean_dec_ref(v_cfg_2088_);
return v_res_2095_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply(lean_object* v_mvarId_2096_, lean_object* v_e_2097_, lean_object* v_cfg_2098_, lean_object* v_term_x3f_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_){
_start:
{
lean_object* v___x_2105_; lean_object* v___f_2106_; lean_object* v___x_2107_; 
v___x_2105_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1));
lean_inc(v_mvarId_2096_);
v___f_2106_ = lean_alloc_closure((void*)(l_Lean_MVarId_apply___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2106_, 0, v_mvarId_2096_);
lean_closure_set(v___f_2106_, 1, v___x_2105_);
lean_closure_set(v___f_2106_, 2, v_e_2097_);
lean_closure_set(v___f_2106_, 3, v_cfg_2098_);
lean_closure_set(v___f_2106_, 4, v_term_x3f_2099_);
v___x_2107_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2096_, v___f_2106_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_);
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___boxed(lean_object* v_mvarId_2108_, lean_object* v_e_2109_, lean_object* v_cfg_2110_, lean_object* v_term_x3f_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_){
_start:
{
lean_object* v_res_2117_; 
v_res_2117_ = l_Lean_MVarId_apply(v_mvarId_2108_, v_e_2109_, v_cfg_2110_, v_term_x3f_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_);
lean_dec(v_a_2115_);
lean_dec_ref(v_a_2114_);
lean_dec(v_a_2113_);
lean_dec_ref(v_a_2112_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1(lean_object* v_mvarId_2118_, lean_object* v_val_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_){
_start:
{
lean_object* v___x_2125_; 
v___x_2125_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2118_, v_val_2119_, v___y_2121_);
return v___x_2125_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___boxed(lean_object* v_mvarId_2126_, lean_object* v_val_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
lean_object* v_res_2133_; 
v_res_2133_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1(v_mvarId_2126_, v_val_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
return v_res_2133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5(lean_object* v_as_2134_, size_t v_i_2135_, size_t v_stop_2136_, lean_object* v_b_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_){
_start:
{
lean_object* v___x_2143_; 
v___x_2143_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_as_2134_, v_i_2135_, v_stop_2136_, v_b_2137_, v___y_2139_);
return v___x_2143_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___boxed(lean_object* v_as_2144_, lean_object* v_i_2145_, lean_object* v_stop_2146_, lean_object* v_b_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
size_t v_i_boxed_2153_; size_t v_stop_boxed_2154_; lean_object* v_res_2155_; 
v_i_boxed_2153_ = lean_unbox_usize(v_i_2145_);
lean_dec(v_i_2145_);
v_stop_boxed_2154_ = lean_unbox_usize(v_stop_2146_);
lean_dec(v_stop_2146_);
v_res_2155_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5(v_as_2144_, v_i_boxed_2153_, v_stop_boxed_2154_, v_b_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_);
lean_dec(v___y_2151_);
lean_dec_ref(v___y_2150_);
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2148_);
lean_dec_ref(v_as_2144_);
return v_res_2155_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1(lean_object* v_00_u03b2_2156_, lean_object* v_x_2157_, lean_object* v_x_2158_, lean_object* v_x_2159_){
_start:
{
lean_object* v___x_2160_; 
v___x_2160_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1___redArg(v_x_2157_, v_x_2158_, v_x_2159_);
return v___x_2160_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_2161_, lean_object* v_x_2162_, size_t v_x_2163_, size_t v_x_2164_, lean_object* v_x_2165_, lean_object* v_x_2166_){
_start:
{
lean_object* v___x_2167_; 
v___x_2167_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_x_2162_, v_x_2163_, v_x_2164_, v_x_2165_, v_x_2166_);
return v___x_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2168_, lean_object* v_x_2169_, lean_object* v_x_2170_, lean_object* v_x_2171_, lean_object* v_x_2172_, lean_object* v_x_2173_){
_start:
{
size_t v_x_7975__boxed_2174_; size_t v_x_7976__boxed_2175_; lean_object* v_res_2176_; 
v_x_7975__boxed_2174_ = lean_unbox_usize(v_x_2170_);
lean_dec(v_x_2170_);
v_x_7976__boxed_2175_ = lean_unbox_usize(v_x_2171_);
lean_dec(v_x_2171_);
v_res_2176_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3(v_00_u03b2_2168_, v_x_2169_, v_x_7975__boxed_2174_, v_x_7976__boxed_2175_, v_x_2172_, v_x_2173_);
return v_res_2176_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_2177_, lean_object* v_n_2178_, lean_object* v_k_2179_, lean_object* v_v_2180_){
_start:
{
lean_object* v___x_2181_; 
v___x_2181_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8___redArg(v_n_2178_, v_k_2179_, v_v_2180_);
return v___x_2181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9(lean_object* v_00_u03b2_2182_, size_t v_depth_2183_, lean_object* v_keys_2184_, lean_object* v_vals_2185_, lean_object* v_heq_2186_, lean_object* v_i_2187_, lean_object* v_entries_2188_){
_start:
{
lean_object* v___x_2189_; 
v___x_2189_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(v_depth_2183_, v_keys_2184_, v_vals_2185_, v_i_2187_, v_entries_2188_);
return v___x_2189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___boxed(lean_object* v_00_u03b2_2190_, lean_object* v_depth_2191_, lean_object* v_keys_2192_, lean_object* v_vals_2193_, lean_object* v_heq_2194_, lean_object* v_i_2195_, lean_object* v_entries_2196_){
_start:
{
size_t v_depth_boxed_2197_; lean_object* v_res_2198_; 
v_depth_boxed_2197_ = lean_unbox_usize(v_depth_2191_);
lean_dec(v_depth_2191_);
v_res_2198_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9(v_00_u03b2_2190_, v_depth_boxed_2197_, v_keys_2192_, v_vals_2193_, v_heq_2194_, v_i_2195_, v_entries_2196_);
lean_dec_ref(v_vals_2193_);
lean_dec_ref(v_keys_2192_);
return v_res_2198_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9(lean_object* v_00_u03b2_2199_, lean_object* v_x_2200_, lean_object* v_x_2201_, lean_object* v_x_2202_, lean_object* v_x_2203_){
_start:
{
lean_object* v___x_2204_; 
v___x_2204_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9___redArg(v_x_2200_, v_x_2201_, v_x_2202_, v_x_2203_);
return v___x_2204_;
}
}
static lean_object* _init_l_Lean_MVarId_applyConst___closed__1(void){
_start:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2206_ = ((lean_object*)(l_Lean_MVarId_applyConst___closed__0));
v___x_2207_ = l_Lean_stringToMessageData(v___x_2206_);
return v___x_2207_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyConst(lean_object* v_mvar_2208_, lean_object* v_c_2209_, lean_object* v_cfg_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_){
_start:
{
lean_object* v___x_2216_; 
lean_inc(v_c_2209_);
v___x_2216_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_c_2209_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_);
if (lean_obj_tag(v___x_2216_) == 0)
{
lean_object* v_a_2217_; lean_object* v___x_2218_; uint8_t v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; 
v_a_2217_ = lean_ctor_get(v___x_2216_, 0);
lean_inc(v_a_2217_);
lean_dec_ref(v___x_2216_);
v___x_2218_ = lean_obj_once(&l_Lean_MVarId_applyConst___closed__1, &l_Lean_MVarId_applyConst___closed__1_once, _init_l_Lean_MVarId_applyConst___closed__1);
v___x_2219_ = 0;
v___x_2220_ = l_Lean_MessageData_ofConstName(v_c_2209_, v___x_2219_);
v___x_2221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2218_);
lean_ctor_set(v___x_2221_, 1, v___x_2220_);
v___x_2222_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2221_);
lean_ctor_set(v___x_2222_, 1, v___x_2218_);
v___x_2223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2222_);
v___x_2224_ = l_Lean_MVarId_apply(v_mvar_2208_, v_a_2217_, v_cfg_2210_, v___x_2223_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_);
return v___x_2224_;
}
else
{
lean_object* v_a_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2232_; 
lean_dec_ref(v_cfg_2210_);
lean_dec(v_c_2209_);
lean_dec(v_mvar_2208_);
v_a_2225_ = lean_ctor_get(v___x_2216_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2216_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2227_ = v___x_2216_;
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_a_2225_);
lean_dec(v___x_2216_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2230_; 
if (v_isShared_2228_ == 0)
{
v___x_2230_ = v___x_2227_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_a_2225_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyConst___boxed(lean_object* v_mvar_2233_, lean_object* v_c_2234_, lean_object* v_cfg_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l_Lean_MVarId_applyConst(v_mvar_2233_, v_c_2234_, v_cfg_2235_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_);
lean_dec(v_a_2239_);
lean_dec_ref(v_a_2238_);
lean_dec(v_a_2237_);
lean_dec_ref(v_a_2236_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1(lean_object* v_msgData_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_){
_start:
{
lean_object* v___x_2248_; lean_object* v_env_2249_; lean_object* v___x_2250_; lean_object* v_mctx_2251_; lean_object* v_lctx_2252_; lean_object* v_options_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2248_ = lean_st_ref_get(v___y_2246_);
v_env_2249_ = lean_ctor_get(v___x_2248_, 0);
lean_inc_ref(v_env_2249_);
lean_dec(v___x_2248_);
v___x_2250_ = lean_st_ref_get(v___y_2244_);
v_mctx_2251_ = lean_ctor_get(v___x_2250_, 0);
lean_inc_ref(v_mctx_2251_);
lean_dec(v___x_2250_);
v_lctx_2252_ = lean_ctor_get(v___y_2243_, 2);
v_options_2253_ = lean_ctor_get(v___y_2245_, 2);
lean_inc_ref(v_options_2253_);
lean_inc_ref(v_lctx_2252_);
v___x_2254_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2254_, 0, v_env_2249_);
lean_ctor_set(v___x_2254_, 1, v_mctx_2251_);
lean_ctor_set(v___x_2254_, 2, v_lctx_2252_);
lean_ctor_set(v___x_2254_, 3, v_options_2253_);
v___x_2255_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2254_);
lean_ctor_set(v___x_2255_, 1, v_msgData_2242_);
v___x_2256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2256_, 0, v___x_2255_);
return v___x_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1___boxed(lean_object* v_msgData_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1(v_msgData_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(lean_object* v_msg_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
lean_object* v_ref_2270_; lean_object* v___x_2271_; lean_object* v_a_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2280_; 
v_ref_2270_ = lean_ctor_get(v___y_2267_, 5);
v___x_2271_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1(v_msg_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_);
v_a_2272_ = lean_ctor_get(v___x_2271_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v___x_2271_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2274_ = v___x_2271_;
v_isShared_2275_ = v_isSharedCheck_2280_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_a_2272_);
lean_dec(v___x_2271_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2280_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2276_; lean_object* v___x_2278_; 
lean_inc(v_ref_2270_);
v___x_2276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2276_, 0, v_ref_2270_);
lean_ctor_set(v___x_2276_, 1, v_a_2272_);
if (v_isShared_2275_ == 0)
{
lean_ctor_set_tag(v___x_2274_, 1);
lean_ctor_set(v___x_2274_, 0, v___x_2276_);
v___x_2278_ = v___x_2274_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v___x_2276_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg___boxed(lean_object* v_msg_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_){
_start:
{
lean_object* v_res_2287_; 
v_res_2287_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v_msg_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_);
lean_dec(v___y_2285_);
lean_dec_ref(v___y_2284_);
lean_dec(v___y_2283_);
lean_dec_ref(v___y_2282_);
return v_res_2287_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0(size_t v_sz_2288_, size_t v_i_2289_, lean_object* v_bs_2290_){
_start:
{
uint8_t v___x_2291_; 
v___x_2291_ = lean_usize_dec_lt(v_i_2289_, v_sz_2288_);
if (v___x_2291_ == 0)
{
return v_bs_2290_;
}
else
{
lean_object* v_v_2292_; lean_object* v___x_2293_; lean_object* v_bs_x27_2294_; lean_object* v___x_2295_; size_t v___x_2296_; size_t v___x_2297_; lean_object* v___x_2298_; 
v_v_2292_ = lean_array_uget(v_bs_2290_, v_i_2289_);
v___x_2293_ = lean_unsigned_to_nat(0u);
v_bs_x27_2294_ = lean_array_uset(v_bs_2290_, v_i_2289_, v___x_2293_);
v___x_2295_ = l_Lean_Expr_mvarId_x21(v_v_2292_);
lean_dec(v_v_2292_);
v___x_2296_ = ((size_t)1ULL);
v___x_2297_ = lean_usize_add(v_i_2289_, v___x_2296_);
v___x_2298_ = lean_array_uset(v_bs_x27_2294_, v_i_2289_, v___x_2295_);
v_i_2289_ = v___x_2297_;
v_bs_2290_ = v___x_2298_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0___boxed(lean_object* v_sz_2300_, lean_object* v_i_2301_, lean_object* v_bs_2302_){
_start:
{
size_t v_sz_boxed_2303_; size_t v_i_boxed_2304_; lean_object* v_res_2305_; 
v_sz_boxed_2303_ = lean_unbox_usize(v_sz_2300_);
lean_dec(v_sz_2300_);
v_i_boxed_2304_ = lean_unbox_usize(v_i_2301_);
lean_dec(v_i_2301_);
v_res_2305_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0(v_sz_boxed_2303_, v_i_boxed_2304_, v_bs_2302_);
return v_res_2305_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2307_; lean_object* v___x_2308_; 
v___x_2307_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__0));
v___x_2308_ = l_Lean_stringToMessageData(v___x_2307_);
return v___x_2308_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___x_2310_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__2));
v___x_2311_ = l_Lean_stringToMessageData(v___x_2310_);
return v___x_2311_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___x_2313_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__4));
v___x_2314_ = l_Lean_stringToMessageData(v___x_2313_);
return v___x_2314_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__7(void){
_start:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; 
v___x_2316_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__6));
v___x_2317_ = l_Lean_stringToMessageData(v___x_2316_);
return v___x_2317_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__9(void){
_start:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___x_2319_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__8));
v___x_2320_ = l_Lean_stringToMessageData(v___x_2319_);
return v___x_2320_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__11(void){
_start:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___x_2322_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__10));
v___x_2323_ = l_Lean_stringToMessageData(v___x_2322_);
return v___x_2323_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN___lam__0(lean_object* v_mvarId_2324_, lean_object* v___x_2325_, lean_object* v_e_2326_, lean_object* v_n_2327_, uint8_t v_useApproxDefEq_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_){
_start:
{
lean_object* v___x_2334_; 
lean_inc(v_mvarId_2324_);
v___x_2334_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2324_, v___x_2325_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_object* v___x_2335_; 
lean_dec_ref(v___x_2334_);
lean_inc(v_mvarId_2324_);
v___x_2335_ = l_Lean_MVarId_getType(v_mvarId_2324_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
if (lean_obj_tag(v___x_2335_) == 0)
{
lean_object* v_a_2336_; lean_object* v___x_2337_; 
v_a_2336_ = lean_ctor_get(v___x_2335_, 0);
lean_inc(v_a_2336_);
lean_dec_ref(v___x_2335_);
lean_inc(v___y_2332_);
lean_inc_ref(v___y_2331_);
lean_inc(v___y_2330_);
lean_inc_ref(v___y_2329_);
lean_inc_ref(v_e_2326_);
v___x_2337_ = lean_infer_type(v_e_2326_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v_a_2338_; uint8_t v___x_2339_; lean_object* v___x_2340_; 
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
lean_inc(v_a_2338_);
lean_dec_ref(v___x_2337_);
v___x_2339_ = 0;
lean_inc(v_n_2327_);
v___x_2340_ = l_Lean_Meta_forallMetaBoundedTelescope(v_a_2338_, v_n_2327_, v___x_2339_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_object* v_a_2341_; lean_object* v_fst_2342_; lean_object* v_snd_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2433_; 
v_a_2341_ = lean_ctor_get(v___x_2340_, 0);
lean_inc(v_a_2341_);
lean_dec_ref(v___x_2340_);
v_fst_2342_ = lean_ctor_get(v_a_2341_, 0);
v_snd_2343_ = lean_ctor_get(v_a_2341_, 1);
v_isSharedCheck_2433_ = !lean_is_exclusive(v_a_2341_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2345_ = v_a_2341_;
v_isShared_2346_ = v_isSharedCheck_2433_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_snd_2343_);
lean_inc(v_fst_2342_);
lean_dec(v_a_2341_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2433_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___y_2348_; lean_object* v_snd_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2431_; 
v_snd_2363_ = lean_ctor_get(v_snd_2343_, 1);
v_isSharedCheck_2431_ = !lean_is_exclusive(v_snd_2343_);
if (v_isSharedCheck_2431_ == 0)
{
lean_object* v_unused_2432_; 
v_unused_2432_ = lean_ctor_get(v_snd_2343_, 0);
lean_dec(v_unused_2432_);
v___x_2365_ = v_snd_2343_;
v_isShared_2366_ = v_isSharedCheck_2431_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_snd_2363_);
lean_dec(v_snd_2343_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2431_;
goto v_resetjp_2364_;
}
v___jp_2347_:
{
lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2361_; 
lean_inc(v_fst_2342_);
v___x_2349_ = l_Lean_Expr_beta(v_e_2326_, v_fst_2342_);
v___x_2350_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2324_, v___x_2349_, v___y_2348_);
lean_dec(v___y_2348_);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2361_ == 0)
{
lean_object* v_unused_2362_; 
v_unused_2362_ = lean_ctor_get(v___x_2350_, 0);
lean_dec(v_unused_2362_);
v___x_2352_ = v___x_2350_;
v_isShared_2353_ = v_isSharedCheck_2361_;
goto v_resetjp_2351_;
}
else
{
lean_dec(v___x_2350_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2361_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
size_t v_sz_2354_; size_t v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2359_; 
v_sz_2354_ = lean_array_size(v_fst_2342_);
v___x_2355_ = ((size_t)0ULL);
v___x_2356_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0(v_sz_2354_, v___x_2355_, v_fst_2342_);
v___x_2357_ = lean_array_to_list(v___x_2356_);
if (v_isShared_2353_ == 0)
{
lean_ctor_set(v___x_2352_, 0, v___x_2357_);
v___x_2359_ = v___x_2352_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v___x_2357_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
return v___x_2359_;
}
}
}
v_resetjp_2364_:
{
lean_object* v___y_2368_; lean_object* v___y_2369_; lean_object* v___y_2370_; lean_object* v___y_2371_; lean_object* v___x_2411_; uint8_t v___x_2412_; 
v___x_2411_ = lean_array_get_size(v_fst_2342_);
v___x_2412_ = lean_nat_dec_eq(v___x_2411_, v_n_2327_);
if (v___x_2412_ == 0)
{
lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v_a_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2430_; 
lean_del_object(v___x_2365_);
lean_del_object(v___x_2345_);
lean_dec(v_fst_2342_);
lean_dec(v_a_2336_);
lean_dec_ref(v_e_2326_);
lean_dec(v_mvarId_2324_);
v___x_2413_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__9, &l_Lean_MVarId_applyN___lam__0___closed__9_once, _init_l_Lean_MVarId_applyN___lam__0___closed__9);
v___x_2414_ = l_Nat_reprFast(v_n_2327_);
v___x_2415_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2415_, 0, v___x_2414_);
v___x_2416_ = l_Lean_MessageData_ofFormat(v___x_2415_);
v___x_2417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2417_, 0, v___x_2413_);
lean_ctor_set(v___x_2417_, 1, v___x_2416_);
v___x_2418_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__11, &l_Lean_MVarId_applyN___lam__0___closed__11_once, _init_l_Lean_MVarId_applyN___lam__0___closed__11);
v___x_2419_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2419_, 0, v___x_2417_);
lean_ctor_set(v___x_2419_, 1, v___x_2418_);
v___x_2420_ = l_Lean_indentExpr(v_snd_2363_);
v___x_2421_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2421_, 0, v___x_2419_);
lean_ctor_set(v___x_2421_, 1, v___x_2420_);
v___x_2422_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_2421_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
v_a_2423_ = lean_ctor_get(v___x_2422_, 0);
v_isSharedCheck_2430_ = !lean_is_exclusive(v___x_2422_);
if (v_isSharedCheck_2430_ == 0)
{
v___x_2425_ = v___x_2422_;
v_isShared_2426_ = v_isSharedCheck_2430_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_a_2423_);
lean_dec(v___x_2422_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2430_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v___x_2428_; 
if (v_isShared_2426_ == 0)
{
v___x_2428_ = v___x_2425_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v_a_2423_);
v___x_2428_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
return v___x_2428_;
}
}
}
else
{
v___y_2368_ = v___y_2329_;
v___y_2369_ = v___y_2330_;
v___y_2370_ = v___y_2331_;
v___y_2371_ = v___y_2332_;
goto v___jp_2367_;
}
v___jp_2367_:
{
lean_object* v___x_2372_; 
lean_inc(v_a_2336_);
lean_inc(v_snd_2363_);
v___x_2372_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(v_useApproxDefEq_2328_, v_snd_2363_, v_a_2336_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_);
if (lean_obj_tag(v___x_2372_) == 0)
{
lean_object* v_a_2373_; uint8_t v___x_2374_; 
v_a_2373_ = lean_ctor_get(v___x_2372_, 0);
lean_inc(v_a_2373_);
lean_dec_ref(v___x_2372_);
v___x_2374_ = lean_unbox(v_a_2373_);
lean_dec(v_a_2373_);
if (v___x_2374_ == 0)
{
lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2378_; 
lean_dec(v_fst_2342_);
lean_dec_ref(v_e_2326_);
lean_dec(v_mvarId_2324_);
v___x_2375_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__1, &l_Lean_MVarId_applyN___lam__0___closed__1_once, _init_l_Lean_MVarId_applyN___lam__0___closed__1);
v___x_2376_ = l_Lean_indentExpr(v_a_2336_);
if (v_isShared_2366_ == 0)
{
lean_ctor_set_tag(v___x_2365_, 7);
lean_ctor_set(v___x_2365_, 1, v___x_2376_);
lean_ctor_set(v___x_2365_, 0, v___x_2375_);
v___x_2378_ = v___x_2365_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v___x_2375_);
lean_ctor_set(v_reuseFailAlloc_2402_, 1, v___x_2376_);
v___x_2378_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
lean_object* v___x_2379_; lean_object* v___x_2381_; 
v___x_2379_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__3, &l_Lean_MVarId_applyN___lam__0___closed__3_once, _init_l_Lean_MVarId_applyN___lam__0___closed__3);
if (v_isShared_2346_ == 0)
{
lean_ctor_set_tag(v___x_2345_, 7);
lean_ctor_set(v___x_2345_, 1, v___x_2379_);
lean_ctor_set(v___x_2345_, 0, v___x_2378_);
v___x_2381_ = v___x_2345_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v___x_2378_);
lean_ctor_set(v_reuseFailAlloc_2401_, 1, v___x_2379_);
v___x_2381_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v_a_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2400_; 
v___x_2382_ = l_Lean_indentExpr(v_snd_2363_);
v___x_2383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2381_);
lean_ctor_set(v___x_2383_, 1, v___x_2382_);
v___x_2384_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__5, &l_Lean_MVarId_applyN___lam__0___closed__5_once, _init_l_Lean_MVarId_applyN___lam__0___closed__5);
v___x_2385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2385_, 0, v___x_2383_);
lean_ctor_set(v___x_2385_, 1, v___x_2384_);
v___x_2386_ = l_Nat_reprFast(v_n_2327_);
v___x_2387_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2386_);
v___x_2388_ = l_Lean_MessageData_ofFormat(v___x_2387_);
v___x_2389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2385_);
lean_ctor_set(v___x_2389_, 1, v___x_2388_);
v___x_2390_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__7, &l_Lean_MVarId_applyN___lam__0___closed__7_once, _init_l_Lean_MVarId_applyN___lam__0___closed__7);
v___x_2391_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2389_);
lean_ctor_set(v___x_2391_, 1, v___x_2390_);
v___x_2392_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_2391_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_);
lean_dec(v___y_2371_);
lean_dec_ref(v___y_2370_);
lean_dec(v___y_2369_);
lean_dec_ref(v___y_2368_);
v_a_2393_ = lean_ctor_get(v___x_2392_, 0);
v_isSharedCheck_2400_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2395_ = v___x_2392_;
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_a_2393_);
lean_dec(v___x_2392_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v___x_2398_; 
if (v_isShared_2396_ == 0)
{
v___x_2398_ = v___x_2395_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v_a_2393_);
v___x_2398_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
return v___x_2398_;
}
}
}
}
}
else
{
lean_dec(v___y_2371_);
lean_dec_ref(v___y_2370_);
lean_dec_ref(v___y_2368_);
lean_del_object(v___x_2365_);
lean_dec(v_snd_2363_);
lean_del_object(v___x_2345_);
lean_dec(v_a_2336_);
lean_dec(v_n_2327_);
v___y_2348_ = v___y_2369_;
goto v___jp_2347_;
}
}
else
{
lean_object* v_a_2403_; lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2410_; 
lean_dec(v___y_2371_);
lean_dec_ref(v___y_2370_);
lean_dec(v___y_2369_);
lean_dec_ref(v___y_2368_);
lean_del_object(v___x_2365_);
lean_dec(v_snd_2363_);
lean_del_object(v___x_2345_);
lean_dec(v_fst_2342_);
lean_dec(v_a_2336_);
lean_dec(v_n_2327_);
lean_dec_ref(v_e_2326_);
lean_dec(v_mvarId_2324_);
v_a_2403_ = lean_ctor_get(v___x_2372_, 0);
v_isSharedCheck_2410_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2410_ == 0)
{
v___x_2405_ = v___x_2372_;
v_isShared_2406_ = v_isSharedCheck_2410_;
goto v_resetjp_2404_;
}
else
{
lean_inc(v_a_2403_);
lean_dec(v___x_2372_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2410_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
lean_object* v___x_2408_; 
if (v_isShared_2406_ == 0)
{
v___x_2408_ = v___x_2405_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v_a_2403_);
v___x_2408_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
return v___x_2408_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2441_; 
lean_dec(v_a_2336_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec(v_n_2327_);
lean_dec_ref(v_e_2326_);
lean_dec(v_mvarId_2324_);
v_a_2434_ = lean_ctor_get(v___x_2340_, 0);
v_isSharedCheck_2441_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2441_ == 0)
{
v___x_2436_ = v___x_2340_;
v_isShared_2437_ = v_isSharedCheck_2441_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_a_2434_);
lean_dec(v___x_2340_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2441_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
lean_object* v___x_2439_; 
if (v_isShared_2437_ == 0)
{
v___x_2439_ = v___x_2436_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v_a_2434_);
v___x_2439_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
return v___x_2439_;
}
}
}
}
else
{
lean_object* v_a_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2449_; 
lean_dec(v_a_2336_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec(v_n_2327_);
lean_dec_ref(v_e_2326_);
lean_dec(v_mvarId_2324_);
v_a_2442_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2449_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2444_ = v___x_2337_;
v_isShared_2445_ = v_isSharedCheck_2449_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_a_2442_);
lean_dec(v___x_2337_);
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
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec(v_n_2327_);
lean_dec_ref(v_e_2326_);
lean_dec(v_mvarId_2324_);
v_a_2450_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2457_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2452_ = v___x_2335_;
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_a_2450_);
lean_dec(v___x_2335_);
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
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec(v_n_2327_);
lean_dec_ref(v_e_2326_);
lean_dec(v_mvarId_2324_);
v_a_2458_ = lean_ctor_get(v___x_2334_, 0);
v_isSharedCheck_2465_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2460_ = v___x_2334_;
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_a_2458_);
lean_dec(v___x_2334_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN___lam__0___boxed(lean_object* v_mvarId_2466_, lean_object* v___x_2467_, lean_object* v_e_2468_, lean_object* v_n_2469_, lean_object* v_useApproxDefEq_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_){
_start:
{
uint8_t v_useApproxDefEq_boxed_2476_; lean_object* v_res_2477_; 
v_useApproxDefEq_boxed_2476_ = lean_unbox(v_useApproxDefEq_2470_);
v_res_2477_ = l_Lean_MVarId_applyN___lam__0(v_mvarId_2466_, v___x_2467_, v_e_2468_, v_n_2469_, v_useApproxDefEq_boxed_2476_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_);
return v_res_2477_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN(lean_object* v_mvarId_2478_, lean_object* v_e_2479_, lean_object* v_n_2480_, uint8_t v_useApproxDefEq_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_){
_start:
{
lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___f_2489_; lean_object* v___x_2490_; 
v___x_2487_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1));
v___x_2488_ = lean_box(v_useApproxDefEq_2481_);
lean_inc(v_mvarId_2478_);
v___f_2489_ = lean_alloc_closure((void*)(l_Lean_MVarId_applyN___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2489_, 0, v_mvarId_2478_);
lean_closure_set(v___f_2489_, 1, v___x_2487_);
lean_closure_set(v___f_2489_, 2, v_e_2479_);
lean_closure_set(v___f_2489_, 3, v_n_2480_);
lean_closure_set(v___f_2489_, 4, v___x_2488_);
v___x_2490_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2478_, v___f_2489_, v_a_2482_, v_a_2483_, v_a_2484_, v_a_2485_);
return v___x_2490_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN___boxed(lean_object* v_mvarId_2491_, lean_object* v_e_2492_, lean_object* v_n_2493_, lean_object* v_useApproxDefEq_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_){
_start:
{
uint8_t v_useApproxDefEq_boxed_2500_; lean_object* v_res_2501_; 
v_useApproxDefEq_boxed_2500_ = lean_unbox(v_useApproxDefEq_2494_);
v_res_2501_ = l_Lean_MVarId_applyN(v_mvarId_2491_, v_e_2492_, v_n_2493_, v_useApproxDefEq_boxed_2500_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_);
lean_dec(v_a_2498_);
lean_dec_ref(v_a_2497_);
lean_dec(v_a_2496_);
lean_dec_ref(v_a_2495_);
return v_res_2501_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1(lean_object* v_00_u03b1_2502_, lean_object* v_msg_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_){
_start:
{
lean_object* v___x_2509_; 
v___x_2509_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v_msg_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_);
return v___x_2509_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___boxed(lean_object* v_00_u03b1_2510_, lean_object* v_msg_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_){
_start:
{
lean_object* v_res_2517_; 
v_res_2517_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1(v_00_u03b1_2510_, v_msg_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_);
lean_dec(v___y_2515_);
lean_dec_ref(v___y_2514_);
lean_dec(v___y_2513_);
lean_dec_ref(v___y_2512_);
return v_res_2517_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6(void){
_start:
{
lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2528_ = lean_box(0);
v___x_2529_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__5));
v___x_2530_ = l_Lean_mkConst(v___x_2529_, v___x_2528_);
return v___x_2530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(lean_object* v_tag_2531_, lean_object* v_type_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_){
_start:
{
lean_object* v___x_2539_; 
lean_inc(v_a_2537_);
lean_inc_ref(v_a_2536_);
lean_inc(v_a_2535_);
lean_inc_ref(v_a_2534_);
v___x_2539_ = lean_whnf(v_type_2532_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_);
if (lean_obj_tag(v___x_2539_) == 0)
{
lean_object* v_a_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; uint8_t v___x_2543_; 
v_a_2540_ = lean_ctor_get(v___x_2539_, 0);
lean_inc(v_a_2540_);
lean_dec_ref(v___x_2539_);
v___x_2541_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__1));
v___x_2542_ = lean_unsigned_to_nat(2u);
v___x_2543_ = l_Lean_Expr_isAppOfArity(v_a_2540_, v___x_2541_, v___x_2542_);
if (v___x_2543_ == 0)
{
lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2544_ = lean_st_ref_get(v_a_2533_);
v___x_2545_ = lean_array_get_size(v___x_2544_);
lean_dec(v___x_2544_);
v___x_2546_ = lean_unsigned_to_nat(1u);
v___x_2547_ = lean_nat_add(v___x_2545_, v___x_2546_);
v___x_2548_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__3));
v___x_2549_ = lean_name_append_index_after(v___x_2548_, v___x_2547_);
v___x_2550_ = l_Lean_Name_append(v_tag_2531_, v___x_2549_);
v___x_2551_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_2540_, v___x_2550_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_);
if (lean_obj_tag(v___x_2551_) == 0)
{
lean_object* v_a_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2563_; 
v_a_2552_ = lean_ctor_get(v___x_2551_, 0);
v_isSharedCheck_2563_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2554_ = v___x_2551_;
v_isShared_2555_ = v_isSharedCheck_2563_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_a_2552_);
lean_dec(v___x_2551_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2563_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2561_; 
v___x_2556_ = lean_st_ref_take(v_a_2533_);
v___x_2557_ = l_Lean_Expr_mvarId_x21(v_a_2552_);
v___x_2558_ = lean_array_push(v___x_2556_, v___x_2557_);
v___x_2559_ = lean_st_ref_set(v_a_2533_, v___x_2558_);
if (v_isShared_2555_ == 0)
{
v___x_2561_ = v___x_2554_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_a_2552_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
return v___x_2561_;
}
}
}
else
{
return v___x_2551_;
}
}
else
{
lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___x_2564_ = l_Lean_Expr_appFn_x21(v_a_2540_);
v___x_2565_ = l_Lean_Expr_appArg_x21(v___x_2564_);
lean_dec_ref(v___x_2564_);
lean_inc_ref(v___x_2565_);
lean_inc(v_tag_2531_);
v___x_2566_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_tag_2531_, v___x_2565_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v_a_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; 
v_a_2567_ = lean_ctor_get(v___x_2566_, 0);
lean_inc(v_a_2567_);
lean_dec_ref(v___x_2566_);
v___x_2568_ = l_Lean_Expr_appArg_x21(v_a_2540_);
lean_dec(v_a_2540_);
lean_inc_ref(v___x_2568_);
v___x_2569_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_tag_2531_, v___x_2568_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_);
if (lean_obj_tag(v___x_2569_) == 0)
{
lean_object* v_a_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2579_; 
v_a_2570_ = lean_ctor_get(v___x_2569_, 0);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2572_ = v___x_2569_;
v_isShared_2573_ = v_isSharedCheck_2579_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_a_2570_);
lean_dec(v___x_2569_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2579_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2577_; 
v___x_2574_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6, &l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6);
v___x_2575_ = l_Lean_mkApp4(v___x_2574_, v___x_2565_, v___x_2568_, v_a_2567_, v_a_2570_);
if (v_isShared_2573_ == 0)
{
lean_ctor_set(v___x_2572_, 0, v___x_2575_);
v___x_2577_ = v___x_2572_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v___x_2575_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
else
{
lean_dec_ref(v___x_2568_);
lean_dec(v_a_2567_);
lean_dec_ref(v___x_2565_);
return v___x_2569_;
}
}
else
{
lean_dec_ref(v___x_2565_);
lean_dec(v_a_2540_);
lean_dec(v_tag_2531_);
return v___x_2566_;
}
}
}
else
{
lean_dec(v_tag_2531_);
return v___x_2539_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___boxed(lean_object* v_tag_2580_, lean_object* v_type_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_){
_start:
{
lean_object* v_res_2588_; 
v_res_2588_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_tag_2580_, v_type_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_);
lean_dec(v_a_2586_);
lean_dec_ref(v_a_2585_);
lean_dec(v_a_2584_);
lean_dec_ref(v_a_2583_);
lean_dec(v_a_2582_);
return v_res_2588_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore___lam__0(lean_object* v_mvarId_2589_, lean_object* v___x_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_){
_start:
{
lean_object* v___x_2596_; 
lean_inc(v_mvarId_2589_);
v___x_2596_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2589_, v___x_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_);
if (lean_obj_tag(v___x_2596_) == 0)
{
lean_object* v___x_2597_; 
lean_dec_ref(v___x_2596_);
lean_inc(v_mvarId_2589_);
v___x_2597_ = l_Lean_MVarId_getType_x27(v_mvarId_2589_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_object* v_a_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2643_; 
v_a_2598_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2600_ = v___x_2597_;
v_isShared_2601_ = v_isSharedCheck_2643_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_a_2598_);
lean_dec(v___x_2597_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2643_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v___x_2602_; lean_object* v___x_2603_; uint8_t v___x_2604_; 
v___x_2602_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__1));
v___x_2603_ = lean_unsigned_to_nat(2u);
v___x_2604_ = l_Lean_Expr_isAppOfArity(v_a_2598_, v___x_2602_, v___x_2603_);
if (v___x_2604_ == 0)
{
lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2608_; 
lean_dec(v_a_2598_);
v___x_2605_ = lean_box(0);
v___x_2606_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2606_, 0, v_mvarId_2589_);
lean_ctor_set(v___x_2606_, 1, v___x_2605_);
if (v_isShared_2601_ == 0)
{
lean_ctor_set(v___x_2600_, 0, v___x_2606_);
v___x_2608_ = v___x_2600_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v___x_2606_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
else
{
lean_object* v___x_2610_; 
lean_del_object(v___x_2600_);
lean_inc(v_mvarId_2589_);
v___x_2610_ = l_Lean_MVarId_getTag(v_mvarId_2589_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_);
if (lean_obj_tag(v___x_2610_) == 0)
{
lean_object* v_a_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; 
v_a_2611_ = lean_ctor_get(v___x_2610_, 0);
lean_inc(v_a_2611_);
lean_dec_ref(v___x_2610_);
v___x_2612_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__0));
v___x_2613_ = lean_st_mk_ref(v___x_2612_);
v___x_2614_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_a_2611_, v_a_2598_, v___x_2613_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_);
if (lean_obj_tag(v___x_2614_) == 0)
{
lean_object* v_a_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2625_; 
v_a_2615_ = lean_ctor_get(v___x_2614_, 0);
lean_inc(v_a_2615_);
lean_dec_ref(v___x_2614_);
v___x_2616_ = lean_st_ref_get(v___x_2613_);
lean_dec(v___x_2613_);
v___x_2617_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2589_, v_a_2615_, v___y_2592_);
v_isSharedCheck_2625_ = !lean_is_exclusive(v___x_2617_);
if (v_isSharedCheck_2625_ == 0)
{
lean_object* v_unused_2626_; 
v_unused_2626_ = lean_ctor_get(v___x_2617_, 0);
lean_dec(v_unused_2626_);
v___x_2619_ = v___x_2617_;
v_isShared_2620_ = v_isSharedCheck_2625_;
goto v_resetjp_2618_;
}
else
{
lean_dec(v___x_2617_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2625_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2621_; lean_object* v___x_2623_; 
v___x_2621_ = lean_array_to_list(v___x_2616_);
if (v_isShared_2620_ == 0)
{
lean_ctor_set(v___x_2619_, 0, v___x_2621_);
v___x_2623_ = v___x_2619_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v___x_2621_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
return v___x_2623_;
}
}
}
else
{
lean_object* v_a_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2634_; 
lean_dec(v___x_2613_);
lean_dec(v_mvarId_2589_);
v_a_2627_ = lean_ctor_get(v___x_2614_, 0);
v_isSharedCheck_2634_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2629_ = v___x_2614_;
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_a_2627_);
lean_dec(v___x_2614_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v___x_2632_; 
if (v_isShared_2630_ == 0)
{
v___x_2632_ = v___x_2629_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_a_2627_);
v___x_2632_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
return v___x_2632_;
}
}
}
}
else
{
lean_object* v_a_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2642_; 
lean_dec(v_a_2598_);
lean_dec(v_mvarId_2589_);
v_a_2635_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2642_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2637_ = v___x_2610_;
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_a_2635_);
lean_dec(v___x_2610_);
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
}
}
else
{
lean_object* v_a_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2651_; 
lean_dec(v_mvarId_2589_);
v_a_2644_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2646_ = v___x_2597_;
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_a_2644_);
lean_dec(v___x_2597_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2649_; 
if (v_isShared_2647_ == 0)
{
v___x_2649_ = v___x_2646_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_a_2644_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
}
}
else
{
lean_object* v_a_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2659_; 
lean_dec(v_mvarId_2589_);
v_a_2652_ = lean_ctor_get(v___x_2596_, 0);
v_isSharedCheck_2659_ = !lean_is_exclusive(v___x_2596_);
if (v_isSharedCheck_2659_ == 0)
{
v___x_2654_ = v___x_2596_;
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_a_2652_);
lean_dec(v___x_2596_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore___lam__0___boxed(lean_object* v_mvarId_2660_, lean_object* v___x_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_){
_start:
{
lean_object* v_res_2667_; 
v_res_2667_ = l_Lean_MVarId_splitAndCore___lam__0(v_mvarId_2660_, v___x_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_);
lean_dec(v___y_2665_);
lean_dec_ref(v___y_2664_);
lean_dec(v___y_2663_);
lean_dec_ref(v___y_2662_);
return v_res_2667_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore(lean_object* v_mvarId_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_){
_start:
{
lean_object* v___x_2677_; lean_object* v___f_2678_; lean_object* v___x_2679_; 
v___x_2677_ = ((lean_object*)(l_Lean_MVarId_splitAndCore___closed__1));
lean_inc(v_mvarId_2671_);
v___f_2678_ = lean_alloc_closure((void*)(l_Lean_MVarId_splitAndCore___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2678_, 0, v_mvarId_2671_);
lean_closure_set(v___f_2678_, 1, v___x_2677_);
v___x_2679_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2671_, v___f_2678_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_);
return v___x_2679_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore___boxed(lean_object* v_mvarId_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_){
_start:
{
lean_object* v_res_2686_; 
v_res_2686_ = l_Lean_MVarId_splitAndCore(v_mvarId_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_);
lean_dec(v_a_2684_);
lean_dec_ref(v_a_2683_);
lean_dec(v_a_2682_);
lean_dec_ref(v_a_2681_);
return v_res_2686_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAnd(lean_object* v_mvarId_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_){
_start:
{
lean_object* v___x_2693_; 
v___x_2693_ = l_Lean_MVarId_splitAndCore(v_mvarId_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_);
return v___x_2693_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAnd___boxed(lean_object* v_mvarId_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_){
_start:
{
lean_object* v_res_2700_; 
v_res_2700_ = l_Lean_MVarId_splitAnd(v_mvarId_2694_, v_a_2695_, v_a_2696_, v_a_2697_, v_a_2698_);
lean_dec(v_a_2698_);
lean_dec_ref(v_a_2697_);
lean_dec(v_a_2696_);
lean_dec_ref(v_a_2695_);
return v_res_2700_;
}
}
static lean_object* _init_l_Lean_MVarId_exfalso___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; 
v___x_2704_ = lean_box(0);
v___x_2705_ = ((lean_object*)(l_Lean_MVarId_exfalso___lam__0___closed__1));
v___x_2706_ = l_Lean_mkConst(v___x_2705_, v___x_2704_);
return v___x_2706_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso___lam__0(lean_object* v_mvarId_2711_, lean_object* v___x_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_){
_start:
{
lean_object* v___x_2718_; 
lean_inc(v_mvarId_2711_);
v___x_2718_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2711_, v___x_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_);
if (lean_obj_tag(v___x_2718_) == 0)
{
lean_object* v___x_2719_; 
lean_dec_ref(v___x_2718_);
lean_inc(v_mvarId_2711_);
v___x_2719_ = l_Lean_MVarId_getType(v_mvarId_2711_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_);
if (lean_obj_tag(v___x_2719_) == 0)
{
lean_object* v_a_2720_; lean_object* v___x_2721_; lean_object* v_a_2722_; lean_object* v___x_2723_; 
v_a_2720_ = lean_ctor_get(v___x_2719_, 0);
lean_inc(v_a_2720_);
lean_dec_ref(v___x_2719_);
v___x_2721_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_a_2720_, v___y_2714_);
v_a_2722_ = lean_ctor_get(v___x_2721_, 0);
lean_inc_n(v_a_2722_, 2);
lean_dec_ref(v___x_2721_);
v___x_2723_ = l_Lean_Meta_getLevel(v_a_2722_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_);
if (lean_obj_tag(v___x_2723_) == 0)
{
lean_object* v_a_2724_; lean_object* v___x_2725_; 
v_a_2724_ = lean_ctor_get(v___x_2723_, 0);
lean_inc(v_a_2724_);
lean_dec_ref(v___x_2723_);
lean_inc(v_mvarId_2711_);
v___x_2725_ = l_Lean_MVarId_getTag(v_mvarId_2711_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_);
if (lean_obj_tag(v___x_2725_) == 0)
{
lean_object* v_a_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; 
v_a_2726_ = lean_ctor_get(v___x_2725_, 0);
lean_inc(v_a_2726_);
lean_dec_ref(v___x_2725_);
v___x_2727_ = lean_box(0);
v___x_2728_ = lean_obj_once(&l_Lean_MVarId_exfalso___lam__0___closed__2, &l_Lean_MVarId_exfalso___lam__0___closed__2_once, _init_l_Lean_MVarId_exfalso___lam__0___closed__2);
v___x_2729_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_2728_, v_a_2726_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_);
if (lean_obj_tag(v___x_2729_) == 0)
{
lean_object* v_a_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2743_; 
v_a_2730_ = lean_ctor_get(v___x_2729_, 0);
lean_inc_n(v_a_2730_, 2);
lean_dec_ref(v___x_2729_);
v___x_2731_ = ((lean_object*)(l_Lean_MVarId_exfalso___lam__0___closed__4));
v___x_2732_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2732_, 0, v_a_2724_);
lean_ctor_set(v___x_2732_, 1, v___x_2727_);
v___x_2733_ = l_Lean_mkConst(v___x_2731_, v___x_2732_);
v___x_2734_ = l_Lean_mkAppB(v___x_2733_, v_a_2722_, v_a_2730_);
v___x_2735_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2711_, v___x_2734_, v___y_2714_);
v_isSharedCheck_2743_ = !lean_is_exclusive(v___x_2735_);
if (v_isSharedCheck_2743_ == 0)
{
lean_object* v_unused_2744_; 
v_unused_2744_ = lean_ctor_get(v___x_2735_, 0);
lean_dec(v_unused_2744_);
v___x_2737_ = v___x_2735_;
v_isShared_2738_ = v_isSharedCheck_2743_;
goto v_resetjp_2736_;
}
else
{
lean_dec(v___x_2735_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2743_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v___x_2739_; lean_object* v___x_2741_; 
v___x_2739_ = l_Lean_Expr_mvarId_x21(v_a_2730_);
lean_dec(v_a_2730_);
if (v_isShared_2738_ == 0)
{
lean_ctor_set(v___x_2737_, 0, v___x_2739_);
v___x_2741_ = v___x_2737_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v___x_2739_);
v___x_2741_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
return v___x_2741_;
}
}
}
else
{
lean_object* v_a_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2752_; 
lean_dec(v_a_2724_);
lean_dec(v_a_2722_);
lean_dec(v_mvarId_2711_);
v_a_2745_ = lean_ctor_get(v___x_2729_, 0);
v_isSharedCheck_2752_ = !lean_is_exclusive(v___x_2729_);
if (v_isSharedCheck_2752_ == 0)
{
v___x_2747_ = v___x_2729_;
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_a_2745_);
lean_dec(v___x_2729_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
lean_object* v___x_2750_; 
if (v_isShared_2748_ == 0)
{
v___x_2750_ = v___x_2747_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v_a_2745_);
v___x_2750_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
return v___x_2750_;
}
}
}
}
else
{
lean_object* v_a_2753_; lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2760_; 
lean_dec(v_a_2724_);
lean_dec(v_a_2722_);
lean_dec(v_mvarId_2711_);
v_a_2753_ = lean_ctor_get(v___x_2725_, 0);
v_isSharedCheck_2760_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2755_ = v___x_2725_;
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
else
{
lean_inc(v_a_2753_);
lean_dec(v___x_2725_);
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
lean_dec(v_a_2722_);
lean_dec(v_mvarId_2711_);
v_a_2761_ = lean_ctor_get(v___x_2723_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2723_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2763_ = v___x_2723_;
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_a_2761_);
lean_dec(v___x_2723_);
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
lean_dec(v_mvarId_2711_);
v_a_2769_ = lean_ctor_get(v___x_2719_, 0);
v_isSharedCheck_2776_ = !lean_is_exclusive(v___x_2719_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2771_ = v___x_2719_;
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_a_2769_);
lean_dec(v___x_2719_);
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
lean_dec(v_mvarId_2711_);
v_a_2777_ = lean_ctor_get(v___x_2718_, 0);
v_isSharedCheck_2784_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2779_ = v___x_2718_;
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_a_2777_);
lean_dec(v___x_2718_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso___lam__0___boxed(lean_object* v_mvarId_2785_, lean_object* v___x_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_){
_start:
{
lean_object* v_res_2792_; 
v_res_2792_ = l_Lean_MVarId_exfalso___lam__0(v_mvarId_2785_, v___x_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
lean_dec(v___y_2790_);
lean_dec_ref(v___y_2789_);
lean_dec(v___y_2788_);
lean_dec_ref(v___y_2787_);
return v_res_2792_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso(lean_object* v_mvarId_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_){
_start:
{
lean_object* v___x_2802_; lean_object* v___f_2803_; lean_object* v___x_2804_; 
v___x_2802_ = ((lean_object*)(l_Lean_MVarId_exfalso___closed__1));
lean_inc(v_mvarId_2796_);
v___f_2803_ = lean_alloc_closure((void*)(l_Lean_MVarId_exfalso___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2803_, 0, v_mvarId_2796_);
lean_closure_set(v___f_2803_, 1, v___x_2802_);
v___x_2804_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2796_, v___f_2803_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_);
return v___x_2804_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso___boxed(lean_object* v_mvarId_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_){
_start:
{
lean_object* v_res_2811_; 
v_res_2811_ = l_Lean_MVarId_exfalso(v_mvarId_2805_, v_a_2806_, v_a_2807_, v_a_2808_, v_a_2809_);
lean_dec(v_a_2809_);
lean_dec_ref(v_a_2808_);
lean_dec(v_a_2807_);
lean_dec_ref(v_a_2806_);
return v_res_2811_;
}
}
static lean_object* _init_l_Lean_MVarId_nthConstructor___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2815_; lean_object* v___x_2816_; 
v___x_2815_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__1));
v___x_2816_ = l_Lean_MessageData_ofFormat(v___x_2815_);
return v___x_2816_;
}
}
static lean_object* _init_l_Lean_MVarId_nthConstructor___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2817_; lean_object* v___x_2818_; 
v___x_2817_ = lean_obj_once(&l_Lean_MVarId_nthConstructor___lam__0___closed__2, &l_Lean_MVarId_nthConstructor___lam__0___closed__2_once, _init_l_Lean_MVarId_nthConstructor___lam__0___closed__2);
v___x_2818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2818_, 0, v___x_2817_);
return v___x_2818_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___lam__0(lean_object* v_goal_2823_, lean_object* v_name_2824_, lean_object* v_idx_2825_, lean_object* v_expected_x3f_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_){
_start:
{
lean_object* v___y_2833_; lean_object* v___y_2834_; lean_object* v___y_2835_; lean_object* v___y_2836_; lean_object* v___x_2839_; 
lean_inc(v_name_2824_);
lean_inc(v_goal_2823_);
v___x_2839_ = l_Lean_MVarId_checkNotAssigned(v_goal_2823_, v_name_2824_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_);
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_object* v___x_2840_; 
lean_dec_ref(v___x_2839_);
lean_inc(v_goal_2823_);
v___x_2840_ = l_Lean_MVarId_getType_x27(v_goal_2823_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_);
if (lean_obj_tag(v___x_2840_) == 0)
{
lean_object* v_a_2841_; lean_object* v___x_2842_; 
v_a_2841_ = lean_ctor_get(v___x_2840_, 0);
lean_inc(v_a_2841_);
lean_dec_ref(v___x_2840_);
v___x_2842_ = l_Lean_Expr_getAppFn(v_a_2841_);
lean_dec(v_a_2841_);
if (lean_obj_tag(v___x_2842_) == 4)
{
lean_object* v_declName_2843_; lean_object* v_us_2844_; lean_object* v___x_2845_; lean_object* v_env_2846_; uint8_t v___x_2847_; lean_object* v___x_2848_; 
v_declName_2843_ = lean_ctor_get(v___x_2842_, 0);
lean_inc(v_declName_2843_);
v_us_2844_ = lean_ctor_get(v___x_2842_, 1);
lean_inc(v_us_2844_);
lean_dec_ref(v___x_2842_);
v___x_2845_ = lean_st_ref_get(v___y_2830_);
v_env_2846_ = lean_ctor_get(v___x_2845_, 0);
lean_inc_ref(v_env_2846_);
lean_dec(v___x_2845_);
v___x_2847_ = 0;
v___x_2848_ = l_Lean_Environment_find_x3f(v_env_2846_, v_declName_2843_, v___x_2847_);
if (lean_obj_tag(v___x_2848_) == 0)
{
lean_dec(v_us_2844_);
lean_dec(v_expected_x3f_2826_);
lean_dec(v_idx_2825_);
v___y_2833_ = v___y_2827_;
v___y_2834_ = v___y_2828_;
v___y_2835_ = v___y_2829_;
v___y_2836_ = v___y_2830_;
goto v___jp_2832_;
}
else
{
lean_object* v_val_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2919_; 
v_val_2849_ = lean_ctor_get(v___x_2848_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2848_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2851_ = v___x_2848_;
v_isShared_2852_ = v_isSharedCheck_2919_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_val_2849_);
lean_dec(v___x_2848_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2919_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
if (lean_obj_tag(v_val_2849_) == 5)
{
lean_object* v_val_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2918_; 
v_val_2853_ = lean_ctor_get(v_val_2849_, 0);
v_isSharedCheck_2918_ = !lean_is_exclusive(v_val_2849_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2855_ = v_val_2849_;
v_isShared_2856_ = v_isSharedCheck_2918_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_val_2853_);
lean_dec(v_val_2849_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2918_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v___y_2858_; lean_object* v___y_2859_; lean_object* v___y_2860_; lean_object* v___y_2861_; 
if (lean_obj_tag(v_expected_x3f_2826_) == 1)
{
lean_object* v_val_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2917_; 
v_val_2888_ = lean_ctor_get(v_expected_x3f_2826_, 0);
v_isSharedCheck_2917_ = !lean_is_exclusive(v_expected_x3f_2826_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2890_ = v_expected_x3f_2826_;
v_isShared_2891_ = v_isSharedCheck_2917_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_val_2888_);
lean_dec(v_expected_x3f_2826_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2917_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v_ctors_2892_; lean_object* v___x_2893_; uint8_t v___x_2894_; 
v_ctors_2892_ = lean_ctor_get(v_val_2853_, 4);
v___x_2893_ = l_List_lengthTR___redArg(v_ctors_2892_);
v___x_2894_ = lean_nat_dec_eq(v___x_2893_, v_val_2888_);
lean_dec(v___x_2893_);
if (v___x_2894_ == 0)
{
uint8_t v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2906_; 
v___x_2895_ = 1;
lean_inc(v_name_2824_);
v___x_2896_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2824_, v___x_2895_);
v___x_2897_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__7));
v___x_2898_ = lean_string_append(v___x_2896_, v___x_2897_);
v___x_2899_ = l_Nat_reprFast(v_val_2888_);
v___x_2900_ = lean_string_append(v___x_2898_, v___x_2899_);
lean_dec_ref(v___x_2899_);
v___x_2901_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__6));
v___x_2902_ = lean_string_append(v___x_2900_, v___x_2901_);
v___x_2903_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2903_, 0, v___x_2902_);
v___x_2904_ = l_Lean_MessageData_ofFormat(v___x_2903_);
if (v_isShared_2891_ == 0)
{
lean_ctor_set(v___x_2890_, 0, v___x_2904_);
v___x_2906_ = v___x_2890_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v___x_2904_);
v___x_2906_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
lean_object* v___x_2907_; 
lean_inc(v_goal_2823_);
lean_inc(v_name_2824_);
v___x_2907_ = l_Lean_Meta_throwTacticEx___redArg(v_name_2824_, v_goal_2823_, v___x_2906_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_);
if (lean_obj_tag(v___x_2907_) == 0)
{
lean_dec_ref(v___x_2907_);
v___y_2858_ = v___y_2827_;
v___y_2859_ = v___y_2828_;
v___y_2860_ = v___y_2829_;
v___y_2861_ = v___y_2830_;
goto v___jp_2857_;
}
else
{
lean_object* v_a_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2915_; 
lean_del_object(v___x_2855_);
lean_dec_ref(v_val_2853_);
lean_del_object(v___x_2851_);
lean_dec(v_us_2844_);
lean_dec(v_idx_2825_);
lean_dec(v_name_2824_);
lean_dec(v_goal_2823_);
v_a_2908_ = lean_ctor_get(v___x_2907_, 0);
v_isSharedCheck_2915_ = !lean_is_exclusive(v___x_2907_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2910_ = v___x_2907_;
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_a_2908_);
lean_dec(v___x_2907_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
lean_object* v___x_2913_; 
if (v_isShared_2911_ == 0)
{
v___x_2913_ = v___x_2910_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_a_2908_);
v___x_2913_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
return v___x_2913_;
}
}
}
}
}
else
{
lean_del_object(v___x_2890_);
lean_dec(v_val_2888_);
v___y_2858_ = v___y_2827_;
v___y_2859_ = v___y_2828_;
v___y_2860_ = v___y_2829_;
v___y_2861_ = v___y_2830_;
goto v___jp_2857_;
}
}
}
else
{
lean_dec(v_expected_x3f_2826_);
v___y_2858_ = v___y_2827_;
v___y_2859_ = v___y_2828_;
v___y_2860_ = v___y_2829_;
v___y_2861_ = v___y_2830_;
goto v___jp_2857_;
}
v___jp_2857_:
{
lean_object* v_ctors_2862_; lean_object* v___x_2863_; uint8_t v___x_2864_; 
v_ctors_2862_ = lean_ctor_get(v_val_2853_, 4);
lean_inc(v_ctors_2862_);
lean_dec_ref(v_val_2853_);
v___x_2863_ = l_List_lengthTR___redArg(v_ctors_2862_);
v___x_2864_ = lean_nat_dec_lt(v_idx_2825_, v___x_2863_);
if (v___x_2864_ == 0)
{
lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2875_; 
lean_dec(v_ctors_2862_);
lean_dec(v_us_2844_);
v___x_2865_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__4));
v___x_2866_ = l_Nat_reprFast(v_idx_2825_);
v___x_2867_ = lean_string_append(v___x_2865_, v___x_2866_);
lean_dec_ref(v___x_2866_);
v___x_2868_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__5));
v___x_2869_ = lean_string_append(v___x_2867_, v___x_2868_);
v___x_2870_ = l_Nat_reprFast(v___x_2863_);
v___x_2871_ = lean_string_append(v___x_2869_, v___x_2870_);
lean_dec_ref(v___x_2870_);
v___x_2872_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__6));
v___x_2873_ = lean_string_append(v___x_2871_, v___x_2872_);
if (v_isShared_2856_ == 0)
{
lean_ctor_set_tag(v___x_2855_, 3);
lean_ctor_set(v___x_2855_, 0, v___x_2873_);
v___x_2875_ = v___x_2855_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v___x_2873_);
v___x_2875_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
lean_object* v___x_2876_; lean_object* v___x_2878_; 
v___x_2876_ = l_Lean_MessageData_ofFormat(v___x_2875_);
if (v_isShared_2852_ == 0)
{
lean_ctor_set(v___x_2851_, 0, v___x_2876_);
v___x_2878_ = v___x_2851_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v___x_2876_);
v___x_2878_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
lean_object* v___x_2879_; 
v___x_2879_ = l_Lean_Meta_throwTacticEx___redArg(v_name_2824_, v_goal_2823_, v___x_2878_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_);
return v___x_2879_;
}
}
}
else
{
lean_object* v___x_2882_; lean_object* v___x_2883_; uint8_t v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; 
lean_dec(v___x_2863_);
lean_del_object(v___x_2855_);
lean_del_object(v___x_2851_);
lean_dec(v_name_2824_);
v___x_2882_ = l_List_get___redArg(v_ctors_2862_, v_idx_2825_);
lean_dec(v_ctors_2862_);
v___x_2883_ = l_Lean_mkConst(v___x_2882_, v_us_2844_);
v___x_2884_ = 0;
v___x_2885_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_2885_, 0, v___x_2884_);
lean_ctor_set_uint8(v___x_2885_, 1, v___x_2864_);
lean_ctor_set_uint8(v___x_2885_, 2, v___x_2847_);
lean_ctor_set_uint8(v___x_2885_, 3, v___x_2864_);
v___x_2886_ = lean_box(0);
v___x_2887_ = l_Lean_MVarId_apply(v_goal_2823_, v___x_2883_, v___x_2885_, v___x_2886_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_);
return v___x_2887_;
}
}
}
}
else
{
lean_del_object(v___x_2851_);
lean_dec(v_val_2849_);
lean_dec(v_us_2844_);
lean_dec(v_expected_x3f_2826_);
lean_dec(v_idx_2825_);
v___y_2833_ = v___y_2827_;
v___y_2834_ = v___y_2828_;
v___y_2835_ = v___y_2829_;
v___y_2836_ = v___y_2830_;
goto v___jp_2832_;
}
}
}
}
else
{
lean_dec_ref(v___x_2842_);
lean_dec(v_expected_x3f_2826_);
lean_dec(v_idx_2825_);
v___y_2833_ = v___y_2827_;
v___y_2834_ = v___y_2828_;
v___y_2835_ = v___y_2829_;
v___y_2836_ = v___y_2830_;
goto v___jp_2832_;
}
}
else
{
lean_object* v_a_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2927_; 
lean_dec(v_expected_x3f_2826_);
lean_dec(v_idx_2825_);
lean_dec(v_name_2824_);
lean_dec(v_goal_2823_);
v_a_2920_ = lean_ctor_get(v___x_2840_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2922_ = v___x_2840_;
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_a_2920_);
lean_dec(v___x_2840_);
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
lean_dec(v_expected_x3f_2826_);
lean_dec(v_idx_2825_);
lean_dec(v_name_2824_);
lean_dec(v_goal_2823_);
v_a_2928_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_2935_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2935_ == 0)
{
v___x_2930_ = v___x_2839_;
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
else
{
lean_inc(v_a_2928_);
lean_dec(v___x_2839_);
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
v___jp_2832_:
{
lean_object* v___x_2837_; lean_object* v___x_2838_; 
v___x_2837_ = lean_obj_once(&l_Lean_MVarId_nthConstructor___lam__0___closed__3, &l_Lean_MVarId_nthConstructor___lam__0___closed__3_once, _init_l_Lean_MVarId_nthConstructor___lam__0___closed__3);
v___x_2838_ = l_Lean_Meta_throwTacticEx___redArg(v_name_2824_, v_goal_2823_, v___x_2837_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_);
return v___x_2838_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___lam__0___boxed(lean_object* v_goal_2936_, lean_object* v_name_2937_, lean_object* v_idx_2938_, lean_object* v_expected_x3f_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_){
_start:
{
lean_object* v_res_2945_; 
v_res_2945_ = l_Lean_MVarId_nthConstructor___lam__0(v_goal_2936_, v_name_2937_, v_idx_2938_, v_expected_x3f_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_);
lean_dec(v___y_2943_);
lean_dec_ref(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
return v_res_2945_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor(lean_object* v_name_2946_, lean_object* v_idx_2947_, lean_object* v_expected_x3f_2948_, lean_object* v_goal_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_){
_start:
{
lean_object* v___f_2955_; lean_object* v___x_2956_; 
lean_inc(v_goal_2949_);
v___f_2955_ = lean_alloc_closure((void*)(l_Lean_MVarId_nthConstructor___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2955_, 0, v_goal_2949_);
lean_closure_set(v___f_2955_, 1, v_name_2946_);
lean_closure_set(v___f_2955_, 2, v_idx_2947_);
lean_closure_set(v___f_2955_, 3, v_expected_x3f_2948_);
v___x_2956_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_goal_2949_, v___f_2955_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_);
return v___x_2956_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___boxed(lean_object* v_name_2957_, lean_object* v_idx_2958_, lean_object* v_expected_x3f_2959_, lean_object* v_goal_2960_, lean_object* v_a_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_){
_start:
{
lean_object* v_res_2966_; 
v_res_2966_ = l_Lean_MVarId_nthConstructor(v_name_2957_, v_idx_2958_, v_expected_x3f_2959_, v_goal_2960_, v_a_2961_, v_a_2962_, v_a_2963_, v_a_2964_);
lean_dec(v_a_2964_);
lean_dec_ref(v_a_2963_);
lean_dec(v_a_2962_);
lean_dec_ref(v_a_2961_);
return v_res_2966_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(lean_object* v_x_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_){
_start:
{
lean_object* v___x_2973_; 
v___x_2973_ = l_Lean_Meta_saveState___redArg(v___y_2969_, v___y_2971_);
if (lean_obj_tag(v___x_2973_) == 0)
{
lean_object* v_a_2974_; lean_object* v___x_2975_; 
v_a_2974_ = lean_ctor_get(v___x_2973_, 0);
lean_inc(v_a_2974_);
lean_dec_ref(v___x_2973_);
lean_inc(v___y_2971_);
lean_inc_ref(v___y_2970_);
lean_inc(v___y_2969_);
lean_inc_ref(v___y_2968_);
v___x_2975_ = lean_apply_5(v_x_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, lean_box(0));
if (lean_obj_tag(v___x_2975_) == 0)
{
lean_object* v_a_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_2984_; 
lean_dec(v_a_2974_);
v_a_2976_ = lean_ctor_get(v___x_2975_, 0);
v_isSharedCheck_2984_ = !lean_is_exclusive(v___x_2975_);
if (v_isSharedCheck_2984_ == 0)
{
v___x_2978_ = v___x_2975_;
v_isShared_2979_ = v_isSharedCheck_2984_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_a_2976_);
lean_dec(v___x_2975_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_2984_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v___x_2980_; lean_object* v___x_2982_; 
v___x_2980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2980_, 0, v_a_2976_);
if (v_isShared_2979_ == 0)
{
lean_ctor_set(v___x_2978_, 0, v___x_2980_);
v___x_2982_ = v___x_2978_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v___x_2980_);
v___x_2982_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
return v___x_2982_;
}
}
}
else
{
lean_object* v_a_2985_; lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_3014_; 
v_a_2985_ = lean_ctor_get(v___x_2975_, 0);
v_isSharedCheck_3014_ = !lean_is_exclusive(v___x_2975_);
if (v_isSharedCheck_3014_ == 0)
{
v___x_2987_ = v___x_2975_;
v_isShared_2988_ = v_isSharedCheck_3014_;
goto v_resetjp_2986_;
}
else
{
lean_inc(v_a_2985_);
lean_dec(v___x_2975_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_3014_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
uint8_t v___y_2990_; uint8_t v___x_3012_; 
v___x_3012_ = l_Lean_Exception_isInterrupt(v_a_2985_);
if (v___x_3012_ == 0)
{
uint8_t v___x_3013_; 
lean_inc(v_a_2985_);
v___x_3013_ = l_Lean_Exception_isRuntime(v_a_2985_);
v___y_2990_ = v___x_3013_;
goto v___jp_2989_;
}
else
{
v___y_2990_ = v___x_3012_;
goto v___jp_2989_;
}
v___jp_2989_:
{
if (v___y_2990_ == 0)
{
lean_object* v___x_2991_; 
lean_del_object(v___x_2987_);
lean_dec(v_a_2985_);
v___x_2991_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2974_, v___y_2969_, v___y_2971_);
lean_dec(v_a_2974_);
if (lean_obj_tag(v___x_2991_) == 0)
{
lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_2999_; 
v_isSharedCheck_2999_ = !lean_is_exclusive(v___x_2991_);
if (v_isSharedCheck_2999_ == 0)
{
lean_object* v_unused_3000_; 
v_unused_3000_ = lean_ctor_get(v___x_2991_, 0);
lean_dec(v_unused_3000_);
v___x_2993_ = v___x_2991_;
v_isShared_2994_ = v_isSharedCheck_2999_;
goto v_resetjp_2992_;
}
else
{
lean_dec(v___x_2991_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_2999_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v___x_2995_; lean_object* v___x_2997_; 
v___x_2995_ = lean_box(0);
if (v_isShared_2994_ == 0)
{
lean_ctor_set(v___x_2993_, 0, v___x_2995_);
v___x_2997_ = v___x_2993_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v___x_2995_);
v___x_2997_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
return v___x_2997_;
}
}
}
else
{
lean_object* v_a_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3008_; 
v_a_3001_ = lean_ctor_get(v___x_2991_, 0);
v_isSharedCheck_3008_ = !lean_is_exclusive(v___x_2991_);
if (v_isSharedCheck_3008_ == 0)
{
v___x_3003_ = v___x_2991_;
v_isShared_3004_ = v_isSharedCheck_3008_;
goto v_resetjp_3002_;
}
else
{
lean_inc(v_a_3001_);
lean_dec(v___x_2991_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3008_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
lean_object* v___x_3006_; 
if (v_isShared_3004_ == 0)
{
v___x_3006_ = v___x_3003_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v_a_3001_);
v___x_3006_ = v_reuseFailAlloc_3007_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
return v___x_3006_;
}
}
}
}
else
{
lean_object* v___x_3010_; 
lean_dec(v_a_2974_);
if (v_isShared_2988_ == 0)
{
v___x_3010_ = v___x_2987_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v_a_2985_);
v___x_3010_ = v_reuseFailAlloc_3011_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
return v___x_3010_;
}
}
}
}
}
}
else
{
lean_object* v_a_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3022_; 
lean_dec_ref(v_x_2967_);
v_a_3015_ = lean_ctor_get(v___x_2973_, 0);
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_2973_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_3017_ = v___x_2973_;
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_a_3015_);
lean_dec(v___x_2973_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
lean_object* v___x_3020_; 
if (v_isShared_3018_ == 0)
{
v___x_3020_ = v___x_3017_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_a_3015_);
v___x_3020_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
return v___x_3020_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg___boxed(lean_object* v_x_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_){
_start:
{
lean_object* v_res_3029_; 
v_res_3029_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v_x_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_);
lean_dec(v___y_3027_);
lean_dec_ref(v___y_3026_);
lean_dec(v___y_3025_);
lean_dec_ref(v___y_3024_);
return v_res_3029_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0(lean_object* v_00_u03b1_3030_, lean_object* v_x_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_){
_start:
{
lean_object* v___x_3037_; 
v___x_3037_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v_x_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_);
return v___x_3037_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___boxed(lean_object* v_00_u03b1_3038_, lean_object* v_x_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_){
_start:
{
lean_object* v_res_3045_; 
v_res_3045_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0(v_00_u03b1_3038_, v_x_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_);
lean_dec(v___y_3043_);
lean_dec_ref(v___y_3042_);
lean_dec(v___y_3041_);
lean_dec_ref(v___y_3040_);
return v_res_3045_;
}
}
static lean_object* _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3047_; lean_object* v___x_3048_; 
v___x_3047_ = ((lean_object*)(l_Lean_MVarId_iffOfEq___lam__0___closed__0));
v___x_3048_ = l_Lean_stringToMessageData(v___x_3047_);
return v___x_3048_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq___lam__0(lean_object* v_mvarId_3049_, lean_object* v___x_3050_, lean_object* v___x_3051_, lean_object* v___x_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_){
_start:
{
lean_object* v___x_3058_; 
v___x_3058_ = l_Lean_MVarId_apply(v_mvarId_3049_, v___x_3050_, v___x_3051_, v___x_3052_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_);
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v_a_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3075_; 
v_a_3059_ = lean_ctor_get(v___x_3058_, 0);
v_isSharedCheck_3075_ = !lean_is_exclusive(v___x_3058_);
if (v_isSharedCheck_3075_ == 0)
{
v___x_3061_ = v___x_3058_;
v_isShared_3062_ = v_isSharedCheck_3075_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_a_3059_);
lean_dec(v___x_3058_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3075_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; 
if (lean_obj_tag(v_a_3059_) == 1)
{
lean_object* v_tail_3070_; 
v_tail_3070_ = lean_ctor_get(v_a_3059_, 1);
if (lean_obj_tag(v_tail_3070_) == 0)
{
lean_object* v_head_3071_; lean_object* v___x_3073_; 
v_head_3071_ = lean_ctor_get(v_a_3059_, 0);
lean_inc(v_head_3071_);
lean_dec_ref(v_a_3059_);
if (v_isShared_3062_ == 0)
{
lean_ctor_set(v___x_3061_, 0, v_head_3071_);
v___x_3073_ = v___x_3061_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v_head_3071_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
else
{
lean_dec_ref(v_a_3059_);
lean_del_object(v___x_3061_);
v___y_3064_ = v___y_3053_;
v___y_3065_ = v___y_3054_;
v___y_3066_ = v___y_3055_;
v___y_3067_ = v___y_3056_;
goto v___jp_3063_;
}
}
else
{
lean_del_object(v___x_3061_);
lean_dec(v_a_3059_);
v___y_3064_ = v___y_3053_;
v___y_3065_ = v___y_3054_;
v___y_3066_ = v___y_3055_;
v___y_3067_ = v___y_3056_;
goto v___jp_3063_;
}
v___jp_3063_:
{
lean_object* v___x_3068_; lean_object* v___x_3069_; 
v___x_3068_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3069_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3068_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_);
return v___x_3069_;
}
}
}
else
{
lean_object* v_a_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3083_; 
v_a_3076_ = lean_ctor_get(v___x_3058_, 0);
v_isSharedCheck_3083_ = !lean_is_exclusive(v___x_3058_);
if (v_isSharedCheck_3083_ == 0)
{
v___x_3078_ = v___x_3058_;
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_a_3076_);
lean_dec(v___x_3058_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___x_3081_; 
if (v_isShared_3079_ == 0)
{
v___x_3081_ = v___x_3078_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3082_; 
v_reuseFailAlloc_3082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3082_, 0, v_a_3076_);
v___x_3081_ = v_reuseFailAlloc_3082_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
return v___x_3081_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq___lam__0___boxed(lean_object* v_mvarId_3084_, lean_object* v___x_3085_, lean_object* v___x_3086_, lean_object* v___x_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_){
_start:
{
lean_object* v_res_3093_; 
v_res_3093_ = l_Lean_MVarId_iffOfEq___lam__0(v_mvarId_3084_, v___x_3085_, v___x_3086_, v___x_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_);
lean_dec(v___y_3091_);
lean_dec_ref(v___y_3090_);
lean_dec(v___y_3089_);
lean_dec_ref(v___y_3088_);
return v_res_3093_;
}
}
static lean_object* _init_l_Lean_MVarId_iffOfEq___closed__2(void){
_start:
{
lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
v___x_3097_ = lean_box(0);
v___x_3098_ = ((lean_object*)(l_Lean_MVarId_iffOfEq___closed__1));
v___x_3099_ = l_Lean_mkConst(v___x_3098_, v___x_3097_);
return v___x_3099_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq(lean_object* v_mvarId_3104_, lean_object* v_a_3105_, lean_object* v_a_3106_, lean_object* v_a_3107_, lean_object* v_a_3108_){
_start:
{
lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___f_3113_; lean_object* v___x_3114_; 
v___x_3110_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___closed__2, &l_Lean_MVarId_iffOfEq___closed__2_once, _init_l_Lean_MVarId_iffOfEq___closed__2);
v___x_3111_ = ((lean_object*)(l_Lean_MVarId_iffOfEq___closed__3));
v___x_3112_ = lean_box(0);
lean_inc(v_mvarId_3104_);
v___f_3113_ = lean_alloc_closure((void*)(l_Lean_MVarId_iffOfEq___lam__0___boxed), 9, 4);
lean_closure_set(v___f_3113_, 0, v_mvarId_3104_);
lean_closure_set(v___f_3113_, 1, v___x_3110_);
lean_closure_set(v___f_3113_, 2, v___x_3111_);
lean_closure_set(v___f_3113_, 3, v___x_3112_);
v___x_3114_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v___f_3113_, v_a_3105_, v_a_3106_, v_a_3107_, v_a_3108_);
if (lean_obj_tag(v___x_3114_) == 0)
{
lean_object* v_a_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3126_; 
v_a_3115_ = lean_ctor_get(v___x_3114_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_3114_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3117_ = v___x_3114_;
v_isShared_3118_ = v_isSharedCheck_3126_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_a_3115_);
lean_dec(v___x_3114_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3126_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
if (lean_obj_tag(v_a_3115_) == 0)
{
lean_object* v___x_3120_; 
if (v_isShared_3118_ == 0)
{
lean_ctor_set(v___x_3117_, 0, v_mvarId_3104_);
v___x_3120_ = v___x_3117_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v_mvarId_3104_);
v___x_3120_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
return v___x_3120_;
}
}
else
{
lean_object* v_val_3122_; lean_object* v___x_3124_; 
lean_dec(v_mvarId_3104_);
v_val_3122_ = lean_ctor_get(v_a_3115_, 0);
lean_inc(v_val_3122_);
lean_dec_ref(v_a_3115_);
if (v_isShared_3118_ == 0)
{
lean_ctor_set(v___x_3117_, 0, v_val_3122_);
v___x_3124_ = v___x_3117_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_val_3122_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
return v___x_3124_;
}
}
}
}
else
{
lean_object* v_a_3127_; lean_object* v___x_3129_; uint8_t v_isShared_3130_; uint8_t v_isSharedCheck_3134_; 
lean_dec(v_mvarId_3104_);
v_a_3127_ = lean_ctor_get(v___x_3114_, 0);
v_isSharedCheck_3134_ = !lean_is_exclusive(v___x_3114_);
if (v_isSharedCheck_3134_ == 0)
{
v___x_3129_ = v___x_3114_;
v_isShared_3130_ = v_isSharedCheck_3134_;
goto v_resetjp_3128_;
}
else
{
lean_inc(v_a_3127_);
lean_dec(v___x_3114_);
v___x_3129_ = lean_box(0);
v_isShared_3130_ = v_isSharedCheck_3134_;
goto v_resetjp_3128_;
}
v_resetjp_3128_:
{
lean_object* v___x_3132_; 
if (v_isShared_3130_ == 0)
{
v___x_3132_ = v___x_3129_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v_a_3127_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq___boxed(lean_object* v_mvarId_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_, lean_object* v_a_3138_, lean_object* v_a_3139_, lean_object* v_a_3140_){
_start:
{
lean_object* v_res_3141_; 
v_res_3141_ = l_Lean_MVarId_iffOfEq(v_mvarId_3135_, v_a_3136_, v_a_3137_, v_a_3138_, v_a_3139_);
lean_dec(v_a_3139_);
lean_dec_ref(v_a_3138_);
lean_dec(v_a_3137_);
lean_dec_ref(v_a_3136_);
return v_res_3141_;
}
}
static lean_object* _init_l_Lean_MVarId_propext___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; 
v___x_3148_ = lean_box(0);
v___x_3149_ = ((lean_object*)(l_Lean_MVarId_propext___lam__0___closed__3));
v___x_3150_ = l_Lean_mkConst(v___x_3149_, v___x_3148_);
return v___x_3150_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___lam__0(uint8_t v___x_3151_, lean_object* v_mvarId_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_){
_start:
{
lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3161_; lean_object* v___y_3162_; lean_object* v___x_3165_; uint8_t v_foApprox_3166_; uint8_t v_ctxApprox_3167_; uint8_t v_quasiPatternApprox_3168_; uint8_t v_constApprox_3169_; uint8_t v_isDefEqStuckEx_3170_; uint8_t v_unificationHints_3171_; uint8_t v_proofIrrelevance_3172_; uint8_t v_assignSyntheticOpaque_3173_; uint8_t v_offsetCnstrs_3174_; uint8_t v_etaStruct_3175_; uint8_t v_univApprox_3176_; uint8_t v_iota_3177_; uint8_t v_beta_3178_; uint8_t v_proj_3179_; uint8_t v_zeta_3180_; uint8_t v_zetaDelta_3181_; uint8_t v_zetaUnused_3182_; uint8_t v_zetaHave_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3271_; 
v___x_3165_ = l_Lean_Meta_Context_config(v___y_3153_);
v_foApprox_3166_ = lean_ctor_get_uint8(v___x_3165_, 0);
v_ctxApprox_3167_ = lean_ctor_get_uint8(v___x_3165_, 1);
v_quasiPatternApprox_3168_ = lean_ctor_get_uint8(v___x_3165_, 2);
v_constApprox_3169_ = lean_ctor_get_uint8(v___x_3165_, 3);
v_isDefEqStuckEx_3170_ = lean_ctor_get_uint8(v___x_3165_, 4);
v_unificationHints_3171_ = lean_ctor_get_uint8(v___x_3165_, 5);
v_proofIrrelevance_3172_ = lean_ctor_get_uint8(v___x_3165_, 6);
v_assignSyntheticOpaque_3173_ = lean_ctor_get_uint8(v___x_3165_, 7);
v_offsetCnstrs_3174_ = lean_ctor_get_uint8(v___x_3165_, 8);
v_etaStruct_3175_ = lean_ctor_get_uint8(v___x_3165_, 10);
v_univApprox_3176_ = lean_ctor_get_uint8(v___x_3165_, 11);
v_iota_3177_ = lean_ctor_get_uint8(v___x_3165_, 12);
v_beta_3178_ = lean_ctor_get_uint8(v___x_3165_, 13);
v_proj_3179_ = lean_ctor_get_uint8(v___x_3165_, 14);
v_zeta_3180_ = lean_ctor_get_uint8(v___x_3165_, 15);
v_zetaDelta_3181_ = lean_ctor_get_uint8(v___x_3165_, 16);
v_zetaUnused_3182_ = lean_ctor_get_uint8(v___x_3165_, 17);
v_zetaHave_3183_ = lean_ctor_get_uint8(v___x_3165_, 18);
v_isSharedCheck_3271_ = !lean_is_exclusive(v___x_3165_);
if (v_isSharedCheck_3271_ == 0)
{
v___x_3185_ = v___x_3165_;
v_isShared_3186_ = v_isSharedCheck_3271_;
goto v_resetjp_3184_;
}
else
{
lean_dec(v___x_3165_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3271_;
goto v_resetjp_3184_;
}
v___jp_3158_:
{
lean_object* v___x_3163_; lean_object* v___x_3164_; 
v___x_3163_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3164_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3163_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_);
return v___x_3164_;
}
v_resetjp_3184_:
{
uint8_t v_trackZetaDelta_3187_; lean_object* v_zetaDeltaSet_3188_; lean_object* v_lctx_3189_; lean_object* v_localInstances_3190_; lean_object* v_defEqCtx_x3f_3191_; lean_object* v_synthPendingDepth_3192_; lean_object* v_canUnfold_x3f_3193_; uint8_t v_univApprox_3194_; uint8_t v_inTypeClassResolution_3195_; uint8_t v_cacheInferType_3196_; lean_object* v_config_3198_; 
v_trackZetaDelta_3187_ = lean_ctor_get_uint8(v___y_3153_, sizeof(void*)*7);
v_zetaDeltaSet_3188_ = lean_ctor_get(v___y_3153_, 1);
v_lctx_3189_ = lean_ctor_get(v___y_3153_, 2);
v_localInstances_3190_ = lean_ctor_get(v___y_3153_, 3);
v_defEqCtx_x3f_3191_ = lean_ctor_get(v___y_3153_, 4);
v_synthPendingDepth_3192_ = lean_ctor_get(v___y_3153_, 5);
v_canUnfold_x3f_3193_ = lean_ctor_get(v___y_3153_, 6);
v_univApprox_3194_ = lean_ctor_get_uint8(v___y_3153_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3195_ = lean_ctor_get_uint8(v___y_3153_, sizeof(void*)*7 + 2);
v_cacheInferType_3196_ = lean_ctor_get_uint8(v___y_3153_, sizeof(void*)*7 + 3);
if (v_isShared_3186_ == 0)
{
v_config_3198_ = v___x_3185_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3270_; 
v_reuseFailAlloc_3270_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3270_, 0, v_foApprox_3166_);
lean_ctor_set_uint8(v_reuseFailAlloc_3270_, 1, v_ctxApprox_3167_);
lean_ctor_set_uint8(v_reuseFailAlloc_3270_, 2, v_quasiPatternApprox_3168_);
lean_ctor_set_uint8(v_reuseFailAlloc_3270_, 3, v_constApprox_3169_);
lean_ctor_set_uint8(v_reuseFailAlloc_3270_, 4, v_isDefEqStuckEx_3170_);
lean_ctor_set_uint8(v_reuseFailAlloc_3270_, 5, v_unificationHints_3171_);
lean_ctor_set_uint8(v_reuseFailAlloc_3270_, 6, v_proofIrrelevance_3172_);
lean_ctor_set_uint8(v_reuseFailAlloc_3270_, 7, v_assignSyntheticOpaque_3173_);
lean_ctor_set_uint8(v_reuseFailAlloc_3270_, 8, v_offsetCnstrs_3174_);
lean_ctor_set_uint8(v_reuseFailAlloc_3270_, 10, v_etaStruct_3175_);
lean_ctor_set_uint8(v_reuseFailAlloc_3270_, 11, v_univApprox_3176_);
lean_ctor_set_uint8(v_reuseFailAlloc_3270_, 12, v_iota_3177_);
lean_ctor_set_uint8(v_reuseFailAlloc_3270_, 13, v_beta_3178_);
lean_ctor_set_uint8(v_reuseFailAlloc_3270_, 14, v_proj_3179_);
lean_ctor_set_uint8(v_reuseFailAlloc_3270_, 15, v_zeta_3180_);
lean_ctor_set_uint8(v_reuseFailAlloc_3270_, 16, v_zetaDelta_3181_);
lean_ctor_set_uint8(v_reuseFailAlloc_3270_, 17, v_zetaUnused_3182_);
lean_ctor_set_uint8(v_reuseFailAlloc_3270_, 18, v_zetaHave_3183_);
v_config_3198_ = v_reuseFailAlloc_3270_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
uint64_t v___x_3199_; uint64_t v___x_3200_; uint64_t v___x_3201_; uint64_t v___x_3202_; uint64_t v___x_3203_; uint64_t v_key_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; 
lean_ctor_set_uint8(v_config_3198_, 9, v___x_3151_);
v___x_3199_ = l_Lean_Meta_Context_configKey(v___y_3153_);
v___x_3200_ = 2ULL;
v___x_3201_ = lean_uint64_shift_right(v___x_3199_, v___x_3200_);
v___x_3202_ = lean_uint64_shift_left(v___x_3201_, v___x_3200_);
v___x_3203_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3151_);
v_key_3204_ = lean_uint64_lor(v___x_3202_, v___x_3203_);
v___x_3205_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3205_, 0, v_config_3198_);
lean_ctor_set_uint64(v___x_3205_, sizeof(void*)*1, v_key_3204_);
lean_inc(v_canUnfold_x3f_3193_);
lean_inc(v_synthPendingDepth_3192_);
lean_inc(v_defEqCtx_x3f_3191_);
lean_inc_ref(v_localInstances_3190_);
lean_inc_ref(v_lctx_3189_);
lean_inc(v_zetaDeltaSet_3188_);
v___x_3206_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3206_, 0, v___x_3205_);
lean_ctor_set(v___x_3206_, 1, v_zetaDeltaSet_3188_);
lean_ctor_set(v___x_3206_, 2, v_lctx_3189_);
lean_ctor_set(v___x_3206_, 3, v_localInstances_3190_);
lean_ctor_set(v___x_3206_, 4, v_defEqCtx_x3f_3191_);
lean_ctor_set(v___x_3206_, 5, v_synthPendingDepth_3192_);
lean_ctor_set(v___x_3206_, 6, v_canUnfold_x3f_3193_);
lean_ctor_set_uint8(v___x_3206_, sizeof(void*)*7, v_trackZetaDelta_3187_);
lean_ctor_set_uint8(v___x_3206_, sizeof(void*)*7 + 1, v_univApprox_3194_);
lean_ctor_set_uint8(v___x_3206_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3195_);
lean_ctor_set_uint8(v___x_3206_, sizeof(void*)*7 + 3, v_cacheInferType_3196_);
lean_inc(v_mvarId_3152_);
v___x_3207_ = l_Lean_MVarId_getType_x27(v_mvarId_3152_, v___x_3206_, v___y_3154_, v___y_3155_, v___y_3156_);
lean_dec_ref(v___x_3206_);
if (lean_obj_tag(v___x_3207_) == 0)
{
lean_object* v_a_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; uint8_t v___x_3211_; 
v_a_3208_ = lean_ctor_get(v___x_3207_, 0);
lean_inc(v_a_3208_);
lean_dec_ref(v___x_3207_);
v___x_3209_ = ((lean_object*)(l_Lean_MVarId_propext___lam__0___closed__1));
v___x_3210_ = lean_unsigned_to_nat(3u);
v___x_3211_ = l_Lean_Expr_isAppOfArity(v_a_3208_, v___x_3209_, v___x_3210_);
if (v___x_3211_ == 0)
{
lean_object* v___x_3237_; lean_object* v___x_3238_; 
lean_dec(v_a_3208_);
lean_dec(v_mvarId_3152_);
v___x_3237_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3238_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3237_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_);
return v___x_3238_;
}
else
{
lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; 
v___x_3239_ = l_Lean_Expr_appFn_x21(v_a_3208_);
lean_dec(v_a_3208_);
v___x_3240_ = l_Lean_Expr_appArg_x21(v___x_3239_);
lean_dec_ref(v___x_3239_);
v___x_3241_ = l_Lean_Meta_isProp(v___x_3240_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_);
if (lean_obj_tag(v___x_3241_) == 0)
{
lean_object* v_a_3242_; uint8_t v___x_3243_; 
v_a_3242_ = lean_ctor_get(v___x_3241_, 0);
lean_inc(v_a_3242_);
lean_dec_ref(v___x_3241_);
v___x_3243_ = lean_unbox(v_a_3242_);
lean_dec(v_a_3242_);
if (v___x_3243_ == 0)
{
lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v_a_3246_; lean_object* v___x_3248_; uint8_t v_isShared_3249_; uint8_t v_isSharedCheck_3253_; 
lean_dec(v_mvarId_3152_);
v___x_3244_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3245_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3244_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_);
v_a_3246_ = lean_ctor_get(v___x_3245_, 0);
v_isSharedCheck_3253_ = !lean_is_exclusive(v___x_3245_);
if (v_isSharedCheck_3253_ == 0)
{
v___x_3248_ = v___x_3245_;
v_isShared_3249_ = v_isSharedCheck_3253_;
goto v_resetjp_3247_;
}
else
{
lean_inc(v_a_3246_);
lean_dec(v___x_3245_);
v___x_3248_ = lean_box(0);
v_isShared_3249_ = v_isSharedCheck_3253_;
goto v_resetjp_3247_;
}
v_resetjp_3247_:
{
lean_object* v___x_3251_; 
if (v_isShared_3249_ == 0)
{
v___x_3251_ = v___x_3248_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3252_; 
v_reuseFailAlloc_3252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3252_, 0, v_a_3246_);
v___x_3251_ = v_reuseFailAlloc_3252_;
goto v_reusejp_3250_;
}
v_reusejp_3250_:
{
return v___x_3251_;
}
}
}
else
{
goto v___jp_3212_;
}
}
else
{
lean_object* v_a_3254_; lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3261_; 
lean_dec(v_mvarId_3152_);
v_a_3254_ = lean_ctor_get(v___x_3241_, 0);
v_isSharedCheck_3261_ = !lean_is_exclusive(v___x_3241_);
if (v_isSharedCheck_3261_ == 0)
{
v___x_3256_ = v___x_3241_;
v_isShared_3257_ = v_isSharedCheck_3261_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_a_3254_);
lean_dec(v___x_3241_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3261_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
lean_object* v___x_3259_; 
if (v_isShared_3257_ == 0)
{
v___x_3259_ = v___x_3256_;
goto v_reusejp_3258_;
}
else
{
lean_object* v_reuseFailAlloc_3260_; 
v_reuseFailAlloc_3260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3260_, 0, v_a_3254_);
v___x_3259_ = v_reuseFailAlloc_3260_;
goto v_reusejp_3258_;
}
v_reusejp_3258_:
{
return v___x_3259_;
}
}
}
}
v___jp_3212_:
{
lean_object* v___x_3213_; uint8_t v___x_3214_; uint8_t v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; 
v___x_3213_ = lean_obj_once(&l_Lean_MVarId_propext___lam__0___closed__4, &l_Lean_MVarId_propext___lam__0___closed__4_once, _init_l_Lean_MVarId_propext___lam__0___closed__4);
v___x_3214_ = 0;
v___x_3215_ = 0;
v___x_3216_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3216_, 0, v___x_3214_);
lean_ctor_set_uint8(v___x_3216_, 1, v___x_3211_);
lean_ctor_set_uint8(v___x_3216_, 2, v___x_3215_);
lean_ctor_set_uint8(v___x_3216_, 3, v___x_3211_);
v___x_3217_ = lean_box(0);
v___x_3218_ = l_Lean_MVarId_apply(v_mvarId_3152_, v___x_3213_, v___x_3216_, v___x_3217_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_);
if (lean_obj_tag(v___x_3218_) == 0)
{
lean_object* v_a_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3228_; 
v_a_3219_ = lean_ctor_get(v___x_3218_, 0);
v_isSharedCheck_3228_ = !lean_is_exclusive(v___x_3218_);
if (v_isSharedCheck_3228_ == 0)
{
v___x_3221_ = v___x_3218_;
v_isShared_3222_ = v_isSharedCheck_3228_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_a_3219_);
lean_dec(v___x_3218_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3228_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
if (lean_obj_tag(v_a_3219_) == 1)
{
lean_object* v_tail_3223_; 
v_tail_3223_ = lean_ctor_get(v_a_3219_, 1);
if (lean_obj_tag(v_tail_3223_) == 0)
{
lean_object* v_head_3224_; lean_object* v___x_3226_; 
v_head_3224_ = lean_ctor_get(v_a_3219_, 0);
lean_inc(v_head_3224_);
lean_dec_ref(v_a_3219_);
if (v_isShared_3222_ == 0)
{
lean_ctor_set(v___x_3221_, 0, v_head_3224_);
v___x_3226_ = v___x_3221_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v_head_3224_);
v___x_3226_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
return v___x_3226_;
}
}
else
{
lean_dec_ref(v_a_3219_);
lean_del_object(v___x_3221_);
v___y_3159_ = v___y_3153_;
v___y_3160_ = v___y_3154_;
v___y_3161_ = v___y_3155_;
v___y_3162_ = v___y_3156_;
goto v___jp_3158_;
}
}
else
{
lean_del_object(v___x_3221_);
lean_dec(v_a_3219_);
v___y_3159_ = v___y_3153_;
v___y_3160_ = v___y_3154_;
v___y_3161_ = v___y_3155_;
v___y_3162_ = v___y_3156_;
goto v___jp_3158_;
}
}
}
else
{
lean_object* v_a_3229_; lean_object* v___x_3231_; uint8_t v_isShared_3232_; uint8_t v_isSharedCheck_3236_; 
v_a_3229_ = lean_ctor_get(v___x_3218_, 0);
v_isSharedCheck_3236_ = !lean_is_exclusive(v___x_3218_);
if (v_isSharedCheck_3236_ == 0)
{
v___x_3231_ = v___x_3218_;
v_isShared_3232_ = v_isSharedCheck_3236_;
goto v_resetjp_3230_;
}
else
{
lean_inc(v_a_3229_);
lean_dec(v___x_3218_);
v___x_3231_ = lean_box(0);
v_isShared_3232_ = v_isSharedCheck_3236_;
goto v_resetjp_3230_;
}
v_resetjp_3230_:
{
lean_object* v___x_3234_; 
if (v_isShared_3232_ == 0)
{
v___x_3234_ = v___x_3231_;
goto v_reusejp_3233_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v_a_3229_);
v___x_3234_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3233_;
}
v_reusejp_3233_:
{
return v___x_3234_;
}
}
}
}
}
else
{
lean_object* v_a_3262_; lean_object* v___x_3264_; uint8_t v_isShared_3265_; uint8_t v_isSharedCheck_3269_; 
lean_dec(v_mvarId_3152_);
v_a_3262_ = lean_ctor_get(v___x_3207_, 0);
v_isSharedCheck_3269_ = !lean_is_exclusive(v___x_3207_);
if (v_isSharedCheck_3269_ == 0)
{
v___x_3264_ = v___x_3207_;
v_isShared_3265_ = v_isSharedCheck_3269_;
goto v_resetjp_3263_;
}
else
{
lean_inc(v_a_3262_);
lean_dec(v___x_3207_);
v___x_3264_ = lean_box(0);
v_isShared_3265_ = v_isSharedCheck_3269_;
goto v_resetjp_3263_;
}
v_resetjp_3263_:
{
lean_object* v___x_3267_; 
if (v_isShared_3265_ == 0)
{
v___x_3267_ = v___x_3264_;
goto v_reusejp_3266_;
}
else
{
lean_object* v_reuseFailAlloc_3268_; 
v_reuseFailAlloc_3268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3268_, 0, v_a_3262_);
v___x_3267_ = v_reuseFailAlloc_3268_;
goto v_reusejp_3266_;
}
v_reusejp_3266_:
{
return v___x_3267_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___lam__0___boxed(lean_object* v___x_3272_, lean_object* v_mvarId_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_){
_start:
{
uint8_t v___x_2435__boxed_3279_; lean_object* v_res_3280_; 
v___x_2435__boxed_3279_ = lean_unbox(v___x_3272_);
v_res_3280_ = l_Lean_MVarId_propext___lam__0(v___x_2435__boxed_3279_, v_mvarId_3273_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_);
lean_dec(v___y_3277_);
lean_dec_ref(v___y_3276_);
lean_dec(v___y_3275_);
lean_dec_ref(v___y_3274_);
return v_res_3280_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext(lean_object* v_mvarId_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_){
_start:
{
uint8_t v___x_3287_; lean_object* v___x_3288_; lean_object* v___f_3289_; lean_object* v___x_3290_; 
v___x_3287_ = 2;
v___x_3288_ = lean_box(v___x_3287_);
lean_inc(v_mvarId_3281_);
v___f_3289_ = lean_alloc_closure((void*)(l_Lean_MVarId_propext___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3289_, 0, v___x_3288_);
lean_closure_set(v___f_3289_, 1, v_mvarId_3281_);
v___x_3290_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v___f_3289_, v_a_3282_, v_a_3283_, v_a_3284_, v_a_3285_);
if (lean_obj_tag(v___x_3290_) == 0)
{
lean_object* v_a_3291_; lean_object* v___x_3293_; uint8_t v_isShared_3294_; uint8_t v_isSharedCheck_3302_; 
v_a_3291_ = lean_ctor_get(v___x_3290_, 0);
v_isSharedCheck_3302_ = !lean_is_exclusive(v___x_3290_);
if (v_isSharedCheck_3302_ == 0)
{
v___x_3293_ = v___x_3290_;
v_isShared_3294_ = v_isSharedCheck_3302_;
goto v_resetjp_3292_;
}
else
{
lean_inc(v_a_3291_);
lean_dec(v___x_3290_);
v___x_3293_ = lean_box(0);
v_isShared_3294_ = v_isSharedCheck_3302_;
goto v_resetjp_3292_;
}
v_resetjp_3292_:
{
if (lean_obj_tag(v_a_3291_) == 0)
{
lean_object* v___x_3296_; 
if (v_isShared_3294_ == 0)
{
lean_ctor_set(v___x_3293_, 0, v_mvarId_3281_);
v___x_3296_ = v___x_3293_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3297_; 
v_reuseFailAlloc_3297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3297_, 0, v_mvarId_3281_);
v___x_3296_ = v_reuseFailAlloc_3297_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
return v___x_3296_;
}
}
else
{
lean_object* v_val_3298_; lean_object* v___x_3300_; 
lean_dec(v_mvarId_3281_);
v_val_3298_ = lean_ctor_get(v_a_3291_, 0);
lean_inc(v_val_3298_);
lean_dec_ref(v_a_3291_);
if (v_isShared_3294_ == 0)
{
lean_ctor_set(v___x_3293_, 0, v_val_3298_);
v___x_3300_ = v___x_3293_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v_val_3298_);
v___x_3300_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
return v___x_3300_;
}
}
}
}
else
{
lean_object* v_a_3303_; lean_object* v___x_3305_; uint8_t v_isShared_3306_; uint8_t v_isSharedCheck_3310_; 
lean_dec(v_mvarId_3281_);
v_a_3303_ = lean_ctor_get(v___x_3290_, 0);
v_isSharedCheck_3310_ = !lean_is_exclusive(v___x_3290_);
if (v_isSharedCheck_3310_ == 0)
{
v___x_3305_ = v___x_3290_;
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
else
{
lean_inc(v_a_3303_);
lean_dec(v___x_3290_);
v___x_3305_ = lean_box(0);
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
v_resetjp_3304_:
{
lean_object* v___x_3308_; 
if (v_isShared_3306_ == 0)
{
v___x_3308_ = v___x_3305_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3309_; 
v_reuseFailAlloc_3309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3309_, 0, v_a_3303_);
v___x_3308_ = v_reuseFailAlloc_3309_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
return v___x_3308_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___boxed(lean_object* v_mvarId_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_, lean_object* v_a_3316_){
_start:
{
lean_object* v_res_3317_; 
v_res_3317_ = l_Lean_MVarId_propext(v_mvarId_3311_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_);
lean_dec(v_a_3315_);
lean_dec_ref(v_a_3314_);
lean_dec(v_a_3313_);
lean_dec_ref(v_a_3312_);
return v_res_3317_;
}
}
static uint64_t _init_l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0(void){
_start:
{
uint8_t v___x_3318_; uint64_t v___x_3319_; 
v___x_3318_ = 2;
v___x_3319_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3318_);
return v___x_3319_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__0(lean_object* v_mvarId_3326_, lean_object* v___x_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_){
_start:
{
lean_object* v___x_3333_; 
lean_inc(v_mvarId_3326_);
v___x_3333_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3326_, v___x_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_);
if (lean_obj_tag(v___x_3333_) == 0)
{
lean_object* v___x_3334_; uint8_t v_foApprox_3335_; uint8_t v_ctxApprox_3336_; uint8_t v_quasiPatternApprox_3337_; uint8_t v_constApprox_3338_; uint8_t v_isDefEqStuckEx_3339_; uint8_t v_unificationHints_3340_; uint8_t v_proofIrrelevance_3341_; uint8_t v_assignSyntheticOpaque_3342_; uint8_t v_offsetCnstrs_3343_; uint8_t v_etaStruct_3344_; uint8_t v_univApprox_3345_; uint8_t v_iota_3346_; uint8_t v_beta_3347_; uint8_t v_proj_3348_; uint8_t v_zeta_3349_; uint8_t v_zetaDelta_3350_; uint8_t v_zetaUnused_3351_; uint8_t v_zetaHave_3352_; lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3422_; 
lean_dec_ref(v___x_3333_);
v___x_3334_ = l_Lean_Meta_Context_config(v___y_3328_);
v_foApprox_3335_ = lean_ctor_get_uint8(v___x_3334_, 0);
v_ctxApprox_3336_ = lean_ctor_get_uint8(v___x_3334_, 1);
v_quasiPatternApprox_3337_ = lean_ctor_get_uint8(v___x_3334_, 2);
v_constApprox_3338_ = lean_ctor_get_uint8(v___x_3334_, 3);
v_isDefEqStuckEx_3339_ = lean_ctor_get_uint8(v___x_3334_, 4);
v_unificationHints_3340_ = lean_ctor_get_uint8(v___x_3334_, 5);
v_proofIrrelevance_3341_ = lean_ctor_get_uint8(v___x_3334_, 6);
v_assignSyntheticOpaque_3342_ = lean_ctor_get_uint8(v___x_3334_, 7);
v_offsetCnstrs_3343_ = lean_ctor_get_uint8(v___x_3334_, 8);
v_etaStruct_3344_ = lean_ctor_get_uint8(v___x_3334_, 10);
v_univApprox_3345_ = lean_ctor_get_uint8(v___x_3334_, 11);
v_iota_3346_ = lean_ctor_get_uint8(v___x_3334_, 12);
v_beta_3347_ = lean_ctor_get_uint8(v___x_3334_, 13);
v_proj_3348_ = lean_ctor_get_uint8(v___x_3334_, 14);
v_zeta_3349_ = lean_ctor_get_uint8(v___x_3334_, 15);
v_zetaDelta_3350_ = lean_ctor_get_uint8(v___x_3334_, 16);
v_zetaUnused_3351_ = lean_ctor_get_uint8(v___x_3334_, 17);
v_zetaHave_3352_ = lean_ctor_get_uint8(v___x_3334_, 18);
v_isSharedCheck_3422_ = !lean_is_exclusive(v___x_3334_);
if (v_isSharedCheck_3422_ == 0)
{
v___x_3354_ = v___x_3334_;
v_isShared_3355_ = v_isSharedCheck_3422_;
goto v_resetjp_3353_;
}
else
{
lean_dec(v___x_3334_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3422_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
uint8_t v_trackZetaDelta_3356_; lean_object* v_zetaDeltaSet_3357_; lean_object* v_lctx_3358_; lean_object* v_localInstances_3359_; lean_object* v_defEqCtx_x3f_3360_; lean_object* v_synthPendingDepth_3361_; lean_object* v_canUnfold_x3f_3362_; uint8_t v_univApprox_3363_; uint8_t v_inTypeClassResolution_3364_; uint8_t v_cacheInferType_3365_; uint8_t v___x_3366_; lean_object* v_config_3368_; 
v_trackZetaDelta_3356_ = lean_ctor_get_uint8(v___y_3328_, sizeof(void*)*7);
v_zetaDeltaSet_3357_ = lean_ctor_get(v___y_3328_, 1);
v_lctx_3358_ = lean_ctor_get(v___y_3328_, 2);
v_localInstances_3359_ = lean_ctor_get(v___y_3328_, 3);
v_defEqCtx_x3f_3360_ = lean_ctor_get(v___y_3328_, 4);
v_synthPendingDepth_3361_ = lean_ctor_get(v___y_3328_, 5);
v_canUnfold_x3f_3362_ = lean_ctor_get(v___y_3328_, 6);
v_univApprox_3363_ = lean_ctor_get_uint8(v___y_3328_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3364_ = lean_ctor_get_uint8(v___y_3328_, sizeof(void*)*7 + 2);
v_cacheInferType_3365_ = lean_ctor_get_uint8(v___y_3328_, sizeof(void*)*7 + 3);
v___x_3366_ = 2;
if (v_isShared_3355_ == 0)
{
v_config_3368_ = v___x_3354_;
goto v_reusejp_3367_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3421_, 0, v_foApprox_3335_);
lean_ctor_set_uint8(v_reuseFailAlloc_3421_, 1, v_ctxApprox_3336_);
lean_ctor_set_uint8(v_reuseFailAlloc_3421_, 2, v_quasiPatternApprox_3337_);
lean_ctor_set_uint8(v_reuseFailAlloc_3421_, 3, v_constApprox_3338_);
lean_ctor_set_uint8(v_reuseFailAlloc_3421_, 4, v_isDefEqStuckEx_3339_);
lean_ctor_set_uint8(v_reuseFailAlloc_3421_, 5, v_unificationHints_3340_);
lean_ctor_set_uint8(v_reuseFailAlloc_3421_, 6, v_proofIrrelevance_3341_);
lean_ctor_set_uint8(v_reuseFailAlloc_3421_, 7, v_assignSyntheticOpaque_3342_);
lean_ctor_set_uint8(v_reuseFailAlloc_3421_, 8, v_offsetCnstrs_3343_);
lean_ctor_set_uint8(v_reuseFailAlloc_3421_, 10, v_etaStruct_3344_);
lean_ctor_set_uint8(v_reuseFailAlloc_3421_, 11, v_univApprox_3345_);
lean_ctor_set_uint8(v_reuseFailAlloc_3421_, 12, v_iota_3346_);
lean_ctor_set_uint8(v_reuseFailAlloc_3421_, 13, v_beta_3347_);
lean_ctor_set_uint8(v_reuseFailAlloc_3421_, 14, v_proj_3348_);
lean_ctor_set_uint8(v_reuseFailAlloc_3421_, 15, v_zeta_3349_);
lean_ctor_set_uint8(v_reuseFailAlloc_3421_, 16, v_zetaDelta_3350_);
lean_ctor_set_uint8(v_reuseFailAlloc_3421_, 17, v_zetaUnused_3351_);
lean_ctor_set_uint8(v_reuseFailAlloc_3421_, 18, v_zetaHave_3352_);
v_config_3368_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3367_;
}
v_reusejp_3367_:
{
uint64_t v___x_3369_; uint64_t v___x_3370_; uint64_t v___x_3371_; uint64_t v___x_3372_; uint64_t v___x_3373_; uint64_t v_key_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; 
lean_ctor_set_uint8(v_config_3368_, 9, v___x_3366_);
v___x_3369_ = l_Lean_Meta_Context_configKey(v___y_3328_);
v___x_3370_ = 2ULL;
v___x_3371_ = lean_uint64_shift_right(v___x_3369_, v___x_3370_);
v___x_3372_ = lean_uint64_shift_left(v___x_3371_, v___x_3370_);
v___x_3373_ = lean_uint64_once(&l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0, &l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0_once, _init_l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0);
v_key_3374_ = lean_uint64_lor(v___x_3372_, v___x_3373_);
v___x_3375_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3375_, 0, v_config_3368_);
lean_ctor_set_uint64(v___x_3375_, sizeof(void*)*1, v_key_3374_);
lean_inc(v_canUnfold_x3f_3362_);
lean_inc(v_synthPendingDepth_3361_);
lean_inc(v_defEqCtx_x3f_3360_);
lean_inc_ref(v_localInstances_3359_);
lean_inc_ref(v_lctx_3358_);
lean_inc(v_zetaDeltaSet_3357_);
v___x_3376_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3376_, 0, v___x_3375_);
lean_ctor_set(v___x_3376_, 1, v_zetaDeltaSet_3357_);
lean_ctor_set(v___x_3376_, 2, v_lctx_3358_);
lean_ctor_set(v___x_3376_, 3, v_localInstances_3359_);
lean_ctor_set(v___x_3376_, 4, v_defEqCtx_x3f_3360_);
lean_ctor_set(v___x_3376_, 5, v_synthPendingDepth_3361_);
lean_ctor_set(v___x_3376_, 6, v_canUnfold_x3f_3362_);
lean_ctor_set_uint8(v___x_3376_, sizeof(void*)*7, v_trackZetaDelta_3356_);
lean_ctor_set_uint8(v___x_3376_, sizeof(void*)*7 + 1, v_univApprox_3363_);
lean_ctor_set_uint8(v___x_3376_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3364_);
lean_ctor_set_uint8(v___x_3376_, sizeof(void*)*7 + 3, v_cacheInferType_3365_);
lean_inc(v_mvarId_3326_);
v___x_3377_ = l_Lean_MVarId_getType_x27(v_mvarId_3326_, v___x_3376_, v___y_3329_, v___y_3330_, v___y_3331_);
lean_dec_ref(v___x_3376_);
if (lean_obj_tag(v___x_3377_) == 0)
{
lean_object* v_a_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; uint8_t v___x_3381_; 
v_a_3378_ = lean_ctor_get(v___x_3377_, 0);
lean_inc(v_a_3378_);
lean_dec_ref(v___x_3377_);
v___x_3379_ = ((lean_object*)(l_Lean_MVarId_proofIrrelHeq___lam__0___closed__2));
v___x_3380_ = lean_unsigned_to_nat(4u);
v___x_3381_ = l_Lean_Expr_isAppOfArity(v_a_3378_, v___x_3379_, v___x_3380_);
if (v___x_3381_ == 0)
{
lean_object* v___x_3382_; lean_object* v___x_3383_; 
lean_dec(v_a_3378_);
lean_dec(v_mvarId_3326_);
v___x_3382_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3383_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3382_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_);
return v___x_3383_;
}
else
{
lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; 
v___x_3384_ = l_Lean_Expr_appFn_x21(v_a_3378_);
v___x_3385_ = l_Lean_Expr_appFn_x21(v___x_3384_);
lean_dec_ref(v___x_3384_);
v___x_3386_ = l_Lean_Expr_appArg_x21(v___x_3385_);
lean_dec_ref(v___x_3385_);
v___x_3387_ = l_Lean_Expr_appArg_x21(v_a_3378_);
lean_dec(v_a_3378_);
v___x_3388_ = ((lean_object*)(l_Lean_MVarId_proofIrrelHeq___lam__0___closed__4));
v___x_3389_ = lean_unsigned_to_nat(2u);
v___x_3390_ = lean_mk_empty_array_with_capacity(v___x_3389_);
v___x_3391_ = lean_array_push(v___x_3390_, v___x_3386_);
v___x_3392_ = lean_array_push(v___x_3391_, v___x_3387_);
v___x_3393_ = l_Lean_Meta_mkAppM(v___x_3388_, v___x_3392_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_);
if (lean_obj_tag(v___x_3393_) == 0)
{
lean_object* v_a_3394_; lean_object* v___x_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3403_; 
v_a_3394_ = lean_ctor_get(v___x_3393_, 0);
lean_inc(v_a_3394_);
lean_dec_ref(v___x_3393_);
v___x_3395_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_3326_, v_a_3394_, v___y_3329_);
v_isSharedCheck_3403_ = !lean_is_exclusive(v___x_3395_);
if (v_isSharedCheck_3403_ == 0)
{
lean_object* v_unused_3404_; 
v_unused_3404_ = lean_ctor_get(v___x_3395_, 0);
lean_dec(v_unused_3404_);
v___x_3397_ = v___x_3395_;
v_isShared_3398_ = v_isSharedCheck_3403_;
goto v_resetjp_3396_;
}
else
{
lean_dec(v___x_3395_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3403_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
lean_object* v___x_3399_; lean_object* v___x_3401_; 
v___x_3399_ = lean_box(v___x_3381_);
if (v_isShared_3398_ == 0)
{
lean_ctor_set(v___x_3397_, 0, v___x_3399_);
v___x_3401_ = v___x_3397_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v___x_3399_);
v___x_3401_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
return v___x_3401_;
}
}
}
else
{
lean_object* v_a_3405_; lean_object* v___x_3407_; uint8_t v_isShared_3408_; uint8_t v_isSharedCheck_3412_; 
lean_dec(v_mvarId_3326_);
v_a_3405_ = lean_ctor_get(v___x_3393_, 0);
v_isSharedCheck_3412_ = !lean_is_exclusive(v___x_3393_);
if (v_isSharedCheck_3412_ == 0)
{
v___x_3407_ = v___x_3393_;
v_isShared_3408_ = v_isSharedCheck_3412_;
goto v_resetjp_3406_;
}
else
{
lean_inc(v_a_3405_);
lean_dec(v___x_3393_);
v___x_3407_ = lean_box(0);
v_isShared_3408_ = v_isSharedCheck_3412_;
goto v_resetjp_3406_;
}
v_resetjp_3406_:
{
lean_object* v___x_3410_; 
if (v_isShared_3408_ == 0)
{
v___x_3410_ = v___x_3407_;
goto v_reusejp_3409_;
}
else
{
lean_object* v_reuseFailAlloc_3411_; 
v_reuseFailAlloc_3411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3411_, 0, v_a_3405_);
v___x_3410_ = v_reuseFailAlloc_3411_;
goto v_reusejp_3409_;
}
v_reusejp_3409_:
{
return v___x_3410_;
}
}
}
}
}
else
{
lean_object* v_a_3413_; lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3420_; 
lean_dec(v_mvarId_3326_);
v_a_3413_ = lean_ctor_get(v___x_3377_, 0);
v_isSharedCheck_3420_ = !lean_is_exclusive(v___x_3377_);
if (v_isSharedCheck_3420_ == 0)
{
v___x_3415_ = v___x_3377_;
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
else
{
lean_inc(v_a_3413_);
lean_dec(v___x_3377_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v___x_3418_; 
if (v_isShared_3416_ == 0)
{
v___x_3418_ = v___x_3415_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v_a_3413_);
v___x_3418_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
return v___x_3418_;
}
}
}
}
}
}
else
{
lean_object* v_a_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3430_; 
lean_dec(v_mvarId_3326_);
v_a_3423_ = lean_ctor_get(v___x_3333_, 0);
v_isSharedCheck_3430_ = !lean_is_exclusive(v___x_3333_);
if (v_isSharedCheck_3430_ == 0)
{
v___x_3425_ = v___x_3333_;
v_isShared_3426_ = v_isSharedCheck_3430_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_a_3423_);
lean_dec(v___x_3333_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3430_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
lean_object* v___x_3428_; 
if (v_isShared_3426_ == 0)
{
v___x_3428_ = v___x_3425_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v_a_3423_);
v___x_3428_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
return v___x_3428_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__0___boxed(lean_object* v_mvarId_3431_, lean_object* v___x_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_){
_start:
{
lean_object* v_res_3438_; 
v_res_3438_ = l_Lean_MVarId_proofIrrelHeq___lam__0(v_mvarId_3431_, v___x_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_);
lean_dec(v___y_3436_);
lean_dec_ref(v___y_3435_);
lean_dec(v___y_3434_);
lean_dec_ref(v___y_3433_);
return v_res_3438_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__1(lean_object* v___f_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_){
_start:
{
lean_object* v___x_3445_; 
v___x_3445_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v___f_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_);
if (lean_obj_tag(v___x_3445_) == 0)
{
lean_object* v_a_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3459_; 
v_a_3446_ = lean_ctor_get(v___x_3445_, 0);
v_isSharedCheck_3459_ = !lean_is_exclusive(v___x_3445_);
if (v_isSharedCheck_3459_ == 0)
{
v___x_3448_ = v___x_3445_;
v_isShared_3449_ = v_isSharedCheck_3459_;
goto v_resetjp_3447_;
}
else
{
lean_inc(v_a_3446_);
lean_dec(v___x_3445_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3459_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
if (lean_obj_tag(v_a_3446_) == 0)
{
uint8_t v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3453_; 
v___x_3450_ = 0;
v___x_3451_ = lean_box(v___x_3450_);
if (v_isShared_3449_ == 0)
{
lean_ctor_set(v___x_3448_, 0, v___x_3451_);
v___x_3453_ = v___x_3448_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v___x_3451_);
v___x_3453_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
return v___x_3453_;
}
}
else
{
lean_object* v_val_3455_; lean_object* v___x_3457_; 
v_val_3455_ = lean_ctor_get(v_a_3446_, 0);
lean_inc(v_val_3455_);
lean_dec_ref(v_a_3446_);
if (v_isShared_3449_ == 0)
{
lean_ctor_set(v___x_3448_, 0, v_val_3455_);
v___x_3457_ = v___x_3448_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v_val_3455_);
v___x_3457_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
return v___x_3457_;
}
}
}
}
else
{
lean_object* v_a_3460_; lean_object* v___x_3462_; uint8_t v_isShared_3463_; uint8_t v_isSharedCheck_3467_; 
v_a_3460_ = lean_ctor_get(v___x_3445_, 0);
v_isSharedCheck_3467_ = !lean_is_exclusive(v___x_3445_);
if (v_isSharedCheck_3467_ == 0)
{
v___x_3462_ = v___x_3445_;
v_isShared_3463_ = v_isSharedCheck_3467_;
goto v_resetjp_3461_;
}
else
{
lean_inc(v_a_3460_);
lean_dec(v___x_3445_);
v___x_3462_ = lean_box(0);
v_isShared_3463_ = v_isSharedCheck_3467_;
goto v_resetjp_3461_;
}
v_resetjp_3461_:
{
lean_object* v___x_3465_; 
if (v_isShared_3463_ == 0)
{
v___x_3465_ = v___x_3462_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v_a_3460_);
v___x_3465_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
return v___x_3465_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__1___boxed(lean_object* v___f_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_){
_start:
{
lean_object* v_res_3474_; 
v_res_3474_ = l_Lean_MVarId_proofIrrelHeq___lam__1(v___f_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_);
lean_dec(v___y_3472_);
lean_dec_ref(v___y_3471_);
lean_dec(v___y_3470_);
lean_dec_ref(v___y_3469_);
return v_res_3474_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq(lean_object* v_mvarId_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_){
_start:
{
lean_object* v___x_3484_; lean_object* v___f_3485_; lean_object* v___f_3486_; lean_object* v___x_3487_; 
v___x_3484_ = ((lean_object*)(l_Lean_MVarId_proofIrrelHeq___closed__1));
lean_inc(v_mvarId_3478_);
v___f_3485_ = lean_alloc_closure((void*)(l_Lean_MVarId_proofIrrelHeq___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3485_, 0, v_mvarId_3478_);
lean_closure_set(v___f_3485_, 1, v___x_3484_);
v___f_3486_ = lean_alloc_closure((void*)(l_Lean_MVarId_proofIrrelHeq___lam__1___boxed), 6, 1);
lean_closure_set(v___f_3486_, 0, v___f_3485_);
v___x_3487_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_3478_, v___f_3486_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_);
return v___x_3487_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___boxed(lean_object* v_mvarId_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_){
_start:
{
lean_object* v_res_3494_; 
v_res_3494_ = l_Lean_MVarId_proofIrrelHeq(v_mvarId_3488_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_);
lean_dec(v_a_3492_);
lean_dec_ref(v_a_3491_);
lean_dec(v_a_3490_);
lean_dec_ref(v_a_3489_);
return v_res_3494_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim___lam__0(lean_object* v_mvarId_3499_, lean_object* v___x_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_){
_start:
{
lean_object* v___x_3506_; 
lean_inc(v_mvarId_3499_);
v___x_3506_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3499_, v___x_3500_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_);
if (lean_obj_tag(v___x_3506_) == 0)
{
lean_object* v___x_3507_; uint8_t v_foApprox_3508_; uint8_t v_ctxApprox_3509_; uint8_t v_quasiPatternApprox_3510_; uint8_t v_constApprox_3511_; uint8_t v_isDefEqStuckEx_3512_; uint8_t v_unificationHints_3513_; uint8_t v_proofIrrelevance_3514_; uint8_t v_assignSyntheticOpaque_3515_; uint8_t v_offsetCnstrs_3516_; uint8_t v_etaStruct_3517_; uint8_t v_univApprox_3518_; uint8_t v_iota_3519_; uint8_t v_beta_3520_; uint8_t v_proj_3521_; uint8_t v_zeta_3522_; uint8_t v_zetaDelta_3523_; uint8_t v_zetaUnused_3524_; uint8_t v_zetaHave_3525_; lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3594_; 
lean_dec_ref(v___x_3506_);
v___x_3507_ = l_Lean_Meta_Context_config(v___y_3501_);
v_foApprox_3508_ = lean_ctor_get_uint8(v___x_3507_, 0);
v_ctxApprox_3509_ = lean_ctor_get_uint8(v___x_3507_, 1);
v_quasiPatternApprox_3510_ = lean_ctor_get_uint8(v___x_3507_, 2);
v_constApprox_3511_ = lean_ctor_get_uint8(v___x_3507_, 3);
v_isDefEqStuckEx_3512_ = lean_ctor_get_uint8(v___x_3507_, 4);
v_unificationHints_3513_ = lean_ctor_get_uint8(v___x_3507_, 5);
v_proofIrrelevance_3514_ = lean_ctor_get_uint8(v___x_3507_, 6);
v_assignSyntheticOpaque_3515_ = lean_ctor_get_uint8(v___x_3507_, 7);
v_offsetCnstrs_3516_ = lean_ctor_get_uint8(v___x_3507_, 8);
v_etaStruct_3517_ = lean_ctor_get_uint8(v___x_3507_, 10);
v_univApprox_3518_ = lean_ctor_get_uint8(v___x_3507_, 11);
v_iota_3519_ = lean_ctor_get_uint8(v___x_3507_, 12);
v_beta_3520_ = lean_ctor_get_uint8(v___x_3507_, 13);
v_proj_3521_ = lean_ctor_get_uint8(v___x_3507_, 14);
v_zeta_3522_ = lean_ctor_get_uint8(v___x_3507_, 15);
v_zetaDelta_3523_ = lean_ctor_get_uint8(v___x_3507_, 16);
v_zetaUnused_3524_ = lean_ctor_get_uint8(v___x_3507_, 17);
v_zetaHave_3525_ = lean_ctor_get_uint8(v___x_3507_, 18);
v_isSharedCheck_3594_ = !lean_is_exclusive(v___x_3507_);
if (v_isSharedCheck_3594_ == 0)
{
v___x_3527_ = v___x_3507_;
v_isShared_3528_ = v_isSharedCheck_3594_;
goto v_resetjp_3526_;
}
else
{
lean_dec(v___x_3507_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_3594_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
uint8_t v_trackZetaDelta_3529_; lean_object* v_zetaDeltaSet_3530_; lean_object* v_lctx_3531_; lean_object* v_localInstances_3532_; lean_object* v_defEqCtx_x3f_3533_; lean_object* v_synthPendingDepth_3534_; lean_object* v_canUnfold_x3f_3535_; uint8_t v_univApprox_3536_; uint8_t v_inTypeClassResolution_3537_; uint8_t v_cacheInferType_3538_; uint8_t v___x_3539_; lean_object* v_config_3541_; 
v_trackZetaDelta_3529_ = lean_ctor_get_uint8(v___y_3501_, sizeof(void*)*7);
v_zetaDeltaSet_3530_ = lean_ctor_get(v___y_3501_, 1);
v_lctx_3531_ = lean_ctor_get(v___y_3501_, 2);
v_localInstances_3532_ = lean_ctor_get(v___y_3501_, 3);
v_defEqCtx_x3f_3533_ = lean_ctor_get(v___y_3501_, 4);
v_synthPendingDepth_3534_ = lean_ctor_get(v___y_3501_, 5);
v_canUnfold_x3f_3535_ = lean_ctor_get(v___y_3501_, 6);
v_univApprox_3536_ = lean_ctor_get_uint8(v___y_3501_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3537_ = lean_ctor_get_uint8(v___y_3501_, sizeof(void*)*7 + 2);
v_cacheInferType_3538_ = lean_ctor_get_uint8(v___y_3501_, sizeof(void*)*7 + 3);
v___x_3539_ = 2;
if (v_isShared_3528_ == 0)
{
v_config_3541_ = v___x_3527_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3593_, 0, v_foApprox_3508_);
lean_ctor_set_uint8(v_reuseFailAlloc_3593_, 1, v_ctxApprox_3509_);
lean_ctor_set_uint8(v_reuseFailAlloc_3593_, 2, v_quasiPatternApprox_3510_);
lean_ctor_set_uint8(v_reuseFailAlloc_3593_, 3, v_constApprox_3511_);
lean_ctor_set_uint8(v_reuseFailAlloc_3593_, 4, v_isDefEqStuckEx_3512_);
lean_ctor_set_uint8(v_reuseFailAlloc_3593_, 5, v_unificationHints_3513_);
lean_ctor_set_uint8(v_reuseFailAlloc_3593_, 6, v_proofIrrelevance_3514_);
lean_ctor_set_uint8(v_reuseFailAlloc_3593_, 7, v_assignSyntheticOpaque_3515_);
lean_ctor_set_uint8(v_reuseFailAlloc_3593_, 8, v_offsetCnstrs_3516_);
lean_ctor_set_uint8(v_reuseFailAlloc_3593_, 10, v_etaStruct_3517_);
lean_ctor_set_uint8(v_reuseFailAlloc_3593_, 11, v_univApprox_3518_);
lean_ctor_set_uint8(v_reuseFailAlloc_3593_, 12, v_iota_3519_);
lean_ctor_set_uint8(v_reuseFailAlloc_3593_, 13, v_beta_3520_);
lean_ctor_set_uint8(v_reuseFailAlloc_3593_, 14, v_proj_3521_);
lean_ctor_set_uint8(v_reuseFailAlloc_3593_, 15, v_zeta_3522_);
lean_ctor_set_uint8(v_reuseFailAlloc_3593_, 16, v_zetaDelta_3523_);
lean_ctor_set_uint8(v_reuseFailAlloc_3593_, 17, v_zetaUnused_3524_);
lean_ctor_set_uint8(v_reuseFailAlloc_3593_, 18, v_zetaHave_3525_);
v_config_3541_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
uint64_t v___x_3542_; uint64_t v___x_3543_; uint64_t v___x_3544_; uint64_t v___x_3545_; uint64_t v___x_3546_; uint64_t v_key_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; 
lean_ctor_set_uint8(v_config_3541_, 9, v___x_3539_);
v___x_3542_ = l_Lean_Meta_Context_configKey(v___y_3501_);
v___x_3543_ = 2ULL;
v___x_3544_ = lean_uint64_shift_right(v___x_3542_, v___x_3543_);
v___x_3545_ = lean_uint64_shift_left(v___x_3544_, v___x_3543_);
v___x_3546_ = lean_uint64_once(&l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0, &l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0_once, _init_l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0);
v_key_3547_ = lean_uint64_lor(v___x_3545_, v___x_3546_);
v___x_3548_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3548_, 0, v_config_3541_);
lean_ctor_set_uint64(v___x_3548_, sizeof(void*)*1, v_key_3547_);
lean_inc(v_canUnfold_x3f_3535_);
lean_inc(v_synthPendingDepth_3534_);
lean_inc(v_defEqCtx_x3f_3533_);
lean_inc_ref(v_localInstances_3532_);
lean_inc_ref(v_lctx_3531_);
lean_inc(v_zetaDeltaSet_3530_);
v___x_3549_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3549_, 0, v___x_3548_);
lean_ctor_set(v___x_3549_, 1, v_zetaDeltaSet_3530_);
lean_ctor_set(v___x_3549_, 2, v_lctx_3531_);
lean_ctor_set(v___x_3549_, 3, v_localInstances_3532_);
lean_ctor_set(v___x_3549_, 4, v_defEqCtx_x3f_3533_);
lean_ctor_set(v___x_3549_, 5, v_synthPendingDepth_3534_);
lean_ctor_set(v___x_3549_, 6, v_canUnfold_x3f_3535_);
lean_ctor_set_uint8(v___x_3549_, sizeof(void*)*7, v_trackZetaDelta_3529_);
lean_ctor_set_uint8(v___x_3549_, sizeof(void*)*7 + 1, v_univApprox_3536_);
lean_ctor_set_uint8(v___x_3549_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3537_);
lean_ctor_set_uint8(v___x_3549_, sizeof(void*)*7 + 3, v_cacheInferType_3538_);
lean_inc(v_mvarId_3499_);
v___x_3550_ = l_Lean_MVarId_getType_x27(v_mvarId_3499_, v___x_3549_, v___y_3502_, v___y_3503_, v___y_3504_);
lean_dec_ref(v___x_3549_);
if (lean_obj_tag(v___x_3550_) == 0)
{
lean_object* v_a_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; uint8_t v___x_3554_; 
v_a_3551_ = lean_ctor_get(v___x_3550_, 0);
lean_inc(v_a_3551_);
lean_dec_ref(v___x_3550_);
v___x_3552_ = ((lean_object*)(l_Lean_MVarId_propext___lam__0___closed__1));
v___x_3553_ = lean_unsigned_to_nat(3u);
v___x_3554_ = l_Lean_Expr_isAppOfArity(v_a_3551_, v___x_3552_, v___x_3553_);
if (v___x_3554_ == 0)
{
lean_object* v___x_3555_; lean_object* v___x_3556_; 
lean_dec(v_a_3551_);
lean_dec(v_mvarId_3499_);
v___x_3555_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3556_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3555_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_);
return v___x_3556_;
}
else
{
lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; 
v___x_3557_ = l_Lean_Expr_appFn_x21(v_a_3551_);
v___x_3558_ = l_Lean_Expr_appArg_x21(v___x_3557_);
lean_dec_ref(v___x_3557_);
v___x_3559_ = l_Lean_Expr_appArg_x21(v_a_3551_);
lean_dec(v_a_3551_);
v___x_3560_ = ((lean_object*)(l_Lean_MVarId_subsingletonElim___lam__0___closed__1));
v___x_3561_ = lean_unsigned_to_nat(2u);
v___x_3562_ = lean_mk_empty_array_with_capacity(v___x_3561_);
v___x_3563_ = lean_array_push(v___x_3562_, v___x_3558_);
v___x_3564_ = lean_array_push(v___x_3563_, v___x_3559_);
v___x_3565_ = l_Lean_Meta_mkAppM(v___x_3560_, v___x_3564_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_);
if (lean_obj_tag(v___x_3565_) == 0)
{
lean_object* v_a_3566_; lean_object* v___x_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3575_; 
v_a_3566_ = lean_ctor_get(v___x_3565_, 0);
lean_inc(v_a_3566_);
lean_dec_ref(v___x_3565_);
v___x_3567_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_3499_, v_a_3566_, v___y_3502_);
v_isSharedCheck_3575_ = !lean_is_exclusive(v___x_3567_);
if (v_isSharedCheck_3575_ == 0)
{
lean_object* v_unused_3576_; 
v_unused_3576_ = lean_ctor_get(v___x_3567_, 0);
lean_dec(v_unused_3576_);
v___x_3569_ = v___x_3567_;
v_isShared_3570_ = v_isSharedCheck_3575_;
goto v_resetjp_3568_;
}
else
{
lean_dec(v___x_3567_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3575_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v___x_3571_; lean_object* v___x_3573_; 
v___x_3571_ = lean_box(v___x_3554_);
if (v_isShared_3570_ == 0)
{
lean_ctor_set(v___x_3569_, 0, v___x_3571_);
v___x_3573_ = v___x_3569_;
goto v_reusejp_3572_;
}
else
{
lean_object* v_reuseFailAlloc_3574_; 
v_reuseFailAlloc_3574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3574_, 0, v___x_3571_);
v___x_3573_ = v_reuseFailAlloc_3574_;
goto v_reusejp_3572_;
}
v_reusejp_3572_:
{
return v___x_3573_;
}
}
}
else
{
lean_object* v_a_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3584_; 
lean_dec(v_mvarId_3499_);
v_a_3577_ = lean_ctor_get(v___x_3565_, 0);
v_isSharedCheck_3584_ = !lean_is_exclusive(v___x_3565_);
if (v_isSharedCheck_3584_ == 0)
{
v___x_3579_ = v___x_3565_;
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
else
{
lean_inc(v_a_3577_);
lean_dec(v___x_3565_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
lean_object* v___x_3582_; 
if (v_isShared_3580_ == 0)
{
v___x_3582_ = v___x_3579_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v_a_3577_);
v___x_3582_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
return v___x_3582_;
}
}
}
}
}
else
{
lean_object* v_a_3585_; lean_object* v___x_3587_; uint8_t v_isShared_3588_; uint8_t v_isSharedCheck_3592_; 
lean_dec(v_mvarId_3499_);
v_a_3585_ = lean_ctor_get(v___x_3550_, 0);
v_isSharedCheck_3592_ = !lean_is_exclusive(v___x_3550_);
if (v_isSharedCheck_3592_ == 0)
{
v___x_3587_ = v___x_3550_;
v_isShared_3588_ = v_isSharedCheck_3592_;
goto v_resetjp_3586_;
}
else
{
lean_inc(v_a_3585_);
lean_dec(v___x_3550_);
v___x_3587_ = lean_box(0);
v_isShared_3588_ = v_isSharedCheck_3592_;
goto v_resetjp_3586_;
}
v_resetjp_3586_:
{
lean_object* v___x_3590_; 
if (v_isShared_3588_ == 0)
{
v___x_3590_ = v___x_3587_;
goto v_reusejp_3589_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v_a_3585_);
v___x_3590_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3589_;
}
v_reusejp_3589_:
{
return v___x_3590_;
}
}
}
}
}
}
else
{
lean_object* v_a_3595_; lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3602_; 
lean_dec(v_mvarId_3499_);
v_a_3595_ = lean_ctor_get(v___x_3506_, 0);
v_isSharedCheck_3602_ = !lean_is_exclusive(v___x_3506_);
if (v_isSharedCheck_3602_ == 0)
{
v___x_3597_ = v___x_3506_;
v_isShared_3598_ = v_isSharedCheck_3602_;
goto v_resetjp_3596_;
}
else
{
lean_inc(v_a_3595_);
lean_dec(v___x_3506_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_3602_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
lean_object* v___x_3600_; 
if (v_isShared_3598_ == 0)
{
v___x_3600_ = v___x_3597_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v_a_3595_);
v___x_3600_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
return v___x_3600_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim___lam__0___boxed(lean_object* v_mvarId_3603_, lean_object* v___x_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_){
_start:
{
lean_object* v_res_3610_; 
v_res_3610_ = l_Lean_MVarId_subsingletonElim___lam__0(v_mvarId_3603_, v___x_3604_, v___y_3605_, v___y_3606_, v___y_3607_, v___y_3608_);
lean_dec(v___y_3608_);
lean_dec_ref(v___y_3607_);
lean_dec(v___y_3606_);
lean_dec_ref(v___y_3605_);
return v_res_3610_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim(lean_object* v_mvarId_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_, lean_object* v_a_3617_, lean_object* v_a_3618_){
_start:
{
lean_object* v___x_3620_; lean_object* v___f_3621_; lean_object* v___f_3622_; lean_object* v___x_3623_; 
v___x_3620_ = ((lean_object*)(l_Lean_MVarId_subsingletonElim___closed__1));
lean_inc(v_mvarId_3614_);
v___f_3621_ = lean_alloc_closure((void*)(l_Lean_MVarId_subsingletonElim___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3621_, 0, v_mvarId_3614_);
lean_closure_set(v___f_3621_, 1, v___x_3620_);
v___f_3622_ = lean_alloc_closure((void*)(l_Lean_MVarId_proofIrrelHeq___lam__1___boxed), 6, 1);
lean_closure_set(v___f_3622_, 0, v___f_3621_);
v___x_3623_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_3614_, v___f_3622_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_);
return v___x_3623_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim___boxed(lean_object* v_mvarId_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_, lean_object* v_a_3627_, lean_object* v_a_3628_, lean_object* v_a_3629_){
_start:
{
lean_object* v_res_3630_; 
v_res_3630_ = l_Lean_MVarId_subsingletonElim(v_mvarId_3624_, v_a_3625_, v_a_3626_, v_a_3627_, v_a_3628_);
lean_dec(v_a_3628_);
lean_dec_ref(v_a_3627_);
lean_dec(v_a_3626_);
lean_dec_ref(v_a_3625_);
return v_res_3630_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_PrettyPrinter(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Apply(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
