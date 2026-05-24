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
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_synthAppInstances(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_synthAppInstances___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Meta_synthAppInstances_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Meta_synthAppInstances_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_148_ = 3ULL;
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
lean_dec_ref_known(v___x_156_, 7);
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
lean_ctor_set(v___x_232_, 0, v___y_236_);
v___x_239_ = v___x_232_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v___y_236_);
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
lean_ctor_set(v___x_247_, 1, v___y_235_);
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
lean_dec_ref_known(v___x_254_, 1);
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
v___y_235_ = v_a_255_;
v___y_236_ = v___x_260_;
v___y_237_ = v___x_261_;
goto v___jp_234_;
}
else
{
lean_object* v_val_262_; 
v_val_262_ = lean_ctor_get(v_term_x3f_217_, 0);
lean_inc(v_val_262_);
lean_dec_ref_known(v_term_x3f_217_, 1);
v___y_235_ = v_a_255_;
v___y_236_ = v___x_260_;
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
lean_dec_ref_known(v___x_517_, 1);
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
lean_dec_ref_known(v___x_517_, 1);
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
lean_dec_ref_known(v___y_455_, 1);
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
lean_dec_ref_known(v_fst_459_, 1);
lean_inc(v_a_432_);
v___x_470_ = l_Lean_Meta_isExprDefEq(v_a_432_, v_val_469_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
if (lean_obj_tag(v___x_470_) == 0)
{
lean_object* v_a_471_; uint8_t v___x_472_; 
v_a_471_ = lean_ctor_get(v___x_470_, 0);
lean_inc(v_a_471_);
lean_dec_ref_known(v___x_470_, 1);
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
lean_dec_ref_known(v___x_474_, 1);
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
lean_dec_ref_known(v___y_455_, 1);
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
lean_dec_ref_known(v_fst_580_, 1);
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
lean_dec_ref_known(v_fst_580_, 1);
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
lean_dec_ref_known(v_fst_580_, 1);
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
size_t v_x_3030__boxed_661_; uint8_t v_res_662_; lean_object* v_r_663_; 
v_x_3030__boxed_661_ = lean_unbox_usize(v_x_659_);
lean_dec(v_x_659_);
v_res_662_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(v_x_658_, v_x_3030__boxed_661_, v_x_660_);
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
lean_dec_ref_known(v___x_731_, 1);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg(lean_object* v_tacticName_769_, lean_object* v_mvarId_770_, uint8_t v_allowSynthFailures_771_, lean_object* v_a_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; uint8_t v___x_780_; 
v___x_778_ = lean_array_get_size(v_a_772_);
v___x_779_ = lean_unsigned_to_nat(0u);
v___x_780_ = lean_nat_dec_eq(v___x_778_, v___x_779_);
if (v___x_780_ == 0)
{
lean_object* v___x_781_; 
lean_inc(v_mvarId_770_);
lean_inc(v_tacticName_769_);
v___x_781_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step(v_tacticName_769_, v_mvarId_770_, v_allowSynthFailures_771_, v_a_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
lean_dec_ref(v_a_772_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_object* v_a_782_; 
v_a_782_ = lean_ctor_get(v___x_781_, 0);
lean_inc(v_a_782_);
lean_dec_ref_known(v___x_781_, 1);
v_a_772_ = v_a_782_;
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
lean_ctor_set(v___x_784_, 0, v_a_772_);
return v___x_784_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg___boxed(lean_object* v_tacticName_785_, lean_object* v_mvarId_786_, lean_object* v_allowSynthFailures_787_, lean_object* v_a_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
uint8_t v_allowSynthFailures_boxed_794_; lean_object* v_res_795_; 
v_allowSynthFailures_boxed_794_ = lean_unbox(v_allowSynthFailures_787_);
v_res_795_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg(v_tacticName_785_, v_mvarId_786_, v_allowSynthFailures_boxed_794_, v_a_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
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
lean_dec_ref_known(v___x_814_, 1);
v_fst_816_ = lean_ctor_get(v_a_815_, 0);
lean_inc(v_fst_816_);
lean_dec(v_a_815_);
v___x_817_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg(v_tacticName_796_, v_mvarId_797_, v_allowSynthFailures_801_, v_fst_816_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Meta_synthAppInstances_spec__2(lean_object* v_tacticName_871_, lean_object* v_mvarId_872_, uint8_t v_allowSynthFailures_873_, lean_object* v_inst_874_, lean_object* v_a_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg(v_tacticName_871_, v_mvarId_872_, v_allowSynthFailures_873_, v_a_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Meta_synthAppInstances_spec__2___boxed(lean_object* v_tacticName_882_, lean_object* v_mvarId_883_, lean_object* v_allowSynthFailures_884_, lean_object* v_inst_885_, lean_object* v_a_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
uint8_t v_allowSynthFailures_boxed_892_; lean_object* v_res_893_; 
v_allowSynthFailures_boxed_892_ = lean_unbox(v_allowSynthFailures_884_);
v_res_893_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_synthAppInstances_spec__2(v_tacticName_882_, v_mvarId_883_, v_allowSynthFailures_boxed_892_, v_inst_885_, v_a_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
return v_res_893_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0(lean_object* v_00_u03b2_894_, lean_object* v_x_895_, lean_object* v_x_896_){
_start:
{
uint8_t v___x_897_; 
v___x_897_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(v_x_895_, v_x_896_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___boxed(lean_object* v_00_u03b2_898_, lean_object* v_x_899_, lean_object* v_x_900_){
_start:
{
uint8_t v_res_901_; lean_object* v_r_902_; 
v_res_901_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0(v_00_u03b2_898_, v_x_899_, v_x_900_);
lean_dec(v_x_900_);
lean_dec_ref(v_x_899_);
v_r_902_ = lean_box(v_res_901_);
return v_r_902_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_903_, lean_object* v_x_904_, size_t v_x_905_, lean_object* v_x_906_){
_start:
{
uint8_t v___x_907_; 
v___x_907_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(v_x_904_, v_x_905_, v_x_906_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_908_, lean_object* v_x_909_, lean_object* v_x_910_, lean_object* v_x_911_){
_start:
{
size_t v_x_3370__boxed_912_; uint8_t v_res_913_; lean_object* v_r_914_; 
v_x_3370__boxed_912_ = lean_unbox_usize(v_x_910_);
lean_dec(v_x_910_);
v_res_913_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1(v_00_u03b2_908_, v_x_909_, v_x_3370__boxed_912_, v_x_911_);
lean_dec(v_x_911_);
lean_dec_ref(v_x_909_);
v_r_914_ = lean_box(v_res_913_);
return v_r_914_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_915_, lean_object* v_keys_916_, lean_object* v_vals_917_, lean_object* v_heq_918_, lean_object* v_i_919_, lean_object* v_k_920_){
_start:
{
uint8_t v___x_921_; 
v___x_921_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_916_, v_i_919_, v_k_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_922_, lean_object* v_keys_923_, lean_object* v_vals_924_, lean_object* v_heq_925_, lean_object* v_i_926_, lean_object* v_k_927_){
_start:
{
uint8_t v_res_928_; lean_object* v_r_929_; 
v_res_928_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_922_, v_keys_923_, v_vals_924_, v_heq_925_, v_i_926_, v_k_927_);
lean_dec(v_k_927_);
lean_dec_ref(v_vals_924_);
lean_dec_ref(v_keys_923_);
v_r_929_ = lean_box(v_res_928_);
return v_r_929_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(lean_object* v_newMVars_930_, lean_object* v_binderInfos_931_, lean_object* v_a_932_, lean_object* v_n_933_, lean_object* v_i_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v_zero_940_; uint8_t v_isZero_941_; 
v_zero_940_ = lean_unsigned_to_nat(0u);
v_isZero_941_ = lean_nat_dec_eq(v_i_934_, v_zero_940_);
if (v_isZero_941_ == 1)
{
lean_object* v___x_942_; lean_object* v___x_943_; 
lean_dec(v_i_934_);
lean_dec(v_a_932_);
v___x_942_ = lean_box(0);
v___x_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_943_, 0, v___x_942_);
return v___x_943_;
}
else
{
lean_object* v_one_944_; lean_object* v_n_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v_a_951_; uint8_t v___x_952_; 
v_one_944_ = lean_unsigned_to_nat(1u);
v_n_945_ = lean_nat_sub(v_i_934_, v_one_944_);
lean_dec(v_i_934_);
v___x_946_ = lean_nat_sub(v_n_933_, v_n_945_);
v___x_947_ = lean_nat_sub(v___x_946_, v_one_944_);
lean_dec(v___x_946_);
v___x_948_ = lean_array_fget_borrowed(v_newMVars_930_, v___x_947_);
v___x_949_ = l_Lean_Expr_mvarId_x21(v___x_948_);
v___x_950_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v___x_949_, v___y_936_);
v_a_951_ = lean_ctor_get(v___x_950_, 0);
lean_inc(v_a_951_);
lean_dec_ref(v___x_950_);
v___x_952_ = lean_unbox(v_a_951_);
lean_dec(v_a_951_);
if (v___x_952_ == 0)
{
uint8_t v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; uint8_t v___x_956_; uint8_t v___x_957_; 
v___x_953_ = 0;
v___x_954_ = lean_box(v___x_953_);
v___x_955_ = lean_array_get(v___x_954_, v_binderInfos_931_, v___x_947_);
lean_dec(v___x_947_);
lean_dec(v___x_954_);
v___x_956_ = lean_unbox(v___x_955_);
lean_dec(v___x_955_);
v___x_957_ = l_Lean_BinderInfo_isInstImplicit(v___x_956_);
if (v___x_957_ == 0)
{
lean_object* v___x_958_; 
lean_inc(v___x_949_);
v___x_958_ = l_Lean_MVarId_getTag(v___x_949_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v_a_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v_a_959_ = lean_ctor_get(v___x_958_, 0);
lean_inc(v_a_959_);
lean_dec_ref_known(v___x_958_, 1);
lean_inc(v_a_932_);
v___x_960_ = l_Lean_Meta_appendTag(v_a_932_, v_a_959_);
v___x_961_ = l_Lean_MVarId_setTag___redArg(v___x_949_, v___x_960_, v___y_936_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_dec_ref_known(v___x_961_, 1);
v_i_934_ = v_n_945_;
goto _start;
}
else
{
lean_dec(v_n_945_);
lean_dec(v_a_932_);
return v___x_961_;
}
}
else
{
lean_object* v_a_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_970_; 
lean_dec(v___x_949_);
lean_dec(v_n_945_);
lean_dec(v_a_932_);
v_a_963_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_970_ == 0)
{
v___x_965_ = v___x_958_;
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_a_963_);
lean_dec(v___x_958_);
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
else
{
lean_dec(v___x_949_);
v_i_934_ = v_n_945_;
goto _start;
}
}
else
{
lean_dec(v___x_949_);
lean_dec(v___x_947_);
v_i_934_ = v_n_945_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg___boxed(lean_object* v_newMVars_973_, lean_object* v_binderInfos_974_, lean_object* v_a_975_, lean_object* v_n_976_, lean_object* v_i_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(v_newMVars_973_, v_binderInfos_974_, v_a_975_, v_n_976_, v_i_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v_n_976_);
lean_dec_ref(v_binderInfos_974_);
lean_dec_ref(v_newMVars_973_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendParentTag(lean_object* v_mvarId_984_, lean_object* v_newMVars_985_, lean_object* v_binderInfos_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_){
_start:
{
lean_object* v___x_992_; 
v___x_992_ = l_Lean_MVarId_getTag(v_mvarId_984_, v_a_987_, v_a_988_, v_a_989_, v_a_990_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1011_; 
v_a_993_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_995_ = v___x_992_;
v_isShared_996_ = v_isSharedCheck_1011_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_992_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1011_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_997_; lean_object* v___x_998_; uint8_t v___x_999_; 
v___x_997_ = lean_array_get_size(v_newMVars_985_);
v___x_998_ = lean_unsigned_to_nat(1u);
v___x_999_ = lean_nat_dec_eq(v___x_997_, v___x_998_);
if (v___x_999_ == 0)
{
uint8_t v___x_1000_; 
v___x_1000_ = l_Lean_Name_isAnonymous(v_a_993_);
if (v___x_1000_ == 0)
{
lean_object* v___x_1001_; 
lean_del_object(v___x_995_);
v___x_1001_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(v_newMVars_985_, v_binderInfos_986_, v_a_993_, v___x_997_, v___x_997_, v_a_987_, v_a_988_, v_a_989_, v_a_990_);
return v___x_1001_;
}
else
{
lean_object* v___x_1002_; lean_object* v___x_1004_; 
lean_dec(v_a_993_);
v___x_1002_ = lean_box(0);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 0, v___x_1002_);
v___x_1004_ = v___x_995_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v___x_1002_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
}
else
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
lean_del_object(v___x_995_);
v___x_1006_ = l_Lean_instInhabitedExpr;
v___x_1007_ = lean_unsigned_to_nat(0u);
v___x_1008_ = lean_array_get_borrowed(v___x_1006_, v_newMVars_985_, v___x_1007_);
v___x_1009_ = l_Lean_Expr_mvarId_x21(v___x_1008_);
v___x_1010_ = l_Lean_MVarId_setTag___redArg(v___x_1009_, v_a_993_, v_a_988_);
return v___x_1010_;
}
}
}
else
{
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1019_; 
v_a_1012_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1014_ = v___x_992_;
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_992_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1017_; 
if (v_isShared_1015_ == 0)
{
v___x_1017_ = v___x_1014_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_a_1012_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendParentTag___boxed(lean_object* v_mvarId_1020_, lean_object* v_newMVars_1021_, lean_object* v_binderInfos_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l_Lean_Meta_appendParentTag(v_mvarId_1020_, v_newMVars_1021_, v_binderInfos_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_);
lean_dec(v_a_1026_);
lean_dec_ref(v_a_1025_);
lean_dec(v_a_1024_);
lean_dec_ref(v_a_1023_);
lean_dec_ref(v_binderInfos_1022_);
lean_dec_ref(v_newMVars_1021_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0(lean_object* v_newMVars_1029_, lean_object* v_binderInfos_1030_, lean_object* v_a_1031_, lean_object* v_n_1032_, lean_object* v_i_1033_, lean_object* v_a_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(v_newMVars_1029_, v_binderInfos_1030_, v_a_1031_, v_n_1032_, v_i_1033_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___boxed(lean_object* v_newMVars_1041_, lean_object* v_binderInfos_1042_, lean_object* v_a_1043_, lean_object* v_n_1044_, lean_object* v_i_1045_, lean_object* v_a_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0(v_newMVars_1041_, v_binderInfos_1042_, v_a_1043_, v_n_1044_, v_i_1045_, v_a_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v_n_1044_);
lean_dec_ref(v_binderInfos_1042_);
lean_dec_ref(v_newMVars_1041_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_postprocessAppMVars(lean_object* v_tacticName_1053_, lean_object* v_mvarId_1054_, lean_object* v_newMVars_1055_, lean_object* v_binderInfos_1056_, uint8_t v_synthAssignedInstances_1057_, uint8_t v_allowSynthFailures_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = l_Lean_Meta_synthAppInstances(v_tacticName_1053_, v_mvarId_1054_, v_newMVars_1055_, v_binderInfos_1056_, v_synthAssignedInstances_1057_, v_allowSynthFailures_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_postprocessAppMVars___boxed(lean_object* v_tacticName_1065_, lean_object* v_mvarId_1066_, lean_object* v_newMVars_1067_, lean_object* v_binderInfos_1068_, lean_object* v_synthAssignedInstances_1069_, lean_object* v_allowSynthFailures_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_){
_start:
{
uint8_t v_synthAssignedInstances_boxed_1076_; uint8_t v_allowSynthFailures_boxed_1077_; lean_object* v_res_1078_; 
v_synthAssignedInstances_boxed_1076_ = lean_unbox(v_synthAssignedInstances_1069_);
v_allowSynthFailures_boxed_1077_ = lean_unbox(v_allowSynthFailures_1070_);
v_res_1078_ = l_Lean_Meta_postprocessAppMVars(v_tacticName_1065_, v_mvarId_1066_, v_newMVars_1067_, v_binderInfos_1068_, v_synthAssignedInstances_boxed_1076_, v_allowSynthFailures_boxed_1077_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_);
lean_dec(v_a_1074_);
lean_dec_ref(v_a_1073_);
lean_dec(v_a_1072_);
lean_dec_ref(v_a_1071_);
lean_dec_ref(v_newMVars_1067_);
return v_res_1078_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0(lean_object* v_mvar_1079_, lean_object* v_mvarId_1080_){
_start:
{
lean_object* v___x_1081_; uint8_t v___x_1082_; 
v___x_1081_ = l_Lean_Expr_mvarId_x21(v_mvar_1079_);
v___x_1082_ = l_Lean_instBEqMVarId_beq(v_mvarId_1080_, v___x_1081_);
lean_dec(v___x_1081_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0___boxed(lean_object* v_mvar_1083_, lean_object* v_mvarId_1084_){
_start:
{
uint8_t v_res_1085_; lean_object* v_r_1086_; 
v_res_1085_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0(v_mvar_1083_, v_mvarId_1084_);
lean_dec(v_mvarId_1084_);
lean_dec_ref(v_mvar_1083_);
v_r_1086_ = lean_box(v_res_1085_);
return v_r_1086_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0(lean_object* v_mvar_1087_, lean_object* v_as_1088_, size_t v_i_1089_, size_t v_stop_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
uint8_t v___x_1096_; 
v___x_1096_ = lean_usize_dec_eq(v_i_1089_, v_stop_1090_);
if (v___x_1096_ == 0)
{
uint8_t v___x_1097_; uint8_t v_a_1099_; lean_object* v___x_1105_; uint8_t v___x_1106_; 
v___x_1097_ = 1;
v___x_1105_ = lean_array_uget_borrowed(v_as_1088_, v_i_1089_);
v___x_1106_ = lean_expr_eqv(v_mvar_1087_, v___x_1105_);
if (v___x_1106_ == 0)
{
lean_object* v___x_1107_; 
lean_inc(v___y_1094_);
lean_inc_ref(v___y_1093_);
lean_inc(v___y_1092_);
lean_inc_ref(v___y_1091_);
lean_inc(v___x_1105_);
v___x_1107_ = lean_infer_type(v___x_1105_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_);
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1119_; 
v_a_1108_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1110_ = v___x_1107_;
v_isShared_1111_ = v_isSharedCheck_1119_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1107_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1119_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___f_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
lean_inc_ref(v_mvar_1087_);
v___f_1112_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1112_, 0, v_mvar_1087_);
v___x_1113_ = lean_box(0);
v___x_1114_ = l_Lean_FindMVar_main(v___f_1112_, v_a_1108_, v___x_1113_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_del_object(v___x_1110_);
v_a_1099_ = v___x_1106_;
goto v___jp_1098_;
}
else
{
lean_object* v___x_1115_; lean_object* v___x_1117_; 
lean_dec_ref_known(v___x_1114_, 1);
lean_dec_ref(v_mvar_1087_);
v___x_1115_ = lean_box(v___x_1097_);
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 0, v___x_1115_);
v___x_1117_ = v___x_1110_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v___x_1115_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
}
}
else
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
lean_dec_ref(v_mvar_1087_);
v_a_1120_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v___x_1107_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1107_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_a_1120_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
else
{
v_a_1099_ = v___x_1096_;
goto v___jp_1098_;
}
v___jp_1098_:
{
if (v_a_1099_ == 0)
{
size_t v___x_1100_; size_t v___x_1101_; 
v___x_1100_ = ((size_t)1ULL);
v___x_1101_ = lean_usize_add(v_i_1089_, v___x_1100_);
v_i_1089_ = v___x_1101_;
goto _start;
}
else
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
lean_dec_ref(v_mvar_1087_);
v___x_1103_ = lean_box(v___x_1097_);
v___x_1104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1103_);
return v___x_1104_;
}
}
}
else
{
uint8_t v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
lean_dec_ref(v_mvar_1087_);
v___x_1128_ = 0;
v___x_1129_ = lean_box(v___x_1128_);
v___x_1130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1129_);
return v___x_1130_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___boxed(lean_object* v_mvar_1131_, lean_object* v_as_1132_, lean_object* v_i_1133_, lean_object* v_stop_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
size_t v_i_boxed_1140_; size_t v_stop_boxed_1141_; lean_object* v_res_1142_; 
v_i_boxed_1140_ = lean_unbox_usize(v_i_1133_);
lean_dec(v_i_1133_);
v_stop_boxed_1141_ = lean_unbox_usize(v_stop_1134_);
lean_dec(v_stop_1134_);
v_res_1142_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0(v_mvar_1131_, v_as_1132_, v_i_boxed_1140_, v_stop_boxed_1141_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_);
lean_dec(v___y_1138_);
lean_dec_ref(v___y_1137_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
lean_dec_ref(v_as_1132_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(lean_object* v_mvar_1143_, lean_object* v_otherMVars_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_){
_start:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; uint8_t v___x_1152_; 
v___x_1150_ = lean_unsigned_to_nat(0u);
v___x_1151_ = lean_array_get_size(v_otherMVars_1144_);
v___x_1152_ = lean_nat_dec_lt(v___x_1150_, v___x_1151_);
if (v___x_1152_ == 0)
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
lean_dec_ref(v_mvar_1143_);
v___x_1153_ = lean_box(v___x_1152_);
v___x_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1153_);
return v___x_1154_;
}
else
{
if (v___x_1152_ == 0)
{
lean_object* v___x_1155_; lean_object* v___x_1156_; 
lean_dec_ref(v_mvar_1143_);
v___x_1155_ = lean_box(v___x_1152_);
v___x_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1155_);
return v___x_1156_;
}
else
{
size_t v___x_1157_; size_t v___x_1158_; lean_object* v___x_1159_; 
v___x_1157_ = ((size_t)0ULL);
v___x_1158_ = lean_usize_of_nat(v___x_1151_);
v___x_1159_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0(v_mvar_1143_, v_otherMVars_1144_, v___x_1157_, v___x_1158_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_);
return v___x_1159_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___boxed(lean_object* v_mvar_1160_, lean_object* v_otherMVars_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(v_mvar_1160_, v_otherMVars_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_);
lean_dec(v_a_1165_);
lean_dec_ref(v_a_1164_);
lean_dec(v_a_1163_);
lean_dec_ref(v_a_1162_);
lean_dec_ref(v_otherMVars_1161_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(lean_object* v_mvars_1168_, lean_object* v_as_1169_, size_t v_i_1170_, size_t v_stop_1171_, lean_object* v_b_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
uint8_t v___x_1178_; 
v___x_1178_ = lean_usize_dec_eq(v_i_1170_, v_stop_1171_);
if (v___x_1178_ == 0)
{
lean_object* v_fst_1179_; lean_object* v_snd_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1210_; 
v_fst_1179_ = lean_ctor_get(v_b_1172_, 0);
v_snd_1180_ = lean_ctor_get(v_b_1172_, 1);
v_isSharedCheck_1210_ = !lean_is_exclusive(v_b_1172_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1182_ = v_b_1172_;
v_isShared_1183_ = v_isSharedCheck_1210_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_snd_1180_);
lean_inc(v_fst_1179_);
lean_dec(v_b_1172_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1210_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1184_; lean_object* v_currMVarId_1185_; lean_object* v___x_1186_; 
v___x_1184_ = lean_array_uget_borrowed(v_as_1169_, v_i_1170_);
v_currMVarId_1185_ = l_Lean_Expr_mvarId_x21(v___x_1184_);
lean_inc(v___x_1184_);
v___x_1186_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(v___x_1184_, v_mvars_1168_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_);
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_object* v_a_1187_; lean_object* v_a_1189_; uint8_t v___x_1193_; 
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
lean_inc(v_a_1187_);
lean_dec_ref_known(v___x_1186_, 1);
v___x_1193_ = lean_unbox(v_a_1187_);
lean_dec(v_a_1187_);
if (v___x_1193_ == 0)
{
lean_object* v___x_1194_; lean_object* v___x_1196_; 
v___x_1194_ = lean_array_push(v_fst_1179_, v_currMVarId_1185_);
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 0, v___x_1194_);
v___x_1196_ = v___x_1182_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v___x_1194_);
lean_ctor_set(v_reuseFailAlloc_1197_, 1, v_snd_1180_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
v_a_1189_ = v___x_1196_;
goto v___jp_1188_;
}
}
else
{
lean_object* v___x_1198_; lean_object* v___x_1200_; 
v___x_1198_ = lean_array_push(v_snd_1180_, v_currMVarId_1185_);
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 1, v___x_1198_);
v___x_1200_ = v___x_1182_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_fst_1179_);
lean_ctor_set(v_reuseFailAlloc_1201_, 1, v___x_1198_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
v_a_1189_ = v___x_1200_;
goto v___jp_1188_;
}
}
v___jp_1188_:
{
size_t v___x_1190_; size_t v___x_1191_; 
v___x_1190_ = ((size_t)1ULL);
v___x_1191_ = lean_usize_add(v_i_1170_, v___x_1190_);
v_i_1170_ = v___x_1191_;
v_b_1172_ = v_a_1189_;
goto _start;
}
}
else
{
lean_object* v_a_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1209_; 
lean_dec(v_currMVarId_1185_);
lean_del_object(v___x_1182_);
lean_dec(v_snd_1180_);
lean_dec(v_fst_1179_);
v_a_1202_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1204_ = v___x_1186_;
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_a_1202_);
lean_dec(v___x_1186_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1207_; 
if (v_isShared_1205_ == 0)
{
v___x_1207_ = v___x_1204_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_a_1202_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
}
}
else
{
lean_object* v___x_1211_; 
v___x_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1211_, 0, v_b_1172_);
return v___x_1211_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0___boxed(lean_object* v_mvars_1212_, lean_object* v_as_1213_, lean_object* v_i_1214_, lean_object* v_stop_1215_, lean_object* v_b_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
size_t v_i_boxed_1222_; size_t v_stop_boxed_1223_; lean_object* v_res_1224_; 
v_i_boxed_1222_ = lean_unbox_usize(v_i_1214_);
lean_dec(v_i_1214_);
v_stop_boxed_1223_ = lean_unbox_usize(v_stop_1215_);
lean_dec(v_stop_1215_);
v_res_1224_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(v_mvars_1212_, v_as_1213_, v_i_boxed_1222_, v_stop_boxed_1223_, v_b_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1217_);
lean_dec_ref(v_as_1213_);
lean_dec_ref(v_mvars_1212_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(lean_object* v_mvars_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_){
_start:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; uint8_t v___x_1238_; 
v___x_1235_ = lean_unsigned_to_nat(0u);
v___x_1236_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1));
v___x_1237_ = lean_array_get_size(v_mvars_1229_);
v___x_1238_ = lean_nat_dec_lt(v___x_1235_, v___x_1237_);
if (v___x_1238_ == 0)
{
lean_object* v___x_1239_; 
v___x_1239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1236_);
return v___x_1239_;
}
else
{
uint8_t v___x_1240_; 
v___x_1240_ = lean_nat_dec_le(v___x_1237_, v___x_1237_);
if (v___x_1240_ == 0)
{
if (v___x_1238_ == 0)
{
lean_object* v___x_1241_; 
v___x_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1236_);
return v___x_1241_;
}
else
{
size_t v___x_1242_; size_t v___x_1243_; lean_object* v___x_1244_; 
v___x_1242_ = ((size_t)0ULL);
v___x_1243_ = lean_usize_of_nat(v___x_1237_);
v___x_1244_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(v_mvars_1229_, v_mvars_1229_, v___x_1242_, v___x_1243_, v___x_1236_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_);
return v___x_1244_;
}
}
else
{
size_t v___x_1245_; size_t v___x_1246_; lean_object* v___x_1247_; 
v___x_1245_ = ((size_t)0ULL);
v___x_1246_ = lean_usize_of_nat(v___x_1237_);
v___x_1247_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(v_mvars_1229_, v_mvars_1229_, v___x_1245_, v___x_1246_, v___x_1236_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_);
return v___x_1247_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___boxed(lean_object* v_mvars_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(v_mvars_1248_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_);
lean_dec(v_a_1252_);
lean_dec_ref(v_a_1251_);
lean_dec(v_a_1250_);
lean_dec_ref(v_a_1249_);
lean_dec_ref(v_mvars_1248_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals_spec__0(lean_object* v_a_1255_, lean_object* v_a_1256_){
_start:
{
if (lean_obj_tag(v_a_1255_) == 0)
{
lean_object* v___x_1257_; 
v___x_1257_ = l_List_reverse___redArg(v_a_1256_);
return v___x_1257_;
}
else
{
lean_object* v_head_1258_; lean_object* v_tail_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1268_; 
v_head_1258_ = lean_ctor_get(v_a_1255_, 0);
v_tail_1259_ = lean_ctor_get(v_a_1255_, 1);
v_isSharedCheck_1268_ = !lean_is_exclusive(v_a_1255_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1261_ = v_a_1255_;
v_isShared_1262_ = v_isSharedCheck_1268_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_tail_1259_);
lean_inc(v_head_1258_);
lean_dec(v_a_1255_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1268_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1263_; lean_object* v___x_1265_; 
v___x_1263_ = l_Lean_Expr_mvarId_x21(v_head_1258_);
lean_dec(v_head_1258_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 1, v_a_1256_);
lean_ctor_set(v___x_1261_, 0, v___x_1263_);
v___x_1265_ = v___x_1261_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v___x_1263_);
lean_ctor_set(v_reuseFailAlloc_1267_, 1, v_a_1256_);
v___x_1265_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
v_a_1255_ = v_tail_1259_;
v_a_1256_ = v___x_1265_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(lean_object* v_mvars_1269_, uint8_t v_x_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_){
_start:
{
switch(v_x_1270_)
{
case 0:
{
lean_object* v___x_1276_; 
v___x_1276_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(v_mvars_1269_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_);
lean_dec_ref(v_mvars_1269_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1289_; 
v_a_1277_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1279_ = v___x_1276_;
v_isShared_1280_ = v_isSharedCheck_1289_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_dec(v___x_1276_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1289_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v_fst_1281_; lean_object* v_snd_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1287_; 
v_fst_1281_ = lean_ctor_get(v_a_1277_, 0);
lean_inc(v_fst_1281_);
v_snd_1282_ = lean_ctor_get(v_a_1277_, 1);
lean_inc(v_snd_1282_);
lean_dec(v_a_1277_);
v___x_1283_ = lean_array_to_list(v_fst_1281_);
v___x_1284_ = lean_array_to_list(v_snd_1282_);
v___x_1285_ = l_List_appendTR___redArg(v___x_1283_, v___x_1284_);
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 0, v___x_1285_);
v___x_1287_ = v___x_1279_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v___x_1285_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
else
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
v_a_1290_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1292_ = v___x_1276_;
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1276_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1295_; 
if (v_isShared_1293_ == 0)
{
v___x_1295_ = v___x_1292_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_a_1290_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
case 1:
{
lean_object* v___x_1298_; 
v___x_1298_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(v_mvars_1269_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_);
lean_dec_ref(v_mvars_1269_);
if (lean_obj_tag(v___x_1298_) == 0)
{
lean_object* v_a_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1308_; 
v_a_1299_ = lean_ctor_get(v___x_1298_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1301_ = v___x_1298_;
v_isShared_1302_ = v_isSharedCheck_1308_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_a_1299_);
lean_dec(v___x_1298_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1308_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v_fst_1303_; lean_object* v___x_1304_; lean_object* v___x_1306_; 
v_fst_1303_ = lean_ctor_get(v_a_1299_, 0);
lean_inc(v_fst_1303_);
lean_dec(v_a_1299_);
v___x_1304_ = lean_array_to_list(v_fst_1303_);
if (v_isShared_1302_ == 0)
{
lean_ctor_set(v___x_1301_, 0, v___x_1304_);
v___x_1306_ = v___x_1301_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v___x_1304_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
}
else
{
lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1316_; 
v_a_1309_ = lean_ctor_get(v___x_1298_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1311_ = v___x_1298_;
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v___x_1298_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1314_; 
if (v_isShared_1312_ == 0)
{
v___x_1314_ = v___x_1311_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_a_1309_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
}
default: 
{
lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1317_ = lean_array_to_list(v_mvars_1269_);
v___x_1318_ = lean_box(0);
v___x_1319_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals_spec__0(v___x_1317_, v___x_1318_);
v___x_1320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
return v___x_1320_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals___boxed(lean_object* v_mvars_1321_, lean_object* v_x_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_){
_start:
{
uint8_t v_x_820__boxed_1328_; lean_object* v_res_1329_; 
v_x_820__boxed_1328_ = lean_unbox(v_x_1322_);
v_res_1329_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(v_mvars_1321_, v_x_820__boxed_1328_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
lean_dec(v_a_1326_);
lean_dec_ref(v_a_1325_);
lean_dec(v_a_1324_);
lean_dec_ref(v_a_1323_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(uint8_t v_approx_1330_, lean_object* v_a_1331_, lean_object* v_b_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_){
_start:
{
if (v_approx_1330_ == 0)
{
lean_object* v___x_1338_; 
v___x_1338_ = l_Lean_Meta_isExprDefEqGuarded(v_a_1331_, v_b_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_);
return v___x_1338_;
}
else
{
lean_object* v___x_1339_; uint8_t v_constApprox_1340_; uint8_t v_isDefEqStuckEx_1341_; uint8_t v_unificationHints_1342_; uint8_t v_proofIrrelevance_1343_; uint8_t v_assignSyntheticOpaque_1344_; uint8_t v_offsetCnstrs_1345_; uint8_t v_transparency_1346_; uint8_t v_etaStruct_1347_; uint8_t v_univApprox_1348_; uint8_t v_iota_1349_; uint8_t v_beta_1350_; uint8_t v_proj_1351_; uint8_t v_zeta_1352_; uint8_t v_zetaDelta_1353_; uint8_t v_zetaUnused_1354_; uint8_t v_zetaHave_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1376_; 
v___x_1339_ = l_Lean_Meta_Context_config(v_a_1333_);
v_constApprox_1340_ = lean_ctor_get_uint8(v___x_1339_, 3);
v_isDefEqStuckEx_1341_ = lean_ctor_get_uint8(v___x_1339_, 4);
v_unificationHints_1342_ = lean_ctor_get_uint8(v___x_1339_, 5);
v_proofIrrelevance_1343_ = lean_ctor_get_uint8(v___x_1339_, 6);
v_assignSyntheticOpaque_1344_ = lean_ctor_get_uint8(v___x_1339_, 7);
v_offsetCnstrs_1345_ = lean_ctor_get_uint8(v___x_1339_, 8);
v_transparency_1346_ = lean_ctor_get_uint8(v___x_1339_, 9);
v_etaStruct_1347_ = lean_ctor_get_uint8(v___x_1339_, 10);
v_univApprox_1348_ = lean_ctor_get_uint8(v___x_1339_, 11);
v_iota_1349_ = lean_ctor_get_uint8(v___x_1339_, 12);
v_beta_1350_ = lean_ctor_get_uint8(v___x_1339_, 13);
v_proj_1351_ = lean_ctor_get_uint8(v___x_1339_, 14);
v_zeta_1352_ = lean_ctor_get_uint8(v___x_1339_, 15);
v_zetaDelta_1353_ = lean_ctor_get_uint8(v___x_1339_, 16);
v_zetaUnused_1354_ = lean_ctor_get_uint8(v___x_1339_, 17);
v_zetaHave_1355_ = lean_ctor_get_uint8(v___x_1339_, 18);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1357_ = v___x_1339_;
v_isShared_1358_ = v_isSharedCheck_1376_;
goto v_resetjp_1356_;
}
else
{
lean_dec(v___x_1339_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1376_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1360_; 
if (v_isShared_1358_ == 0)
{
v___x_1360_ = v___x_1357_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1375_, 3, v_constApprox_1340_);
lean_ctor_set_uint8(v_reuseFailAlloc_1375_, 4, v_isDefEqStuckEx_1341_);
lean_ctor_set_uint8(v_reuseFailAlloc_1375_, 5, v_unificationHints_1342_);
lean_ctor_set_uint8(v_reuseFailAlloc_1375_, 6, v_proofIrrelevance_1343_);
lean_ctor_set_uint8(v_reuseFailAlloc_1375_, 7, v_assignSyntheticOpaque_1344_);
lean_ctor_set_uint8(v_reuseFailAlloc_1375_, 8, v_offsetCnstrs_1345_);
lean_ctor_set_uint8(v_reuseFailAlloc_1375_, 9, v_transparency_1346_);
lean_ctor_set_uint8(v_reuseFailAlloc_1375_, 10, v_etaStruct_1347_);
lean_ctor_set_uint8(v_reuseFailAlloc_1375_, 11, v_univApprox_1348_);
lean_ctor_set_uint8(v_reuseFailAlloc_1375_, 12, v_iota_1349_);
lean_ctor_set_uint8(v_reuseFailAlloc_1375_, 13, v_beta_1350_);
lean_ctor_set_uint8(v_reuseFailAlloc_1375_, 14, v_proj_1351_);
lean_ctor_set_uint8(v_reuseFailAlloc_1375_, 15, v_zeta_1352_);
lean_ctor_set_uint8(v_reuseFailAlloc_1375_, 16, v_zetaDelta_1353_);
lean_ctor_set_uint8(v_reuseFailAlloc_1375_, 17, v_zetaUnused_1354_);
lean_ctor_set_uint8(v_reuseFailAlloc_1375_, 18, v_zetaHave_1355_);
v___x_1360_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
uint8_t v_trackZetaDelta_1361_; lean_object* v_zetaDeltaSet_1362_; lean_object* v_lctx_1363_; lean_object* v_localInstances_1364_; lean_object* v_defEqCtx_x3f_1365_; lean_object* v_synthPendingDepth_1366_; lean_object* v_canUnfold_x3f_1367_; uint8_t v_univApprox_1368_; uint8_t v_inTypeClassResolution_1369_; uint8_t v_cacheInferType_1370_; uint64_t v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; 
lean_ctor_set_uint8(v___x_1360_, 0, v_approx_1330_);
lean_ctor_set_uint8(v___x_1360_, 1, v_approx_1330_);
lean_ctor_set_uint8(v___x_1360_, 2, v_approx_1330_);
v_trackZetaDelta_1361_ = lean_ctor_get_uint8(v_a_1333_, sizeof(void*)*7);
v_zetaDeltaSet_1362_ = lean_ctor_get(v_a_1333_, 1);
v_lctx_1363_ = lean_ctor_get(v_a_1333_, 2);
v_localInstances_1364_ = lean_ctor_get(v_a_1333_, 3);
v_defEqCtx_x3f_1365_ = lean_ctor_get(v_a_1333_, 4);
v_synthPendingDepth_1366_ = lean_ctor_get(v_a_1333_, 5);
v_canUnfold_x3f_1367_ = lean_ctor_get(v_a_1333_, 6);
v_univApprox_1368_ = lean_ctor_get_uint8(v_a_1333_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1369_ = lean_ctor_get_uint8(v_a_1333_, sizeof(void*)*7 + 2);
v_cacheInferType_1370_ = lean_ctor_get_uint8(v_a_1333_, sizeof(void*)*7 + 3);
v___x_1371_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1360_);
v___x_1372_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1372_, 0, v___x_1360_);
lean_ctor_set_uint64(v___x_1372_, sizeof(void*)*1, v___x_1371_);
lean_inc(v_canUnfold_x3f_1367_);
lean_inc(v_synthPendingDepth_1366_);
lean_inc(v_defEqCtx_x3f_1365_);
lean_inc_ref(v_localInstances_1364_);
lean_inc_ref(v_lctx_1363_);
lean_inc(v_zetaDeltaSet_1362_);
v___x_1373_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1373_, 0, v___x_1372_);
lean_ctor_set(v___x_1373_, 1, v_zetaDeltaSet_1362_);
lean_ctor_set(v___x_1373_, 2, v_lctx_1363_);
lean_ctor_set(v___x_1373_, 3, v_localInstances_1364_);
lean_ctor_set(v___x_1373_, 4, v_defEqCtx_x3f_1365_);
lean_ctor_set(v___x_1373_, 5, v_synthPendingDepth_1366_);
lean_ctor_set(v___x_1373_, 6, v_canUnfold_x3f_1367_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*7, v_trackZetaDelta_1361_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*7 + 1, v_univApprox_1368_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1369_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*7 + 3, v_cacheInferType_1370_);
v___x_1374_ = l_Lean_Meta_isExprDefEqGuarded(v_a_1331_, v_b_1332_, v___x_1373_, v_a_1334_, v_a_1335_, v_a_1336_);
lean_dec_ref_known(v___x_1373_, 7);
return v___x_1374_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply___boxed(lean_object* v_approx_1377_, lean_object* v_a_1378_, lean_object* v_b_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_){
_start:
{
uint8_t v_approx_boxed_1385_; lean_object* v_res_1386_; 
v_approx_boxed_1385_ = lean_unbox(v_approx_1377_);
v_res_1386_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(v_approx_boxed_1385_, v_a_1378_, v_b_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_);
lean_dec(v_a_1383_);
lean_dec_ref(v_a_1382_);
lean_dec(v_a_1381_);
lean_dec_ref(v_a_1380_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go(lean_object* v_mvarId_1387_, lean_object* v_cfg_1388_, lean_object* v_term_x3f_1389_, lean_object* v_targetType_1390_, lean_object* v_eType_1391_, lean_object* v_rangeNumArgs_1392_, lean_object* v_i_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_){
_start:
{
lean_object* v_lower_1399_; lean_object* v_upper_1400_; uint8_t v___x_1401_; 
v_lower_1399_ = lean_ctor_get(v_rangeNumArgs_1392_, 0);
v_upper_1400_ = lean_ctor_get(v_rangeNumArgs_1392_, 1);
v___x_1401_ = lean_nat_dec_lt(v_i_1393_, v_upper_1400_);
if (v___x_1401_ == 0)
{
lean_object* v___x_1402_; uint8_t v___x_1403_; 
lean_dec(v_i_1393_);
v___x_1402_ = lean_unsigned_to_nat(0u);
v___x_1403_ = lean_nat_dec_eq(v_lower_1399_, v___x_1402_);
if (v___x_1403_ == 0)
{
lean_object* v___x_1404_; uint8_t v___x_1405_; lean_object* v___x_1406_; 
lean_inc(v_lower_1399_);
v___x_1404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1404_, 0, v_lower_1399_);
v___x_1405_ = 0;
lean_inc_ref(v_eType_1391_);
v___x_1406_ = l_Lean_Meta_forallMetaTelescopeReducing(v_eType_1391_, v___x_1404_, v___x_1405_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_);
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_object* v_a_1407_; lean_object* v_snd_1408_; lean_object* v_snd_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
v_a_1407_ = lean_ctor_get(v___x_1406_, 0);
lean_inc(v_a_1407_);
lean_dec_ref_known(v___x_1406_, 1);
v_snd_1408_ = lean_ctor_get(v_a_1407_, 1);
lean_inc(v_snd_1408_);
lean_dec(v_a_1407_);
v_snd_1409_ = lean_ctor_get(v_snd_1408_, 1);
lean_inc(v_snd_1409_);
lean_dec(v_snd_1408_);
v___x_1410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1410_, 0, v_snd_1409_);
v___x_1411_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(v_mvarId_1387_, v_eType_1391_, v___x_1410_, v_targetType_1390_, v_term_x3f_1389_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_);
return v___x_1411_;
}
else
{
lean_object* v_a_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1419_; 
lean_dec_ref(v_eType_1391_);
lean_dec_ref(v_targetType_1390_);
lean_dec(v_term_x3f_1389_);
lean_dec(v_mvarId_1387_);
v_a_1412_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1414_ = v___x_1406_;
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_a_1412_);
lean_dec(v___x_1406_);
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
else
{
lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1420_ = lean_box(0);
v___x_1421_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(v_mvarId_1387_, v_eType_1391_, v___x_1420_, v_targetType_1390_, v_term_x3f_1389_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_);
return v___x_1421_;
}
}
else
{
lean_object* v___x_1422_; 
v___x_1422_ = l_Lean_Meta_saveState___redArg(v_a_1395_, v_a_1397_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v_a_1423_; lean_object* v___x_1424_; uint8_t v___x_1425_; lean_object* v___x_1426_; 
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_a_1423_);
lean_dec_ref_known(v___x_1422_, 1);
lean_inc(v_i_1393_);
v___x_1424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1424_, 0, v_i_1393_);
v___x_1425_ = 0;
lean_inc_ref(v_eType_1391_);
v___x_1426_ = l_Lean_Meta_forallMetaTelescopeReducing(v_eType_1391_, v___x_1424_, v___x_1425_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v_a_1427_; lean_object* v_snd_1428_; lean_object* v_fst_1429_; lean_object* v_fst_1430_; lean_object* v_snd_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1469_; 
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
lean_inc(v_a_1427_);
lean_dec_ref_known(v___x_1426_, 1);
v_snd_1428_ = lean_ctor_get(v_a_1427_, 1);
lean_inc(v_snd_1428_);
v_fst_1429_ = lean_ctor_get(v_a_1427_, 0);
lean_inc(v_fst_1429_);
lean_dec(v_a_1427_);
v_fst_1430_ = lean_ctor_get(v_snd_1428_, 0);
v_snd_1431_ = lean_ctor_get(v_snd_1428_, 1);
v_isSharedCheck_1469_ = !lean_is_exclusive(v_snd_1428_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1433_ = v_snd_1428_;
v_isShared_1434_ = v_isSharedCheck_1469_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_snd_1431_);
lean_inc(v_fst_1430_);
lean_dec(v_snd_1428_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1469_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
uint8_t v_approx_1435_; lean_object* v___x_1436_; 
v_approx_1435_ = lean_ctor_get_uint8(v_cfg_1388_, 3);
lean_inc_ref(v_targetType_1390_);
v___x_1436_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(v_approx_1435_, v_snd_1431_, v_targetType_1390_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_);
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1460_; 
v_a_1437_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1439_ = v___x_1436_;
v_isShared_1440_ = v_isSharedCheck_1460_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___x_1436_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1460_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
uint8_t v___x_1441_; 
v___x_1441_ = lean_unbox(v_a_1437_);
lean_dec(v_a_1437_);
if (v___x_1441_ == 0)
{
lean_object* v___x_1442_; 
lean_del_object(v___x_1439_);
lean_del_object(v___x_1433_);
lean_dec(v_fst_1430_);
lean_dec(v_fst_1429_);
v___x_1442_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1423_, v_a_1395_, v_a_1397_);
lean_dec(v_a_1423_);
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_object* v___x_1443_; lean_object* v___x_1444_; 
lean_dec_ref_known(v___x_1442_, 1);
v___x_1443_ = lean_unsigned_to_nat(1u);
v___x_1444_ = lean_nat_add(v_i_1393_, v___x_1443_);
lean_dec(v_i_1393_);
v_i_1393_ = v___x_1444_;
goto _start;
}
else
{
lean_object* v_a_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1453_; 
lean_dec(v_i_1393_);
lean_dec_ref(v_eType_1391_);
lean_dec_ref(v_targetType_1390_);
lean_dec(v_term_x3f_1389_);
lean_dec(v_mvarId_1387_);
v_a_1446_ = lean_ctor_get(v___x_1442_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1448_ = v___x_1442_;
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_a_1446_);
lean_dec(v___x_1442_);
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
else
{
lean_object* v___x_1455_; 
lean_dec(v_a_1423_);
lean_dec(v_i_1393_);
lean_dec_ref(v_eType_1391_);
lean_dec_ref(v_targetType_1390_);
lean_dec(v_term_x3f_1389_);
lean_dec(v_mvarId_1387_);
if (v_isShared_1434_ == 0)
{
lean_ctor_set(v___x_1433_, 1, v_fst_1430_);
lean_ctor_set(v___x_1433_, 0, v_fst_1429_);
v___x_1455_ = v___x_1433_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_fst_1429_);
lean_ctor_set(v_reuseFailAlloc_1459_, 1, v_fst_1430_);
v___x_1455_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
lean_object* v___x_1457_; 
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 0, v___x_1455_);
v___x_1457_ = v___x_1439_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v___x_1455_);
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
}
else
{
lean_object* v_a_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1468_; 
lean_del_object(v___x_1433_);
lean_dec(v_fst_1430_);
lean_dec(v_fst_1429_);
lean_dec(v_a_1423_);
lean_dec(v_i_1393_);
lean_dec_ref(v_eType_1391_);
lean_dec_ref(v_targetType_1390_);
lean_dec(v_term_x3f_1389_);
lean_dec(v_mvarId_1387_);
v_a_1461_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1463_ = v___x_1436_;
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_a_1461_);
lean_dec(v___x_1436_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1466_; 
if (v_isShared_1464_ == 0)
{
v___x_1466_ = v___x_1463_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_a_1461_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
}
}
else
{
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1477_; 
lean_dec(v_a_1423_);
lean_dec(v_i_1393_);
lean_dec_ref(v_eType_1391_);
lean_dec_ref(v_targetType_1390_);
lean_dec(v_term_x3f_1389_);
lean_dec(v_mvarId_1387_);
v_a_1470_ = lean_ctor_get(v___x_1426_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1472_ = v___x_1426_;
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___x_1426_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1475_; 
if (v_isShared_1473_ == 0)
{
v___x_1475_ = v___x_1472_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_a_1470_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
}
else
{
lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1485_; 
lean_dec(v_i_1393_);
lean_dec_ref(v_eType_1391_);
lean_dec_ref(v_targetType_1390_);
lean_dec(v_term_x3f_1389_);
lean_dec(v_mvarId_1387_);
v_a_1478_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1480_ = v___x_1422_;
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1422_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go___boxed(lean_object* v_mvarId_1486_, lean_object* v_cfg_1487_, lean_object* v_term_x3f_1488_, lean_object* v_targetType_1489_, lean_object* v_eType_1490_, lean_object* v_rangeNumArgs_1491_, lean_object* v_i_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go(v_mvarId_1486_, v_cfg_1487_, v_term_x3f_1488_, v_targetType_1489_, v_eType_1490_, v_rangeNumArgs_1491_, v_i_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_);
lean_dec(v_a_1496_);
lean_dec_ref(v_a_1495_);
lean_dec(v_a_1494_);
lean_dec_ref(v_a_1493_);
lean_dec_ref(v_rangeNumArgs_1491_);
lean_dec_ref(v_cfg_1487_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go_match__1_splitter___redArg(lean_object* v_x_1499_, lean_object* v_h__1_1500_){
_start:
{
lean_object* v_snd_1501_; lean_object* v_fst_1502_; lean_object* v_fst_1503_; lean_object* v_snd_1504_; lean_object* v___x_1505_; 
v_snd_1501_ = lean_ctor_get(v_x_1499_, 1);
lean_inc(v_snd_1501_);
v_fst_1502_ = lean_ctor_get(v_x_1499_, 0);
lean_inc(v_fst_1502_);
lean_dec_ref(v_x_1499_);
v_fst_1503_ = lean_ctor_get(v_snd_1501_, 0);
lean_inc(v_fst_1503_);
v_snd_1504_ = lean_ctor_get(v_snd_1501_, 1);
lean_inc(v_snd_1504_);
lean_dec(v_snd_1501_);
v___x_1505_ = lean_apply_3(v_h__1_1500_, v_fst_1502_, v_fst_1503_, v_snd_1504_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go_match__1_splitter(lean_object* v_motive_1506_, lean_object* v_x_1507_, lean_object* v_h__1_1508_){
_start:
{
lean_object* v_snd_1509_; lean_object* v_fst_1510_; lean_object* v_fst_1511_; lean_object* v_snd_1512_; lean_object* v___x_1513_; 
v_snd_1509_ = lean_ctor_get(v_x_1507_, 1);
lean_inc(v_snd_1509_);
v_fst_1510_ = lean_ctor_get(v_x_1507_, 0);
lean_inc(v_fst_1510_);
lean_dec_ref(v_x_1507_);
v_fst_1511_ = lean_ctor_get(v_snd_1509_, 0);
lean_inc(v_fst_1511_);
v_snd_1512_ = lean_ctor_get(v_snd_1509_, 1);
lean_inc(v_snd_1512_);
lean_dec(v_snd_1509_);
v___x_1513_ = lean_apply_3(v_h__1_1508_, v_fst_1510_, v_fst_1511_, v_snd_1512_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(lean_object* v_e_1514_, lean_object* v___y_1515_){
_start:
{
uint8_t v___x_1517_; 
v___x_1517_ = l_Lean_Expr_hasMVar(v_e_1514_);
if (v___x_1517_ == 0)
{
lean_object* v___x_1518_; 
v___x_1518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1518_, 0, v_e_1514_);
return v___x_1518_;
}
else
{
lean_object* v___x_1519_; lean_object* v_mctx_1520_; lean_object* v___x_1521_; lean_object* v_fst_1522_; lean_object* v_snd_1523_; lean_object* v___x_1524_; lean_object* v_cache_1525_; lean_object* v_zetaDeltaFVarIds_1526_; lean_object* v_postponed_1527_; lean_object* v_diag_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1537_; 
v___x_1519_ = lean_st_ref_get(v___y_1515_);
v_mctx_1520_ = lean_ctor_get(v___x_1519_, 0);
lean_inc_ref(v_mctx_1520_);
lean_dec(v___x_1519_);
v___x_1521_ = l_Lean_instantiateMVarsCore(v_mctx_1520_, v_e_1514_);
v_fst_1522_ = lean_ctor_get(v___x_1521_, 0);
lean_inc(v_fst_1522_);
v_snd_1523_ = lean_ctor_get(v___x_1521_, 1);
lean_inc(v_snd_1523_);
lean_dec_ref(v___x_1521_);
v___x_1524_ = lean_st_ref_take(v___y_1515_);
v_cache_1525_ = lean_ctor_get(v___x_1524_, 1);
v_zetaDeltaFVarIds_1526_ = lean_ctor_get(v___x_1524_, 2);
v_postponed_1527_ = lean_ctor_get(v___x_1524_, 3);
v_diag_1528_ = lean_ctor_get(v___x_1524_, 4);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1537_ == 0)
{
lean_object* v_unused_1538_; 
v_unused_1538_ = lean_ctor_get(v___x_1524_, 0);
lean_dec(v_unused_1538_);
v___x_1530_ = v___x_1524_;
v_isShared_1531_ = v_isSharedCheck_1537_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_diag_1528_);
lean_inc(v_postponed_1527_);
lean_inc(v_zetaDeltaFVarIds_1526_);
lean_inc(v_cache_1525_);
lean_dec(v___x_1524_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1537_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1533_; 
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 0, v_snd_1523_);
v___x_1533_ = v___x_1530_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_snd_1523_);
lean_ctor_set(v_reuseFailAlloc_1536_, 1, v_cache_1525_);
lean_ctor_set(v_reuseFailAlloc_1536_, 2, v_zetaDeltaFVarIds_1526_);
lean_ctor_set(v_reuseFailAlloc_1536_, 3, v_postponed_1527_);
lean_ctor_set(v_reuseFailAlloc_1536_, 4, v_diag_1528_);
v___x_1533_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1534_ = lean_st_ref_set(v___y_1515_, v___x_1533_);
v___x_1535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1535_, 0, v_fst_1522_);
return v___x_1535_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg___boxed(lean_object* v_e_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_){
_start:
{
lean_object* v_res_1542_; 
v_res_1542_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_e_1539_, v___y_1540_);
lean_dec(v___y_1540_);
return v_res_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0(lean_object* v_e_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_){
_start:
{
lean_object* v___x_1549_; 
v___x_1549_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_e_1543_, v___y_1545_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___boxed(lean_object* v_e_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0(v_e_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
lean_dec(v___y_1552_);
lean_dec_ref(v___y_1551_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(lean_object* v_mvarId_1557_, lean_object* v_x_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_){
_start:
{
lean_object* v___x_1564_; 
v___x_1564_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1557_, v_x_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v_a_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1572_; 
v_a_1565_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1567_ = v___x_1564_;
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_a_1565_);
lean_dec(v___x_1564_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1570_; 
if (v_isShared_1568_ == 0)
{
v___x_1570_ = v___x_1567_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_a_1565_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
else
{
lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1580_; 
v_a_1573_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1575_ = v___x_1564_;
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v___x_1564_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg___boxed(lean_object* v_mvarId_1581_, lean_object* v_x_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_1581_, v_x_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec(v___y_1584_);
lean_dec_ref(v___y_1583_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6(lean_object* v_00_u03b1_1589_, lean_object* v_mvarId_1590_, lean_object* v_x_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_){
_start:
{
lean_object* v___x_1597_; 
v___x_1597_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_1590_, v_x_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___boxed(lean_object* v_00_u03b1_1598_, lean_object* v_mvarId_1599_, lean_object* v_x_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6(v_00_u03b1_1598_, v_mvarId_1599_, v_x_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
lean_dec(v___y_1602_);
lean_dec_ref(v___y_1601_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(lean_object* v_as_1607_, size_t v_i_1608_, size_t v_stop_1609_, lean_object* v_b_1610_, lean_object* v___y_1611_){
_start:
{
lean_object* v_a_1614_; uint8_t v___x_1618_; 
v___x_1618_ = lean_usize_dec_eq(v_i_1608_, v_stop_1609_);
if (v___x_1618_ == 0)
{
lean_object* v___x_1619_; lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1619_ = lean_array_uget_borrowed(v_as_1607_, v_i_1608_);
v___x_1622_ = l_Lean_Expr_mvarId_x21(v___x_1619_);
v___x_1623_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v___x_1622_, v___y_1611_);
lean_dec(v___x_1622_);
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_object* v_a_1624_; uint8_t v___x_1625_; 
v_a_1624_ = lean_ctor_get(v___x_1623_, 0);
lean_inc(v_a_1624_);
lean_dec_ref_known(v___x_1623_, 1);
v___x_1625_ = lean_unbox(v_a_1624_);
lean_dec(v_a_1624_);
if (v___x_1625_ == 0)
{
goto v___jp_1620_;
}
else
{
v_a_1614_ = v_b_1610_;
goto v___jp_1613_;
}
}
else
{
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_object* v_a_1626_; uint8_t v___x_1627_; 
v_a_1626_ = lean_ctor_get(v___x_1623_, 0);
lean_inc(v_a_1626_);
lean_dec_ref_known(v___x_1623_, 1);
v___x_1627_ = lean_unbox(v_a_1626_);
lean_dec(v_a_1626_);
if (v___x_1627_ == 0)
{
v_a_1614_ = v_b_1610_;
goto v___jp_1613_;
}
else
{
goto v___jp_1620_;
}
}
else
{
lean_object* v_a_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1635_; 
lean_dec_ref(v_b_1610_);
v_a_1628_ = lean_ctor_get(v___x_1623_, 0);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1630_ = v___x_1623_;
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_a_1628_);
lean_dec(v___x_1623_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1633_; 
if (v_isShared_1631_ == 0)
{
v___x_1633_ = v___x_1630_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_a_1628_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
}
}
v___jp_1620_:
{
lean_object* v___x_1621_; 
lean_inc(v___x_1619_);
v___x_1621_ = lean_array_push(v_b_1610_, v___x_1619_);
v_a_1614_ = v___x_1621_;
goto v___jp_1613_;
}
}
else
{
lean_object* v___x_1636_; 
v___x_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1636_, 0, v_b_1610_);
return v___x_1636_;
}
v___jp_1613_:
{
size_t v___x_1615_; size_t v___x_1616_; 
v___x_1615_ = ((size_t)1ULL);
v___x_1616_ = lean_usize_add(v_i_1608_, v___x_1615_);
v_i_1608_ = v___x_1616_;
v_b_1610_ = v_a_1614_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg___boxed(lean_object* v_as_1637_, lean_object* v_i_1638_, lean_object* v_stop_1639_, lean_object* v_b_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_){
_start:
{
size_t v_i_boxed_1643_; size_t v_stop_boxed_1644_; lean_object* v_res_1645_; 
v_i_boxed_1643_ = lean_unbox_usize(v_i_1638_);
lean_dec(v_i_1638_);
v_stop_boxed_1644_ = lean_unbox_usize(v_stop_1639_);
lean_dec(v_stop_1639_);
v_res_1645_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_as_1637_, v_i_boxed_1643_, v_stop_boxed_1644_, v_b_1640_, v___y_1641_);
lean_dec(v___y_1641_);
lean_dec_ref(v_as_1637_);
return v_res_1645_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_apply_spec__3(lean_object* v_as_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_){
_start:
{
if (lean_obj_tag(v_as_1646_) == 0)
{
lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1652_ = lean_box(0);
v___x_1653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1652_);
return v___x_1653_;
}
else
{
lean_object* v_head_1654_; lean_object* v_tail_1655_; lean_object* v___x_1656_; 
v_head_1654_ = lean_ctor_get(v_as_1646_, 0);
lean_inc(v_head_1654_);
v_tail_1655_ = lean_ctor_get(v_as_1646_, 1);
lean_inc(v_tail_1655_);
lean_dec_ref_known(v_as_1646_, 2);
v___x_1656_ = l_Lean_MVarId_headBetaType(v_head_1654_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_dec_ref_known(v___x_1656_, 1);
v_as_1646_ = v_tail_1655_;
goto _start;
}
else
{
lean_dec(v_tail_1655_);
return v___x_1656_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_MVarId_apply_spec__3___boxed(lean_object* v_as_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l_List_forM___at___00Lean_MVarId_apply_spec__3(v_as_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
return v_res_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9___redArg(lean_object* v_x_1665_, lean_object* v_x_1666_, lean_object* v_x_1667_, lean_object* v_x_1668_){
_start:
{
lean_object* v_ks_1669_; lean_object* v_vs_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1694_; 
v_ks_1669_ = lean_ctor_get(v_x_1665_, 0);
v_vs_1670_ = lean_ctor_get(v_x_1665_, 1);
v_isSharedCheck_1694_ = !lean_is_exclusive(v_x_1665_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1672_ = v_x_1665_;
v_isShared_1673_ = v_isSharedCheck_1694_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_vs_1670_);
lean_inc(v_ks_1669_);
lean_dec(v_x_1665_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1694_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1674_; uint8_t v___x_1675_; 
v___x_1674_ = lean_array_get_size(v_ks_1669_);
v___x_1675_ = lean_nat_dec_lt(v_x_1666_, v___x_1674_);
if (v___x_1675_ == 0)
{
lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1679_; 
lean_dec(v_x_1666_);
v___x_1676_ = lean_array_push(v_ks_1669_, v_x_1667_);
v___x_1677_ = lean_array_push(v_vs_1670_, v_x_1668_);
if (v_isShared_1673_ == 0)
{
lean_ctor_set(v___x_1672_, 1, v___x_1677_);
lean_ctor_set(v___x_1672_, 0, v___x_1676_);
v___x_1679_ = v___x_1672_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v___x_1676_);
lean_ctor_set(v_reuseFailAlloc_1680_, 1, v___x_1677_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
else
{
lean_object* v_k_x27_1681_; uint8_t v___x_1682_; 
v_k_x27_1681_ = lean_array_fget_borrowed(v_ks_1669_, v_x_1666_);
v___x_1682_ = l_Lean_instBEqMVarId_beq(v_x_1667_, v_k_x27_1681_);
if (v___x_1682_ == 0)
{
lean_object* v___x_1684_; 
if (v_isShared_1673_ == 0)
{
v___x_1684_ = v___x_1672_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_ks_1669_);
lean_ctor_set(v_reuseFailAlloc_1688_, 1, v_vs_1670_);
v___x_1684_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1685_ = lean_unsigned_to_nat(1u);
v___x_1686_ = lean_nat_add(v_x_1666_, v___x_1685_);
lean_dec(v_x_1666_);
v_x_1665_ = v___x_1684_;
v_x_1666_ = v___x_1686_;
goto _start;
}
}
else
{
lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1692_; 
v___x_1689_ = lean_array_fset(v_ks_1669_, v_x_1666_, v_x_1667_);
v___x_1690_ = lean_array_fset(v_vs_1670_, v_x_1666_, v_x_1668_);
lean_dec(v_x_1666_);
if (v_isShared_1673_ == 0)
{
lean_ctor_set(v___x_1672_, 1, v___x_1690_);
lean_ctor_set(v___x_1672_, 0, v___x_1689_);
v___x_1692_ = v___x_1672_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v___x_1689_);
lean_ctor_set(v_reuseFailAlloc_1693_, 1, v___x_1690_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8___redArg(lean_object* v_n_1695_, lean_object* v_k_1696_, lean_object* v_v_1697_){
_start:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1698_ = lean_unsigned_to_nat(0u);
v___x_1699_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9___redArg(v_n_1695_, v___x_1698_, v_k_1696_, v_v_1697_);
return v___x_1699_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1700_; 
v___x_1700_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(lean_object* v_x_1701_, size_t v_x_1702_, size_t v_x_1703_, lean_object* v_x_1704_, lean_object* v_x_1705_){
_start:
{
if (lean_obj_tag(v_x_1701_) == 0)
{
lean_object* v_es_1706_; size_t v___x_1707_; size_t v___x_1708_; size_t v___x_1709_; size_t v___x_1710_; lean_object* v_j_1711_; lean_object* v___x_1712_; uint8_t v___x_1713_; 
v_es_1706_ = lean_ctor_get(v_x_1701_, 0);
v___x_1707_ = ((size_t)5ULL);
v___x_1708_ = ((size_t)1ULL);
v___x_1709_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1710_ = lean_usize_land(v_x_1702_, v___x_1709_);
v_j_1711_ = lean_usize_to_nat(v___x_1710_);
v___x_1712_ = lean_array_get_size(v_es_1706_);
v___x_1713_ = lean_nat_dec_lt(v_j_1711_, v___x_1712_);
if (v___x_1713_ == 0)
{
lean_dec(v_j_1711_);
lean_dec(v_x_1705_);
lean_dec(v_x_1704_);
return v_x_1701_;
}
else
{
lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1750_; 
lean_inc_ref(v_es_1706_);
v_isSharedCheck_1750_ = !lean_is_exclusive(v_x_1701_);
if (v_isSharedCheck_1750_ == 0)
{
lean_object* v_unused_1751_; 
v_unused_1751_ = lean_ctor_get(v_x_1701_, 0);
lean_dec(v_unused_1751_);
v___x_1715_ = v_x_1701_;
v_isShared_1716_ = v_isSharedCheck_1750_;
goto v_resetjp_1714_;
}
else
{
lean_dec(v_x_1701_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1750_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v_v_1717_; lean_object* v___x_1718_; lean_object* v_xs_x27_1719_; lean_object* v___y_1721_; 
v_v_1717_ = lean_array_fget(v_es_1706_, v_j_1711_);
v___x_1718_ = lean_box(0);
v_xs_x27_1719_ = lean_array_fset(v_es_1706_, v_j_1711_, v___x_1718_);
switch(lean_obj_tag(v_v_1717_))
{
case 0:
{
lean_object* v_key_1726_; lean_object* v_val_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1737_; 
v_key_1726_ = lean_ctor_get(v_v_1717_, 0);
v_val_1727_ = lean_ctor_get(v_v_1717_, 1);
v_isSharedCheck_1737_ = !lean_is_exclusive(v_v_1717_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1729_ = v_v_1717_;
v_isShared_1730_ = v_isSharedCheck_1737_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_val_1727_);
lean_inc(v_key_1726_);
lean_dec(v_v_1717_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1737_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
uint8_t v___x_1731_; 
v___x_1731_ = l_Lean_instBEqMVarId_beq(v_x_1704_, v_key_1726_);
if (v___x_1731_ == 0)
{
lean_object* v___x_1732_; lean_object* v___x_1733_; 
lean_del_object(v___x_1729_);
v___x_1732_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1726_, v_val_1727_, v_x_1704_, v_x_1705_);
v___x_1733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1732_);
v___y_1721_ = v___x_1733_;
goto v___jp_1720_;
}
else
{
lean_object* v___x_1735_; 
lean_dec(v_val_1727_);
lean_dec(v_key_1726_);
if (v_isShared_1730_ == 0)
{
lean_ctor_set(v___x_1729_, 1, v_x_1705_);
lean_ctor_set(v___x_1729_, 0, v_x_1704_);
v___x_1735_ = v___x_1729_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_x_1704_);
lean_ctor_set(v_reuseFailAlloc_1736_, 1, v_x_1705_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
v___y_1721_ = v___x_1735_;
goto v___jp_1720_;
}
}
}
}
case 1:
{
lean_object* v_node_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1748_; 
v_node_1738_ = lean_ctor_get(v_v_1717_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v_v_1717_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1740_ = v_v_1717_;
v_isShared_1741_ = v_isSharedCheck_1748_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_node_1738_);
lean_dec(v_v_1717_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1748_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
size_t v___x_1742_; size_t v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1746_; 
v___x_1742_ = lean_usize_shift_right(v_x_1702_, v___x_1707_);
v___x_1743_ = lean_usize_add(v_x_1703_, v___x_1708_);
v___x_1744_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_node_1738_, v___x_1742_, v___x_1743_, v_x_1704_, v_x_1705_);
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 0, v___x_1744_);
v___x_1746_ = v___x_1740_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v___x_1744_);
v___x_1746_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
v___y_1721_ = v___x_1746_;
goto v___jp_1720_;
}
}
}
default: 
{
lean_object* v___x_1749_; 
v___x_1749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1749_, 0, v_x_1704_);
lean_ctor_set(v___x_1749_, 1, v_x_1705_);
v___y_1721_ = v___x_1749_;
goto v___jp_1720_;
}
}
v___jp_1720_:
{
lean_object* v___x_1722_; lean_object* v___x_1724_; 
v___x_1722_ = lean_array_fset(v_xs_x27_1719_, v_j_1711_, v___y_1721_);
lean_dec(v_j_1711_);
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 0, v___x_1722_);
v___x_1724_ = v___x_1715_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v___x_1722_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
}
}
}
}
}
else
{
lean_object* v_ks_1752_; lean_object* v_vs_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1773_; 
v_ks_1752_ = lean_ctor_get(v_x_1701_, 0);
v_vs_1753_ = lean_ctor_get(v_x_1701_, 1);
v_isSharedCheck_1773_ = !lean_is_exclusive(v_x_1701_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1755_ = v_x_1701_;
v_isShared_1756_ = v_isSharedCheck_1773_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_vs_1753_);
lean_inc(v_ks_1752_);
lean_dec(v_x_1701_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1773_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1758_; 
if (v_isShared_1756_ == 0)
{
v___x_1758_ = v___x_1755_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v_ks_1752_);
lean_ctor_set(v_reuseFailAlloc_1772_, 1, v_vs_1753_);
v___x_1758_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
lean_object* v_newNode_1759_; uint8_t v___y_1761_; size_t v___x_1767_; uint8_t v___x_1768_; 
v_newNode_1759_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8___redArg(v___x_1758_, v_x_1704_, v_x_1705_);
v___x_1767_ = ((size_t)7ULL);
v___x_1768_ = lean_usize_dec_le(v___x_1767_, v_x_1703_);
if (v___x_1768_ == 0)
{
lean_object* v___x_1769_; lean_object* v___x_1770_; uint8_t v___x_1771_; 
v___x_1769_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1759_);
v___x_1770_ = lean_unsigned_to_nat(4u);
v___x_1771_ = lean_nat_dec_lt(v___x_1769_, v___x_1770_);
lean_dec(v___x_1769_);
v___y_1761_ = v___x_1771_;
goto v___jp_1760_;
}
else
{
v___y_1761_ = v___x_1768_;
goto v___jp_1760_;
}
v___jp_1760_:
{
if (v___y_1761_ == 0)
{
lean_object* v_ks_1762_; lean_object* v_vs_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
v_ks_1762_ = lean_ctor_get(v_newNode_1759_, 0);
lean_inc_ref(v_ks_1762_);
v_vs_1763_ = lean_ctor_get(v_newNode_1759_, 1);
lean_inc_ref(v_vs_1763_);
lean_dec_ref(v_newNode_1759_);
v___x_1764_ = lean_unsigned_to_nat(0u);
v___x_1765_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0);
v___x_1766_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(v_x_1703_, v_ks_1762_, v_vs_1763_, v___x_1764_, v___x_1765_);
lean_dec_ref(v_vs_1763_);
lean_dec_ref(v_ks_1762_);
return v___x_1766_;
}
else
{
return v_newNode_1759_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(size_t v_depth_1774_, lean_object* v_keys_1775_, lean_object* v_vals_1776_, lean_object* v_i_1777_, lean_object* v_entries_1778_){
_start:
{
lean_object* v___x_1779_; uint8_t v___x_1780_; 
v___x_1779_ = lean_array_get_size(v_keys_1775_);
v___x_1780_ = lean_nat_dec_lt(v_i_1777_, v___x_1779_);
if (v___x_1780_ == 0)
{
lean_dec(v_i_1777_);
return v_entries_1778_;
}
else
{
lean_object* v_k_1781_; lean_object* v_v_1782_; uint64_t v___x_1783_; size_t v_h_1784_; size_t v___x_1785_; lean_object* v___x_1786_; size_t v___x_1787_; size_t v___x_1788_; size_t v___x_1789_; size_t v_h_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
v_k_1781_ = lean_array_fget_borrowed(v_keys_1775_, v_i_1777_);
v_v_1782_ = lean_array_fget_borrowed(v_vals_1776_, v_i_1777_);
v___x_1783_ = l_Lean_instHashableMVarId_hash(v_k_1781_);
v_h_1784_ = lean_uint64_to_usize(v___x_1783_);
v___x_1785_ = ((size_t)5ULL);
v___x_1786_ = lean_unsigned_to_nat(1u);
v___x_1787_ = ((size_t)1ULL);
v___x_1788_ = lean_usize_sub(v_depth_1774_, v___x_1787_);
v___x_1789_ = lean_usize_mul(v___x_1785_, v___x_1788_);
v_h_1790_ = lean_usize_shift_right(v_h_1784_, v___x_1789_);
v___x_1791_ = lean_nat_add(v_i_1777_, v___x_1786_);
lean_dec(v_i_1777_);
lean_inc(v_v_1782_);
lean_inc(v_k_1781_);
v___x_1792_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_entries_1778_, v_h_1790_, v_depth_1774_, v_k_1781_, v_v_1782_);
v_i_1777_ = v___x_1791_;
v_entries_1778_ = v___x_1792_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg___boxed(lean_object* v_depth_1794_, lean_object* v_keys_1795_, lean_object* v_vals_1796_, lean_object* v_i_1797_, lean_object* v_entries_1798_){
_start:
{
size_t v_depth_boxed_1799_; lean_object* v_res_1800_; 
v_depth_boxed_1799_ = lean_unbox_usize(v_depth_1794_);
lean_dec(v_depth_1794_);
v_res_1800_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(v_depth_boxed_1799_, v_keys_1795_, v_vals_1796_, v_i_1797_, v_entries_1798_);
lean_dec_ref(v_vals_1796_);
lean_dec_ref(v_keys_1795_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_x_1801_, lean_object* v_x_1802_, lean_object* v_x_1803_, lean_object* v_x_1804_, lean_object* v_x_1805_){
_start:
{
size_t v_x_7242__boxed_1806_; size_t v_x_7243__boxed_1807_; lean_object* v_res_1808_; 
v_x_7242__boxed_1806_ = lean_unbox_usize(v_x_1802_);
lean_dec(v_x_1802_);
v_x_7243__boxed_1807_ = lean_unbox_usize(v_x_1803_);
lean_dec(v_x_1803_);
v_res_1808_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_x_1801_, v_x_7242__boxed_1806_, v_x_7243__boxed_1807_, v_x_1804_, v_x_1805_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1___redArg(lean_object* v_x_1809_, lean_object* v_x_1810_, lean_object* v_x_1811_){
_start:
{
uint64_t v___x_1812_; size_t v___x_1813_; size_t v___x_1814_; lean_object* v___x_1815_; 
v___x_1812_ = l_Lean_instHashableMVarId_hash(v_x_1810_);
v___x_1813_ = lean_uint64_to_usize(v___x_1812_);
v___x_1814_ = ((size_t)1ULL);
v___x_1815_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_x_1809_, v___x_1813_, v___x_1814_, v_x_1810_, v_x_1811_);
return v___x_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(lean_object* v_mvarId_1816_, lean_object* v_val_1817_, lean_object* v___y_1818_){
_start:
{
lean_object* v___x_1820_; lean_object* v_mctx_1821_; lean_object* v_cache_1822_; lean_object* v_zetaDeltaFVarIds_1823_; lean_object* v_postponed_1824_; lean_object* v_diag_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1853_; 
v___x_1820_ = lean_st_ref_take(v___y_1818_);
v_mctx_1821_ = lean_ctor_get(v___x_1820_, 0);
v_cache_1822_ = lean_ctor_get(v___x_1820_, 1);
v_zetaDeltaFVarIds_1823_ = lean_ctor_get(v___x_1820_, 2);
v_postponed_1824_ = lean_ctor_get(v___x_1820_, 3);
v_diag_1825_ = lean_ctor_get(v___x_1820_, 4);
v_isSharedCheck_1853_ = !lean_is_exclusive(v___x_1820_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1827_ = v___x_1820_;
v_isShared_1828_ = v_isSharedCheck_1853_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_diag_1825_);
lean_inc(v_postponed_1824_);
lean_inc(v_zetaDeltaFVarIds_1823_);
lean_inc(v_cache_1822_);
lean_inc(v_mctx_1821_);
lean_dec(v___x_1820_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1853_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v_depth_1829_; lean_object* v_levelAssignDepth_1830_; lean_object* v_lmvarCounter_1831_; lean_object* v_mvarCounter_1832_; lean_object* v_lDecls_1833_; lean_object* v_decls_1834_; lean_object* v_userNames_1835_; lean_object* v_lAssignment_1836_; lean_object* v_eAssignment_1837_; lean_object* v_dAssignment_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1852_; 
v_depth_1829_ = lean_ctor_get(v_mctx_1821_, 0);
v_levelAssignDepth_1830_ = lean_ctor_get(v_mctx_1821_, 1);
v_lmvarCounter_1831_ = lean_ctor_get(v_mctx_1821_, 2);
v_mvarCounter_1832_ = lean_ctor_get(v_mctx_1821_, 3);
v_lDecls_1833_ = lean_ctor_get(v_mctx_1821_, 4);
v_decls_1834_ = lean_ctor_get(v_mctx_1821_, 5);
v_userNames_1835_ = lean_ctor_get(v_mctx_1821_, 6);
v_lAssignment_1836_ = lean_ctor_get(v_mctx_1821_, 7);
v_eAssignment_1837_ = lean_ctor_get(v_mctx_1821_, 8);
v_dAssignment_1838_ = lean_ctor_get(v_mctx_1821_, 9);
v_isSharedCheck_1852_ = !lean_is_exclusive(v_mctx_1821_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1840_ = v_mctx_1821_;
v_isShared_1841_ = v_isSharedCheck_1852_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_dAssignment_1838_);
lean_inc(v_eAssignment_1837_);
lean_inc(v_lAssignment_1836_);
lean_inc(v_userNames_1835_);
lean_inc(v_decls_1834_);
lean_inc(v_lDecls_1833_);
lean_inc(v_mvarCounter_1832_);
lean_inc(v_lmvarCounter_1831_);
lean_inc(v_levelAssignDepth_1830_);
lean_inc(v_depth_1829_);
lean_dec(v_mctx_1821_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1852_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1842_; lean_object* v___x_1844_; 
v___x_1842_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1___redArg(v_eAssignment_1837_, v_mvarId_1816_, v_val_1817_);
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 8, v___x_1842_);
v___x_1844_ = v___x_1840_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_depth_1829_);
lean_ctor_set(v_reuseFailAlloc_1851_, 1, v_levelAssignDepth_1830_);
lean_ctor_set(v_reuseFailAlloc_1851_, 2, v_lmvarCounter_1831_);
lean_ctor_set(v_reuseFailAlloc_1851_, 3, v_mvarCounter_1832_);
lean_ctor_set(v_reuseFailAlloc_1851_, 4, v_lDecls_1833_);
lean_ctor_set(v_reuseFailAlloc_1851_, 5, v_decls_1834_);
lean_ctor_set(v_reuseFailAlloc_1851_, 6, v_userNames_1835_);
lean_ctor_set(v_reuseFailAlloc_1851_, 7, v_lAssignment_1836_);
lean_ctor_set(v_reuseFailAlloc_1851_, 8, v___x_1842_);
lean_ctor_set(v_reuseFailAlloc_1851_, 9, v_dAssignment_1838_);
v___x_1844_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
lean_object* v___x_1846_; 
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 0, v___x_1844_);
v___x_1846_ = v___x_1827_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v___x_1844_);
lean_ctor_set(v_reuseFailAlloc_1850_, 1, v_cache_1822_);
lean_ctor_set(v_reuseFailAlloc_1850_, 2, v_zetaDeltaFVarIds_1823_);
lean_ctor_set(v_reuseFailAlloc_1850_, 3, v_postponed_1824_);
lean_ctor_set(v_reuseFailAlloc_1850_, 4, v_diag_1825_);
v___x_1846_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1847_ = lean_st_ref_set(v___y_1818_, v___x_1846_);
v___x_1848_ = lean_box(0);
v___x_1849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1848_);
return v___x_1849_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg___boxed(lean_object* v_mvarId_1854_, lean_object* v_val_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_){
_start:
{
lean_object* v_res_1858_; 
v_res_1858_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_1854_, v_val_1855_, v___y_1856_);
lean_dec(v___y_1856_);
return v_res_1858_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_MVarId_apply_spec__2(lean_object* v_a_1859_, lean_object* v_x_1860_){
_start:
{
if (lean_obj_tag(v_x_1860_) == 0)
{
uint8_t v___x_1861_; 
v___x_1861_ = 0;
return v___x_1861_;
}
else
{
lean_object* v_head_1862_; lean_object* v_tail_1863_; uint8_t v___x_1864_; 
v_head_1862_ = lean_ctor_get(v_x_1860_, 0);
v_tail_1863_ = lean_ctor_get(v_x_1860_, 1);
v___x_1864_ = l_Lean_instBEqMVarId_beq(v_a_1859_, v_head_1862_);
if (v___x_1864_ == 0)
{
v_x_1860_ = v_tail_1863_;
goto _start;
}
else
{
return v___x_1864_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_MVarId_apply_spec__2___boxed(lean_object* v_a_1866_, lean_object* v_x_1867_){
_start:
{
uint8_t v_res_1868_; lean_object* v_r_1869_; 
v_res_1868_ = l_List_elem___at___00Lean_MVarId_apply_spec__2(v_a_1866_, v_x_1867_);
lean_dec(v_x_1867_);
lean_dec(v_a_1866_);
v_r_1869_ = lean_box(v_res_1868_);
return v_r_1869_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(lean_object* v_a_1870_, lean_object* v_as_1871_, size_t v_i_1872_, size_t v_stop_1873_, lean_object* v_b_1874_){
_start:
{
lean_object* v___y_1876_; uint8_t v___x_1880_; 
v___x_1880_ = lean_usize_dec_eq(v_i_1872_, v_stop_1873_);
if (v___x_1880_ == 0)
{
lean_object* v___x_1881_; uint8_t v___x_1882_; 
v___x_1881_ = lean_array_uget_borrowed(v_as_1871_, v_i_1872_);
v___x_1882_ = l_List_elem___at___00Lean_MVarId_apply_spec__2(v___x_1881_, v_a_1870_);
if (v___x_1882_ == 0)
{
lean_object* v___x_1883_; 
lean_inc(v___x_1881_);
v___x_1883_ = lean_array_push(v_b_1874_, v___x_1881_);
v___y_1876_ = v___x_1883_;
goto v___jp_1875_;
}
else
{
v___y_1876_ = v_b_1874_;
goto v___jp_1875_;
}
}
else
{
return v_b_1874_;
}
v___jp_1875_:
{
size_t v___x_1877_; size_t v___x_1878_; 
v___x_1877_ = ((size_t)1ULL);
v___x_1878_ = lean_usize_add(v_i_1872_, v___x_1877_);
v_i_1872_ = v___x_1878_;
v_b_1874_ = v___y_1876_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4___boxed(lean_object* v_a_1884_, lean_object* v_as_1885_, lean_object* v_i_1886_, lean_object* v_stop_1887_, lean_object* v_b_1888_){
_start:
{
size_t v_i_boxed_1889_; size_t v_stop_boxed_1890_; lean_object* v_res_1891_; 
v_i_boxed_1889_ = lean_unbox_usize(v_i_1886_);
lean_dec(v_i_1886_);
v_stop_boxed_1890_ = lean_unbox_usize(v_stop_1887_);
lean_dec(v_stop_1887_);
v_res_1891_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(v_a_1884_, v_as_1885_, v_i_boxed_1889_, v_stop_boxed_1890_, v_b_1888_);
lean_dec_ref(v_as_1885_);
lean_dec(v_a_1884_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___lam__0(lean_object* v_mvarId_1892_, lean_object* v___x_1893_, lean_object* v_e_1894_, lean_object* v_cfg_1895_, lean_object* v_term_x3f_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_){
_start:
{
lean_object* v___y_1903_; lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1929_; lean_object* v___y_1930_; lean_object* v___y_1931_; lean_object* v___y_1932_; lean_object* v___y_1933_; uint8_t v___y_1934_; lean_object* v___y_1935_; lean_object* v___y_1936_; lean_object* v_a_1937_; lean_object* v___y_1970_; lean_object* v___y_1971_; lean_object* v___y_1972_; lean_object* v___y_1973_; lean_object* v___y_1974_; uint8_t v___y_1975_; lean_object* v___y_1976_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v___x_1988_; 
lean_inc(v___x_1893_);
lean_inc(v_mvarId_1892_);
v___x_1988_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1892_, v___x_1893_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_object* v___x_1989_; 
lean_dec_ref_known(v___x_1988_, 1);
lean_inc(v_mvarId_1892_);
v___x_1989_ = l_Lean_MVarId_getType(v_mvarId_1892_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_object* v_a_1990_; lean_object* v___x_1991_; 
v_a_1990_ = lean_ctor_get(v___x_1989_, 0);
lean_inc(v_a_1990_);
lean_dec_ref_known(v___x_1989_, 1);
lean_inc(v___y_1900_);
lean_inc_ref(v___y_1899_);
lean_inc(v___y_1898_);
lean_inc_ref(v___y_1897_);
lean_inc_ref(v_e_1894_);
v___x_1991_ = lean_infer_type(v_e_1894_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_object* v_a_1992_; lean_object* v_rangeNumArgs_1994_; lean_object* v_lower_1995_; lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v___y_1999_; lean_object* v___x_2039_; 
v_a_1992_ = lean_ctor_get(v___x_1991_, 0);
lean_inc_n(v_a_1992_, 2);
lean_dec_ref_known(v___x_1991_, 1);
v___x_2039_ = l_Lean_Meta_getExpectedNumArgsAux(v_a_1992_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v_a_2040_; lean_object* v_snd_2041_; uint8_t v___x_2042_; 
v_a_2040_ = lean_ctor_get(v___x_2039_, 0);
lean_inc(v_a_2040_);
lean_dec_ref_known(v___x_2039_, 1);
v_snd_2041_ = lean_ctor_get(v_a_2040_, 1);
v___x_2042_ = lean_unbox(v_snd_2041_);
if (v___x_2042_ == 0)
{
lean_object* v_fst_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2063_; 
v_fst_2043_ = lean_ctor_get(v_a_2040_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v_a_2040_);
if (v_isSharedCheck_2063_ == 0)
{
lean_object* v_unused_2064_; 
v_unused_2064_ = lean_ctor_get(v_a_2040_, 1);
lean_dec(v_unused_2064_);
v___x_2045_ = v_a_2040_;
v_isShared_2046_ = v_isSharedCheck_2063_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_fst_2043_);
lean_dec(v_a_2040_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2063_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2047_; 
lean_inc(v_a_1990_);
v___x_2047_ = l_Lean_Meta_getExpectedNumArgs(v_a_1990_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v_a_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2053_; 
v_a_2048_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_a_2048_);
lean_dec_ref_known(v___x_2047_, 1);
v___x_2049_ = lean_nat_sub(v_fst_2043_, v_a_2048_);
lean_dec(v_a_2048_);
v___x_2050_ = lean_unsigned_to_nat(1u);
v___x_2051_ = lean_nat_add(v_fst_2043_, v___x_2050_);
lean_dec(v_fst_2043_);
lean_inc(v___x_2049_);
if (v_isShared_2046_ == 0)
{
lean_ctor_set(v___x_2045_, 1, v___x_2051_);
lean_ctor_set(v___x_2045_, 0, v___x_2049_);
v___x_2053_ = v___x_2045_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v___x_2049_);
lean_ctor_set(v_reuseFailAlloc_2054_, 1, v___x_2051_);
v___x_2053_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
v_rangeNumArgs_1994_ = v___x_2053_;
v_lower_1995_ = v___x_2049_;
v___y_1996_ = v___y_1897_;
v___y_1997_ = v___y_1898_;
v___y_1998_ = v___y_1899_;
v___y_1999_ = v___y_1900_;
goto v___jp_1993_;
}
}
else
{
lean_object* v_a_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2062_; 
lean_del_object(v___x_2045_);
lean_dec(v_fst_2043_);
lean_dec(v_a_1992_);
lean_dec(v_a_1990_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec(v_term_x3f_1896_);
lean_dec_ref(v_e_1894_);
lean_dec(v___x_1893_);
lean_dec(v_mvarId_1892_);
v_a_2055_ = lean_ctor_get(v___x_2047_, 0);
v_isSharedCheck_2062_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2057_ = v___x_2047_;
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_a_2055_);
lean_dec(v___x_2047_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2060_; 
if (v_isShared_2058_ == 0)
{
v___x_2060_ = v___x_2057_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_a_2055_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
}
}
}
}
}
else
{
lean_object* v_fst_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2074_; 
v_fst_2065_ = lean_ctor_get(v_a_2040_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v_a_2040_);
if (v_isSharedCheck_2074_ == 0)
{
lean_object* v_unused_2075_; 
v_unused_2075_ = lean_ctor_get(v_a_2040_, 1);
lean_dec(v_unused_2075_);
v___x_2067_ = v_a_2040_;
v_isShared_2068_ = v_isSharedCheck_2074_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_fst_2065_);
lean_dec(v_a_2040_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2074_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2072_; 
v___x_2069_ = lean_unsigned_to_nat(1u);
v___x_2070_ = lean_nat_add(v_fst_2065_, v___x_2069_);
lean_inc(v_fst_2065_);
if (v_isShared_2068_ == 0)
{
lean_ctor_set(v___x_2067_, 1, v___x_2070_);
v___x_2072_ = v___x_2067_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_fst_2065_);
lean_ctor_set(v_reuseFailAlloc_2073_, 1, v___x_2070_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
v_rangeNumArgs_1994_ = v___x_2072_;
v_lower_1995_ = v_fst_2065_;
v___y_1996_ = v___y_1897_;
v___y_1997_ = v___y_1898_;
v___y_1998_ = v___y_1899_;
v___y_1999_ = v___y_1900_;
goto v___jp_1993_;
}
}
}
}
else
{
lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2083_; 
lean_dec(v_a_1992_);
lean_dec(v_a_1990_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec(v_term_x3f_1896_);
lean_dec_ref(v_e_1894_);
lean_dec(v___x_1893_);
lean_dec(v_mvarId_1892_);
v_a_2076_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2078_ = v___x_2039_;
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_2039_);
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
v___jp_1993_:
{
lean_object* v___x_2000_; 
lean_inc(v_mvarId_1892_);
v___x_2000_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go(v_mvarId_1892_, v_cfg_1895_, v_term_x3f_1896_, v_a_1990_, v_a_1992_, v_rangeNumArgs_1994_, v_lower_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
lean_dec_ref(v_rangeNumArgs_1994_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_object* v_a_2001_; lean_object* v_fst_2002_; lean_object* v_snd_2003_; uint8_t v_newGoals_2004_; uint8_t v_synthAssignedInstances_2005_; uint8_t v_allowSynthFailures_2006_; lean_object* v___x_2007_; 
v_a_2001_ = lean_ctor_get(v___x_2000_, 0);
lean_inc(v_a_2001_);
lean_dec_ref_known(v___x_2000_, 1);
v_fst_2002_ = lean_ctor_get(v_a_2001_, 0);
lean_inc(v_fst_2002_);
v_snd_2003_ = lean_ctor_get(v_a_2001_, 1);
lean_inc_n(v_snd_2003_, 2);
lean_dec(v_a_2001_);
v_newGoals_2004_ = lean_ctor_get_uint8(v_cfg_1895_, 0);
v_synthAssignedInstances_2005_ = lean_ctor_get_uint8(v_cfg_1895_, 1);
v_allowSynthFailures_2006_ = lean_ctor_get_uint8(v_cfg_1895_, 2);
lean_inc(v_mvarId_1892_);
v___x_2007_ = l_Lean_Meta_synthAppInstances(v___x_1893_, v_mvarId_1892_, v_fst_2002_, v_snd_2003_, v_synthAssignedInstances_2005_, v_allowSynthFailures_2006_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v___x_2008_; lean_object* v_a_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; uint8_t v___x_2015_; 
lean_dec_ref_known(v___x_2007_, 1);
v___x_2008_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_e_1894_, v___y_1997_);
v_a_2009_ = lean_ctor_get(v___x_2008_, 0);
lean_inc_n(v_a_2009_, 2);
lean_dec_ref(v___x_2008_);
v___x_2010_ = l_Lean_mkAppN(v_a_2009_, v_fst_2002_);
lean_inc(v_mvarId_1892_);
v___x_2011_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_1892_, v___x_2010_, v___y_1997_);
lean_dec_ref(v___x_2011_);
v___x_2012_ = lean_unsigned_to_nat(0u);
v___x_2013_ = lean_array_get_size(v_fst_2002_);
v___x_2014_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0));
v___x_2015_ = lean_nat_dec_lt(v___x_2012_, v___x_2013_);
if (v___x_2015_ == 0)
{
lean_dec(v_fst_2002_);
v___y_1929_ = v___y_1999_;
v___y_1930_ = v___x_2012_;
v___y_1931_ = v_a_2009_;
v___y_1932_ = v___y_1998_;
v___y_1933_ = v___y_1997_;
v___y_1934_ = v_newGoals_2004_;
v___y_1935_ = v_snd_2003_;
v___y_1936_ = v___y_1996_;
v_a_1937_ = v___x_2014_;
goto v___jp_1928_;
}
else
{
uint8_t v___x_2016_; 
v___x_2016_ = lean_nat_dec_le(v___x_2013_, v___x_2013_);
if (v___x_2016_ == 0)
{
if (v___x_2015_ == 0)
{
lean_dec(v_fst_2002_);
v___y_1929_ = v___y_1999_;
v___y_1930_ = v___x_2012_;
v___y_1931_ = v_a_2009_;
v___y_1932_ = v___y_1998_;
v___y_1933_ = v___y_1997_;
v___y_1934_ = v_newGoals_2004_;
v___y_1935_ = v_snd_2003_;
v___y_1936_ = v___y_1996_;
v_a_1937_ = v___x_2014_;
goto v___jp_1928_;
}
else
{
size_t v___x_2017_; size_t v___x_2018_; lean_object* v___x_2019_; 
v___x_2017_ = ((size_t)0ULL);
v___x_2018_ = lean_usize_of_nat(v___x_2013_);
v___x_2019_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_fst_2002_, v___x_2017_, v___x_2018_, v___x_2014_, v___y_1997_);
lean_dec(v_fst_2002_);
v___y_1970_ = v___y_1999_;
v___y_1971_ = v___x_2012_;
v___y_1972_ = v_a_2009_;
v___y_1973_ = v___y_1998_;
v___y_1974_ = v___y_1997_;
v___y_1975_ = v_newGoals_2004_;
v___y_1976_ = v_snd_2003_;
v___y_1977_ = v___y_1996_;
v___y_1978_ = v___x_2019_;
goto v___jp_1969_;
}
}
else
{
size_t v___x_2020_; size_t v___x_2021_; lean_object* v___x_2022_; 
v___x_2020_ = ((size_t)0ULL);
v___x_2021_ = lean_usize_of_nat(v___x_2013_);
v___x_2022_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_fst_2002_, v___x_2020_, v___x_2021_, v___x_2014_, v___y_1997_);
lean_dec(v_fst_2002_);
v___y_1970_ = v___y_1999_;
v___y_1971_ = v___x_2012_;
v___y_1972_ = v_a_2009_;
v___y_1973_ = v___y_1998_;
v___y_1974_ = v___y_1997_;
v___y_1975_ = v_newGoals_2004_;
v___y_1976_ = v_snd_2003_;
v___y_1977_ = v___y_1996_;
v___y_1978_ = v___x_2022_;
goto v___jp_1969_;
}
}
}
else
{
lean_object* v_a_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2030_; 
lean_dec(v_snd_2003_);
lean_dec(v_fst_2002_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1996_);
lean_dec_ref(v_e_1894_);
lean_dec(v_mvarId_1892_);
v_a_2023_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2030_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_2025_ = v___x_2007_;
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_a_2023_);
lean_dec(v___x_2007_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2028_; 
if (v_isShared_2026_ == 0)
{
v___x_2028_ = v___x_2025_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v_a_2023_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
return v___x_2028_;
}
}
}
}
else
{
lean_object* v_a_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2038_; 
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1996_);
lean_dec_ref(v_e_1894_);
lean_dec(v___x_1893_);
lean_dec(v_mvarId_1892_);
v_a_2031_ = lean_ctor_get(v___x_2000_, 0);
v_isSharedCheck_2038_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_2033_ = v___x_2000_;
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_a_2031_);
lean_dec(v___x_2000_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2036_; 
if (v_isShared_2034_ == 0)
{
v___x_2036_ = v___x_2033_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_a_2031_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
return v___x_2036_;
}
}
}
}
}
else
{
lean_object* v_a_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2091_; 
lean_dec(v_a_1990_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec(v_term_x3f_1896_);
lean_dec_ref(v_e_1894_);
lean_dec(v___x_1893_);
lean_dec(v_mvarId_1892_);
v_a_2084_ = lean_ctor_get(v___x_1991_, 0);
v_isSharedCheck_2091_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2086_ = v___x_1991_;
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_a_2084_);
lean_dec(v___x_1991_);
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
}
else
{
lean_object* v_a_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2099_; 
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec(v_term_x3f_1896_);
lean_dec_ref(v_e_1894_);
lean_dec(v___x_1893_);
lean_dec(v_mvarId_1892_);
v_a_2092_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_2099_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2094_ = v___x_1989_;
v_isShared_2095_ = v_isSharedCheck_2099_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_a_2092_);
lean_dec(v___x_1989_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2099_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v___x_2097_; 
if (v_isShared_2095_ == 0)
{
v___x_2097_ = v___x_2094_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v_a_2092_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
}
}
else
{
lean_object* v_a_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2107_; 
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec(v_term_x3f_1896_);
lean_dec_ref(v_e_1894_);
lean_dec(v___x_1893_);
lean_dec(v_mvarId_1892_);
v_a_2100_ = lean_ctor_get(v___x_1988_, 0);
v_isSharedCheck_2107_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2102_ = v___x_1988_;
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_a_2100_);
lean_dec(v___x_1988_);
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
v___jp_1902_:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1909_ = lean_array_to_list(v___y_1908_);
v___x_1910_ = l_List_appendTR___redArg(v___y_1906_, v___x_1909_);
lean_inc(v___x_1910_);
v___x_1911_ = l_List_forM___at___00Lean_MVarId_apply_spec__3(v___x_1910_, v___y_1907_, v___y_1905_, v___y_1904_, v___y_1903_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1904_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1907_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1918_; 
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1918_ == 0)
{
lean_object* v_unused_1919_; 
v_unused_1919_ = lean_ctor_get(v___x_1911_, 0);
lean_dec(v_unused_1919_);
v___x_1913_ = v___x_1911_;
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
else
{
lean_dec(v___x_1911_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1916_; 
if (v_isShared_1914_ == 0)
{
lean_ctor_set(v___x_1913_, 0, v___x_1910_);
v___x_1916_ = v___x_1913_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v___x_1910_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
else
{
lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1927_; 
lean_dec(v___x_1910_);
v_a_1920_ = lean_ctor_get(v___x_1911_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1922_ = v___x_1911_;
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1911_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1925_; 
if (v_isShared_1923_ == 0)
{
v___x_1925_ = v___x_1922_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_a_1920_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
}
}
v___jp_1928_:
{
lean_object* v___x_1938_; 
v___x_1938_ = l_Lean_Meta_appendParentTag(v_mvarId_1892_, v_a_1937_, v___y_1935_, v___y_1936_, v___y_1933_, v___y_1932_, v___y_1929_);
lean_dec_ref(v___y_1935_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v___x_1939_; 
lean_dec_ref_known(v___x_1938_, 1);
v___x_1939_ = l_Lean_Meta_getMVarsNoDelayed(v___y_1931_, v___y_1936_, v___y_1933_, v___y_1932_, v___y_1929_);
if (lean_obj_tag(v___x_1939_) == 0)
{
lean_object* v_a_1940_; lean_object* v___x_1941_; 
v_a_1940_ = lean_ctor_get(v___x_1939_, 0);
lean_inc(v_a_1940_);
lean_dec_ref_known(v___x_1939_, 1);
v___x_1941_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(v_a_1937_, v___y_1934_, v___y_1936_, v___y_1933_, v___y_1932_, v___y_1929_);
if (lean_obj_tag(v___x_1941_) == 0)
{
lean_object* v_a_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; uint8_t v___x_1945_; 
v_a_1942_ = lean_ctor_get(v___x_1941_, 0);
lean_inc(v_a_1942_);
lean_dec_ref_known(v___x_1941_, 1);
v___x_1943_ = lean_array_get_size(v_a_1940_);
v___x_1944_ = lean_mk_empty_array_with_capacity(v___y_1930_);
v___x_1945_ = lean_nat_dec_lt(v___y_1930_, v___x_1943_);
if (v___x_1945_ == 0)
{
lean_dec(v_a_1940_);
v___y_1903_ = v___y_1929_;
v___y_1904_ = v___y_1932_;
v___y_1905_ = v___y_1933_;
v___y_1906_ = v_a_1942_;
v___y_1907_ = v___y_1936_;
v___y_1908_ = v___x_1944_;
goto v___jp_1902_;
}
else
{
uint8_t v___x_1946_; 
v___x_1946_ = lean_nat_dec_le(v___x_1943_, v___x_1943_);
if (v___x_1946_ == 0)
{
if (v___x_1945_ == 0)
{
lean_dec(v_a_1940_);
v___y_1903_ = v___y_1929_;
v___y_1904_ = v___y_1932_;
v___y_1905_ = v___y_1933_;
v___y_1906_ = v_a_1942_;
v___y_1907_ = v___y_1936_;
v___y_1908_ = v___x_1944_;
goto v___jp_1902_;
}
else
{
size_t v___x_1947_; size_t v___x_1948_; lean_object* v___x_1949_; 
v___x_1947_ = ((size_t)0ULL);
v___x_1948_ = lean_usize_of_nat(v___x_1943_);
v___x_1949_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(v_a_1942_, v_a_1940_, v___x_1947_, v___x_1948_, v___x_1944_);
lean_dec(v_a_1940_);
v___y_1903_ = v___y_1929_;
v___y_1904_ = v___y_1932_;
v___y_1905_ = v___y_1933_;
v___y_1906_ = v_a_1942_;
v___y_1907_ = v___y_1936_;
v___y_1908_ = v___x_1949_;
goto v___jp_1902_;
}
}
else
{
size_t v___x_1950_; size_t v___x_1951_; lean_object* v___x_1952_; 
v___x_1950_ = ((size_t)0ULL);
v___x_1951_ = lean_usize_of_nat(v___x_1943_);
v___x_1952_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(v_a_1942_, v_a_1940_, v___x_1950_, v___x_1951_, v___x_1944_);
lean_dec(v_a_1940_);
v___y_1903_ = v___y_1929_;
v___y_1904_ = v___y_1932_;
v___y_1905_ = v___y_1933_;
v___y_1906_ = v_a_1942_;
v___y_1907_ = v___y_1936_;
v___y_1908_ = v___x_1952_;
goto v___jp_1902_;
}
}
}
else
{
lean_dec(v_a_1940_);
lean_dec_ref(v___y_1936_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
lean_dec(v___y_1929_);
return v___x_1941_;
}
}
else
{
lean_object* v_a_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1960_; 
lean_dec_ref(v_a_1937_);
lean_dec_ref(v___y_1936_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
lean_dec(v___y_1929_);
v_a_1953_ = lean_ctor_get(v___x_1939_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1955_ = v___x_1939_;
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_a_1953_);
lean_dec(v___x_1939_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___x_1958_; 
if (v_isShared_1956_ == 0)
{
v___x_1958_ = v___x_1955_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_a_1953_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
}
else
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1968_; 
lean_dec_ref(v_a_1937_);
lean_dec_ref(v___y_1936_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
lean_dec_ref(v___y_1931_);
lean_dec(v___y_1929_);
v_a_1961_ = lean_ctor_get(v___x_1938_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1963_ = v___x_1938_;
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___x_1938_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1966_; 
if (v_isShared_1964_ == 0)
{
v___x_1966_ = v___x_1963_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_a_1961_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
}
}
v___jp_1969_:
{
if (lean_obj_tag(v___y_1978_) == 0)
{
lean_object* v_a_1979_; 
v_a_1979_ = lean_ctor_get(v___y_1978_, 0);
lean_inc(v_a_1979_);
lean_dec_ref_known(v___y_1978_, 1);
v___y_1929_ = v___y_1970_;
v___y_1930_ = v___y_1971_;
v___y_1931_ = v___y_1972_;
v___y_1932_ = v___y_1973_;
v___y_1933_ = v___y_1974_;
v___y_1934_ = v___y_1975_;
v___y_1935_ = v___y_1976_;
v___y_1936_ = v___y_1977_;
v_a_1937_ = v_a_1979_;
goto v___jp_1928_;
}
else
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1987_; 
lean_dec_ref(v___y_1977_);
lean_dec_ref(v___y_1976_);
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_dec(v___y_1970_);
lean_dec(v_mvarId_1892_);
v_a_1980_ = lean_ctor_get(v___y_1978_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___y_1978_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1982_ = v___y_1978_;
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___y_1978_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1985_; 
if (v_isShared_1983_ == 0)
{
v___x_1985_ = v___x_1982_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_a_1980_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___lam__0___boxed(lean_object* v_mvarId_2108_, lean_object* v___x_2109_, lean_object* v_e_2110_, lean_object* v_cfg_2111_, lean_object* v_term_x3f_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_){
_start:
{
lean_object* v_res_2118_; 
v_res_2118_ = l_Lean_MVarId_apply___lam__0(v_mvarId_2108_, v___x_2109_, v_e_2110_, v_cfg_2111_, v_term_x3f_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
lean_dec_ref(v_cfg_2111_);
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply(lean_object* v_mvarId_2119_, lean_object* v_e_2120_, lean_object* v_cfg_2121_, lean_object* v_term_x3f_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_){
_start:
{
lean_object* v___x_2128_; lean_object* v___f_2129_; lean_object* v___x_2130_; 
v___x_2128_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1));
lean_inc(v_mvarId_2119_);
v___f_2129_ = lean_alloc_closure((void*)(l_Lean_MVarId_apply___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2129_, 0, v_mvarId_2119_);
lean_closure_set(v___f_2129_, 1, v___x_2128_);
lean_closure_set(v___f_2129_, 2, v_e_2120_);
lean_closure_set(v___f_2129_, 3, v_cfg_2121_);
lean_closure_set(v___f_2129_, 4, v_term_x3f_2122_);
v___x_2130_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2119_, v___f_2129_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_);
return v___x_2130_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_apply___boxed(lean_object* v_mvarId_2131_, lean_object* v_e_2132_, lean_object* v_cfg_2133_, lean_object* v_term_x3f_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_){
_start:
{
lean_object* v_res_2140_; 
v_res_2140_ = l_Lean_MVarId_apply(v_mvarId_2131_, v_e_2132_, v_cfg_2133_, v_term_x3f_2134_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_);
lean_dec(v_a_2138_);
lean_dec_ref(v_a_2137_);
lean_dec(v_a_2136_);
lean_dec_ref(v_a_2135_);
return v_res_2140_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1(lean_object* v_mvarId_2141_, lean_object* v_val_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_){
_start:
{
lean_object* v___x_2148_; 
v___x_2148_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2141_, v_val_2142_, v___y_2144_);
return v___x_2148_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___boxed(lean_object* v_mvarId_2149_, lean_object* v_val_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_){
_start:
{
lean_object* v_res_2156_; 
v_res_2156_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1(v_mvarId_2149_, v_val_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
lean_dec(v___y_2154_);
lean_dec_ref(v___y_2153_);
lean_dec(v___y_2152_);
lean_dec_ref(v___y_2151_);
return v_res_2156_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5(lean_object* v_as_2157_, size_t v_i_2158_, size_t v_stop_2159_, lean_object* v_b_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_){
_start:
{
lean_object* v___x_2166_; 
v___x_2166_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_as_2157_, v_i_2158_, v_stop_2159_, v_b_2160_, v___y_2162_);
return v___x_2166_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___boxed(lean_object* v_as_2167_, lean_object* v_i_2168_, lean_object* v_stop_2169_, lean_object* v_b_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_){
_start:
{
size_t v_i_boxed_2176_; size_t v_stop_boxed_2177_; lean_object* v_res_2178_; 
v_i_boxed_2176_ = lean_unbox_usize(v_i_2168_);
lean_dec(v_i_2168_);
v_stop_boxed_2177_ = lean_unbox_usize(v_stop_2169_);
lean_dec(v_stop_2169_);
v_res_2178_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5(v_as_2167_, v_i_boxed_2176_, v_stop_boxed_2177_, v_b_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_);
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2173_);
lean_dec(v___y_2172_);
lean_dec_ref(v___y_2171_);
lean_dec_ref(v_as_2167_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1(lean_object* v_00_u03b2_2179_, lean_object* v_x_2180_, lean_object* v_x_2181_, lean_object* v_x_2182_){
_start:
{
lean_object* v___x_2183_; 
v___x_2183_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1___redArg(v_x_2180_, v_x_2181_, v_x_2182_);
return v___x_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_2184_, lean_object* v_x_2185_, size_t v_x_2186_, size_t v_x_2187_, lean_object* v_x_2188_, lean_object* v_x_2189_){
_start:
{
lean_object* v___x_2190_; 
v___x_2190_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_x_2185_, v_x_2186_, v_x_2187_, v_x_2188_, v_x_2189_);
return v___x_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2191_, lean_object* v_x_2192_, lean_object* v_x_2193_, lean_object* v_x_2194_, lean_object* v_x_2195_, lean_object* v_x_2196_){
_start:
{
size_t v_x_7975__boxed_2197_; size_t v_x_7976__boxed_2198_; lean_object* v_res_2199_; 
v_x_7975__boxed_2197_ = lean_unbox_usize(v_x_2193_);
lean_dec(v_x_2193_);
v_x_7976__boxed_2198_ = lean_unbox_usize(v_x_2194_);
lean_dec(v_x_2194_);
v_res_2199_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3(v_00_u03b2_2191_, v_x_2192_, v_x_7975__boxed_2197_, v_x_7976__boxed_2198_, v_x_2195_, v_x_2196_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_2200_, lean_object* v_n_2201_, lean_object* v_k_2202_, lean_object* v_v_2203_){
_start:
{
lean_object* v___x_2204_; 
v___x_2204_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8___redArg(v_n_2201_, v_k_2202_, v_v_2203_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9(lean_object* v_00_u03b2_2205_, size_t v_depth_2206_, lean_object* v_keys_2207_, lean_object* v_vals_2208_, lean_object* v_heq_2209_, lean_object* v_i_2210_, lean_object* v_entries_2211_){
_start:
{
lean_object* v___x_2212_; 
v___x_2212_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(v_depth_2206_, v_keys_2207_, v_vals_2208_, v_i_2210_, v_entries_2211_);
return v___x_2212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___boxed(lean_object* v_00_u03b2_2213_, lean_object* v_depth_2214_, lean_object* v_keys_2215_, lean_object* v_vals_2216_, lean_object* v_heq_2217_, lean_object* v_i_2218_, lean_object* v_entries_2219_){
_start:
{
size_t v_depth_boxed_2220_; lean_object* v_res_2221_; 
v_depth_boxed_2220_ = lean_unbox_usize(v_depth_2214_);
lean_dec(v_depth_2214_);
v_res_2221_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9(v_00_u03b2_2213_, v_depth_boxed_2220_, v_keys_2215_, v_vals_2216_, v_heq_2217_, v_i_2218_, v_entries_2219_);
lean_dec_ref(v_vals_2216_);
lean_dec_ref(v_keys_2215_);
return v_res_2221_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9(lean_object* v_00_u03b2_2222_, lean_object* v_x_2223_, lean_object* v_x_2224_, lean_object* v_x_2225_, lean_object* v_x_2226_){
_start:
{
lean_object* v___x_2227_; 
v___x_2227_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9___redArg(v_x_2223_, v_x_2224_, v_x_2225_, v_x_2226_);
return v___x_2227_;
}
}
static lean_object* _init_l_Lean_MVarId_applyConst___closed__1(void){
_start:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2229_ = ((lean_object*)(l_Lean_MVarId_applyConst___closed__0));
v___x_2230_ = l_Lean_stringToMessageData(v___x_2229_);
return v___x_2230_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyConst(lean_object* v_mvar_2231_, lean_object* v_c_2232_, lean_object* v_cfg_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_){
_start:
{
lean_object* v___x_2239_; 
lean_inc(v_c_2232_);
v___x_2239_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_c_2232_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_);
if (lean_obj_tag(v___x_2239_) == 0)
{
lean_object* v_a_2240_; lean_object* v___x_2241_; uint8_t v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
v_a_2240_ = lean_ctor_get(v___x_2239_, 0);
lean_inc(v_a_2240_);
lean_dec_ref_known(v___x_2239_, 1);
v___x_2241_ = lean_obj_once(&l_Lean_MVarId_applyConst___closed__1, &l_Lean_MVarId_applyConst___closed__1_once, _init_l_Lean_MVarId_applyConst___closed__1);
v___x_2242_ = 0;
v___x_2243_ = l_Lean_MessageData_ofConstName(v_c_2232_, v___x_2242_);
v___x_2244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2241_);
lean_ctor_set(v___x_2244_, 1, v___x_2243_);
v___x_2245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2245_, 0, v___x_2244_);
lean_ctor_set(v___x_2245_, 1, v___x_2241_);
v___x_2246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2245_);
v___x_2247_ = l_Lean_MVarId_apply(v_mvar_2231_, v_a_2240_, v_cfg_2233_, v___x_2246_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_);
return v___x_2247_;
}
else
{
lean_object* v_a_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2255_; 
lean_dec_ref(v_cfg_2233_);
lean_dec(v_c_2232_);
lean_dec(v_mvar_2231_);
v_a_2248_ = lean_ctor_get(v___x_2239_, 0);
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2239_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2250_ = v___x_2239_;
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_a_2248_);
lean_dec(v___x_2239_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v___x_2253_; 
if (v_isShared_2251_ == 0)
{
v___x_2253_ = v___x_2250_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_a_2248_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
return v___x_2253_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyConst___boxed(lean_object* v_mvar_2256_, lean_object* v_c_2257_, lean_object* v_cfg_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_){
_start:
{
lean_object* v_res_2264_; 
v_res_2264_ = l_Lean_MVarId_applyConst(v_mvar_2256_, v_c_2257_, v_cfg_2258_, v_a_2259_, v_a_2260_, v_a_2261_, v_a_2262_);
lean_dec(v_a_2262_);
lean_dec_ref(v_a_2261_);
lean_dec(v_a_2260_);
lean_dec_ref(v_a_2259_);
return v_res_2264_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1(lean_object* v_msgData_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_){
_start:
{
lean_object* v___x_2271_; lean_object* v_env_2272_; lean_object* v___x_2273_; lean_object* v_mctx_2274_; lean_object* v_lctx_2275_; lean_object* v_options_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
v___x_2271_ = lean_st_ref_get(v___y_2269_);
v_env_2272_ = lean_ctor_get(v___x_2271_, 0);
lean_inc_ref(v_env_2272_);
lean_dec(v___x_2271_);
v___x_2273_ = lean_st_ref_get(v___y_2267_);
v_mctx_2274_ = lean_ctor_get(v___x_2273_, 0);
lean_inc_ref(v_mctx_2274_);
lean_dec(v___x_2273_);
v_lctx_2275_ = lean_ctor_get(v___y_2266_, 2);
v_options_2276_ = lean_ctor_get(v___y_2268_, 2);
lean_inc_ref(v_options_2276_);
lean_inc_ref(v_lctx_2275_);
v___x_2277_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2277_, 0, v_env_2272_);
lean_ctor_set(v___x_2277_, 1, v_mctx_2274_);
lean_ctor_set(v___x_2277_, 2, v_lctx_2275_);
lean_ctor_set(v___x_2277_, 3, v_options_2276_);
v___x_2278_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2277_);
lean_ctor_set(v___x_2278_, 1, v_msgData_2265_);
v___x_2279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2279_, 0, v___x_2278_);
return v___x_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1___boxed(lean_object* v_msgData_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_){
_start:
{
lean_object* v_res_2286_; 
v_res_2286_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1(v_msgData_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(lean_object* v_msg_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_){
_start:
{
lean_object* v_ref_2293_; lean_object* v___x_2294_; lean_object* v_a_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2303_; 
v_ref_2293_ = lean_ctor_get(v___y_2290_, 5);
v___x_2294_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1(v_msg_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_);
v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2303_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2303_ == 0)
{
v___x_2297_ = v___x_2294_;
v_isShared_2298_ = v_isSharedCheck_2303_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_a_2295_);
lean_dec(v___x_2294_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2303_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2299_; lean_object* v___x_2301_; 
lean_inc(v_ref_2293_);
v___x_2299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2299_, 0, v_ref_2293_);
lean_ctor_set(v___x_2299_, 1, v_a_2295_);
if (v_isShared_2298_ == 0)
{
lean_ctor_set_tag(v___x_2297_, 1);
lean_ctor_set(v___x_2297_, 0, v___x_2299_);
v___x_2301_ = v___x_2297_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v___x_2299_);
v___x_2301_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
return v___x_2301_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg___boxed(lean_object* v_msg_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_){
_start:
{
lean_object* v_res_2310_; 
v_res_2310_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v_msg_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
lean_dec(v___y_2308_);
lean_dec_ref(v___y_2307_);
lean_dec(v___y_2306_);
lean_dec_ref(v___y_2305_);
return v_res_2310_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0(size_t v_sz_2311_, size_t v_i_2312_, lean_object* v_bs_2313_){
_start:
{
uint8_t v___x_2314_; 
v___x_2314_ = lean_usize_dec_lt(v_i_2312_, v_sz_2311_);
if (v___x_2314_ == 0)
{
return v_bs_2313_;
}
else
{
lean_object* v_v_2315_; lean_object* v___x_2316_; lean_object* v_bs_x27_2317_; lean_object* v___x_2318_; size_t v___x_2319_; size_t v___x_2320_; lean_object* v___x_2321_; 
v_v_2315_ = lean_array_uget(v_bs_2313_, v_i_2312_);
v___x_2316_ = lean_unsigned_to_nat(0u);
v_bs_x27_2317_ = lean_array_uset(v_bs_2313_, v_i_2312_, v___x_2316_);
v___x_2318_ = l_Lean_Expr_mvarId_x21(v_v_2315_);
lean_dec(v_v_2315_);
v___x_2319_ = ((size_t)1ULL);
v___x_2320_ = lean_usize_add(v_i_2312_, v___x_2319_);
v___x_2321_ = lean_array_uset(v_bs_x27_2317_, v_i_2312_, v___x_2318_);
v_i_2312_ = v___x_2320_;
v_bs_2313_ = v___x_2321_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0___boxed(lean_object* v_sz_2323_, lean_object* v_i_2324_, lean_object* v_bs_2325_){
_start:
{
size_t v_sz_boxed_2326_; size_t v_i_boxed_2327_; lean_object* v_res_2328_; 
v_sz_boxed_2326_ = lean_unbox_usize(v_sz_2323_);
lean_dec(v_sz_2323_);
v_i_boxed_2327_ = lean_unbox_usize(v_i_2324_);
lean_dec(v_i_2324_);
v_res_2328_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0(v_sz_boxed_2326_, v_i_boxed_2327_, v_bs_2325_);
return v_res_2328_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; 
v___x_2330_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__0));
v___x_2331_ = l_Lean_stringToMessageData(v___x_2330_);
return v___x_2331_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2333_; lean_object* v___x_2334_; 
v___x_2333_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__2));
v___x_2334_ = l_Lean_stringToMessageData(v___x_2333_);
return v___x_2334_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___x_2336_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__4));
v___x_2337_ = l_Lean_stringToMessageData(v___x_2336_);
return v___x_2337_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__7(void){
_start:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; 
v___x_2339_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__6));
v___x_2340_ = l_Lean_stringToMessageData(v___x_2339_);
return v___x_2340_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__9(void){
_start:
{
lean_object* v___x_2342_; lean_object* v___x_2343_; 
v___x_2342_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__8));
v___x_2343_ = l_Lean_stringToMessageData(v___x_2342_);
return v___x_2343_;
}
}
static lean_object* _init_l_Lean_MVarId_applyN___lam__0___closed__11(void){
_start:
{
lean_object* v___x_2345_; lean_object* v___x_2346_; 
v___x_2345_ = ((lean_object*)(l_Lean_MVarId_applyN___lam__0___closed__10));
v___x_2346_ = l_Lean_stringToMessageData(v___x_2345_);
return v___x_2346_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN___lam__0(lean_object* v_mvarId_2347_, lean_object* v___x_2348_, lean_object* v_e_2349_, lean_object* v_n_2350_, uint8_t v_useApproxDefEq_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_){
_start:
{
lean_object* v___x_2357_; 
lean_inc(v_mvarId_2347_);
v___x_2357_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2347_, v___x_2348_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_);
if (lean_obj_tag(v___x_2357_) == 0)
{
lean_object* v___x_2358_; 
lean_dec_ref_known(v___x_2357_, 1);
lean_inc(v_mvarId_2347_);
v___x_2358_ = l_Lean_MVarId_getType(v_mvarId_2347_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_);
if (lean_obj_tag(v___x_2358_) == 0)
{
lean_object* v_a_2359_; lean_object* v___x_2360_; 
v_a_2359_ = lean_ctor_get(v___x_2358_, 0);
lean_inc(v_a_2359_);
lean_dec_ref_known(v___x_2358_, 1);
lean_inc(v___y_2355_);
lean_inc_ref(v___y_2354_);
lean_inc(v___y_2353_);
lean_inc_ref(v___y_2352_);
lean_inc_ref(v_e_2349_);
v___x_2360_ = lean_infer_type(v_e_2349_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_);
if (lean_obj_tag(v___x_2360_) == 0)
{
lean_object* v_a_2361_; uint8_t v___x_2362_; lean_object* v___x_2363_; 
v_a_2361_ = lean_ctor_get(v___x_2360_, 0);
lean_inc(v_a_2361_);
lean_dec_ref_known(v___x_2360_, 1);
v___x_2362_ = 0;
lean_inc(v_n_2350_);
v___x_2363_ = l_Lean_Meta_forallMetaBoundedTelescope(v_a_2361_, v_n_2350_, v___x_2362_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_);
if (lean_obj_tag(v___x_2363_) == 0)
{
lean_object* v_a_2364_; lean_object* v_fst_2365_; lean_object* v_snd_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2456_; 
v_a_2364_ = lean_ctor_get(v___x_2363_, 0);
lean_inc(v_a_2364_);
lean_dec_ref_known(v___x_2363_, 1);
v_fst_2365_ = lean_ctor_get(v_a_2364_, 0);
v_snd_2366_ = lean_ctor_get(v_a_2364_, 1);
v_isSharedCheck_2456_ = !lean_is_exclusive(v_a_2364_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2368_ = v_a_2364_;
v_isShared_2369_ = v_isSharedCheck_2456_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_snd_2366_);
lean_inc(v_fst_2365_);
lean_dec(v_a_2364_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2456_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___y_2371_; lean_object* v_snd_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2454_; 
v_snd_2386_ = lean_ctor_get(v_snd_2366_, 1);
v_isSharedCheck_2454_ = !lean_is_exclusive(v_snd_2366_);
if (v_isSharedCheck_2454_ == 0)
{
lean_object* v_unused_2455_; 
v_unused_2455_ = lean_ctor_get(v_snd_2366_, 0);
lean_dec(v_unused_2455_);
v___x_2388_ = v_snd_2366_;
v_isShared_2389_ = v_isSharedCheck_2454_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_snd_2386_);
lean_dec(v_snd_2366_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2454_;
goto v_resetjp_2387_;
}
v___jp_2370_:
{
lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2384_; 
lean_inc(v_fst_2365_);
v___x_2372_ = l_Lean_Expr_beta(v_e_2349_, v_fst_2365_);
v___x_2373_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2347_, v___x_2372_, v___y_2371_);
lean_dec(v___y_2371_);
v_isSharedCheck_2384_ = !lean_is_exclusive(v___x_2373_);
if (v_isSharedCheck_2384_ == 0)
{
lean_object* v_unused_2385_; 
v_unused_2385_ = lean_ctor_get(v___x_2373_, 0);
lean_dec(v_unused_2385_);
v___x_2375_ = v___x_2373_;
v_isShared_2376_ = v_isSharedCheck_2384_;
goto v_resetjp_2374_;
}
else
{
lean_dec(v___x_2373_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2384_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
size_t v_sz_2377_; size_t v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2382_; 
v_sz_2377_ = lean_array_size(v_fst_2365_);
v___x_2378_ = ((size_t)0ULL);
v___x_2379_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0(v_sz_2377_, v___x_2378_, v_fst_2365_);
v___x_2380_ = lean_array_to_list(v___x_2379_);
if (v_isShared_2376_ == 0)
{
lean_ctor_set(v___x_2375_, 0, v___x_2380_);
v___x_2382_ = v___x_2375_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v___x_2380_);
v___x_2382_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
return v___x_2382_;
}
}
}
v_resetjp_2387_:
{
lean_object* v___y_2391_; lean_object* v___y_2392_; lean_object* v___y_2393_; lean_object* v___y_2394_; lean_object* v___x_2434_; uint8_t v___x_2435_; 
v___x_2434_ = lean_array_get_size(v_fst_2365_);
v___x_2435_ = lean_nat_dec_eq(v___x_2434_, v_n_2350_);
if (v___x_2435_ == 0)
{
lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v_a_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2453_; 
lean_del_object(v___x_2388_);
lean_del_object(v___x_2368_);
lean_dec(v_fst_2365_);
lean_dec(v_a_2359_);
lean_dec_ref(v_e_2349_);
lean_dec(v_mvarId_2347_);
v___x_2436_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__9, &l_Lean_MVarId_applyN___lam__0___closed__9_once, _init_l_Lean_MVarId_applyN___lam__0___closed__9);
v___x_2437_ = l_Nat_reprFast(v_n_2350_);
v___x_2438_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2438_, 0, v___x_2437_);
v___x_2439_ = l_Lean_MessageData_ofFormat(v___x_2438_);
v___x_2440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2440_, 0, v___x_2436_);
lean_ctor_set(v___x_2440_, 1, v___x_2439_);
v___x_2441_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__11, &l_Lean_MVarId_applyN___lam__0___closed__11_once, _init_l_Lean_MVarId_applyN___lam__0___closed__11);
v___x_2442_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2440_);
lean_ctor_set(v___x_2442_, 1, v___x_2441_);
v___x_2443_ = l_Lean_indentExpr(v_snd_2386_);
v___x_2444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2444_, 0, v___x_2442_);
lean_ctor_set(v___x_2444_, 1, v___x_2443_);
v___x_2445_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_2444_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_);
lean_dec(v___y_2355_);
lean_dec_ref(v___y_2354_);
lean_dec(v___y_2353_);
lean_dec_ref(v___y_2352_);
v_a_2446_ = lean_ctor_get(v___x_2445_, 0);
v_isSharedCheck_2453_ = !lean_is_exclusive(v___x_2445_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2448_ = v___x_2445_;
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_a_2446_);
lean_dec(v___x_2445_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2451_; 
if (v_isShared_2449_ == 0)
{
v___x_2451_ = v___x_2448_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_a_2446_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
}
else
{
v___y_2391_ = v___y_2352_;
v___y_2392_ = v___y_2353_;
v___y_2393_ = v___y_2354_;
v___y_2394_ = v___y_2355_;
goto v___jp_2390_;
}
v___jp_2390_:
{
lean_object* v___x_2395_; 
lean_inc(v_a_2359_);
lean_inc(v_snd_2386_);
v___x_2395_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(v_useApproxDefEq_2351_, v_snd_2386_, v_a_2359_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
if (lean_obj_tag(v___x_2395_) == 0)
{
lean_object* v_a_2396_; uint8_t v___x_2397_; 
v_a_2396_ = lean_ctor_get(v___x_2395_, 0);
lean_inc(v_a_2396_);
lean_dec_ref_known(v___x_2395_, 1);
v___x_2397_ = lean_unbox(v_a_2396_);
lean_dec(v_a_2396_);
if (v___x_2397_ == 0)
{
lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2401_; 
lean_dec(v_fst_2365_);
lean_dec_ref(v_e_2349_);
lean_dec(v_mvarId_2347_);
v___x_2398_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__1, &l_Lean_MVarId_applyN___lam__0___closed__1_once, _init_l_Lean_MVarId_applyN___lam__0___closed__1);
v___x_2399_ = l_Lean_indentExpr(v_a_2359_);
if (v_isShared_2389_ == 0)
{
lean_ctor_set_tag(v___x_2388_, 7);
lean_ctor_set(v___x_2388_, 1, v___x_2399_);
lean_ctor_set(v___x_2388_, 0, v___x_2398_);
v___x_2401_ = v___x_2388_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v___x_2398_);
lean_ctor_set(v_reuseFailAlloc_2425_, 1, v___x_2399_);
v___x_2401_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
lean_object* v___x_2402_; lean_object* v___x_2404_; 
v___x_2402_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__3, &l_Lean_MVarId_applyN___lam__0___closed__3_once, _init_l_Lean_MVarId_applyN___lam__0___closed__3);
if (v_isShared_2369_ == 0)
{
lean_ctor_set_tag(v___x_2368_, 7);
lean_ctor_set(v___x_2368_, 1, v___x_2402_);
lean_ctor_set(v___x_2368_, 0, v___x_2401_);
v___x_2404_ = v___x_2368_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v___x_2401_);
lean_ctor_set(v_reuseFailAlloc_2424_, 1, v___x_2402_);
v___x_2404_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v_a_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2423_; 
v___x_2405_ = l_Lean_indentExpr(v_snd_2386_);
v___x_2406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2404_);
lean_ctor_set(v___x_2406_, 1, v___x_2405_);
v___x_2407_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__5, &l_Lean_MVarId_applyN___lam__0___closed__5_once, _init_l_Lean_MVarId_applyN___lam__0___closed__5);
v___x_2408_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2408_, 0, v___x_2406_);
lean_ctor_set(v___x_2408_, 1, v___x_2407_);
v___x_2409_ = l_Nat_reprFast(v_n_2350_);
v___x_2410_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2409_);
v___x_2411_ = l_Lean_MessageData_ofFormat(v___x_2410_);
v___x_2412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2412_, 0, v___x_2408_);
lean_ctor_set(v___x_2412_, 1, v___x_2411_);
v___x_2413_ = lean_obj_once(&l_Lean_MVarId_applyN___lam__0___closed__7, &l_Lean_MVarId_applyN___lam__0___closed__7_once, _init_l_Lean_MVarId_applyN___lam__0___closed__7);
v___x_2414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2412_);
lean_ctor_set(v___x_2414_, 1, v___x_2413_);
v___x_2415_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_2414_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
v_a_2416_ = lean_ctor_get(v___x_2415_, 0);
v_isSharedCheck_2423_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2423_ == 0)
{
v___x_2418_ = v___x_2415_;
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_a_2416_);
lean_dec(v___x_2415_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2421_; 
if (v_isShared_2419_ == 0)
{
v___x_2421_ = v___x_2418_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v_a_2416_);
v___x_2421_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
return v___x_2421_;
}
}
}
}
}
else
{
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
lean_dec_ref(v___y_2391_);
lean_del_object(v___x_2388_);
lean_dec(v_snd_2386_);
lean_del_object(v___x_2368_);
lean_dec(v_a_2359_);
lean_dec(v_n_2350_);
v___y_2371_ = v___y_2392_;
goto v___jp_2370_;
}
}
else
{
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2433_; 
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
lean_del_object(v___x_2388_);
lean_dec(v_snd_2386_);
lean_del_object(v___x_2368_);
lean_dec(v_fst_2365_);
lean_dec(v_a_2359_);
lean_dec(v_n_2350_);
lean_dec_ref(v_e_2349_);
lean_dec(v_mvarId_2347_);
v_a_2426_ = lean_ctor_get(v___x_2395_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2428_ = v___x_2395_;
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2395_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2431_; 
if (v_isShared_2429_ == 0)
{
v___x_2431_ = v___x_2428_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_a_2426_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2464_; 
lean_dec(v_a_2359_);
lean_dec(v___y_2355_);
lean_dec_ref(v___y_2354_);
lean_dec(v___y_2353_);
lean_dec_ref(v___y_2352_);
lean_dec(v_n_2350_);
lean_dec_ref(v_e_2349_);
lean_dec(v_mvarId_2347_);
v_a_2457_ = lean_ctor_get(v___x_2363_, 0);
v_isSharedCheck_2464_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2464_ == 0)
{
v___x_2459_ = v___x_2363_;
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_a_2457_);
lean_dec(v___x_2363_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v___x_2462_; 
if (v_isShared_2460_ == 0)
{
v___x_2462_ = v___x_2459_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v_a_2457_);
v___x_2462_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
return v___x_2462_;
}
}
}
}
else
{
lean_object* v_a_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2472_; 
lean_dec(v_a_2359_);
lean_dec(v___y_2355_);
lean_dec_ref(v___y_2354_);
lean_dec(v___y_2353_);
lean_dec_ref(v___y_2352_);
lean_dec(v_n_2350_);
lean_dec_ref(v_e_2349_);
lean_dec(v_mvarId_2347_);
v_a_2465_ = lean_ctor_get(v___x_2360_, 0);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2467_ = v___x_2360_;
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_a_2465_);
lean_dec(v___x_2360_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___x_2470_; 
if (v_isShared_2468_ == 0)
{
v___x_2470_ = v___x_2467_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v_a_2465_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
}
}
else
{
lean_object* v_a_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2480_; 
lean_dec(v___y_2355_);
lean_dec_ref(v___y_2354_);
lean_dec(v___y_2353_);
lean_dec_ref(v___y_2352_);
lean_dec(v_n_2350_);
lean_dec_ref(v_e_2349_);
lean_dec(v_mvarId_2347_);
v_a_2473_ = lean_ctor_get(v___x_2358_, 0);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2358_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2475_ = v___x_2358_;
v_isShared_2476_ = v_isSharedCheck_2480_;
goto v_resetjp_2474_;
}
else
{
lean_inc(v_a_2473_);
lean_dec(v___x_2358_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2480_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
lean_object* v___x_2478_; 
if (v_isShared_2476_ == 0)
{
v___x_2478_ = v___x_2475_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v_a_2473_);
v___x_2478_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
return v___x_2478_;
}
}
}
}
else
{
lean_object* v_a_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2488_; 
lean_dec(v___y_2355_);
lean_dec_ref(v___y_2354_);
lean_dec(v___y_2353_);
lean_dec_ref(v___y_2352_);
lean_dec(v_n_2350_);
lean_dec_ref(v_e_2349_);
lean_dec(v_mvarId_2347_);
v_a_2481_ = lean_ctor_get(v___x_2357_, 0);
v_isSharedCheck_2488_ = !lean_is_exclusive(v___x_2357_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2483_ = v___x_2357_;
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_a_2481_);
lean_dec(v___x_2357_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v___x_2486_; 
if (v_isShared_2484_ == 0)
{
v___x_2486_ = v___x_2483_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_a_2481_);
v___x_2486_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
return v___x_2486_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN___lam__0___boxed(lean_object* v_mvarId_2489_, lean_object* v___x_2490_, lean_object* v_e_2491_, lean_object* v_n_2492_, lean_object* v_useApproxDefEq_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_){
_start:
{
uint8_t v_useApproxDefEq_boxed_2499_; lean_object* v_res_2500_; 
v_useApproxDefEq_boxed_2499_ = lean_unbox(v_useApproxDefEq_2493_);
v_res_2500_ = l_Lean_MVarId_applyN___lam__0(v_mvarId_2489_, v___x_2490_, v_e_2491_, v_n_2492_, v_useApproxDefEq_boxed_2499_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
return v_res_2500_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN(lean_object* v_mvarId_2501_, lean_object* v_e_2502_, lean_object* v_n_2503_, uint8_t v_useApproxDefEq_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_){
_start:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___f_2512_; lean_object* v___x_2513_; 
v___x_2510_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1));
v___x_2511_ = lean_box(v_useApproxDefEq_2504_);
lean_inc(v_mvarId_2501_);
v___f_2512_ = lean_alloc_closure((void*)(l_Lean_MVarId_applyN___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2512_, 0, v_mvarId_2501_);
lean_closure_set(v___f_2512_, 1, v___x_2510_);
lean_closure_set(v___f_2512_, 2, v_e_2502_);
lean_closure_set(v___f_2512_, 3, v_n_2503_);
lean_closure_set(v___f_2512_, 4, v___x_2511_);
v___x_2513_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2501_, v___f_2512_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_);
return v___x_2513_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyN___boxed(lean_object* v_mvarId_2514_, lean_object* v_e_2515_, lean_object* v_n_2516_, lean_object* v_useApproxDefEq_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_){
_start:
{
uint8_t v_useApproxDefEq_boxed_2523_; lean_object* v_res_2524_; 
v_useApproxDefEq_boxed_2523_ = lean_unbox(v_useApproxDefEq_2517_);
v_res_2524_ = l_Lean_MVarId_applyN(v_mvarId_2514_, v_e_2515_, v_n_2516_, v_useApproxDefEq_boxed_2523_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_);
lean_dec(v_a_2521_);
lean_dec_ref(v_a_2520_);
lean_dec(v_a_2519_);
lean_dec_ref(v_a_2518_);
return v_res_2524_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1(lean_object* v_00_u03b1_2525_, lean_object* v_msg_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_){
_start:
{
lean_object* v___x_2532_; 
v___x_2532_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v_msg_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_);
return v___x_2532_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___boxed(lean_object* v_00_u03b1_2533_, lean_object* v_msg_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_){
_start:
{
lean_object* v_res_2540_; 
v_res_2540_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1(v_00_u03b1_2533_, v_msg_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
lean_dec(v___y_2538_);
lean_dec_ref(v___y_2537_);
lean_dec(v___y_2536_);
lean_dec_ref(v___y_2535_);
return v_res_2540_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6(void){
_start:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; 
v___x_2551_ = lean_box(0);
v___x_2552_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__5));
v___x_2553_ = l_Lean_mkConst(v___x_2552_, v___x_2551_);
return v___x_2553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(lean_object* v_tag_2554_, lean_object* v_type_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_){
_start:
{
lean_object* v___x_2562_; 
lean_inc(v_a_2560_);
lean_inc_ref(v_a_2559_);
lean_inc(v_a_2558_);
lean_inc_ref(v_a_2557_);
v___x_2562_ = lean_whnf(v_type_2555_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_);
if (lean_obj_tag(v___x_2562_) == 0)
{
lean_object* v_a_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; uint8_t v___x_2566_; 
v_a_2563_ = lean_ctor_get(v___x_2562_, 0);
lean_inc(v_a_2563_);
lean_dec_ref_known(v___x_2562_, 1);
v___x_2564_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__1));
v___x_2565_ = lean_unsigned_to_nat(2u);
v___x_2566_ = l_Lean_Expr_isAppOfArity(v_a_2563_, v___x_2564_, v___x_2565_);
if (v___x_2566_ == 0)
{
lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2567_ = lean_st_ref_get(v_a_2556_);
v___x_2568_ = lean_array_get_size(v___x_2567_);
lean_dec(v___x_2567_);
v___x_2569_ = lean_unsigned_to_nat(1u);
v___x_2570_ = lean_nat_add(v___x_2568_, v___x_2569_);
v___x_2571_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__3));
v___x_2572_ = lean_name_append_index_after(v___x_2571_, v___x_2570_);
v___x_2573_ = l_Lean_Name_append(v_tag_2554_, v___x_2572_);
v___x_2574_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_2563_, v___x_2573_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_);
if (lean_obj_tag(v___x_2574_) == 0)
{
lean_object* v_a_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2586_; 
v_a_2575_ = lean_ctor_get(v___x_2574_, 0);
v_isSharedCheck_2586_ = !lean_is_exclusive(v___x_2574_);
if (v_isSharedCheck_2586_ == 0)
{
v___x_2577_ = v___x_2574_;
v_isShared_2578_ = v_isSharedCheck_2586_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_a_2575_);
lean_dec(v___x_2574_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2586_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2584_; 
v___x_2579_ = lean_st_ref_take(v_a_2556_);
v___x_2580_ = l_Lean_Expr_mvarId_x21(v_a_2575_);
v___x_2581_ = lean_array_push(v___x_2579_, v___x_2580_);
v___x_2582_ = lean_st_ref_set(v_a_2556_, v___x_2581_);
if (v_isShared_2578_ == 0)
{
v___x_2584_ = v___x_2577_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v_a_2575_);
v___x_2584_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
return v___x_2584_;
}
}
}
else
{
return v___x_2574_;
}
}
else
{
lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; 
v___x_2587_ = l_Lean_Expr_appFn_x21(v_a_2563_);
v___x_2588_ = l_Lean_Expr_appArg_x21(v___x_2587_);
lean_dec_ref(v___x_2587_);
lean_inc_ref(v___x_2588_);
lean_inc(v_tag_2554_);
v___x_2589_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_tag_2554_, v___x_2588_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_);
if (lean_obj_tag(v___x_2589_) == 0)
{
lean_object* v_a_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; 
v_a_2590_ = lean_ctor_get(v___x_2589_, 0);
lean_inc(v_a_2590_);
lean_dec_ref_known(v___x_2589_, 1);
v___x_2591_ = l_Lean_Expr_appArg_x21(v_a_2563_);
lean_dec(v_a_2563_);
lean_inc_ref(v___x_2591_);
v___x_2592_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_tag_2554_, v___x_2591_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_object* v_a_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2602_; 
v_a_2593_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2602_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2595_ = v___x_2592_;
v_isShared_2596_ = v_isSharedCheck_2602_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_a_2593_);
lean_dec(v___x_2592_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2602_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2600_; 
v___x_2597_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6, &l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6);
v___x_2598_ = l_Lean_mkApp4(v___x_2597_, v___x_2588_, v___x_2591_, v_a_2590_, v_a_2593_);
if (v_isShared_2596_ == 0)
{
lean_ctor_set(v___x_2595_, 0, v___x_2598_);
v___x_2600_ = v___x_2595_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v___x_2598_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
}
else
{
lean_dec_ref(v___x_2591_);
lean_dec(v_a_2590_);
lean_dec_ref(v___x_2588_);
return v___x_2592_;
}
}
else
{
lean_dec_ref(v___x_2588_);
lean_dec(v_a_2563_);
lean_dec(v_tag_2554_);
return v___x_2589_;
}
}
}
else
{
lean_dec(v_tag_2554_);
return v___x_2562_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___boxed(lean_object* v_tag_2603_, lean_object* v_type_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_){
_start:
{
lean_object* v_res_2611_; 
v_res_2611_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_tag_2603_, v_type_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_);
lean_dec(v_a_2609_);
lean_dec_ref(v_a_2608_);
lean_dec(v_a_2607_);
lean_dec_ref(v_a_2606_);
lean_dec(v_a_2605_);
return v_res_2611_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore___lam__0(lean_object* v_mvarId_2612_, lean_object* v___x_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_){
_start:
{
lean_object* v___x_2619_; 
lean_inc(v_mvarId_2612_);
v___x_2619_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2612_, v___x_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_);
if (lean_obj_tag(v___x_2619_) == 0)
{
lean_object* v___x_2620_; 
lean_dec_ref_known(v___x_2619_, 1);
lean_inc(v_mvarId_2612_);
v___x_2620_ = l_Lean_MVarId_getType_x27(v_mvarId_2612_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_);
if (lean_obj_tag(v___x_2620_) == 0)
{
lean_object* v_a_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2666_; 
v_a_2621_ = lean_ctor_get(v___x_2620_, 0);
v_isSharedCheck_2666_ = !lean_is_exclusive(v___x_2620_);
if (v_isSharedCheck_2666_ == 0)
{
v___x_2623_ = v___x_2620_;
v_isShared_2624_ = v_isSharedCheck_2666_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_a_2621_);
lean_dec(v___x_2620_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2666_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2625_; lean_object* v___x_2626_; uint8_t v___x_2627_; 
v___x_2625_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__1));
v___x_2626_ = lean_unsigned_to_nat(2u);
v___x_2627_ = l_Lean_Expr_isAppOfArity(v_a_2621_, v___x_2625_, v___x_2626_);
if (v___x_2627_ == 0)
{
lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2631_; 
lean_dec(v_a_2621_);
v___x_2628_ = lean_box(0);
v___x_2629_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2629_, 0, v_mvarId_2612_);
lean_ctor_set(v___x_2629_, 1, v___x_2628_);
if (v_isShared_2624_ == 0)
{
lean_ctor_set(v___x_2623_, 0, v___x_2629_);
v___x_2631_ = v___x_2623_;
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
else
{
lean_object* v___x_2633_; 
lean_del_object(v___x_2623_);
lean_inc(v_mvarId_2612_);
v___x_2633_ = l_Lean_MVarId_getTag(v_mvarId_2612_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_);
if (lean_obj_tag(v___x_2633_) == 0)
{
lean_object* v_a_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; 
v_a_2634_ = lean_ctor_get(v___x_2633_, 0);
lean_inc(v_a_2634_);
lean_dec_ref_known(v___x_2633_, 1);
v___x_2635_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__0));
v___x_2636_ = lean_st_mk_ref(v___x_2635_);
v___x_2637_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(v_a_2634_, v_a_2621_, v___x_2636_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_);
if (lean_obj_tag(v___x_2637_) == 0)
{
lean_object* v_a_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2648_; 
v_a_2638_ = lean_ctor_get(v___x_2637_, 0);
lean_inc(v_a_2638_);
lean_dec_ref_known(v___x_2637_, 1);
v___x_2639_ = lean_st_ref_get(v___x_2636_);
lean_dec(v___x_2636_);
v___x_2640_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2612_, v_a_2638_, v___y_2615_);
v_isSharedCheck_2648_ = !lean_is_exclusive(v___x_2640_);
if (v_isSharedCheck_2648_ == 0)
{
lean_object* v_unused_2649_; 
v_unused_2649_ = lean_ctor_get(v___x_2640_, 0);
lean_dec(v_unused_2649_);
v___x_2642_ = v___x_2640_;
v_isShared_2643_ = v_isSharedCheck_2648_;
goto v_resetjp_2641_;
}
else
{
lean_dec(v___x_2640_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2648_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v___x_2644_; lean_object* v___x_2646_; 
v___x_2644_ = lean_array_to_list(v___x_2639_);
if (v_isShared_2643_ == 0)
{
lean_ctor_set(v___x_2642_, 0, v___x_2644_);
v___x_2646_ = v___x_2642_;
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
lean_object* v_a_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2657_; 
lean_dec(v___x_2636_);
lean_dec(v_mvarId_2612_);
v_a_2650_ = lean_ctor_get(v___x_2637_, 0);
v_isSharedCheck_2657_ = !lean_is_exclusive(v___x_2637_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2652_ = v___x_2637_;
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_a_2650_);
lean_dec(v___x_2637_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
lean_object* v___x_2655_; 
if (v_isShared_2653_ == 0)
{
v___x_2655_ = v___x_2652_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v_a_2650_);
v___x_2655_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
return v___x_2655_;
}
}
}
}
else
{
lean_object* v_a_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2665_; 
lean_dec(v_a_2621_);
lean_dec(v_mvarId_2612_);
v_a_2658_ = lean_ctor_get(v___x_2633_, 0);
v_isSharedCheck_2665_ = !lean_is_exclusive(v___x_2633_);
if (v_isSharedCheck_2665_ == 0)
{
v___x_2660_ = v___x_2633_;
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_a_2658_);
lean_dec(v___x_2633_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2663_; 
if (v_isShared_2661_ == 0)
{
v___x_2663_ = v___x_2660_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v_a_2658_);
v___x_2663_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
return v___x_2663_;
}
}
}
}
}
}
else
{
lean_object* v_a_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2674_; 
lean_dec(v_mvarId_2612_);
v_a_2667_ = lean_ctor_get(v___x_2620_, 0);
v_isSharedCheck_2674_ = !lean_is_exclusive(v___x_2620_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2669_ = v___x_2620_;
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_a_2667_);
lean_dec(v___x_2620_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2672_; 
if (v_isShared_2670_ == 0)
{
v___x_2672_ = v___x_2669_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v_a_2667_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
}
}
else
{
lean_object* v_a_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2682_; 
lean_dec(v_mvarId_2612_);
v_a_2675_ = lean_ctor_get(v___x_2619_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2619_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2677_ = v___x_2619_;
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_a_2675_);
lean_dec(v___x_2619_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2680_; 
if (v_isShared_2678_ == 0)
{
v___x_2680_ = v___x_2677_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_a_2675_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore___lam__0___boxed(lean_object* v_mvarId_2683_, lean_object* v___x_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_){
_start:
{
lean_object* v_res_2690_; 
v_res_2690_ = l_Lean_MVarId_splitAndCore___lam__0(v_mvarId_2683_, v___x_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_);
lean_dec(v___y_2688_);
lean_dec_ref(v___y_2687_);
lean_dec(v___y_2686_);
lean_dec_ref(v___y_2685_);
return v_res_2690_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore(lean_object* v_mvarId_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_){
_start:
{
lean_object* v___x_2700_; lean_object* v___f_2701_; lean_object* v___x_2702_; 
v___x_2700_ = ((lean_object*)(l_Lean_MVarId_splitAndCore___closed__1));
lean_inc(v_mvarId_2694_);
v___f_2701_ = lean_alloc_closure((void*)(l_Lean_MVarId_splitAndCore___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2701_, 0, v_mvarId_2694_);
lean_closure_set(v___f_2701_, 1, v___x_2700_);
v___x_2702_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2694_, v___f_2701_, v_a_2695_, v_a_2696_, v_a_2697_, v_a_2698_);
return v___x_2702_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAndCore___boxed(lean_object* v_mvarId_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_){
_start:
{
lean_object* v_res_2709_; 
v_res_2709_ = l_Lean_MVarId_splitAndCore(v_mvarId_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_);
lean_dec(v_a_2707_);
lean_dec_ref(v_a_2706_);
lean_dec(v_a_2705_);
lean_dec_ref(v_a_2704_);
return v_res_2709_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAnd(lean_object* v_mvarId_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_){
_start:
{
lean_object* v___x_2716_; 
v___x_2716_ = l_Lean_MVarId_splitAndCore(v_mvarId_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_);
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_splitAnd___boxed(lean_object* v_mvarId_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_){
_start:
{
lean_object* v_res_2723_; 
v_res_2723_ = l_Lean_MVarId_splitAnd(v_mvarId_2717_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_);
lean_dec(v_a_2721_);
lean_dec_ref(v_a_2720_);
lean_dec(v_a_2719_);
lean_dec_ref(v_a_2718_);
return v_res_2723_;
}
}
static lean_object* _init_l_Lean_MVarId_exfalso___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; 
v___x_2727_ = lean_box(0);
v___x_2728_ = ((lean_object*)(l_Lean_MVarId_exfalso___lam__0___closed__1));
v___x_2729_ = l_Lean_mkConst(v___x_2728_, v___x_2727_);
return v___x_2729_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso___lam__0(lean_object* v_mvarId_2734_, lean_object* v___x_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_){
_start:
{
lean_object* v___x_2741_; 
lean_inc(v_mvarId_2734_);
v___x_2741_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_2734_, v___x_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
if (lean_obj_tag(v___x_2741_) == 0)
{
lean_object* v___x_2742_; 
lean_dec_ref_known(v___x_2741_, 1);
lean_inc(v_mvarId_2734_);
v___x_2742_ = l_Lean_MVarId_getType(v_mvarId_2734_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
if (lean_obj_tag(v___x_2742_) == 0)
{
lean_object* v_a_2743_; lean_object* v___x_2744_; lean_object* v_a_2745_; lean_object* v___x_2746_; 
v_a_2743_ = lean_ctor_get(v___x_2742_, 0);
lean_inc(v_a_2743_);
lean_dec_ref_known(v___x_2742_, 1);
v___x_2744_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_a_2743_, v___y_2737_);
v_a_2745_ = lean_ctor_get(v___x_2744_, 0);
lean_inc_n(v_a_2745_, 2);
lean_dec_ref(v___x_2744_);
v___x_2746_ = l_Lean_Meta_getLevel(v_a_2745_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
if (lean_obj_tag(v___x_2746_) == 0)
{
lean_object* v_a_2747_; lean_object* v___x_2748_; 
v_a_2747_ = lean_ctor_get(v___x_2746_, 0);
lean_inc(v_a_2747_);
lean_dec_ref_known(v___x_2746_, 1);
lean_inc(v_mvarId_2734_);
v___x_2748_ = l_Lean_MVarId_getTag(v_mvarId_2734_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
if (lean_obj_tag(v___x_2748_) == 0)
{
lean_object* v_a_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; 
v_a_2749_ = lean_ctor_get(v___x_2748_, 0);
lean_inc(v_a_2749_);
lean_dec_ref_known(v___x_2748_, 1);
v___x_2750_ = lean_box(0);
v___x_2751_ = lean_obj_once(&l_Lean_MVarId_exfalso___lam__0___closed__2, &l_Lean_MVarId_exfalso___lam__0___closed__2_once, _init_l_Lean_MVarId_exfalso___lam__0___closed__2);
v___x_2752_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_2751_, v_a_2749_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
if (lean_obj_tag(v___x_2752_) == 0)
{
lean_object* v_a_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2766_; 
v_a_2753_ = lean_ctor_get(v___x_2752_, 0);
lean_inc_n(v_a_2753_, 2);
lean_dec_ref_known(v___x_2752_, 1);
v___x_2754_ = ((lean_object*)(l_Lean_MVarId_exfalso___lam__0___closed__4));
v___x_2755_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2755_, 0, v_a_2747_);
lean_ctor_set(v___x_2755_, 1, v___x_2750_);
v___x_2756_ = l_Lean_mkConst(v___x_2754_, v___x_2755_);
v___x_2757_ = l_Lean_mkAppB(v___x_2756_, v_a_2745_, v_a_2753_);
v___x_2758_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_2734_, v___x_2757_, v___y_2737_);
v_isSharedCheck_2766_ = !lean_is_exclusive(v___x_2758_);
if (v_isSharedCheck_2766_ == 0)
{
lean_object* v_unused_2767_; 
v_unused_2767_ = lean_ctor_get(v___x_2758_, 0);
lean_dec(v_unused_2767_);
v___x_2760_ = v___x_2758_;
v_isShared_2761_ = v_isSharedCheck_2766_;
goto v_resetjp_2759_;
}
else
{
lean_dec(v___x_2758_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2766_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2762_; lean_object* v___x_2764_; 
v___x_2762_ = l_Lean_Expr_mvarId_x21(v_a_2753_);
lean_dec(v_a_2753_);
if (v_isShared_2761_ == 0)
{
lean_ctor_set(v___x_2760_, 0, v___x_2762_);
v___x_2764_ = v___x_2760_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v___x_2762_);
v___x_2764_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
return v___x_2764_;
}
}
}
else
{
lean_object* v_a_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2775_; 
lean_dec(v_a_2747_);
lean_dec(v_a_2745_);
lean_dec(v_mvarId_2734_);
v_a_2768_ = lean_ctor_get(v___x_2752_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v___x_2752_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2770_ = v___x_2752_;
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_a_2768_);
lean_dec(v___x_2752_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2773_; 
if (v_isShared_2771_ == 0)
{
v___x_2773_ = v___x_2770_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_a_2768_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
return v___x_2773_;
}
}
}
}
else
{
lean_object* v_a_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2783_; 
lean_dec(v_a_2747_);
lean_dec(v_a_2745_);
lean_dec(v_mvarId_2734_);
v_a_2776_ = lean_ctor_get(v___x_2748_, 0);
v_isSharedCheck_2783_ = !lean_is_exclusive(v___x_2748_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2778_ = v___x_2748_;
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_a_2776_);
lean_dec(v___x_2748_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v___x_2781_; 
if (v_isShared_2779_ == 0)
{
v___x_2781_ = v___x_2778_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_a_2776_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
return v___x_2781_;
}
}
}
}
else
{
lean_object* v_a_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2791_; 
lean_dec(v_a_2745_);
lean_dec(v_mvarId_2734_);
v_a_2784_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2786_ = v___x_2746_;
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_a_2784_);
lean_dec(v___x_2746_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v___x_2789_; 
if (v_isShared_2787_ == 0)
{
v___x_2789_ = v___x_2786_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_a_2784_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
}
}
else
{
lean_object* v_a_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2799_; 
lean_dec(v_mvarId_2734_);
v_a_2792_ = lean_ctor_get(v___x_2742_, 0);
v_isSharedCheck_2799_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2794_ = v___x_2742_;
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_a_2792_);
lean_dec(v___x_2742_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v___x_2797_; 
if (v_isShared_2795_ == 0)
{
v___x_2797_ = v___x_2794_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_a_2792_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
return v___x_2797_;
}
}
}
}
else
{
lean_object* v_a_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2807_; 
lean_dec(v_mvarId_2734_);
v_a_2800_ = lean_ctor_get(v___x_2741_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2741_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2802_ = v___x_2741_;
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_a_2800_);
lean_dec(v___x_2741_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2805_; 
if (v_isShared_2803_ == 0)
{
v___x_2805_ = v___x_2802_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_a_2800_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso___lam__0___boxed(lean_object* v_mvarId_2808_, lean_object* v___x_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_){
_start:
{
lean_object* v_res_2815_; 
v_res_2815_ = l_Lean_MVarId_exfalso___lam__0(v_mvarId_2808_, v___x_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
lean_dec(v___y_2813_);
lean_dec_ref(v___y_2812_);
lean_dec(v___y_2811_);
lean_dec_ref(v___y_2810_);
return v_res_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso(lean_object* v_mvarId_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_){
_start:
{
lean_object* v___x_2825_; lean_object* v___f_2826_; lean_object* v___x_2827_; 
v___x_2825_ = ((lean_object*)(l_Lean_MVarId_exfalso___closed__1));
lean_inc(v_mvarId_2819_);
v___f_2826_ = lean_alloc_closure((void*)(l_Lean_MVarId_exfalso___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2826_, 0, v_mvarId_2819_);
lean_closure_set(v___f_2826_, 1, v___x_2825_);
v___x_2827_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_2819_, v___f_2826_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_);
return v___x_2827_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_exfalso___boxed(lean_object* v_mvarId_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_){
_start:
{
lean_object* v_res_2834_; 
v_res_2834_ = l_Lean_MVarId_exfalso(v_mvarId_2828_, v_a_2829_, v_a_2830_, v_a_2831_, v_a_2832_);
lean_dec(v_a_2832_);
lean_dec_ref(v_a_2831_);
lean_dec(v_a_2830_);
lean_dec_ref(v_a_2829_);
return v_res_2834_;
}
}
static lean_object* _init_l_Lean_MVarId_nthConstructor___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2838_; lean_object* v___x_2839_; 
v___x_2838_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__1));
v___x_2839_ = l_Lean_MessageData_ofFormat(v___x_2838_);
return v___x_2839_;
}
}
static lean_object* _init_l_Lean_MVarId_nthConstructor___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2840_ = lean_obj_once(&l_Lean_MVarId_nthConstructor___lam__0___closed__2, &l_Lean_MVarId_nthConstructor___lam__0___closed__2_once, _init_l_Lean_MVarId_nthConstructor___lam__0___closed__2);
v___x_2841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2840_);
return v___x_2841_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___lam__0(lean_object* v_goal_2846_, lean_object* v_name_2847_, lean_object* v_idx_2848_, lean_object* v_expected_x3f_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_){
_start:
{
lean_object* v___y_2856_; lean_object* v___y_2857_; lean_object* v___y_2858_; lean_object* v___y_2859_; lean_object* v___x_2862_; 
lean_inc(v_name_2847_);
lean_inc(v_goal_2846_);
v___x_2862_ = l_Lean_MVarId_checkNotAssigned(v_goal_2846_, v_name_2847_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_);
if (lean_obj_tag(v___x_2862_) == 0)
{
lean_object* v___x_2863_; 
lean_dec_ref_known(v___x_2862_, 1);
lean_inc(v_goal_2846_);
v___x_2863_ = l_Lean_MVarId_getType_x27(v_goal_2846_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_);
if (lean_obj_tag(v___x_2863_) == 0)
{
lean_object* v_a_2864_; lean_object* v___x_2865_; 
v_a_2864_ = lean_ctor_get(v___x_2863_, 0);
lean_inc(v_a_2864_);
lean_dec_ref_known(v___x_2863_, 1);
v___x_2865_ = l_Lean_Expr_getAppFn(v_a_2864_);
lean_dec(v_a_2864_);
if (lean_obj_tag(v___x_2865_) == 4)
{
lean_object* v_declName_2866_; lean_object* v_us_2867_; lean_object* v___x_2868_; lean_object* v_env_2869_; uint8_t v___x_2870_; lean_object* v___x_2871_; 
v_declName_2866_ = lean_ctor_get(v___x_2865_, 0);
lean_inc(v_declName_2866_);
v_us_2867_ = lean_ctor_get(v___x_2865_, 1);
lean_inc(v_us_2867_);
lean_dec_ref_known(v___x_2865_, 2);
v___x_2868_ = lean_st_ref_get(v___y_2853_);
v_env_2869_ = lean_ctor_get(v___x_2868_, 0);
lean_inc_ref(v_env_2869_);
lean_dec(v___x_2868_);
v___x_2870_ = 0;
v___x_2871_ = l_Lean_Environment_find_x3f(v_env_2869_, v_declName_2866_, v___x_2870_);
if (lean_obj_tag(v___x_2871_) == 0)
{
lean_dec(v_us_2867_);
lean_dec(v_expected_x3f_2849_);
lean_dec(v_idx_2848_);
v___y_2856_ = v___y_2850_;
v___y_2857_ = v___y_2851_;
v___y_2858_ = v___y_2852_;
v___y_2859_ = v___y_2853_;
goto v___jp_2855_;
}
else
{
lean_object* v_val_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2942_; 
v_val_2872_ = lean_ctor_get(v___x_2871_, 0);
v_isSharedCheck_2942_ = !lean_is_exclusive(v___x_2871_);
if (v_isSharedCheck_2942_ == 0)
{
v___x_2874_ = v___x_2871_;
v_isShared_2875_ = v_isSharedCheck_2942_;
goto v_resetjp_2873_;
}
else
{
lean_inc(v_val_2872_);
lean_dec(v___x_2871_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2942_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
if (lean_obj_tag(v_val_2872_) == 5)
{
lean_object* v_val_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2941_; 
v_val_2876_ = lean_ctor_get(v_val_2872_, 0);
v_isSharedCheck_2941_ = !lean_is_exclusive(v_val_2872_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2878_ = v_val_2872_;
v_isShared_2879_ = v_isSharedCheck_2941_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_val_2876_);
lean_dec(v_val_2872_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2941_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___y_2881_; lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; 
if (lean_obj_tag(v_expected_x3f_2849_) == 1)
{
lean_object* v_val_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2940_; 
v_val_2911_ = lean_ctor_get(v_expected_x3f_2849_, 0);
v_isSharedCheck_2940_ = !lean_is_exclusive(v_expected_x3f_2849_);
if (v_isSharedCheck_2940_ == 0)
{
v___x_2913_ = v_expected_x3f_2849_;
v_isShared_2914_ = v_isSharedCheck_2940_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_val_2911_);
lean_dec(v_expected_x3f_2849_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2940_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v_ctors_2915_; lean_object* v___x_2916_; uint8_t v___x_2917_; 
v_ctors_2915_ = lean_ctor_get(v_val_2876_, 4);
v___x_2916_ = l_List_lengthTR___redArg(v_ctors_2915_);
v___x_2917_ = lean_nat_dec_eq(v___x_2916_, v_val_2911_);
lean_dec(v___x_2916_);
if (v___x_2917_ == 0)
{
uint8_t v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2929_; 
v___x_2918_ = 1;
lean_inc(v_name_2847_);
v___x_2919_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2847_, v___x_2918_);
v___x_2920_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__7));
v___x_2921_ = lean_string_append(v___x_2919_, v___x_2920_);
v___x_2922_ = l_Nat_reprFast(v_val_2911_);
v___x_2923_ = lean_string_append(v___x_2921_, v___x_2922_);
lean_dec_ref(v___x_2922_);
v___x_2924_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__6));
v___x_2925_ = lean_string_append(v___x_2923_, v___x_2924_);
v___x_2926_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2926_, 0, v___x_2925_);
v___x_2927_ = l_Lean_MessageData_ofFormat(v___x_2926_);
if (v_isShared_2914_ == 0)
{
lean_ctor_set(v___x_2913_, 0, v___x_2927_);
v___x_2929_ = v___x_2913_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v___x_2927_);
v___x_2929_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
lean_object* v___x_2930_; 
lean_inc(v_goal_2846_);
lean_inc(v_name_2847_);
v___x_2930_ = l_Lean_Meta_throwTacticEx___redArg(v_name_2847_, v_goal_2846_, v___x_2929_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_);
if (lean_obj_tag(v___x_2930_) == 0)
{
lean_dec_ref_known(v___x_2930_, 1);
v___y_2881_ = v___y_2850_;
v___y_2882_ = v___y_2851_;
v___y_2883_ = v___y_2852_;
v___y_2884_ = v___y_2853_;
goto v___jp_2880_;
}
else
{
lean_object* v_a_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2938_; 
lean_del_object(v___x_2878_);
lean_dec_ref(v_val_2876_);
lean_del_object(v___x_2874_);
lean_dec(v_us_2867_);
lean_dec(v_idx_2848_);
lean_dec(v_name_2847_);
lean_dec(v_goal_2846_);
v_a_2931_ = lean_ctor_get(v___x_2930_, 0);
v_isSharedCheck_2938_ = !lean_is_exclusive(v___x_2930_);
if (v_isSharedCheck_2938_ == 0)
{
v___x_2933_ = v___x_2930_;
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_a_2931_);
lean_dec(v___x_2930_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v___x_2936_; 
if (v_isShared_2934_ == 0)
{
v___x_2936_ = v___x_2933_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v_a_2931_);
v___x_2936_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
return v___x_2936_;
}
}
}
}
}
else
{
lean_del_object(v___x_2913_);
lean_dec(v_val_2911_);
v___y_2881_ = v___y_2850_;
v___y_2882_ = v___y_2851_;
v___y_2883_ = v___y_2852_;
v___y_2884_ = v___y_2853_;
goto v___jp_2880_;
}
}
}
else
{
lean_dec(v_expected_x3f_2849_);
v___y_2881_ = v___y_2850_;
v___y_2882_ = v___y_2851_;
v___y_2883_ = v___y_2852_;
v___y_2884_ = v___y_2853_;
goto v___jp_2880_;
}
v___jp_2880_:
{
lean_object* v_ctors_2885_; lean_object* v___x_2886_; uint8_t v___x_2887_; 
v_ctors_2885_ = lean_ctor_get(v_val_2876_, 4);
lean_inc(v_ctors_2885_);
lean_dec_ref(v_val_2876_);
v___x_2886_ = l_List_lengthTR___redArg(v_ctors_2885_);
v___x_2887_ = lean_nat_dec_lt(v_idx_2848_, v___x_2886_);
if (v___x_2887_ == 0)
{
lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2898_; 
lean_dec(v_ctors_2885_);
lean_dec(v_us_2867_);
v___x_2888_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__4));
v___x_2889_ = l_Nat_reprFast(v_idx_2848_);
v___x_2890_ = lean_string_append(v___x_2888_, v___x_2889_);
lean_dec_ref(v___x_2889_);
v___x_2891_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__5));
v___x_2892_ = lean_string_append(v___x_2890_, v___x_2891_);
v___x_2893_ = l_Nat_reprFast(v___x_2886_);
v___x_2894_ = lean_string_append(v___x_2892_, v___x_2893_);
lean_dec_ref(v___x_2893_);
v___x_2895_ = ((lean_object*)(l_Lean_MVarId_nthConstructor___lam__0___closed__6));
v___x_2896_ = lean_string_append(v___x_2894_, v___x_2895_);
if (v_isShared_2879_ == 0)
{
lean_ctor_set_tag(v___x_2878_, 3);
lean_ctor_set(v___x_2878_, 0, v___x_2896_);
v___x_2898_ = v___x_2878_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v___x_2896_);
v___x_2898_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
lean_object* v___x_2899_; lean_object* v___x_2901_; 
v___x_2899_ = l_Lean_MessageData_ofFormat(v___x_2898_);
if (v_isShared_2875_ == 0)
{
lean_ctor_set(v___x_2874_, 0, v___x_2899_);
v___x_2901_ = v___x_2874_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v___x_2899_);
v___x_2901_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
lean_object* v___x_2902_; 
v___x_2902_ = l_Lean_Meta_throwTacticEx___redArg(v_name_2847_, v_goal_2846_, v___x_2901_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_);
return v___x_2902_;
}
}
}
else
{
lean_object* v___x_2905_; lean_object* v___x_2906_; uint8_t v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; 
lean_dec(v___x_2886_);
lean_del_object(v___x_2878_);
lean_del_object(v___x_2874_);
lean_dec(v_name_2847_);
v___x_2905_ = l_List_get___redArg(v_ctors_2885_, v_idx_2848_);
lean_dec(v_ctors_2885_);
v___x_2906_ = l_Lean_mkConst(v___x_2905_, v_us_2867_);
v___x_2907_ = 0;
v___x_2908_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_2908_, 0, v___x_2907_);
lean_ctor_set_uint8(v___x_2908_, 1, v___x_2887_);
lean_ctor_set_uint8(v___x_2908_, 2, v___x_2870_);
lean_ctor_set_uint8(v___x_2908_, 3, v___x_2887_);
v___x_2909_ = lean_box(0);
v___x_2910_ = l_Lean_MVarId_apply(v_goal_2846_, v___x_2906_, v___x_2908_, v___x_2909_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_);
return v___x_2910_;
}
}
}
}
else
{
lean_del_object(v___x_2874_);
lean_dec(v_val_2872_);
lean_dec(v_us_2867_);
lean_dec(v_expected_x3f_2849_);
lean_dec(v_idx_2848_);
v___y_2856_ = v___y_2850_;
v___y_2857_ = v___y_2851_;
v___y_2858_ = v___y_2852_;
v___y_2859_ = v___y_2853_;
goto v___jp_2855_;
}
}
}
}
else
{
lean_dec_ref(v___x_2865_);
lean_dec(v_expected_x3f_2849_);
lean_dec(v_idx_2848_);
v___y_2856_ = v___y_2850_;
v___y_2857_ = v___y_2851_;
v___y_2858_ = v___y_2852_;
v___y_2859_ = v___y_2853_;
goto v___jp_2855_;
}
}
else
{
lean_object* v_a_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2950_; 
lean_dec(v_expected_x3f_2849_);
lean_dec(v_idx_2848_);
lean_dec(v_name_2847_);
lean_dec(v_goal_2846_);
v_a_2943_ = lean_ctor_get(v___x_2863_, 0);
v_isSharedCheck_2950_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_2950_ == 0)
{
v___x_2945_ = v___x_2863_;
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_a_2943_);
lean_dec(v___x_2863_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2948_; 
if (v_isShared_2946_ == 0)
{
v___x_2948_ = v___x_2945_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v_a_2943_);
v___x_2948_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
return v___x_2948_;
}
}
}
}
else
{
lean_object* v_a_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_2958_; 
lean_dec(v_expected_x3f_2849_);
lean_dec(v_idx_2848_);
lean_dec(v_name_2847_);
lean_dec(v_goal_2846_);
v_a_2951_ = lean_ctor_get(v___x_2862_, 0);
v_isSharedCheck_2958_ = !lean_is_exclusive(v___x_2862_);
if (v_isSharedCheck_2958_ == 0)
{
v___x_2953_ = v___x_2862_;
v_isShared_2954_ = v_isSharedCheck_2958_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_a_2951_);
lean_dec(v___x_2862_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_2958_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v___x_2956_; 
if (v_isShared_2954_ == 0)
{
v___x_2956_ = v___x_2953_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v_a_2951_);
v___x_2956_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
return v___x_2956_;
}
}
}
v___jp_2855_:
{
lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2860_ = lean_obj_once(&l_Lean_MVarId_nthConstructor___lam__0___closed__3, &l_Lean_MVarId_nthConstructor___lam__0___closed__3_once, _init_l_Lean_MVarId_nthConstructor___lam__0___closed__3);
v___x_2861_ = l_Lean_Meta_throwTacticEx___redArg(v_name_2847_, v_goal_2846_, v___x_2860_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
return v___x_2861_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___lam__0___boxed(lean_object* v_goal_2959_, lean_object* v_name_2960_, lean_object* v_idx_2961_, lean_object* v_expected_x3f_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_){
_start:
{
lean_object* v_res_2968_; 
v_res_2968_ = l_Lean_MVarId_nthConstructor___lam__0(v_goal_2959_, v_name_2960_, v_idx_2961_, v_expected_x3f_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec(v___y_2964_);
lean_dec_ref(v___y_2963_);
return v_res_2968_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor(lean_object* v_name_2969_, lean_object* v_idx_2970_, lean_object* v_expected_x3f_2971_, lean_object* v_goal_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_){
_start:
{
lean_object* v___f_2978_; lean_object* v___x_2979_; 
lean_inc(v_goal_2972_);
v___f_2978_ = lean_alloc_closure((void*)(l_Lean_MVarId_nthConstructor___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2978_, 0, v_goal_2972_);
lean_closure_set(v___f_2978_, 1, v_name_2969_);
lean_closure_set(v___f_2978_, 2, v_idx_2970_);
lean_closure_set(v___f_2978_, 3, v_expected_x3f_2971_);
v___x_2979_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_goal_2972_, v___f_2978_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_);
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_nthConstructor___boxed(lean_object* v_name_2980_, lean_object* v_idx_2981_, lean_object* v_expected_x3f_2982_, lean_object* v_goal_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_){
_start:
{
lean_object* v_res_2989_; 
v_res_2989_ = l_Lean_MVarId_nthConstructor(v_name_2980_, v_idx_2981_, v_expected_x3f_2982_, v_goal_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_);
lean_dec(v_a_2987_);
lean_dec_ref(v_a_2986_);
lean_dec(v_a_2985_);
lean_dec_ref(v_a_2984_);
return v_res_2989_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(lean_object* v_x_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_){
_start:
{
lean_object* v___x_2996_; 
v___x_2996_ = l_Lean_Meta_saveState___redArg(v___y_2992_, v___y_2994_);
if (lean_obj_tag(v___x_2996_) == 0)
{
lean_object* v_a_2997_; lean_object* v___x_2998_; 
v_a_2997_ = lean_ctor_get(v___x_2996_, 0);
lean_inc(v_a_2997_);
lean_dec_ref_known(v___x_2996_, 1);
lean_inc(v___y_2994_);
lean_inc_ref(v___y_2993_);
lean_inc(v___y_2992_);
lean_inc_ref(v___y_2991_);
v___x_2998_ = lean_apply_5(v_x_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_, lean_box(0));
if (lean_obj_tag(v___x_2998_) == 0)
{
lean_object* v_a_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3007_; 
lean_dec(v_a_2997_);
v_a_2999_ = lean_ctor_get(v___x_2998_, 0);
v_isSharedCheck_3007_ = !lean_is_exclusive(v___x_2998_);
if (v_isSharedCheck_3007_ == 0)
{
v___x_3001_ = v___x_2998_;
v_isShared_3002_ = v_isSharedCheck_3007_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_a_2999_);
lean_dec(v___x_2998_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3007_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3003_; lean_object* v___x_3005_; 
v___x_3003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3003_, 0, v_a_2999_);
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
lean_object* v_a_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3037_; 
v_a_3008_ = lean_ctor_get(v___x_2998_, 0);
v_isSharedCheck_3037_ = !lean_is_exclusive(v___x_2998_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_3010_ = v___x_2998_;
v_isShared_3011_ = v_isSharedCheck_3037_;
goto v_resetjp_3009_;
}
else
{
lean_inc(v_a_3008_);
lean_dec(v___x_2998_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3037_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
uint8_t v___y_3013_; uint8_t v___x_3035_; 
v___x_3035_ = l_Lean_Exception_isInterrupt(v_a_3008_);
if (v___x_3035_ == 0)
{
uint8_t v___x_3036_; 
lean_inc(v_a_3008_);
v___x_3036_ = l_Lean_Exception_isRuntime(v_a_3008_);
v___y_3013_ = v___x_3036_;
goto v___jp_3012_;
}
else
{
v___y_3013_ = v___x_3035_;
goto v___jp_3012_;
}
v___jp_3012_:
{
if (v___y_3013_ == 0)
{
lean_object* v___x_3014_; 
lean_del_object(v___x_3010_);
lean_dec(v_a_3008_);
v___x_3014_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2997_, v___y_2992_, v___y_2994_);
lean_dec(v_a_2997_);
if (lean_obj_tag(v___x_3014_) == 0)
{
lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3022_; 
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3022_ == 0)
{
lean_object* v_unused_3023_; 
v_unused_3023_ = lean_ctor_get(v___x_3014_, 0);
lean_dec(v_unused_3023_);
v___x_3016_ = v___x_3014_;
v_isShared_3017_ = v_isSharedCheck_3022_;
goto v_resetjp_3015_;
}
else
{
lean_dec(v___x_3014_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3022_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v___x_3018_; lean_object* v___x_3020_; 
v___x_3018_ = lean_box(0);
if (v_isShared_3017_ == 0)
{
lean_ctor_set(v___x_3016_, 0, v___x_3018_);
v___x_3020_ = v___x_3016_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v___x_3018_);
v___x_3020_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
return v___x_3020_;
}
}
}
else
{
lean_object* v_a_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3031_; 
v_a_3024_ = lean_ctor_get(v___x_3014_, 0);
v_isSharedCheck_3031_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3031_ == 0)
{
v___x_3026_ = v___x_3014_;
v_isShared_3027_ = v_isSharedCheck_3031_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_a_3024_);
lean_dec(v___x_3014_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3031_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
lean_object* v___x_3029_; 
if (v_isShared_3027_ == 0)
{
v___x_3029_ = v___x_3026_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v_a_3024_);
v___x_3029_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
return v___x_3029_;
}
}
}
}
else
{
lean_object* v___x_3033_; 
lean_dec(v_a_2997_);
if (v_isShared_3011_ == 0)
{
v___x_3033_ = v___x_3010_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3034_; 
v_reuseFailAlloc_3034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3034_, 0, v_a_3008_);
v___x_3033_ = v_reuseFailAlloc_3034_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
return v___x_3033_;
}
}
}
}
}
}
else
{
lean_object* v_a_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3045_; 
lean_dec_ref(v_x_2990_);
v_a_3038_ = lean_ctor_get(v___x_2996_, 0);
v_isSharedCheck_3045_ = !lean_is_exclusive(v___x_2996_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_3040_ = v___x_2996_;
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_a_3038_);
lean_dec(v___x_2996_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v___x_3043_; 
if (v_isShared_3041_ == 0)
{
v___x_3043_ = v___x_3040_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_a_3038_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg___boxed(lean_object* v_x_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_){
_start:
{
lean_object* v_res_3052_; 
v_res_3052_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v_x_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_);
lean_dec(v___y_3050_);
lean_dec_ref(v___y_3049_);
lean_dec(v___y_3048_);
lean_dec_ref(v___y_3047_);
return v_res_3052_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0(lean_object* v_00_u03b1_3053_, lean_object* v_x_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_){
_start:
{
lean_object* v___x_3060_; 
v___x_3060_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v_x_3054_, v___y_3055_, v___y_3056_, v___y_3057_, v___y_3058_);
return v___x_3060_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___boxed(lean_object* v_00_u03b1_3061_, lean_object* v_x_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_){
_start:
{
lean_object* v_res_3068_; 
v_res_3068_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0(v_00_u03b1_3061_, v_x_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_);
lean_dec(v___y_3066_);
lean_dec_ref(v___y_3065_);
lean_dec(v___y_3064_);
lean_dec_ref(v___y_3063_);
return v_res_3068_;
}
}
static lean_object* _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3070_; lean_object* v___x_3071_; 
v___x_3070_ = ((lean_object*)(l_Lean_MVarId_iffOfEq___lam__0___closed__0));
v___x_3071_ = l_Lean_stringToMessageData(v___x_3070_);
return v___x_3071_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq___lam__0(lean_object* v_mvarId_3072_, lean_object* v___x_3073_, lean_object* v___x_3074_, lean_object* v___x_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_){
_start:
{
lean_object* v___x_3081_; 
v___x_3081_ = l_Lean_MVarId_apply(v_mvarId_3072_, v___x_3073_, v___x_3074_, v___x_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
if (lean_obj_tag(v___x_3081_) == 0)
{
lean_object* v_a_3082_; lean_object* v___x_3084_; uint8_t v_isShared_3085_; uint8_t v_isSharedCheck_3098_; 
v_a_3082_ = lean_ctor_get(v___x_3081_, 0);
v_isSharedCheck_3098_ = !lean_is_exclusive(v___x_3081_);
if (v_isSharedCheck_3098_ == 0)
{
v___x_3084_ = v___x_3081_;
v_isShared_3085_ = v_isSharedCheck_3098_;
goto v_resetjp_3083_;
}
else
{
lean_inc(v_a_3082_);
lean_dec(v___x_3081_);
v___x_3084_ = lean_box(0);
v_isShared_3085_ = v_isSharedCheck_3098_;
goto v_resetjp_3083_;
}
v_resetjp_3083_:
{
lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; 
if (lean_obj_tag(v_a_3082_) == 1)
{
lean_object* v_tail_3093_; 
v_tail_3093_ = lean_ctor_get(v_a_3082_, 1);
if (lean_obj_tag(v_tail_3093_) == 0)
{
lean_object* v_head_3094_; lean_object* v___x_3096_; 
v_head_3094_ = lean_ctor_get(v_a_3082_, 0);
lean_inc(v_head_3094_);
lean_dec_ref_known(v_a_3082_, 2);
if (v_isShared_3085_ == 0)
{
lean_ctor_set(v___x_3084_, 0, v_head_3094_);
v___x_3096_ = v___x_3084_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v_head_3094_);
v___x_3096_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
return v___x_3096_;
}
}
else
{
lean_dec_ref_known(v_a_3082_, 2);
lean_del_object(v___x_3084_);
v___y_3087_ = v___y_3076_;
v___y_3088_ = v___y_3077_;
v___y_3089_ = v___y_3078_;
v___y_3090_ = v___y_3079_;
goto v___jp_3086_;
}
}
else
{
lean_del_object(v___x_3084_);
lean_dec(v_a_3082_);
v___y_3087_ = v___y_3076_;
v___y_3088_ = v___y_3077_;
v___y_3089_ = v___y_3078_;
v___y_3090_ = v___y_3079_;
goto v___jp_3086_;
}
v___jp_3086_:
{
lean_object* v___x_3091_; lean_object* v___x_3092_; 
v___x_3091_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3092_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3091_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_);
return v___x_3092_;
}
}
}
else
{
lean_object* v_a_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3106_; 
v_a_3099_ = lean_ctor_get(v___x_3081_, 0);
v_isSharedCheck_3106_ = !lean_is_exclusive(v___x_3081_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3101_ = v___x_3081_;
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_a_3099_);
lean_dec(v___x_3081_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
lean_object* v___x_3104_; 
if (v_isShared_3102_ == 0)
{
v___x_3104_ = v___x_3101_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v_a_3099_);
v___x_3104_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
return v___x_3104_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq___lam__0___boxed(lean_object* v_mvarId_3107_, lean_object* v___x_3108_, lean_object* v___x_3109_, lean_object* v___x_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_){
_start:
{
lean_object* v_res_3116_; 
v_res_3116_ = l_Lean_MVarId_iffOfEq___lam__0(v_mvarId_3107_, v___x_3108_, v___x_3109_, v___x_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_);
lean_dec(v___y_3114_);
lean_dec_ref(v___y_3113_);
lean_dec(v___y_3112_);
lean_dec_ref(v___y_3111_);
return v_res_3116_;
}
}
static lean_object* _init_l_Lean_MVarId_iffOfEq___closed__2(void){
_start:
{
lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; 
v___x_3120_ = lean_box(0);
v___x_3121_ = ((lean_object*)(l_Lean_MVarId_iffOfEq___closed__1));
v___x_3122_ = l_Lean_mkConst(v___x_3121_, v___x_3120_);
return v___x_3122_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq(lean_object* v_mvarId_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_){
_start:
{
lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___f_3136_; lean_object* v___x_3137_; 
v___x_3133_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___closed__2, &l_Lean_MVarId_iffOfEq___closed__2_once, _init_l_Lean_MVarId_iffOfEq___closed__2);
v___x_3134_ = ((lean_object*)(l_Lean_MVarId_iffOfEq___closed__3));
v___x_3135_ = lean_box(0);
lean_inc(v_mvarId_3127_);
v___f_3136_ = lean_alloc_closure((void*)(l_Lean_MVarId_iffOfEq___lam__0___boxed), 9, 4);
lean_closure_set(v___f_3136_, 0, v_mvarId_3127_);
lean_closure_set(v___f_3136_, 1, v___x_3133_);
lean_closure_set(v___f_3136_, 2, v___x_3134_);
lean_closure_set(v___f_3136_, 3, v___x_3135_);
v___x_3137_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v___f_3136_, v_a_3128_, v_a_3129_, v_a_3130_, v_a_3131_);
if (lean_obj_tag(v___x_3137_) == 0)
{
lean_object* v_a_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3149_; 
v_a_3138_ = lean_ctor_get(v___x_3137_, 0);
v_isSharedCheck_3149_ = !lean_is_exclusive(v___x_3137_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3140_ = v___x_3137_;
v_isShared_3141_ = v_isSharedCheck_3149_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_a_3138_);
lean_dec(v___x_3137_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3149_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
if (lean_obj_tag(v_a_3138_) == 0)
{
lean_object* v___x_3143_; 
if (v_isShared_3141_ == 0)
{
lean_ctor_set(v___x_3140_, 0, v_mvarId_3127_);
v___x_3143_ = v___x_3140_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v_mvarId_3127_);
v___x_3143_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
return v___x_3143_;
}
}
else
{
lean_object* v_val_3145_; lean_object* v___x_3147_; 
lean_dec(v_mvarId_3127_);
v_val_3145_ = lean_ctor_get(v_a_3138_, 0);
lean_inc(v_val_3145_);
lean_dec_ref_known(v_a_3138_, 1);
if (v_isShared_3141_ == 0)
{
lean_ctor_set(v___x_3140_, 0, v_val_3145_);
v___x_3147_ = v___x_3140_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v_val_3145_);
v___x_3147_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
return v___x_3147_;
}
}
}
}
else
{
lean_object* v_a_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3157_; 
lean_dec(v_mvarId_3127_);
v_a_3150_ = lean_ctor_get(v___x_3137_, 0);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_3137_);
if (v_isSharedCheck_3157_ == 0)
{
v___x_3152_ = v___x_3137_;
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_a_3150_);
lean_dec(v___x_3137_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
lean_object* v___x_3155_; 
if (v_isShared_3153_ == 0)
{
v___x_3155_ = v___x_3152_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_a_3150_);
v___x_3155_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
return v___x_3155_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_iffOfEq___boxed(lean_object* v_mvarId_3158_, lean_object* v_a_3159_, lean_object* v_a_3160_, lean_object* v_a_3161_, lean_object* v_a_3162_, lean_object* v_a_3163_){
_start:
{
lean_object* v_res_3164_; 
v_res_3164_ = l_Lean_MVarId_iffOfEq(v_mvarId_3158_, v_a_3159_, v_a_3160_, v_a_3161_, v_a_3162_);
lean_dec(v_a_3162_);
lean_dec_ref(v_a_3161_);
lean_dec(v_a_3160_);
lean_dec_ref(v_a_3159_);
return v_res_3164_;
}
}
static lean_object* _init_l_Lean_MVarId_propext___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; 
v___x_3171_ = lean_box(0);
v___x_3172_ = ((lean_object*)(l_Lean_MVarId_propext___lam__0___closed__3));
v___x_3173_ = l_Lean_mkConst(v___x_3172_, v___x_3171_);
return v___x_3173_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___lam__0(uint8_t v___x_3174_, lean_object* v_mvarId_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_){
_start:
{
lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___x_3188_; uint8_t v_foApprox_3189_; uint8_t v_ctxApprox_3190_; uint8_t v_quasiPatternApprox_3191_; uint8_t v_constApprox_3192_; uint8_t v_isDefEqStuckEx_3193_; uint8_t v_unificationHints_3194_; uint8_t v_proofIrrelevance_3195_; uint8_t v_assignSyntheticOpaque_3196_; uint8_t v_offsetCnstrs_3197_; uint8_t v_etaStruct_3198_; uint8_t v_univApprox_3199_; uint8_t v_iota_3200_; uint8_t v_beta_3201_; uint8_t v_proj_3202_; uint8_t v_zeta_3203_; uint8_t v_zetaDelta_3204_; uint8_t v_zetaUnused_3205_; uint8_t v_zetaHave_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3294_; 
v___x_3188_ = l_Lean_Meta_Context_config(v___y_3176_);
v_foApprox_3189_ = lean_ctor_get_uint8(v___x_3188_, 0);
v_ctxApprox_3190_ = lean_ctor_get_uint8(v___x_3188_, 1);
v_quasiPatternApprox_3191_ = lean_ctor_get_uint8(v___x_3188_, 2);
v_constApprox_3192_ = lean_ctor_get_uint8(v___x_3188_, 3);
v_isDefEqStuckEx_3193_ = lean_ctor_get_uint8(v___x_3188_, 4);
v_unificationHints_3194_ = lean_ctor_get_uint8(v___x_3188_, 5);
v_proofIrrelevance_3195_ = lean_ctor_get_uint8(v___x_3188_, 6);
v_assignSyntheticOpaque_3196_ = lean_ctor_get_uint8(v___x_3188_, 7);
v_offsetCnstrs_3197_ = lean_ctor_get_uint8(v___x_3188_, 8);
v_etaStruct_3198_ = lean_ctor_get_uint8(v___x_3188_, 10);
v_univApprox_3199_ = lean_ctor_get_uint8(v___x_3188_, 11);
v_iota_3200_ = lean_ctor_get_uint8(v___x_3188_, 12);
v_beta_3201_ = lean_ctor_get_uint8(v___x_3188_, 13);
v_proj_3202_ = lean_ctor_get_uint8(v___x_3188_, 14);
v_zeta_3203_ = lean_ctor_get_uint8(v___x_3188_, 15);
v_zetaDelta_3204_ = lean_ctor_get_uint8(v___x_3188_, 16);
v_zetaUnused_3205_ = lean_ctor_get_uint8(v___x_3188_, 17);
v_zetaHave_3206_ = lean_ctor_get_uint8(v___x_3188_, 18);
v_isSharedCheck_3294_ = !lean_is_exclusive(v___x_3188_);
if (v_isSharedCheck_3294_ == 0)
{
v___x_3208_ = v___x_3188_;
v_isShared_3209_ = v_isSharedCheck_3294_;
goto v_resetjp_3207_;
}
else
{
lean_dec(v___x_3188_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3294_;
goto v_resetjp_3207_;
}
v___jp_3181_:
{
lean_object* v___x_3186_; lean_object* v___x_3187_; 
v___x_3186_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3187_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3186_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_);
return v___x_3187_;
}
v_resetjp_3207_:
{
uint8_t v_trackZetaDelta_3210_; lean_object* v_zetaDeltaSet_3211_; lean_object* v_lctx_3212_; lean_object* v_localInstances_3213_; lean_object* v_defEqCtx_x3f_3214_; lean_object* v_synthPendingDepth_3215_; lean_object* v_canUnfold_x3f_3216_; uint8_t v_univApprox_3217_; uint8_t v_inTypeClassResolution_3218_; uint8_t v_cacheInferType_3219_; lean_object* v_config_3221_; 
v_trackZetaDelta_3210_ = lean_ctor_get_uint8(v___y_3176_, sizeof(void*)*7);
v_zetaDeltaSet_3211_ = lean_ctor_get(v___y_3176_, 1);
v_lctx_3212_ = lean_ctor_get(v___y_3176_, 2);
v_localInstances_3213_ = lean_ctor_get(v___y_3176_, 3);
v_defEqCtx_x3f_3214_ = lean_ctor_get(v___y_3176_, 4);
v_synthPendingDepth_3215_ = lean_ctor_get(v___y_3176_, 5);
v_canUnfold_x3f_3216_ = lean_ctor_get(v___y_3176_, 6);
v_univApprox_3217_ = lean_ctor_get_uint8(v___y_3176_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3218_ = lean_ctor_get_uint8(v___y_3176_, sizeof(void*)*7 + 2);
v_cacheInferType_3219_ = lean_ctor_get_uint8(v___y_3176_, sizeof(void*)*7 + 3);
if (v_isShared_3209_ == 0)
{
v_config_3221_ = v___x_3208_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3293_; 
v_reuseFailAlloc_3293_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3293_, 0, v_foApprox_3189_);
lean_ctor_set_uint8(v_reuseFailAlloc_3293_, 1, v_ctxApprox_3190_);
lean_ctor_set_uint8(v_reuseFailAlloc_3293_, 2, v_quasiPatternApprox_3191_);
lean_ctor_set_uint8(v_reuseFailAlloc_3293_, 3, v_constApprox_3192_);
lean_ctor_set_uint8(v_reuseFailAlloc_3293_, 4, v_isDefEqStuckEx_3193_);
lean_ctor_set_uint8(v_reuseFailAlloc_3293_, 5, v_unificationHints_3194_);
lean_ctor_set_uint8(v_reuseFailAlloc_3293_, 6, v_proofIrrelevance_3195_);
lean_ctor_set_uint8(v_reuseFailAlloc_3293_, 7, v_assignSyntheticOpaque_3196_);
lean_ctor_set_uint8(v_reuseFailAlloc_3293_, 8, v_offsetCnstrs_3197_);
lean_ctor_set_uint8(v_reuseFailAlloc_3293_, 10, v_etaStruct_3198_);
lean_ctor_set_uint8(v_reuseFailAlloc_3293_, 11, v_univApprox_3199_);
lean_ctor_set_uint8(v_reuseFailAlloc_3293_, 12, v_iota_3200_);
lean_ctor_set_uint8(v_reuseFailAlloc_3293_, 13, v_beta_3201_);
lean_ctor_set_uint8(v_reuseFailAlloc_3293_, 14, v_proj_3202_);
lean_ctor_set_uint8(v_reuseFailAlloc_3293_, 15, v_zeta_3203_);
lean_ctor_set_uint8(v_reuseFailAlloc_3293_, 16, v_zetaDelta_3204_);
lean_ctor_set_uint8(v_reuseFailAlloc_3293_, 17, v_zetaUnused_3205_);
lean_ctor_set_uint8(v_reuseFailAlloc_3293_, 18, v_zetaHave_3206_);
v_config_3221_ = v_reuseFailAlloc_3293_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
uint64_t v___x_3222_; uint64_t v___x_3223_; uint64_t v___x_3224_; uint64_t v___x_3225_; uint64_t v___x_3226_; uint64_t v_key_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; 
lean_ctor_set_uint8(v_config_3221_, 9, v___x_3174_);
v___x_3222_ = l_Lean_Meta_Context_configKey(v___y_3176_);
v___x_3223_ = 3ULL;
v___x_3224_ = lean_uint64_shift_right(v___x_3222_, v___x_3223_);
v___x_3225_ = lean_uint64_shift_left(v___x_3224_, v___x_3223_);
v___x_3226_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3174_);
v_key_3227_ = lean_uint64_lor(v___x_3225_, v___x_3226_);
v___x_3228_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3228_, 0, v_config_3221_);
lean_ctor_set_uint64(v___x_3228_, sizeof(void*)*1, v_key_3227_);
lean_inc(v_canUnfold_x3f_3216_);
lean_inc(v_synthPendingDepth_3215_);
lean_inc(v_defEqCtx_x3f_3214_);
lean_inc_ref(v_localInstances_3213_);
lean_inc_ref(v_lctx_3212_);
lean_inc(v_zetaDeltaSet_3211_);
v___x_3229_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3229_, 0, v___x_3228_);
lean_ctor_set(v___x_3229_, 1, v_zetaDeltaSet_3211_);
lean_ctor_set(v___x_3229_, 2, v_lctx_3212_);
lean_ctor_set(v___x_3229_, 3, v_localInstances_3213_);
lean_ctor_set(v___x_3229_, 4, v_defEqCtx_x3f_3214_);
lean_ctor_set(v___x_3229_, 5, v_synthPendingDepth_3215_);
lean_ctor_set(v___x_3229_, 6, v_canUnfold_x3f_3216_);
lean_ctor_set_uint8(v___x_3229_, sizeof(void*)*7, v_trackZetaDelta_3210_);
lean_ctor_set_uint8(v___x_3229_, sizeof(void*)*7 + 1, v_univApprox_3217_);
lean_ctor_set_uint8(v___x_3229_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3218_);
lean_ctor_set_uint8(v___x_3229_, sizeof(void*)*7 + 3, v_cacheInferType_3219_);
lean_inc(v_mvarId_3175_);
v___x_3230_ = l_Lean_MVarId_getType_x27(v_mvarId_3175_, v___x_3229_, v___y_3177_, v___y_3178_, v___y_3179_);
lean_dec_ref_known(v___x_3229_, 7);
if (lean_obj_tag(v___x_3230_) == 0)
{
lean_object* v_a_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; uint8_t v___x_3234_; 
v_a_3231_ = lean_ctor_get(v___x_3230_, 0);
lean_inc(v_a_3231_);
lean_dec_ref_known(v___x_3230_, 1);
v___x_3232_ = ((lean_object*)(l_Lean_MVarId_propext___lam__0___closed__1));
v___x_3233_ = lean_unsigned_to_nat(3u);
v___x_3234_ = l_Lean_Expr_isAppOfArity(v_a_3231_, v___x_3232_, v___x_3233_);
if (v___x_3234_ == 0)
{
lean_object* v___x_3260_; lean_object* v___x_3261_; 
lean_dec(v_a_3231_);
lean_dec(v_mvarId_3175_);
v___x_3260_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3261_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3260_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
return v___x_3261_;
}
else
{
lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; 
v___x_3262_ = l_Lean_Expr_appFn_x21(v_a_3231_);
lean_dec(v_a_3231_);
v___x_3263_ = l_Lean_Expr_appArg_x21(v___x_3262_);
lean_dec_ref(v___x_3262_);
v___x_3264_ = l_Lean_Meta_isProp(v___x_3263_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
if (lean_obj_tag(v___x_3264_) == 0)
{
lean_object* v_a_3265_; uint8_t v___x_3266_; 
v_a_3265_ = lean_ctor_get(v___x_3264_, 0);
lean_inc(v_a_3265_);
lean_dec_ref_known(v___x_3264_, 1);
v___x_3266_ = lean_unbox(v_a_3265_);
lean_dec(v_a_3265_);
if (v___x_3266_ == 0)
{
lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v_a_3269_; lean_object* v___x_3271_; uint8_t v_isShared_3272_; uint8_t v_isSharedCheck_3276_; 
lean_dec(v_mvarId_3175_);
v___x_3267_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3268_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3267_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
v_a_3269_ = lean_ctor_get(v___x_3268_, 0);
v_isSharedCheck_3276_ = !lean_is_exclusive(v___x_3268_);
if (v_isSharedCheck_3276_ == 0)
{
v___x_3271_ = v___x_3268_;
v_isShared_3272_ = v_isSharedCheck_3276_;
goto v_resetjp_3270_;
}
else
{
lean_inc(v_a_3269_);
lean_dec(v___x_3268_);
v___x_3271_ = lean_box(0);
v_isShared_3272_ = v_isSharedCheck_3276_;
goto v_resetjp_3270_;
}
v_resetjp_3270_:
{
lean_object* v___x_3274_; 
if (v_isShared_3272_ == 0)
{
v___x_3274_ = v___x_3271_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3275_; 
v_reuseFailAlloc_3275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3275_, 0, v_a_3269_);
v___x_3274_ = v_reuseFailAlloc_3275_;
goto v_reusejp_3273_;
}
v_reusejp_3273_:
{
return v___x_3274_;
}
}
}
else
{
goto v___jp_3235_;
}
}
else
{
lean_object* v_a_3277_; lean_object* v___x_3279_; uint8_t v_isShared_3280_; uint8_t v_isSharedCheck_3284_; 
lean_dec(v_mvarId_3175_);
v_a_3277_ = lean_ctor_get(v___x_3264_, 0);
v_isSharedCheck_3284_ = !lean_is_exclusive(v___x_3264_);
if (v_isSharedCheck_3284_ == 0)
{
v___x_3279_ = v___x_3264_;
v_isShared_3280_ = v_isSharedCheck_3284_;
goto v_resetjp_3278_;
}
else
{
lean_inc(v_a_3277_);
lean_dec(v___x_3264_);
v___x_3279_ = lean_box(0);
v_isShared_3280_ = v_isSharedCheck_3284_;
goto v_resetjp_3278_;
}
v_resetjp_3278_:
{
lean_object* v___x_3282_; 
if (v_isShared_3280_ == 0)
{
v___x_3282_ = v___x_3279_;
goto v_reusejp_3281_;
}
else
{
lean_object* v_reuseFailAlloc_3283_; 
v_reuseFailAlloc_3283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3283_, 0, v_a_3277_);
v___x_3282_ = v_reuseFailAlloc_3283_;
goto v_reusejp_3281_;
}
v_reusejp_3281_:
{
return v___x_3282_;
}
}
}
}
v___jp_3235_:
{
lean_object* v___x_3236_; uint8_t v___x_3237_; uint8_t v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; 
v___x_3236_ = lean_obj_once(&l_Lean_MVarId_propext___lam__0___closed__4, &l_Lean_MVarId_propext___lam__0___closed__4_once, _init_l_Lean_MVarId_propext___lam__0___closed__4);
v___x_3237_ = 0;
v___x_3238_ = 0;
v___x_3239_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3239_, 0, v___x_3237_);
lean_ctor_set_uint8(v___x_3239_, 1, v___x_3234_);
lean_ctor_set_uint8(v___x_3239_, 2, v___x_3238_);
lean_ctor_set_uint8(v___x_3239_, 3, v___x_3234_);
v___x_3240_ = lean_box(0);
v___x_3241_ = l_Lean_MVarId_apply(v_mvarId_3175_, v___x_3236_, v___x_3239_, v___x_3240_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
if (lean_obj_tag(v___x_3241_) == 0)
{
lean_object* v_a_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3251_; 
v_a_3242_ = lean_ctor_get(v___x_3241_, 0);
v_isSharedCheck_3251_ = !lean_is_exclusive(v___x_3241_);
if (v_isSharedCheck_3251_ == 0)
{
v___x_3244_ = v___x_3241_;
v_isShared_3245_ = v_isSharedCheck_3251_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_a_3242_);
lean_dec(v___x_3241_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3251_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
if (lean_obj_tag(v_a_3242_) == 1)
{
lean_object* v_tail_3246_; 
v_tail_3246_ = lean_ctor_get(v_a_3242_, 1);
if (lean_obj_tag(v_tail_3246_) == 0)
{
lean_object* v_head_3247_; lean_object* v___x_3249_; 
v_head_3247_ = lean_ctor_get(v_a_3242_, 0);
lean_inc(v_head_3247_);
lean_dec_ref_known(v_a_3242_, 2);
if (v_isShared_3245_ == 0)
{
lean_ctor_set(v___x_3244_, 0, v_head_3247_);
v___x_3249_ = v___x_3244_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3250_; 
v_reuseFailAlloc_3250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3250_, 0, v_head_3247_);
v___x_3249_ = v_reuseFailAlloc_3250_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
return v___x_3249_;
}
}
else
{
lean_dec_ref_known(v_a_3242_, 2);
lean_del_object(v___x_3244_);
v___y_3182_ = v___y_3176_;
v___y_3183_ = v___y_3177_;
v___y_3184_ = v___y_3178_;
v___y_3185_ = v___y_3179_;
goto v___jp_3181_;
}
}
else
{
lean_del_object(v___x_3244_);
lean_dec(v_a_3242_);
v___y_3182_ = v___y_3176_;
v___y_3183_ = v___y_3177_;
v___y_3184_ = v___y_3178_;
v___y_3185_ = v___y_3179_;
goto v___jp_3181_;
}
}
}
else
{
lean_object* v_a_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3259_; 
v_a_3252_ = lean_ctor_get(v___x_3241_, 0);
v_isSharedCheck_3259_ = !lean_is_exclusive(v___x_3241_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3254_ = v___x_3241_;
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_a_3252_);
lean_dec(v___x_3241_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v___x_3257_; 
if (v_isShared_3255_ == 0)
{
v___x_3257_ = v___x_3254_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v_a_3252_);
v___x_3257_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
return v___x_3257_;
}
}
}
}
}
else
{
lean_object* v_a_3285_; lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3292_; 
lean_dec(v_mvarId_3175_);
v_a_3285_ = lean_ctor_get(v___x_3230_, 0);
v_isSharedCheck_3292_ = !lean_is_exclusive(v___x_3230_);
if (v_isSharedCheck_3292_ == 0)
{
v___x_3287_ = v___x_3230_;
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
else
{
lean_inc(v_a_3285_);
lean_dec(v___x_3230_);
v___x_3287_ = lean_box(0);
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
v_resetjp_3286_:
{
lean_object* v___x_3290_; 
if (v_isShared_3288_ == 0)
{
v___x_3290_ = v___x_3287_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v_a_3285_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___lam__0___boxed(lean_object* v___x_3295_, lean_object* v_mvarId_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_){
_start:
{
uint8_t v___x_2435__boxed_3302_; lean_object* v_res_3303_; 
v___x_2435__boxed_3302_ = lean_unbox(v___x_3295_);
v_res_3303_ = l_Lean_MVarId_propext___lam__0(v___x_2435__boxed_3302_, v_mvarId_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_);
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3299_);
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3297_);
return v_res_3303_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext(lean_object* v_mvarId_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_){
_start:
{
uint8_t v___x_3310_; lean_object* v___x_3311_; lean_object* v___f_3312_; lean_object* v___x_3313_; 
v___x_3310_ = 2;
v___x_3311_ = lean_box(v___x_3310_);
lean_inc(v_mvarId_3304_);
v___f_3312_ = lean_alloc_closure((void*)(l_Lean_MVarId_propext___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3312_, 0, v___x_3311_);
lean_closure_set(v___f_3312_, 1, v_mvarId_3304_);
v___x_3313_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v___f_3312_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_);
if (lean_obj_tag(v___x_3313_) == 0)
{
lean_object* v_a_3314_; lean_object* v___x_3316_; uint8_t v_isShared_3317_; uint8_t v_isSharedCheck_3325_; 
v_a_3314_ = lean_ctor_get(v___x_3313_, 0);
v_isSharedCheck_3325_ = !lean_is_exclusive(v___x_3313_);
if (v_isSharedCheck_3325_ == 0)
{
v___x_3316_ = v___x_3313_;
v_isShared_3317_ = v_isSharedCheck_3325_;
goto v_resetjp_3315_;
}
else
{
lean_inc(v_a_3314_);
lean_dec(v___x_3313_);
v___x_3316_ = lean_box(0);
v_isShared_3317_ = v_isSharedCheck_3325_;
goto v_resetjp_3315_;
}
v_resetjp_3315_:
{
if (lean_obj_tag(v_a_3314_) == 0)
{
lean_object* v___x_3319_; 
if (v_isShared_3317_ == 0)
{
lean_ctor_set(v___x_3316_, 0, v_mvarId_3304_);
v___x_3319_ = v___x_3316_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v_mvarId_3304_);
v___x_3319_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
return v___x_3319_;
}
}
else
{
lean_object* v_val_3321_; lean_object* v___x_3323_; 
lean_dec(v_mvarId_3304_);
v_val_3321_ = lean_ctor_get(v_a_3314_, 0);
lean_inc(v_val_3321_);
lean_dec_ref_known(v_a_3314_, 1);
if (v_isShared_3317_ == 0)
{
lean_ctor_set(v___x_3316_, 0, v_val_3321_);
v___x_3323_ = v___x_3316_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v_val_3321_);
v___x_3323_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
return v___x_3323_;
}
}
}
}
else
{
lean_object* v_a_3326_; lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3333_; 
lean_dec(v_mvarId_3304_);
v_a_3326_ = lean_ctor_get(v___x_3313_, 0);
v_isSharedCheck_3333_ = !lean_is_exclusive(v___x_3313_);
if (v_isSharedCheck_3333_ == 0)
{
v___x_3328_ = v___x_3313_;
v_isShared_3329_ = v_isSharedCheck_3333_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_a_3326_);
lean_dec(v___x_3313_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3333_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
lean_object* v___x_3331_; 
if (v_isShared_3329_ == 0)
{
v___x_3331_ = v___x_3328_;
goto v_reusejp_3330_;
}
else
{
lean_object* v_reuseFailAlloc_3332_; 
v_reuseFailAlloc_3332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3332_, 0, v_a_3326_);
v___x_3331_ = v_reuseFailAlloc_3332_;
goto v_reusejp_3330_;
}
v_reusejp_3330_:
{
return v___x_3331_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_propext___boxed(lean_object* v_mvarId_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_){
_start:
{
lean_object* v_res_3340_; 
v_res_3340_ = l_Lean_MVarId_propext(v_mvarId_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_);
lean_dec(v_a_3338_);
lean_dec_ref(v_a_3337_);
lean_dec(v_a_3336_);
lean_dec_ref(v_a_3335_);
return v_res_3340_;
}
}
static uint64_t _init_l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0(void){
_start:
{
uint8_t v___x_3341_; uint64_t v___x_3342_; 
v___x_3341_ = 2;
v___x_3342_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3341_);
return v___x_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__0(lean_object* v_mvarId_3349_, lean_object* v___x_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_){
_start:
{
lean_object* v___x_3356_; 
lean_inc(v_mvarId_3349_);
v___x_3356_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3349_, v___x_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_);
if (lean_obj_tag(v___x_3356_) == 0)
{
lean_object* v___x_3357_; uint8_t v_foApprox_3358_; uint8_t v_ctxApprox_3359_; uint8_t v_quasiPatternApprox_3360_; uint8_t v_constApprox_3361_; uint8_t v_isDefEqStuckEx_3362_; uint8_t v_unificationHints_3363_; uint8_t v_proofIrrelevance_3364_; uint8_t v_assignSyntheticOpaque_3365_; uint8_t v_offsetCnstrs_3366_; uint8_t v_etaStruct_3367_; uint8_t v_univApprox_3368_; uint8_t v_iota_3369_; uint8_t v_beta_3370_; uint8_t v_proj_3371_; uint8_t v_zeta_3372_; uint8_t v_zetaDelta_3373_; uint8_t v_zetaUnused_3374_; uint8_t v_zetaHave_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3445_; 
lean_dec_ref_known(v___x_3356_, 1);
v___x_3357_ = l_Lean_Meta_Context_config(v___y_3351_);
v_foApprox_3358_ = lean_ctor_get_uint8(v___x_3357_, 0);
v_ctxApprox_3359_ = lean_ctor_get_uint8(v___x_3357_, 1);
v_quasiPatternApprox_3360_ = lean_ctor_get_uint8(v___x_3357_, 2);
v_constApprox_3361_ = lean_ctor_get_uint8(v___x_3357_, 3);
v_isDefEqStuckEx_3362_ = lean_ctor_get_uint8(v___x_3357_, 4);
v_unificationHints_3363_ = lean_ctor_get_uint8(v___x_3357_, 5);
v_proofIrrelevance_3364_ = lean_ctor_get_uint8(v___x_3357_, 6);
v_assignSyntheticOpaque_3365_ = lean_ctor_get_uint8(v___x_3357_, 7);
v_offsetCnstrs_3366_ = lean_ctor_get_uint8(v___x_3357_, 8);
v_etaStruct_3367_ = lean_ctor_get_uint8(v___x_3357_, 10);
v_univApprox_3368_ = lean_ctor_get_uint8(v___x_3357_, 11);
v_iota_3369_ = lean_ctor_get_uint8(v___x_3357_, 12);
v_beta_3370_ = lean_ctor_get_uint8(v___x_3357_, 13);
v_proj_3371_ = lean_ctor_get_uint8(v___x_3357_, 14);
v_zeta_3372_ = lean_ctor_get_uint8(v___x_3357_, 15);
v_zetaDelta_3373_ = lean_ctor_get_uint8(v___x_3357_, 16);
v_zetaUnused_3374_ = lean_ctor_get_uint8(v___x_3357_, 17);
v_zetaHave_3375_ = lean_ctor_get_uint8(v___x_3357_, 18);
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3357_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3377_ = v___x_3357_;
v_isShared_3378_ = v_isSharedCheck_3445_;
goto v_resetjp_3376_;
}
else
{
lean_dec(v___x_3357_);
v___x_3377_ = lean_box(0);
v_isShared_3378_ = v_isSharedCheck_3445_;
goto v_resetjp_3376_;
}
v_resetjp_3376_:
{
uint8_t v_trackZetaDelta_3379_; lean_object* v_zetaDeltaSet_3380_; lean_object* v_lctx_3381_; lean_object* v_localInstances_3382_; lean_object* v_defEqCtx_x3f_3383_; lean_object* v_synthPendingDepth_3384_; lean_object* v_canUnfold_x3f_3385_; uint8_t v_univApprox_3386_; uint8_t v_inTypeClassResolution_3387_; uint8_t v_cacheInferType_3388_; uint8_t v___x_3389_; lean_object* v_config_3391_; 
v_trackZetaDelta_3379_ = lean_ctor_get_uint8(v___y_3351_, sizeof(void*)*7);
v_zetaDeltaSet_3380_ = lean_ctor_get(v___y_3351_, 1);
v_lctx_3381_ = lean_ctor_get(v___y_3351_, 2);
v_localInstances_3382_ = lean_ctor_get(v___y_3351_, 3);
v_defEqCtx_x3f_3383_ = lean_ctor_get(v___y_3351_, 4);
v_synthPendingDepth_3384_ = lean_ctor_get(v___y_3351_, 5);
v_canUnfold_x3f_3385_ = lean_ctor_get(v___y_3351_, 6);
v_univApprox_3386_ = lean_ctor_get_uint8(v___y_3351_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3387_ = lean_ctor_get_uint8(v___y_3351_, sizeof(void*)*7 + 2);
v_cacheInferType_3388_ = lean_ctor_get_uint8(v___y_3351_, sizeof(void*)*7 + 3);
v___x_3389_ = 2;
if (v_isShared_3378_ == 0)
{
v_config_3391_ = v___x_3377_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3444_, 0, v_foApprox_3358_);
lean_ctor_set_uint8(v_reuseFailAlloc_3444_, 1, v_ctxApprox_3359_);
lean_ctor_set_uint8(v_reuseFailAlloc_3444_, 2, v_quasiPatternApprox_3360_);
lean_ctor_set_uint8(v_reuseFailAlloc_3444_, 3, v_constApprox_3361_);
lean_ctor_set_uint8(v_reuseFailAlloc_3444_, 4, v_isDefEqStuckEx_3362_);
lean_ctor_set_uint8(v_reuseFailAlloc_3444_, 5, v_unificationHints_3363_);
lean_ctor_set_uint8(v_reuseFailAlloc_3444_, 6, v_proofIrrelevance_3364_);
lean_ctor_set_uint8(v_reuseFailAlloc_3444_, 7, v_assignSyntheticOpaque_3365_);
lean_ctor_set_uint8(v_reuseFailAlloc_3444_, 8, v_offsetCnstrs_3366_);
lean_ctor_set_uint8(v_reuseFailAlloc_3444_, 10, v_etaStruct_3367_);
lean_ctor_set_uint8(v_reuseFailAlloc_3444_, 11, v_univApprox_3368_);
lean_ctor_set_uint8(v_reuseFailAlloc_3444_, 12, v_iota_3369_);
lean_ctor_set_uint8(v_reuseFailAlloc_3444_, 13, v_beta_3370_);
lean_ctor_set_uint8(v_reuseFailAlloc_3444_, 14, v_proj_3371_);
lean_ctor_set_uint8(v_reuseFailAlloc_3444_, 15, v_zeta_3372_);
lean_ctor_set_uint8(v_reuseFailAlloc_3444_, 16, v_zetaDelta_3373_);
lean_ctor_set_uint8(v_reuseFailAlloc_3444_, 17, v_zetaUnused_3374_);
lean_ctor_set_uint8(v_reuseFailAlloc_3444_, 18, v_zetaHave_3375_);
v_config_3391_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
uint64_t v___x_3392_; uint64_t v___x_3393_; uint64_t v___x_3394_; uint64_t v___x_3395_; uint64_t v___x_3396_; uint64_t v_key_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; 
lean_ctor_set_uint8(v_config_3391_, 9, v___x_3389_);
v___x_3392_ = l_Lean_Meta_Context_configKey(v___y_3351_);
v___x_3393_ = 3ULL;
v___x_3394_ = lean_uint64_shift_right(v___x_3392_, v___x_3393_);
v___x_3395_ = lean_uint64_shift_left(v___x_3394_, v___x_3393_);
v___x_3396_ = lean_uint64_once(&l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0, &l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0_once, _init_l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0);
v_key_3397_ = lean_uint64_lor(v___x_3395_, v___x_3396_);
v___x_3398_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3398_, 0, v_config_3391_);
lean_ctor_set_uint64(v___x_3398_, sizeof(void*)*1, v_key_3397_);
lean_inc(v_canUnfold_x3f_3385_);
lean_inc(v_synthPendingDepth_3384_);
lean_inc(v_defEqCtx_x3f_3383_);
lean_inc_ref(v_localInstances_3382_);
lean_inc_ref(v_lctx_3381_);
lean_inc(v_zetaDeltaSet_3380_);
v___x_3399_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3399_, 0, v___x_3398_);
lean_ctor_set(v___x_3399_, 1, v_zetaDeltaSet_3380_);
lean_ctor_set(v___x_3399_, 2, v_lctx_3381_);
lean_ctor_set(v___x_3399_, 3, v_localInstances_3382_);
lean_ctor_set(v___x_3399_, 4, v_defEqCtx_x3f_3383_);
lean_ctor_set(v___x_3399_, 5, v_synthPendingDepth_3384_);
lean_ctor_set(v___x_3399_, 6, v_canUnfold_x3f_3385_);
lean_ctor_set_uint8(v___x_3399_, sizeof(void*)*7, v_trackZetaDelta_3379_);
lean_ctor_set_uint8(v___x_3399_, sizeof(void*)*7 + 1, v_univApprox_3386_);
lean_ctor_set_uint8(v___x_3399_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3387_);
lean_ctor_set_uint8(v___x_3399_, sizeof(void*)*7 + 3, v_cacheInferType_3388_);
lean_inc(v_mvarId_3349_);
v___x_3400_ = l_Lean_MVarId_getType_x27(v_mvarId_3349_, v___x_3399_, v___y_3352_, v___y_3353_, v___y_3354_);
lean_dec_ref_known(v___x_3399_, 7);
if (lean_obj_tag(v___x_3400_) == 0)
{
lean_object* v_a_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; uint8_t v___x_3404_; 
v_a_3401_ = lean_ctor_get(v___x_3400_, 0);
lean_inc(v_a_3401_);
lean_dec_ref_known(v___x_3400_, 1);
v___x_3402_ = ((lean_object*)(l_Lean_MVarId_proofIrrelHeq___lam__0___closed__2));
v___x_3403_ = lean_unsigned_to_nat(4u);
v___x_3404_ = l_Lean_Expr_isAppOfArity(v_a_3401_, v___x_3402_, v___x_3403_);
if (v___x_3404_ == 0)
{
lean_object* v___x_3405_; lean_object* v___x_3406_; 
lean_dec(v_a_3401_);
lean_dec(v_mvarId_3349_);
v___x_3405_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3406_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3405_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_);
return v___x_3406_;
}
else
{
lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; 
v___x_3407_ = l_Lean_Expr_appFn_x21(v_a_3401_);
v___x_3408_ = l_Lean_Expr_appFn_x21(v___x_3407_);
lean_dec_ref(v___x_3407_);
v___x_3409_ = l_Lean_Expr_appArg_x21(v___x_3408_);
lean_dec_ref(v___x_3408_);
v___x_3410_ = l_Lean_Expr_appArg_x21(v_a_3401_);
lean_dec(v_a_3401_);
v___x_3411_ = ((lean_object*)(l_Lean_MVarId_proofIrrelHeq___lam__0___closed__4));
v___x_3412_ = lean_unsigned_to_nat(2u);
v___x_3413_ = lean_mk_empty_array_with_capacity(v___x_3412_);
v___x_3414_ = lean_array_push(v___x_3413_, v___x_3409_);
v___x_3415_ = lean_array_push(v___x_3414_, v___x_3410_);
v___x_3416_ = l_Lean_Meta_mkAppM(v___x_3411_, v___x_3415_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_);
if (lean_obj_tag(v___x_3416_) == 0)
{
lean_object* v_a_3417_; lean_object* v___x_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3426_; 
v_a_3417_ = lean_ctor_get(v___x_3416_, 0);
lean_inc(v_a_3417_);
lean_dec_ref_known(v___x_3416_, 1);
v___x_3418_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_3349_, v_a_3417_, v___y_3352_);
v_isSharedCheck_3426_ = !lean_is_exclusive(v___x_3418_);
if (v_isSharedCheck_3426_ == 0)
{
lean_object* v_unused_3427_; 
v_unused_3427_ = lean_ctor_get(v___x_3418_, 0);
lean_dec(v_unused_3427_);
v___x_3420_ = v___x_3418_;
v_isShared_3421_ = v_isSharedCheck_3426_;
goto v_resetjp_3419_;
}
else
{
lean_dec(v___x_3418_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3426_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
lean_object* v___x_3422_; lean_object* v___x_3424_; 
v___x_3422_ = lean_box(v___x_3404_);
if (v_isShared_3421_ == 0)
{
lean_ctor_set(v___x_3420_, 0, v___x_3422_);
v___x_3424_ = v___x_3420_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v___x_3422_);
v___x_3424_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
return v___x_3424_;
}
}
}
else
{
lean_object* v_a_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3435_; 
lean_dec(v_mvarId_3349_);
v_a_3428_ = lean_ctor_get(v___x_3416_, 0);
v_isSharedCheck_3435_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3435_ == 0)
{
v___x_3430_ = v___x_3416_;
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_a_3428_);
lean_dec(v___x_3416_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v___x_3433_; 
if (v_isShared_3431_ == 0)
{
v___x_3433_ = v___x_3430_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v_a_3428_);
v___x_3433_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
return v___x_3433_;
}
}
}
}
}
else
{
lean_object* v_a_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3443_; 
lean_dec(v_mvarId_3349_);
v_a_3436_ = lean_ctor_get(v___x_3400_, 0);
v_isSharedCheck_3443_ = !lean_is_exclusive(v___x_3400_);
if (v_isSharedCheck_3443_ == 0)
{
v___x_3438_ = v___x_3400_;
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_a_3436_);
lean_dec(v___x_3400_);
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
}
}
}
else
{
lean_object* v_a_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3453_; 
lean_dec(v_mvarId_3349_);
v_a_3446_ = lean_ctor_get(v___x_3356_, 0);
v_isSharedCheck_3453_ = !lean_is_exclusive(v___x_3356_);
if (v_isSharedCheck_3453_ == 0)
{
v___x_3448_ = v___x_3356_;
v_isShared_3449_ = v_isSharedCheck_3453_;
goto v_resetjp_3447_;
}
else
{
lean_inc(v_a_3446_);
lean_dec(v___x_3356_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3453_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
lean_object* v___x_3451_; 
if (v_isShared_3449_ == 0)
{
v___x_3451_ = v___x_3448_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v_a_3446_);
v___x_3451_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
return v___x_3451_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__0___boxed(lean_object* v_mvarId_3454_, lean_object* v___x_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_){
_start:
{
lean_object* v_res_3461_; 
v_res_3461_ = l_Lean_MVarId_proofIrrelHeq___lam__0(v_mvarId_3454_, v___x_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_);
lean_dec(v___y_3459_);
lean_dec_ref(v___y_3458_);
lean_dec(v___y_3457_);
lean_dec_ref(v___y_3456_);
return v_res_3461_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__1(lean_object* v___f_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_){
_start:
{
lean_object* v___x_3468_; 
v___x_3468_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(v___f_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_);
if (lean_obj_tag(v___x_3468_) == 0)
{
lean_object* v_a_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3482_; 
v_a_3469_ = lean_ctor_get(v___x_3468_, 0);
v_isSharedCheck_3482_ = !lean_is_exclusive(v___x_3468_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3471_ = v___x_3468_;
v_isShared_3472_ = v_isSharedCheck_3482_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_a_3469_);
lean_dec(v___x_3468_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3482_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
if (lean_obj_tag(v_a_3469_) == 0)
{
uint8_t v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3476_; 
v___x_3473_ = 0;
v___x_3474_ = lean_box(v___x_3473_);
if (v_isShared_3472_ == 0)
{
lean_ctor_set(v___x_3471_, 0, v___x_3474_);
v___x_3476_ = v___x_3471_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v___x_3474_);
v___x_3476_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
return v___x_3476_;
}
}
else
{
lean_object* v_val_3478_; lean_object* v___x_3480_; 
v_val_3478_ = lean_ctor_get(v_a_3469_, 0);
lean_inc(v_val_3478_);
lean_dec_ref_known(v_a_3469_, 1);
if (v_isShared_3472_ == 0)
{
lean_ctor_set(v___x_3471_, 0, v_val_3478_);
v___x_3480_ = v___x_3471_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v_val_3478_);
v___x_3480_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
return v___x_3480_;
}
}
}
}
else
{
lean_object* v_a_3483_; lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3490_; 
v_a_3483_ = lean_ctor_get(v___x_3468_, 0);
v_isSharedCheck_3490_ = !lean_is_exclusive(v___x_3468_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3485_ = v___x_3468_;
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
else
{
lean_inc(v_a_3483_);
lean_dec(v___x_3468_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
lean_object* v___x_3488_; 
if (v_isShared_3486_ == 0)
{
v___x_3488_ = v___x_3485_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_a_3483_);
v___x_3488_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
return v___x_3488_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___lam__1___boxed(lean_object* v___f_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_){
_start:
{
lean_object* v_res_3497_; 
v_res_3497_ = l_Lean_MVarId_proofIrrelHeq___lam__1(v___f_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_);
lean_dec(v___y_3495_);
lean_dec_ref(v___y_3494_);
lean_dec(v___y_3493_);
lean_dec_ref(v___y_3492_);
return v_res_3497_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq(lean_object* v_mvarId_3501_, lean_object* v_a_3502_, lean_object* v_a_3503_, lean_object* v_a_3504_, lean_object* v_a_3505_){
_start:
{
lean_object* v___x_3507_; lean_object* v___f_3508_; lean_object* v___f_3509_; lean_object* v___x_3510_; 
v___x_3507_ = ((lean_object*)(l_Lean_MVarId_proofIrrelHeq___closed__1));
lean_inc(v_mvarId_3501_);
v___f_3508_ = lean_alloc_closure((void*)(l_Lean_MVarId_proofIrrelHeq___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3508_, 0, v_mvarId_3501_);
lean_closure_set(v___f_3508_, 1, v___x_3507_);
v___f_3509_ = lean_alloc_closure((void*)(l_Lean_MVarId_proofIrrelHeq___lam__1___boxed), 6, 1);
lean_closure_set(v___f_3509_, 0, v___f_3508_);
v___x_3510_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_3501_, v___f_3509_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_);
return v___x_3510_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_proofIrrelHeq___boxed(lean_object* v_mvarId_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_){
_start:
{
lean_object* v_res_3517_; 
v_res_3517_ = l_Lean_MVarId_proofIrrelHeq(v_mvarId_3511_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_);
lean_dec(v_a_3515_);
lean_dec_ref(v_a_3514_);
lean_dec(v_a_3513_);
lean_dec_ref(v_a_3512_);
return v_res_3517_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim___lam__0(lean_object* v_mvarId_3522_, lean_object* v___x_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_){
_start:
{
lean_object* v___x_3529_; 
lean_inc(v_mvarId_3522_);
v___x_3529_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3522_, v___x_3523_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_);
if (lean_obj_tag(v___x_3529_) == 0)
{
lean_object* v___x_3530_; uint8_t v_foApprox_3531_; uint8_t v_ctxApprox_3532_; uint8_t v_quasiPatternApprox_3533_; uint8_t v_constApprox_3534_; uint8_t v_isDefEqStuckEx_3535_; uint8_t v_unificationHints_3536_; uint8_t v_proofIrrelevance_3537_; uint8_t v_assignSyntheticOpaque_3538_; uint8_t v_offsetCnstrs_3539_; uint8_t v_etaStruct_3540_; uint8_t v_univApprox_3541_; uint8_t v_iota_3542_; uint8_t v_beta_3543_; uint8_t v_proj_3544_; uint8_t v_zeta_3545_; uint8_t v_zetaDelta_3546_; uint8_t v_zetaUnused_3547_; uint8_t v_zetaHave_3548_; lean_object* v___x_3550_; uint8_t v_isShared_3551_; uint8_t v_isSharedCheck_3617_; 
lean_dec_ref_known(v___x_3529_, 1);
v___x_3530_ = l_Lean_Meta_Context_config(v___y_3524_);
v_foApprox_3531_ = lean_ctor_get_uint8(v___x_3530_, 0);
v_ctxApprox_3532_ = lean_ctor_get_uint8(v___x_3530_, 1);
v_quasiPatternApprox_3533_ = lean_ctor_get_uint8(v___x_3530_, 2);
v_constApprox_3534_ = lean_ctor_get_uint8(v___x_3530_, 3);
v_isDefEqStuckEx_3535_ = lean_ctor_get_uint8(v___x_3530_, 4);
v_unificationHints_3536_ = lean_ctor_get_uint8(v___x_3530_, 5);
v_proofIrrelevance_3537_ = lean_ctor_get_uint8(v___x_3530_, 6);
v_assignSyntheticOpaque_3538_ = lean_ctor_get_uint8(v___x_3530_, 7);
v_offsetCnstrs_3539_ = lean_ctor_get_uint8(v___x_3530_, 8);
v_etaStruct_3540_ = lean_ctor_get_uint8(v___x_3530_, 10);
v_univApprox_3541_ = lean_ctor_get_uint8(v___x_3530_, 11);
v_iota_3542_ = lean_ctor_get_uint8(v___x_3530_, 12);
v_beta_3543_ = lean_ctor_get_uint8(v___x_3530_, 13);
v_proj_3544_ = lean_ctor_get_uint8(v___x_3530_, 14);
v_zeta_3545_ = lean_ctor_get_uint8(v___x_3530_, 15);
v_zetaDelta_3546_ = lean_ctor_get_uint8(v___x_3530_, 16);
v_zetaUnused_3547_ = lean_ctor_get_uint8(v___x_3530_, 17);
v_zetaHave_3548_ = lean_ctor_get_uint8(v___x_3530_, 18);
v_isSharedCheck_3617_ = !lean_is_exclusive(v___x_3530_);
if (v_isSharedCheck_3617_ == 0)
{
v___x_3550_ = v___x_3530_;
v_isShared_3551_ = v_isSharedCheck_3617_;
goto v_resetjp_3549_;
}
else
{
lean_dec(v___x_3530_);
v___x_3550_ = lean_box(0);
v_isShared_3551_ = v_isSharedCheck_3617_;
goto v_resetjp_3549_;
}
v_resetjp_3549_:
{
uint8_t v_trackZetaDelta_3552_; lean_object* v_zetaDeltaSet_3553_; lean_object* v_lctx_3554_; lean_object* v_localInstances_3555_; lean_object* v_defEqCtx_x3f_3556_; lean_object* v_synthPendingDepth_3557_; lean_object* v_canUnfold_x3f_3558_; uint8_t v_univApprox_3559_; uint8_t v_inTypeClassResolution_3560_; uint8_t v_cacheInferType_3561_; uint8_t v___x_3562_; lean_object* v_config_3564_; 
v_trackZetaDelta_3552_ = lean_ctor_get_uint8(v___y_3524_, sizeof(void*)*7);
v_zetaDeltaSet_3553_ = lean_ctor_get(v___y_3524_, 1);
v_lctx_3554_ = lean_ctor_get(v___y_3524_, 2);
v_localInstances_3555_ = lean_ctor_get(v___y_3524_, 3);
v_defEqCtx_x3f_3556_ = lean_ctor_get(v___y_3524_, 4);
v_synthPendingDepth_3557_ = lean_ctor_get(v___y_3524_, 5);
v_canUnfold_x3f_3558_ = lean_ctor_get(v___y_3524_, 6);
v_univApprox_3559_ = lean_ctor_get_uint8(v___y_3524_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3560_ = lean_ctor_get_uint8(v___y_3524_, sizeof(void*)*7 + 2);
v_cacheInferType_3561_ = lean_ctor_get_uint8(v___y_3524_, sizeof(void*)*7 + 3);
v___x_3562_ = 2;
if (v_isShared_3551_ == 0)
{
v_config_3564_ = v___x_3550_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3616_, 0, v_foApprox_3531_);
lean_ctor_set_uint8(v_reuseFailAlloc_3616_, 1, v_ctxApprox_3532_);
lean_ctor_set_uint8(v_reuseFailAlloc_3616_, 2, v_quasiPatternApprox_3533_);
lean_ctor_set_uint8(v_reuseFailAlloc_3616_, 3, v_constApprox_3534_);
lean_ctor_set_uint8(v_reuseFailAlloc_3616_, 4, v_isDefEqStuckEx_3535_);
lean_ctor_set_uint8(v_reuseFailAlloc_3616_, 5, v_unificationHints_3536_);
lean_ctor_set_uint8(v_reuseFailAlloc_3616_, 6, v_proofIrrelevance_3537_);
lean_ctor_set_uint8(v_reuseFailAlloc_3616_, 7, v_assignSyntheticOpaque_3538_);
lean_ctor_set_uint8(v_reuseFailAlloc_3616_, 8, v_offsetCnstrs_3539_);
lean_ctor_set_uint8(v_reuseFailAlloc_3616_, 10, v_etaStruct_3540_);
lean_ctor_set_uint8(v_reuseFailAlloc_3616_, 11, v_univApprox_3541_);
lean_ctor_set_uint8(v_reuseFailAlloc_3616_, 12, v_iota_3542_);
lean_ctor_set_uint8(v_reuseFailAlloc_3616_, 13, v_beta_3543_);
lean_ctor_set_uint8(v_reuseFailAlloc_3616_, 14, v_proj_3544_);
lean_ctor_set_uint8(v_reuseFailAlloc_3616_, 15, v_zeta_3545_);
lean_ctor_set_uint8(v_reuseFailAlloc_3616_, 16, v_zetaDelta_3546_);
lean_ctor_set_uint8(v_reuseFailAlloc_3616_, 17, v_zetaUnused_3547_);
lean_ctor_set_uint8(v_reuseFailAlloc_3616_, 18, v_zetaHave_3548_);
v_config_3564_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
uint64_t v___x_3565_; uint64_t v___x_3566_; uint64_t v___x_3567_; uint64_t v___x_3568_; uint64_t v___x_3569_; uint64_t v_key_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; 
lean_ctor_set_uint8(v_config_3564_, 9, v___x_3562_);
v___x_3565_ = l_Lean_Meta_Context_configKey(v___y_3524_);
v___x_3566_ = 3ULL;
v___x_3567_ = lean_uint64_shift_right(v___x_3565_, v___x_3566_);
v___x_3568_ = lean_uint64_shift_left(v___x_3567_, v___x_3566_);
v___x_3569_ = lean_uint64_once(&l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0, &l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0_once, _init_l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0);
v_key_3570_ = lean_uint64_lor(v___x_3568_, v___x_3569_);
v___x_3571_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3571_, 0, v_config_3564_);
lean_ctor_set_uint64(v___x_3571_, sizeof(void*)*1, v_key_3570_);
lean_inc(v_canUnfold_x3f_3558_);
lean_inc(v_synthPendingDepth_3557_);
lean_inc(v_defEqCtx_x3f_3556_);
lean_inc_ref(v_localInstances_3555_);
lean_inc_ref(v_lctx_3554_);
lean_inc(v_zetaDeltaSet_3553_);
v___x_3572_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3572_, 0, v___x_3571_);
lean_ctor_set(v___x_3572_, 1, v_zetaDeltaSet_3553_);
lean_ctor_set(v___x_3572_, 2, v_lctx_3554_);
lean_ctor_set(v___x_3572_, 3, v_localInstances_3555_);
lean_ctor_set(v___x_3572_, 4, v_defEqCtx_x3f_3556_);
lean_ctor_set(v___x_3572_, 5, v_synthPendingDepth_3557_);
lean_ctor_set(v___x_3572_, 6, v_canUnfold_x3f_3558_);
lean_ctor_set_uint8(v___x_3572_, sizeof(void*)*7, v_trackZetaDelta_3552_);
lean_ctor_set_uint8(v___x_3572_, sizeof(void*)*7 + 1, v_univApprox_3559_);
lean_ctor_set_uint8(v___x_3572_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3560_);
lean_ctor_set_uint8(v___x_3572_, sizeof(void*)*7 + 3, v_cacheInferType_3561_);
lean_inc(v_mvarId_3522_);
v___x_3573_ = l_Lean_MVarId_getType_x27(v_mvarId_3522_, v___x_3572_, v___y_3525_, v___y_3526_, v___y_3527_);
lean_dec_ref_known(v___x_3572_, 7);
if (lean_obj_tag(v___x_3573_) == 0)
{
lean_object* v_a_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; uint8_t v___x_3577_; 
v_a_3574_ = lean_ctor_get(v___x_3573_, 0);
lean_inc(v_a_3574_);
lean_dec_ref_known(v___x_3573_, 1);
v___x_3575_ = ((lean_object*)(l_Lean_MVarId_propext___lam__0___closed__1));
v___x_3576_ = lean_unsigned_to_nat(3u);
v___x_3577_ = l_Lean_Expr_isAppOfArity(v_a_3574_, v___x_3575_, v___x_3576_);
if (v___x_3577_ == 0)
{
lean_object* v___x_3578_; lean_object* v___x_3579_; 
lean_dec(v_a_3574_);
lean_dec(v_mvarId_3522_);
v___x_3578_ = lean_obj_once(&l_Lean_MVarId_iffOfEq___lam__0___closed__1, &l_Lean_MVarId_iffOfEq___lam__0___closed__1_once, _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1);
v___x_3579_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(v___x_3578_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_);
return v___x_3579_;
}
else
{
lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; 
v___x_3580_ = l_Lean_Expr_appFn_x21(v_a_3574_);
v___x_3581_ = l_Lean_Expr_appArg_x21(v___x_3580_);
lean_dec_ref(v___x_3580_);
v___x_3582_ = l_Lean_Expr_appArg_x21(v_a_3574_);
lean_dec(v_a_3574_);
v___x_3583_ = ((lean_object*)(l_Lean_MVarId_subsingletonElim___lam__0___closed__1));
v___x_3584_ = lean_unsigned_to_nat(2u);
v___x_3585_ = lean_mk_empty_array_with_capacity(v___x_3584_);
v___x_3586_ = lean_array_push(v___x_3585_, v___x_3581_);
v___x_3587_ = lean_array_push(v___x_3586_, v___x_3582_);
v___x_3588_ = l_Lean_Meta_mkAppM(v___x_3583_, v___x_3587_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_);
if (lean_obj_tag(v___x_3588_) == 0)
{
lean_object* v_a_3589_; lean_object* v___x_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3598_; 
v_a_3589_ = lean_ctor_get(v___x_3588_, 0);
lean_inc(v_a_3589_);
lean_dec_ref_known(v___x_3588_, 1);
v___x_3590_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_3522_, v_a_3589_, v___y_3525_);
v_isSharedCheck_3598_ = !lean_is_exclusive(v___x_3590_);
if (v_isSharedCheck_3598_ == 0)
{
lean_object* v_unused_3599_; 
v_unused_3599_ = lean_ctor_get(v___x_3590_, 0);
lean_dec(v_unused_3599_);
v___x_3592_ = v___x_3590_;
v_isShared_3593_ = v_isSharedCheck_3598_;
goto v_resetjp_3591_;
}
else
{
lean_dec(v___x_3590_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3598_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
lean_object* v___x_3594_; lean_object* v___x_3596_; 
v___x_3594_ = lean_box(v___x_3577_);
if (v_isShared_3593_ == 0)
{
lean_ctor_set(v___x_3592_, 0, v___x_3594_);
v___x_3596_ = v___x_3592_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v___x_3594_);
v___x_3596_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
return v___x_3596_;
}
}
}
else
{
lean_object* v_a_3600_; lean_object* v___x_3602_; uint8_t v_isShared_3603_; uint8_t v_isSharedCheck_3607_; 
lean_dec(v_mvarId_3522_);
v_a_3600_ = lean_ctor_get(v___x_3588_, 0);
v_isSharedCheck_3607_ = !lean_is_exclusive(v___x_3588_);
if (v_isSharedCheck_3607_ == 0)
{
v___x_3602_ = v___x_3588_;
v_isShared_3603_ = v_isSharedCheck_3607_;
goto v_resetjp_3601_;
}
else
{
lean_inc(v_a_3600_);
lean_dec(v___x_3588_);
v___x_3602_ = lean_box(0);
v_isShared_3603_ = v_isSharedCheck_3607_;
goto v_resetjp_3601_;
}
v_resetjp_3601_:
{
lean_object* v___x_3605_; 
if (v_isShared_3603_ == 0)
{
v___x_3605_ = v___x_3602_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3606_; 
v_reuseFailAlloc_3606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3606_, 0, v_a_3600_);
v___x_3605_ = v_reuseFailAlloc_3606_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
return v___x_3605_;
}
}
}
}
}
else
{
lean_object* v_a_3608_; lean_object* v___x_3610_; uint8_t v_isShared_3611_; uint8_t v_isSharedCheck_3615_; 
lean_dec(v_mvarId_3522_);
v_a_3608_ = lean_ctor_get(v___x_3573_, 0);
v_isSharedCheck_3615_ = !lean_is_exclusive(v___x_3573_);
if (v_isSharedCheck_3615_ == 0)
{
v___x_3610_ = v___x_3573_;
v_isShared_3611_ = v_isSharedCheck_3615_;
goto v_resetjp_3609_;
}
else
{
lean_inc(v_a_3608_);
lean_dec(v___x_3573_);
v___x_3610_ = lean_box(0);
v_isShared_3611_ = v_isSharedCheck_3615_;
goto v_resetjp_3609_;
}
v_resetjp_3609_:
{
lean_object* v___x_3613_; 
if (v_isShared_3611_ == 0)
{
v___x_3613_ = v___x_3610_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v_a_3608_);
v___x_3613_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
return v___x_3613_;
}
}
}
}
}
}
else
{
lean_object* v_a_3618_; lean_object* v___x_3620_; uint8_t v_isShared_3621_; uint8_t v_isSharedCheck_3625_; 
lean_dec(v_mvarId_3522_);
v_a_3618_ = lean_ctor_get(v___x_3529_, 0);
v_isSharedCheck_3625_ = !lean_is_exclusive(v___x_3529_);
if (v_isSharedCheck_3625_ == 0)
{
v___x_3620_ = v___x_3529_;
v_isShared_3621_ = v_isSharedCheck_3625_;
goto v_resetjp_3619_;
}
else
{
lean_inc(v_a_3618_);
lean_dec(v___x_3529_);
v___x_3620_ = lean_box(0);
v_isShared_3621_ = v_isSharedCheck_3625_;
goto v_resetjp_3619_;
}
v_resetjp_3619_:
{
lean_object* v___x_3623_; 
if (v_isShared_3621_ == 0)
{
v___x_3623_ = v___x_3620_;
goto v_reusejp_3622_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v_a_3618_);
v___x_3623_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3622_;
}
v_reusejp_3622_:
{
return v___x_3623_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim___lam__0___boxed(lean_object* v_mvarId_3626_, lean_object* v___x_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_){
_start:
{
lean_object* v_res_3633_; 
v_res_3633_ = l_Lean_MVarId_subsingletonElim___lam__0(v_mvarId_3626_, v___x_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_);
lean_dec(v___y_3631_);
lean_dec_ref(v___y_3630_);
lean_dec(v___y_3629_);
lean_dec_ref(v___y_3628_);
return v_res_3633_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim(lean_object* v_mvarId_3637_, lean_object* v_a_3638_, lean_object* v_a_3639_, lean_object* v_a_3640_, lean_object* v_a_3641_){
_start:
{
lean_object* v___x_3643_; lean_object* v___f_3644_; lean_object* v___f_3645_; lean_object* v___x_3646_; 
v___x_3643_ = ((lean_object*)(l_Lean_MVarId_subsingletonElim___closed__1));
lean_inc(v_mvarId_3637_);
v___f_3644_ = lean_alloc_closure((void*)(l_Lean_MVarId_subsingletonElim___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3644_, 0, v_mvarId_3637_);
lean_closure_set(v___f_3644_, 1, v___x_3643_);
v___f_3645_ = lean_alloc_closure((void*)(l_Lean_MVarId_proofIrrelHeq___lam__1___boxed), 6, 1);
lean_closure_set(v___f_3645_, 0, v___f_3644_);
v___x_3646_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(v_mvarId_3637_, v___f_3645_, v_a_3638_, v_a_3639_, v_a_3640_, v_a_3641_);
return v___x_3646_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_subsingletonElim___boxed(lean_object* v_mvarId_3647_, lean_object* v_a_3648_, lean_object* v_a_3649_, lean_object* v_a_3650_, lean_object* v_a_3651_, lean_object* v_a_3652_){
_start:
{
lean_object* v_res_3653_; 
v_res_3653_ = l_Lean_MVarId_subsingletonElim(v_mvarId_3647_, v_a_3648_, v_a_3649_, v_a_3650_, v_a_3651_);
lean_dec(v_a_3651_);
lean_dec_ref(v_a_3650_);
lean_dec(v_a_3649_);
lean_dec_ref(v_a_3648_);
return v_res_3653_;
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
