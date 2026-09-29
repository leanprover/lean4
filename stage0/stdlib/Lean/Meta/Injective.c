// Lean compiler output
// Module: Lean.Meta.Injective
// Imports: public import Lean.Meta.Basic import Lean.Meta.Tactic.Refl import Lean.Meta.Tactic.Assumption import Lean.Meta.SameCtorUtils import Init.Omega import Lean.Meta.Tactic.Injection import Lean.Meta.Tactic.Simp.Attr
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
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_IO_CancelToken_isSet(lean_object*);
extern lean_object* l_Lean_interruptExceptionId;
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Meta_occursOrInType(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_introSubstEq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_applyN(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_injection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_splitAndCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assumptionCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
lean_object* lean_io_mono_nanos_now();
lean_object* l_Lean_MVarId_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_MVarId_refl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
extern lean_object* l_Lean_Meta_simpExtension;
lean_object* l_Lean_Meta_addSimpTheorem(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_registerReservedNamePredicate(lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_mkArrowN(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Array_unzip___redArg(lean_object*);
lean_object* l_Lean_MVarId_intros(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isInductiveCore_x3f(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* l_Lean_Meta_realizeConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Lean_Meta_isInductivePredicate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_registerReservedNameAction(lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__1_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_elimOptParam___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optParam"};
static const lean_object* l_Lean_Meta_elimOptParam___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_elimOptParam___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_elimOptParam___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_elimOptParam___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(140, 160, 223, 165, 16, 51, 54, 209)}};
static const lean_object* l_Lean_Meta_elimOptParam___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_elimOptParam___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Meta_elimOptParam___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_elimOptParam___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_elimOptParam___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg();
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg___boxed(lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "transform"};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0;
static lean_once_cell_t l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1;
static lean_once_cell_t l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_elimOptParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_elimOptParam___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_elimOptParam___closed__0 = (const lean_object*)&l_Lean_Meta_elimOptParam___closed__0_value;
static const lean_closure_object l_Lean_Meta_elimOptParam___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_elimOptParam___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_elimOptParam___closed__1 = (const lean_object*)&l_Lean_Meta_elimOptParam___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unexpected constructor type for `"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__0 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1;
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__2 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "failed to prove injectivity theorem for constructor `"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__0 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1;
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "`, use 'set_option genInjectivity false' to disable the generation"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__2 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Meta.Injective"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__0 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "_private.Lean.Meta.Injective.0.Lean.Meta.solveEqOfCtorEq"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__1 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__2 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3;
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__4 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "injective"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__5 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__4_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__5_value),LEAN_SCALAR_PTR_LITERAL(39, 126, 11, 127, 131, 182, 22, 10)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__7 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__7_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__8 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9;
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "solving injectivity goal for "};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__10 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__10_value;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11;
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = " with hypothesis "};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__12 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__12_value;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13;
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " at\n"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__14 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__14_value;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkInjectiveTheoremNameFor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inj"};
static const lean_object* l_Lean_Meta_mkInjectiveTheoremNameFor___closed__0 = (const lean_object*)&l_Lean_Meta_mkInjectiveTheoremNameFor___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkInjectiveTheoremNameFor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkInjectiveTheoremNameFor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(38, 11, 58, 56, 192, 58, 162, 195)}};
static const lean_object* l_Lean_Meta_mkInjectiveTheoremNameFor___closed__1 = (const lean_object*)&l_Lean_Meta_mkInjectiveTheoremNameFor___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheoremNameFor(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "generating `"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0;
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "type: "};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkInjectiveEqTheoremNameFor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "injEq"};
static const lean_object* l_Lean_Meta_mkInjectiveEqTheoremNameFor___closed__0 = (const lean_object*)&l_Lean_Meta_mkInjectiveEqTheoremNameFor___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkInjectiveEqTheoremNameFor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkInjectiveEqTheoremNameFor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(139, 235, 155, 31, 77, 126, 235, 172)}};
static const lean_object* l_Lean_Meta_mkInjectiveEqTheoremNameFor___closed__1 = (const lean_object*)&l_Lean_Meta_mkInjectiveEqTheoremNameFor___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveEqTheoremNameFor(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "unexpected number of goals after applying `Lean.and_imp`"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1___closed__0_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1___closed__1;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0___boxed, .m_arity = 8, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__0_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__1_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "injEq_helper"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__2 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__2_value;
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(167, 111, 180, 146, 132, 58, 155, 57)}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__3 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__3_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__4;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "unexpected number of subgoals when proving injective theorem for constructor `"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__1;
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "propIntro"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(189, 136, 38, 165, 207, 169, 133, 34)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__5;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 1, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "genInjectivity"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(56, 68, 112, 222, 169, 79, 62, 37)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 169, .m_capacity = 169, .m_length = 168, .m_data = "generate injectivity theorems for inductive datatype constructors. Temporarily (for bootstrapping reasons) also controls the generation of the\n    `ctorIdx` definition."};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__4_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(53, 17, 232, 138, 187, 170, 36, 13)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_genInjectivity;
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__1 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__2 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__3 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__4 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a constructor"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__0 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__2 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__2_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isCtor\?"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__3 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__3_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__1(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` is not an inductive type"};
static const lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__0 = (const lean_object*)&l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_mkInjectiveTheorems___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkInjectiveTheorems___closed__0;
static lean_once_cell_t l_Lean_Meta_mkInjectiveTheorems___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkInjectiveTheorems___closed__1;
static lean_once_cell_t l_Lean_Meta_mkInjectiveTheorems___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkInjectiveTheorems___closed__2;
static lean_once_cell_t l_Lean_Meta_mkInjectiveTheorems___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkInjectiveTheorems___closed__3;
static const lean_array_object l_Lean_Meta_mkInjectiveTheorems___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_mkInjectiveTheorems___closed__4 = (const lean_object*)&l_Lean_Meta_mkInjectiveTheorems___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__4_value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Injective"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(55, 101, 109, 194, 24, 99, 201, 78)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(74, 76, 255, 124, 31, 108, 47, 16)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 106, 16, 37, 3, 60, 11, 157)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__4_value),LEAN_SCALAR_PTR_LITERAL(3, 239, 173, 245, 77, 160, 209, 24)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(98, 239, 175, 71, 176, 92, 247, 26)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(235, 126, 32, 109, 177, 184, 17, 126)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(214, 151, 10, 103, 183, 199, 62, 165)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__4_value),LEAN_SCALAR_PTR_LITERAL(242, 157, 244, 230, 219, 101, 50, 39)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(67, 105, 167, 47, 98, 73, 248, 220)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0_value)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorAppIndices_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorAppIndices_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "failed to generate heterogeneous injectivity theorem for `"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "HEq"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(67, 180, 169, 191, 74, 196, 152, 188)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "noConfusion"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hinj"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkHInjectiveTheoremNameFor(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object*);
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_box(0);
v___x_5_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__1));
v___x_6_ = l_Lean_mkConst(v___x_5_, v___x_4_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg(lean_object* v_a_7_, lean_object* v_b_8_){
_start:
{
lean_object* v_array_9_; lean_object* v_start_10_; lean_object* v_stop_11_; lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_25_; 
v_array_9_ = lean_ctor_get(v_a_7_, 0);
v_start_10_ = lean_ctor_get(v_a_7_, 1);
v_stop_11_ = lean_ctor_get(v_a_7_, 2);
v_isSharedCheck_25_ = !lean_is_exclusive(v_a_7_);
if (v_isSharedCheck_25_ == 0)
{
v___x_13_ = v_a_7_;
v_isShared_14_ = v_isSharedCheck_25_;
goto v_resetjp_12_;
}
else
{
lean_inc(v_stop_11_);
lean_inc(v_start_10_);
lean_inc(v_array_9_);
lean_dec(v_a_7_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_25_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
uint8_t v___x_15_; 
v___x_15_ = lean_nat_dec_lt(v_start_10_, v_stop_11_);
if (v___x_15_ == 0)
{
lean_del_object(v___x_13_);
lean_dec(v_stop_11_);
lean_dec(v_start_10_);
lean_dec_ref(v_array_9_);
return v_b_8_;
}
else
{
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_19_; 
v___x_16_ = lean_unsigned_to_nat(1u);
v___x_17_ = lean_nat_add(v_start_10_, v___x_16_);
lean_inc_ref(v_array_9_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 1, v___x_17_);
v___x_19_ = v___x_13_;
goto v_reusejp_18_;
}
else
{
lean_object* v_reuseFailAlloc_24_; 
v_reuseFailAlloc_24_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_24_, 0, v_array_9_);
lean_ctor_set(v_reuseFailAlloc_24_, 1, v___x_17_);
lean_ctor_set(v_reuseFailAlloc_24_, 2, v_stop_11_);
v___x_19_ = v_reuseFailAlloc_24_;
goto v_reusejp_18_;
}
v_reusejp_18_:
{
lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_20_ = lean_array_fget(v_array_9_, v_start_10_);
lean_dec(v_start_10_);
lean_dec_ref(v_array_9_);
v___x_21_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__2);
v___x_22_ = l_Lean_mkAppB(v___x_21_, v___x_20_, v_b_8_);
v_a_7_ = v___x_19_;
v_b_8_ = v___x_22_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f(lean_object* v_args_26_){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; uint8_t v___x_29_; 
v___x_27_ = lean_array_get_size(v_args_26_);
v___x_28_ = lean_unsigned_to_nat(0u);
v___x_29_ = lean_nat_dec_eq(v___x_27_, v___x_28_);
if (v___x_29_ == 0)
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v_result_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_30_ = l_Lean_instInhabitedExpr;
v___x_31_ = lean_unsigned_to_nat(1u);
v___x_32_ = lean_nat_sub(v___x_27_, v___x_31_);
v_result_33_ = lean_array_get(v___x_30_, v_args_26_, v___x_32_);
lean_dec(v___x_32_);
v___x_34_ = l_Array_reverse___redArg(v_args_26_);
v___x_35_ = lean_array_get_size(v___x_34_);
v___x_36_ = l_Array_toSubarray___redArg(v___x_34_, v___x_31_, v___x_35_);
v___x_37_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg(v___x_36_, v_result_33_);
v___x_38_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
return v___x_38_;
}
else
{
lean_object* v___x_39_; 
lean_dec_ref(v_args_26_);
v___x_39_ = lean_box(0);
return v___x_39_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0(lean_object* v_inst_40_, lean_object* v_R_41_, lean_object* v_a_42_, lean_object* v_b_43_, lean_object* v_c_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg(v_a_42_, v_b_43_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam___lam__0(lean_object* v_e_51_, lean_object* v___y_52_, lean_object* v___y_53_){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; uint8_t v___x_57_; 
v___x_55_ = ((lean_object*)(l_Lean_Meta_elimOptParam___lam__0___closed__1));
v___x_56_ = lean_unsigned_to_nat(2u);
v___x_57_ = l_Lean_Expr_isAppOfArity(v_e_51_, v___x_55_, v___x_56_);
if (v___x_57_ == 0)
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = ((lean_object*)(l_Lean_Meta_elimOptParam___lam__0___closed__2));
v___x_59_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
return v___x_59_;
}
else
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_60_ = l_Lean_Expr_getAppNumArgs(v_e_51_);
v___x_61_ = lean_unsigned_to_nat(1u);
v___x_62_ = lean_nat_sub(v___x_60_, v___x_61_);
lean_dec(v___x_60_);
v___x_63_ = l_Lean_Expr_getRevArg_x21(v_e_51_, v___x_62_);
v___x_64_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
v___x_65_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
return v___x_65_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam___lam__0___boxed(lean_object* v_e_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Lean_Meta_elimOptParam___lam__0(v_e_66_, v___y_67_, v___y_68_);
lean_dec(v___y_68_);
lean_dec_ref(v___y_67_);
lean_dec_ref(v_e_66_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam___lam__1(lean_object* v_e_71_, lean_object* v___y_72_, lean_object* v___y_73_){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_75_, 0, v_e_71_);
v___x_76_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam___lam__1___boxed(lean_object* v_e_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Lean_Meta_elimOptParam___lam__1(v_e_77_, v___y_78_, v___y_79_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(lean_object* v_x_82_, lean_object* v_x_83_){
_start:
{
if (lean_obj_tag(v_x_83_) == 0)
{
return v_x_82_;
}
else
{
lean_object* v_key_84_; lean_object* v_value_85_; lean_object* v_tail_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_109_; 
v_key_84_ = lean_ctor_get(v_x_83_, 0);
v_value_85_ = lean_ctor_get(v_x_83_, 1);
v_tail_86_ = lean_ctor_get(v_x_83_, 2);
v_isSharedCheck_109_ = !lean_is_exclusive(v_x_83_);
if (v_isSharedCheck_109_ == 0)
{
v___x_88_ = v_x_83_;
v_isShared_89_ = v_isSharedCheck_109_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_tail_86_);
lean_inc(v_value_85_);
lean_inc(v_key_84_);
lean_dec(v_x_83_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_109_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
lean_object* v___x_90_; uint64_t v___x_91_; uint64_t v___x_92_; uint64_t v___x_93_; uint64_t v_fold_94_; uint64_t v___x_95_; uint64_t v___x_96_; uint64_t v___x_97_; size_t v___x_98_; size_t v___x_99_; size_t v___x_100_; size_t v___x_101_; size_t v___x_102_; lean_object* v___x_103_; lean_object* v___x_105_; 
v___x_90_ = lean_array_get_size(v_x_82_);
v___x_91_ = l_Lean_ExprStructEq_hash(v_key_84_);
v___x_92_ = 32ULL;
v___x_93_ = lean_uint64_shift_right(v___x_91_, v___x_92_);
v_fold_94_ = lean_uint64_xor(v___x_91_, v___x_93_);
v___x_95_ = 16ULL;
v___x_96_ = lean_uint64_shift_right(v_fold_94_, v___x_95_);
v___x_97_ = lean_uint64_xor(v_fold_94_, v___x_96_);
v___x_98_ = lean_uint64_to_usize(v___x_97_);
v___x_99_ = lean_usize_of_nat(v___x_90_);
v___x_100_ = ((size_t)1ULL);
v___x_101_ = lean_usize_sub(v___x_99_, v___x_100_);
v___x_102_ = lean_usize_land(v___x_98_, v___x_101_);
v___x_103_ = lean_array_uget_borrowed(v_x_82_, v___x_102_);
lean_inc(v___x_103_);
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 2, v___x_103_);
v___x_105_ = v___x_88_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_key_84_);
lean_ctor_set(v_reuseFailAlloc_108_, 1, v_value_85_);
lean_ctor_set(v_reuseFailAlloc_108_, 2, v___x_103_);
v___x_105_ = v_reuseFailAlloc_108_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
lean_object* v___x_106_; 
v___x_106_ = lean_array_uset(v_x_82_, v___x_102_, v___x_105_);
v_x_82_ = v___x_106_;
v_x_83_ = v_tail_86_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(lean_object* v_i_110_, lean_object* v_source_111_, lean_object* v_target_112_){
_start:
{
lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_113_ = lean_array_get_size(v_source_111_);
v___x_114_ = lean_nat_dec_lt(v_i_110_, v___x_113_);
if (v___x_114_ == 0)
{
lean_dec_ref(v_source_111_);
lean_dec(v_i_110_);
return v_target_112_;
}
else
{
lean_object* v_es_115_; lean_object* v___x_116_; lean_object* v_source_117_; lean_object* v_target_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v_es_115_ = lean_array_fget(v_source_111_, v_i_110_);
v___x_116_ = lean_box(0);
v_source_117_ = lean_array_fset(v_source_111_, v_i_110_, v___x_116_);
v_target_118_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_target_112_, v_es_115_);
v___x_119_ = lean_unsigned_to_nat(1u);
v___x_120_ = lean_nat_add(v_i_110_, v___x_119_);
lean_dec(v_i_110_);
v_i_110_ = v___x_120_;
v_source_111_ = v_source_117_;
v_target_112_ = v_target_118_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11___redArg(lean_object* v_data_122_){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v_nbuckets_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_123_ = lean_array_get_size(v_data_122_);
v___x_124_ = lean_unsigned_to_nat(2u);
v_nbuckets_125_ = lean_nat_mul(v___x_123_, v___x_124_);
v___x_126_ = lean_unsigned_to_nat(0u);
v___x_127_ = lean_box(0);
v___x_128_ = lean_mk_array(v_nbuckets_125_, v___x_127_);
v___x_129_ = lean_array_propagate_mark(v_data_122_, v___x_128_);
v___x_130_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v___x_126_, v_data_122_, v___x_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__12___redArg(lean_object* v_a_131_, lean_object* v_b_132_, lean_object* v_x_133_){
_start:
{
if (lean_obj_tag(v_x_133_) == 0)
{
lean_dec(v_b_132_);
lean_dec_ref(v_a_131_);
return v_x_133_;
}
else
{
lean_object* v_key_134_; lean_object* v_value_135_; lean_object* v_tail_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_148_; 
v_key_134_ = lean_ctor_get(v_x_133_, 0);
v_value_135_ = lean_ctor_get(v_x_133_, 1);
v_tail_136_ = lean_ctor_get(v_x_133_, 2);
v_isSharedCheck_148_ = !lean_is_exclusive(v_x_133_);
if (v_isSharedCheck_148_ == 0)
{
v___x_138_ = v_x_133_;
v_isShared_139_ = v_isSharedCheck_148_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_tail_136_);
lean_inc(v_value_135_);
lean_inc(v_key_134_);
lean_dec(v_x_133_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_148_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
uint8_t v___x_140_; 
v___x_140_ = l_Lean_ExprStructEq_beq(v_key_134_, v_a_131_);
if (v___x_140_ == 0)
{
lean_object* v___x_141_; lean_object* v___x_143_; 
v___x_141_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__12___redArg(v_a_131_, v_b_132_, v_tail_136_);
if (v_isShared_139_ == 0)
{
lean_ctor_set(v___x_138_, 2, v___x_141_);
v___x_143_ = v___x_138_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_key_134_);
lean_ctor_set(v_reuseFailAlloc_144_, 1, v_value_135_);
lean_ctor_set(v_reuseFailAlloc_144_, 2, v___x_141_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
else
{
lean_object* v___x_146_; 
lean_dec(v_value_135_);
lean_dec(v_key_134_);
if (v_isShared_139_ == 0)
{
lean_ctor_set(v___x_138_, 1, v_b_132_);
lean_ctor_set(v___x_138_, 0, v_a_131_);
v___x_146_ = v___x_138_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_a_131_);
lean_ctor_set(v_reuseFailAlloc_147_, 1, v_b_132_);
lean_ctor_set(v_reuseFailAlloc_147_, 2, v_tail_136_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___redArg(lean_object* v_a_149_, lean_object* v_x_150_){
_start:
{
if (lean_obj_tag(v_x_150_) == 0)
{
uint8_t v___x_151_; 
v___x_151_ = 0;
return v___x_151_;
}
else
{
lean_object* v_key_152_; lean_object* v_tail_153_; uint8_t v___x_154_; 
v_key_152_ = lean_ctor_get(v_x_150_, 0);
v_tail_153_ = lean_ctor_get(v_x_150_, 2);
v___x_154_ = l_Lean_ExprStructEq_beq(v_key_152_, v_a_149_);
if (v___x_154_ == 0)
{
v_x_150_ = v_tail_153_;
goto _start;
}
else
{
return v___x_154_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___redArg___boxed(lean_object* v_a_156_, lean_object* v_x_157_){
_start:
{
uint8_t v_res_158_; lean_object* v_r_159_; 
v_res_158_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___redArg(v_a_156_, v_x_157_);
lean_dec(v_x_157_);
lean_dec_ref(v_a_156_);
v_r_159_ = lean_box(v_res_158_);
return v_r_159_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6___redArg(lean_object* v_m_160_, lean_object* v_a_161_, lean_object* v_b_162_){
_start:
{
lean_object* v_size_163_; lean_object* v_buckets_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_207_; 
v_size_163_ = lean_ctor_get(v_m_160_, 0);
v_buckets_164_ = lean_ctor_get(v_m_160_, 1);
v_isSharedCheck_207_ = !lean_is_exclusive(v_m_160_);
if (v_isSharedCheck_207_ == 0)
{
v___x_166_ = v_m_160_;
v_isShared_167_ = v_isSharedCheck_207_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_buckets_164_);
lean_inc(v_size_163_);
lean_dec(v_m_160_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_207_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_168_; uint64_t v___x_169_; uint64_t v___x_170_; uint64_t v___x_171_; uint64_t v_fold_172_; uint64_t v___x_173_; uint64_t v___x_174_; uint64_t v___x_175_; size_t v___x_176_; size_t v___x_177_; size_t v___x_178_; size_t v___x_179_; size_t v___x_180_; lean_object* v_bkt_181_; uint8_t v___x_182_; 
v___x_168_ = lean_array_get_size(v_buckets_164_);
v___x_169_ = l_Lean_ExprStructEq_hash(v_a_161_);
v___x_170_ = 32ULL;
v___x_171_ = lean_uint64_shift_right(v___x_169_, v___x_170_);
v_fold_172_ = lean_uint64_xor(v___x_169_, v___x_171_);
v___x_173_ = 16ULL;
v___x_174_ = lean_uint64_shift_right(v_fold_172_, v___x_173_);
v___x_175_ = lean_uint64_xor(v_fold_172_, v___x_174_);
v___x_176_ = lean_uint64_to_usize(v___x_175_);
v___x_177_ = lean_usize_of_nat(v___x_168_);
v___x_178_ = ((size_t)1ULL);
v___x_179_ = lean_usize_sub(v___x_177_, v___x_178_);
v___x_180_ = lean_usize_land(v___x_176_, v___x_179_);
v_bkt_181_ = lean_array_uget_borrowed(v_buckets_164_, v___x_180_);
v___x_182_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___redArg(v_a_161_, v_bkt_181_);
if (v___x_182_ == 0)
{
lean_object* v___x_183_; lean_object* v_size_x27_184_; lean_object* v___x_185_; lean_object* v_buckets_x27_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; uint8_t v___x_192_; 
v___x_183_ = lean_unsigned_to_nat(1u);
v_size_x27_184_ = lean_nat_add(v_size_163_, v___x_183_);
lean_dec(v_size_163_);
lean_inc(v_bkt_181_);
v___x_185_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_185_, 0, v_a_161_);
lean_ctor_set(v___x_185_, 1, v_b_162_);
lean_ctor_set(v___x_185_, 2, v_bkt_181_);
v_buckets_x27_186_ = lean_array_uset(v_buckets_164_, v___x_180_, v___x_185_);
v___x_187_ = lean_unsigned_to_nat(4u);
v___x_188_ = lean_nat_mul(v_size_x27_184_, v___x_187_);
v___x_189_ = lean_unsigned_to_nat(3u);
v___x_190_ = lean_nat_div(v___x_188_, v___x_189_);
lean_dec(v___x_188_);
v___x_191_ = lean_array_get_size(v_buckets_x27_186_);
v___x_192_ = lean_nat_dec_le(v___x_190_, v___x_191_);
lean_dec(v___x_190_);
if (v___x_192_ == 0)
{
lean_object* v_val_193_; lean_object* v___x_195_; 
v_val_193_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11___redArg(v_buckets_x27_186_);
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 1, v_val_193_);
lean_ctor_set(v___x_166_, 0, v_size_x27_184_);
v___x_195_ = v___x_166_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_size_x27_184_);
lean_ctor_set(v_reuseFailAlloc_196_, 1, v_val_193_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
else
{
lean_object* v___x_198_; 
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 1, v_buckets_x27_186_);
lean_ctor_set(v___x_166_, 0, v_size_x27_184_);
v___x_198_ = v___x_166_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_size_x27_184_);
lean_ctor_set(v_reuseFailAlloc_199_, 1, v_buckets_x27_186_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
}
else
{
lean_object* v___x_200_; lean_object* v_buckets_x27_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_205_; 
lean_inc(v_bkt_181_);
v___x_200_ = lean_box(0);
v_buckets_x27_201_ = lean_array_uset(v_buckets_164_, v___x_180_, v___x_200_);
v___x_202_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__12___redArg(v_a_161_, v_b_162_, v_bkt_181_);
v___x_203_ = lean_array_uset(v_buckets_x27_201_, v___x_180_, v___x_202_);
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 1, v___x_203_);
v___x_205_ = v___x_166_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_size_163_);
lean_ctor_set(v_reuseFailAlloc_206_, 1, v___x_203_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__2(lean_object* v_a_208_, lean_object* v_e_209_, lean_object* v_a_210_){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_212_ = lean_st_ref_take(v_a_208_);
v___x_213_ = lean_box(0);
v___x_214_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6___redArg(v___x_212_, v_e_209_, v_a_210_);
v___x_215_ = lean_st_ref_put(v_a_208_, v___x_214_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__2___boxed(lean_object* v_a_216_, lean_object* v_e_217_, lean_object* v_a_218_, lean_object* v___y_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__2(v_a_216_, v_e_217_, v_a_218_);
lean_dec(v_a_216_);
return v_res_220_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_221_ = lean_box(0);
v___x_222_ = l_Lean_interruptExceptionId;
v___x_223_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_222_);
lean_ctor_set(v___x_223_, 1, v___x_221_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg(){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg___closed__0);
v___x_226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg___boxed(lean_object* v___y_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg();
return v_res_228_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = l_Lean_maxRecDepthErrorMessage;
v___x_235_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
return v___x_235_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__3);
v___x_237_ = l_Lean_MessageData_ofFormat(v___x_236_);
return v___x_237_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_238_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__4);
v___x_239_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__2));
v___x_240_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
lean_ctor_set(v___x_240_, 1, v___x_238_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_ref_241_){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_243_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_244_, 0, v_ref_241_);
lean_ctor_set(v___x_244_, 1, v___x_243_);
v___x_245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_ref_246_, lean_object* v___y_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_246_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(lean_object* v_x_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_){
_start:
{
lean_object* v___y_255_; uint16_t v___y_265_; uint8_t v___y_266_; lean_object* v___y_267_; lean_object* v___y_268_; uint8_t v___y_269_; lean_object* v___y_270_; lean_object* v_toCold_275_; lean_object* v_currRecDepth_276_; lean_object* v_ref_277_; uint16_t v_optionFlags_278_; uint8_t v_suppressElabErrors_279_; uint8_t v_isRecordingDeps_280_; lean_object* v_maxRecDepth_281_; lean_object* v_cancelTk_x3f_282_; 
v_toCold_275_ = lean_ctor_get(v___y_251_, 0);
v_currRecDepth_276_ = lean_ctor_get(v___y_251_, 1);
v_ref_277_ = lean_ctor_get(v___y_251_, 2);
v_optionFlags_278_ = lean_ctor_get_uint16(v___y_251_, sizeof(void*)*3);
v_suppressElabErrors_279_ = lean_ctor_get_uint8(v___y_251_, sizeof(void*)*3 + 2);
v_isRecordingDeps_280_ = lean_ctor_get_uint8(v___y_251_, sizeof(void*)*3 + 3);
v_maxRecDepth_281_ = lean_ctor_get(v_toCold_275_, 3);
v_cancelTk_x3f_282_ = lean_ctor_get(v_toCold_275_, 10);
if (lean_obj_tag(v_cancelTk_x3f_282_) == 1)
{
lean_object* v_val_288_; uint8_t v___x_289_; 
v_val_288_ = lean_ctor_get(v_cancelTk_x3f_282_, 0);
v___x_289_ = l_IO_CancelToken_isSet(v_val_288_);
if (v___x_289_ == 0)
{
goto v___jp_283_;
}
else
{
lean_object* v___x_290_; lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_298_; 
lean_dec_ref(v_x_249_);
v___x_290_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg();
v_a_291_ = lean_ctor_get(v___x_290_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_290_);
if (v_isSharedCheck_298_ == 0)
{
v___x_293_ = v___x_290_;
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_dec(v___x_290_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_296_; 
if (v_isShared_294_ == 0)
{
v___x_296_ = v___x_293_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_a_291_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
}
else
{
goto v___jp_283_;
}
v___jp_254_:
{
if (lean_obj_tag(v___y_255_) == 0)
{
return v___y_255_;
}
else
{
lean_object* v_a_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_263_; 
v_a_256_ = lean_ctor_get(v___y_255_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___y_255_);
if (v_isSharedCheck_263_ == 0)
{
v___x_258_ = v___y_255_;
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_a_256_);
lean_dec(v___y_255_);
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
v___jp_264_:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_271_ = lean_unsigned_to_nat(1u);
v___x_272_ = lean_nat_add(v___y_270_, v___x_271_);
lean_inc_ref(v___y_267_);
v___x_273_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_273_, 0, v___y_267_);
lean_ctor_set(v___x_273_, 1, v___x_272_);
lean_ctor_set(v___x_273_, 2, v___y_268_);
lean_ctor_set_uint16(v___x_273_, sizeof(void*)*3, v___y_265_);
lean_ctor_set_uint8(v___x_273_, sizeof(void*)*3 + 2, v___y_266_);
lean_ctor_set_uint8(v___x_273_, sizeof(void*)*3 + 3, v___y_269_);
lean_inc(v___y_252_);
lean_inc(v___y_250_);
v___x_274_ = lean_apply_4(v_x_249_, v___y_250_, v___x_273_, v___y_252_, lean_box(0));
v___y_255_ = v___x_274_;
goto v___jp_254_;
}
v___jp_283_:
{
lean_object* v___x_284_; uint8_t v___x_285_; 
v___x_284_ = lean_unsigned_to_nat(0u);
v___x_285_ = lean_nat_dec_eq(v_maxRecDepth_281_, v___x_284_);
if (v___x_285_ == 0)
{
uint8_t v___x_286_; 
v___x_286_ = lean_nat_dec_eq(v_currRecDepth_276_, v_maxRecDepth_281_);
if (v___x_286_ == 0)
{
lean_inc(v_ref_277_);
v___y_265_ = v_optionFlags_278_;
v___y_266_ = v_suppressElabErrors_279_;
v___y_267_ = v_toCold_275_;
v___y_268_ = v_ref_277_;
v___y_269_ = v_isRecordingDeps_280_;
v___y_270_ = v_currRecDepth_276_;
goto v___jp_264_;
}
else
{
lean_object* v___x_287_; 
lean_dec_ref(v_x_249_);
lean_inc(v_ref_277_);
v___x_287_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_277_);
v___y_255_ = v___x_287_;
goto v___jp_254_;
}
}
else
{
lean_inc(v_ref_277_);
v___y_265_ = v_optionFlags_278_;
v___y_266_ = v_suppressElabErrors_279_;
v___y_267_ = v_toCold_275_;
v___y_268_ = v_ref_277_;
v___y_269_ = v_isRecordingDeps_280_;
v___y_270_ = v_currRecDepth_276_;
goto v___jp_264_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(v_x_299_, v___y_300_, v___y_301_, v___y_302_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec(v___y_300_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_305_, lean_object* v_x_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_310_ = lean_apply_1(v_x_306_, lean_box(0));
v___x_311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_312_, lean_object* v_x_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(v_00_u03b1_312_, v_x_313_, v___y_314_, v___y_315_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_a_318_, lean_object* v_x_319_){
_start:
{
if (lean_obj_tag(v_x_319_) == 0)
{
lean_object* v___x_320_; 
v___x_320_ = lean_box(0);
return v___x_320_;
}
else
{
lean_object* v_key_321_; lean_object* v_value_322_; lean_object* v_tail_323_; uint8_t v___x_324_; 
v_key_321_ = lean_ctor_get(v_x_319_, 0);
v_value_322_ = lean_ctor_get(v_x_319_, 1);
v_tail_323_ = lean_ctor_get(v_x_319_, 2);
v___x_324_ = l_Lean_ExprStructEq_beq(v_key_321_, v_a_318_);
if (v___x_324_ == 0)
{
v_x_319_ = v_tail_323_;
goto _start;
}
else
{
lean_object* v___x_326_; 
lean_inc(v_value_322_);
v___x_326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_326_, 0, v_value_322_);
return v___x_326_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_a_327_, lean_object* v_x_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(v_a_327_, v_x_328_);
lean_dec(v_x_328_);
lean_dec_ref(v_a_327_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(lean_object* v_m_330_, lean_object* v_a_331_){
_start:
{
lean_object* v_buckets_332_; lean_object* v___x_333_; uint64_t v___x_334_; uint64_t v___x_335_; uint64_t v___x_336_; uint64_t v_fold_337_; uint64_t v___x_338_; uint64_t v___x_339_; uint64_t v___x_340_; size_t v___x_341_; size_t v___x_342_; size_t v___x_343_; size_t v___x_344_; size_t v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v_buckets_332_ = lean_ctor_get(v_m_330_, 1);
v___x_333_ = lean_array_get_size(v_buckets_332_);
v___x_334_ = l_Lean_ExprStructEq_hash(v_a_331_);
v___x_335_ = 32ULL;
v___x_336_ = lean_uint64_shift_right(v___x_334_, v___x_335_);
v_fold_337_ = lean_uint64_xor(v___x_334_, v___x_336_);
v___x_338_ = 16ULL;
v___x_339_ = lean_uint64_shift_right(v_fold_337_, v___x_338_);
v___x_340_ = lean_uint64_xor(v_fold_337_, v___x_339_);
v___x_341_ = lean_uint64_to_usize(v___x_340_);
v___x_342_ = lean_usize_of_nat(v___x_333_);
v___x_343_ = ((size_t)1ULL);
v___x_344_ = lean_usize_sub(v___x_342_, v___x_343_);
v___x_345_ = lean_usize_land(v___x_341_, v___x_344_);
v___x_346_ = lean_array_uget_borrowed(v_buckets_332_, v___x_345_);
v___x_347_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(v_a_331_, v___x_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_348_, lean_object* v_a_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(v_m_348_, v_a_349_);
lean_dec_ref(v_a_349_);
lean_dec_ref(v_m_348_);
return v_res_350_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0(void){
_start:
{
lean_object* v___x_352_; lean_object* v_dummy_353_; 
v___x_352_ = lean_box(0);
v_dummy_353_ = l_Lean_Expr_sort___override(v___x_352_);
return v_dummy_353_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1(lean_object* v_pre_354_, lean_object* v_post_355_, size_t v_sz_356_, size_t v_i_357_, lean_object* v_bs_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
uint8_t v___x_363_; 
v___x_363_ = lean_usize_dec_lt(v_i_357_, v_sz_356_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; 
lean_dec_ref(v_post_355_);
lean_dec_ref(v_pre_354_);
v___x_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_364_, 0, v_bs_358_);
return v___x_364_;
}
else
{
lean_object* v_v_365_; lean_object* v___x_366_; lean_object* v_bs_x27_367_; lean_object* v___x_368_; 
v_v_365_ = lean_array_uget(v_bs_358_, v_i_357_);
v___x_366_ = lean_unsigned_to_nat(0u);
v_bs_x27_367_ = lean_array_uset(v_bs_358_, v_i_357_, v___x_366_);
lean_inc_ref(v_post_355_);
lean_inc_ref(v_pre_354_);
v___x_368_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_354_, v_post_355_, v_v_365_, v___y_359_, v___y_360_, v___y_361_);
if (lean_obj_tag(v___x_368_) == 0)
{
lean_object* v_a_369_; size_t v___x_370_; size_t v___x_371_; lean_object* v___x_372_; 
v_a_369_ = lean_ctor_get(v___x_368_, 0);
lean_inc(v_a_369_);
lean_dec_ref_known(v___x_368_, 1);
v___x_370_ = ((size_t)1ULL);
v___x_371_ = lean_usize_add(v_i_357_, v___x_370_);
v___x_372_ = lean_array_uset(v_bs_x27_367_, v_i_357_, v_a_369_);
v_i_357_ = v___x_371_;
v_bs_358_ = v___x_372_;
goto _start;
}
else
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_381_; 
lean_dec_ref(v_bs_x27_367_);
lean_dec_ref(v_post_355_);
lean_dec_ref(v_pre_354_);
v_a_374_ = lean_ctor_get(v___x_368_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_381_ == 0)
{
v___x_376_ = v___x_368_;
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_368_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
if (v_isShared_377_ == 0)
{
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_374_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4(lean_object* v_pre_382_, lean_object* v_post_383_, lean_object* v_x_384_, lean_object* v_x_385_, lean_object* v_x_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
if (lean_obj_tag(v_x_384_) == 5)
{
lean_object* v_fn_391_; lean_object* v_arg_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v_fn_391_ = lean_ctor_get(v_x_384_, 0);
lean_inc_ref(v_fn_391_);
v_arg_392_ = lean_ctor_get(v_x_384_, 1);
lean_inc_ref(v_arg_392_);
lean_dec_ref_known(v_x_384_, 2);
v___x_393_ = lean_array_set(v_x_385_, v_x_386_, v_arg_392_);
v___x_394_ = lean_unsigned_to_nat(1u);
v___x_395_ = lean_nat_sub(v_x_386_, v___x_394_);
lean_dec(v_x_386_);
v_x_384_ = v_fn_391_;
v_x_385_ = v___x_393_;
v_x_386_ = v___x_395_;
goto _start;
}
else
{
lean_object* v___x_397_; 
lean_dec(v_x_386_);
lean_inc_ref(v_post_383_);
lean_inc_ref(v_pre_382_);
v___x_397_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_382_, v_post_383_, v_x_384_, v___y_387_, v___y_388_, v___y_389_);
if (lean_obj_tag(v___x_397_) == 0)
{
lean_object* v_a_398_; size_t v_sz_399_; size_t v___x_400_; lean_object* v___x_401_; 
v_a_398_ = lean_ctor_get(v___x_397_, 0);
lean_inc(v_a_398_);
lean_dec_ref_known(v___x_397_, 1);
v_sz_399_ = lean_array_size(v_x_385_);
v___x_400_ = ((size_t)0ULL);
lean_inc_ref(v_post_383_);
lean_inc_ref(v_pre_382_);
v___x_401_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1(v_pre_382_, v_post_383_, v_sz_399_, v___x_400_, v_x_385_, v___y_387_, v___y_388_, v___y_389_);
if (lean_obj_tag(v___x_401_) == 0)
{
lean_object* v_a_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v_a_402_ = lean_ctor_get(v___x_401_, 0);
lean_inc(v_a_402_);
lean_dec_ref_known(v___x_401_, 1);
v___x_403_ = l_Lean_mkAppN(v_a_398_, v_a_402_);
lean_dec(v_a_402_);
v___x_404_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_382_, v_post_383_, v___x_403_, v___y_387_, v___y_388_, v___y_389_);
return v___x_404_;
}
else
{
lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_412_; 
lean_dec(v_a_398_);
lean_dec_ref(v_post_383_);
lean_dec_ref(v_pre_382_);
v_a_405_ = lean_ctor_get(v___x_401_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_412_ == 0)
{
v___x_407_ = v___x_401_;
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_401_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_410_; 
if (v_isShared_408_ == 0)
{
v___x_410_ = v___x_407_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_a_405_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
else
{
lean_dec_ref(v_x_385_);
lean_dec_ref(v_post_383_);
lean_dec_ref(v_pre_382_);
return v___x_397_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1(lean_object* v___x_413_, lean_object* v_pre_414_, lean_object* v_e_415_, lean_object* v_post_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l_Lean_Core_checkSystem(v___x_413_, v___y_418_, v___y_419_);
if (lean_obj_tag(v___x_421_) == 0)
{
lean_object* v___x_422_; 
lean_dec_ref_known(v___x_421_, 1);
lean_inc_ref(v_pre_414_);
lean_inc(v___y_419_);
lean_inc_ref(v___y_418_);
lean_inc_ref(v_e_415_);
v___x_422_ = lean_apply_4(v_pre_414_, v_e_415_, v___y_418_, v___y_419_, lean_box(0));
if (lean_obj_tag(v___x_422_) == 0)
{
lean_object* v_a_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_538_; 
v_a_423_ = lean_ctor_get(v___x_422_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_538_ == 0)
{
v___x_425_ = v___x_422_;
v_isShared_426_ = v_isSharedCheck_538_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_a_423_);
lean_dec(v___x_422_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_538_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___y_428_; 
switch(lean_obj_tag(v_a_423_))
{
case 0:
{
lean_object* v_e_528_; lean_object* v___x_530_; 
lean_dec_ref(v_post_416_);
lean_dec_ref(v_e_415_);
lean_dec_ref(v_pre_414_);
v_e_528_ = lean_ctor_get(v_a_423_, 0);
lean_inc_ref(v_e_528_);
lean_dec_ref_known(v_a_423_, 1);
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 0, v_e_528_);
v___x_530_ = v___x_425_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_e_528_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
case 1:
{
lean_object* v_e_532_; lean_object* v___x_533_; 
lean_del_object(v___x_425_);
lean_dec_ref(v_e_415_);
v_e_532_ = lean_ctor_get(v_a_423_, 0);
lean_inc_ref(v_e_532_);
lean_dec_ref_known(v_a_423_, 1);
lean_inc_ref(v_post_416_);
lean_inc_ref(v_pre_414_);
v___x_533_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_414_, v_post_416_, v_e_532_, v___y_417_, v___y_418_, v___y_419_);
if (lean_obj_tag(v___x_533_) == 0)
{
lean_object* v_a_534_; lean_object* v___x_535_; 
v_a_534_ = lean_ctor_get(v___x_533_, 0);
lean_inc(v_a_534_);
lean_dec_ref_known(v___x_533_, 1);
v___x_535_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_414_, v_post_416_, v_a_534_, v___y_417_, v___y_418_, v___y_419_);
return v___x_535_;
}
else
{
lean_dec_ref(v_post_416_);
lean_dec_ref(v_pre_414_);
return v___x_533_;
}
}
default: 
{
lean_object* v_e_x3f_536_; 
lean_del_object(v___x_425_);
v_e_x3f_536_ = lean_ctor_get(v_a_423_, 0);
lean_inc(v_e_x3f_536_);
lean_dec_ref_known(v_a_423_, 1);
if (lean_obj_tag(v_e_x3f_536_) == 0)
{
v___y_428_ = v_e_415_;
goto v___jp_427_;
}
else
{
lean_object* v_val_537_; 
lean_dec_ref(v_e_415_);
v_val_537_ = lean_ctor_get(v_e_x3f_536_, 0);
lean_inc(v_val_537_);
lean_dec_ref_known(v_e_x3f_536_, 1);
v___y_428_ = v_val_537_;
goto v___jp_427_;
}
}
}
v___jp_427_:
{
switch(lean_obj_tag(v___y_428_))
{
case 7:
{
lean_object* v_binderName_429_; lean_object* v_binderType_430_; lean_object* v_body_431_; uint8_t v_binderInfo_432_; lean_object* v___x_433_; 
v_binderName_429_ = lean_ctor_get(v___y_428_, 0);
v_binderType_430_ = lean_ctor_get(v___y_428_, 1);
v_body_431_ = lean_ctor_get(v___y_428_, 2);
v_binderInfo_432_ = lean_ctor_get_uint8(v___y_428_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_430_);
lean_inc_ref(v_post_416_);
lean_inc_ref(v_pre_414_);
v___x_433_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_414_, v_post_416_, v_binderType_430_, v___y_417_, v___y_418_, v___y_419_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v_a_434_; lean_object* v___x_435_; 
v_a_434_ = lean_ctor_get(v___x_433_, 0);
lean_inc(v_a_434_);
lean_dec_ref_known(v___x_433_, 1);
lean_inc_ref(v_body_431_);
lean_inc_ref(v_post_416_);
lean_inc_ref(v_pre_414_);
v___x_435_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_414_, v_post_416_, v_body_431_, v___y_417_, v___y_418_, v___y_419_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v_a_436_; size_t v___x_437_; size_t v___x_438_; uint8_t v___x_439_; 
v_a_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_a_436_);
lean_dec_ref_known(v___x_435_, 1);
v___x_437_ = lean_ptr_addr(v_binderType_430_);
v___x_438_ = lean_ptr_addr(v_a_434_);
v___x_439_ = lean_usize_dec_eq(v___x_437_, v___x_438_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; lean_object* v___x_441_; 
lean_inc(v_binderName_429_);
lean_dec_ref_known(v___y_428_, 3);
v___x_440_ = l_Lean_Expr_forallE___override(v_binderName_429_, v_a_434_, v_a_436_, v_binderInfo_432_);
v___x_441_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_414_, v_post_416_, v___x_440_, v___y_417_, v___y_418_, v___y_419_);
return v___x_441_;
}
else
{
size_t v___x_442_; size_t v___x_443_; uint8_t v___x_444_; 
v___x_442_ = lean_ptr_addr(v_body_431_);
v___x_443_ = lean_ptr_addr(v_a_436_);
v___x_444_ = lean_usize_dec_eq(v___x_442_, v___x_443_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; lean_object* v___x_446_; 
lean_inc(v_binderName_429_);
lean_dec_ref_known(v___y_428_, 3);
v___x_445_ = l_Lean_Expr_forallE___override(v_binderName_429_, v_a_434_, v_a_436_, v_binderInfo_432_);
v___x_446_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_414_, v_post_416_, v___x_445_, v___y_417_, v___y_418_, v___y_419_);
return v___x_446_;
}
else
{
uint8_t v___x_447_; 
v___x_447_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_432_, v_binderInfo_432_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; lean_object* v___x_449_; 
lean_inc(v_binderName_429_);
lean_dec_ref_known(v___y_428_, 3);
v___x_448_ = l_Lean_Expr_forallE___override(v_binderName_429_, v_a_434_, v_a_436_, v_binderInfo_432_);
v___x_449_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_414_, v_post_416_, v___x_448_, v___y_417_, v___y_418_, v___y_419_);
return v___x_449_;
}
else
{
lean_object* v___x_450_; 
lean_dec(v_a_436_);
lean_dec(v_a_434_);
v___x_450_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_414_, v_post_416_, v___y_428_, v___y_417_, v___y_418_, v___y_419_);
return v___x_450_;
}
}
}
}
else
{
lean_dec(v_a_434_);
lean_dec_ref_known(v___y_428_, 3);
lean_dec_ref(v_post_416_);
lean_dec_ref(v_pre_414_);
return v___x_435_;
}
}
else
{
lean_dec_ref_known(v___y_428_, 3);
lean_dec_ref(v_post_416_);
lean_dec_ref(v_pre_414_);
return v___x_433_;
}
}
case 6:
{
lean_object* v_binderName_451_; lean_object* v_binderType_452_; lean_object* v_body_453_; uint8_t v_binderInfo_454_; lean_object* v___x_455_; 
v_binderName_451_ = lean_ctor_get(v___y_428_, 0);
v_binderType_452_ = lean_ctor_get(v___y_428_, 1);
v_body_453_ = lean_ctor_get(v___y_428_, 2);
v_binderInfo_454_ = lean_ctor_get_uint8(v___y_428_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_452_);
lean_inc_ref(v_post_416_);
lean_inc_ref(v_pre_414_);
v___x_455_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_414_, v_post_416_, v_binderType_452_, v___y_417_, v___y_418_, v___y_419_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v_a_456_; lean_object* v___x_457_; 
v_a_456_ = lean_ctor_get(v___x_455_, 0);
lean_inc(v_a_456_);
lean_dec_ref_known(v___x_455_, 1);
lean_inc_ref(v_body_453_);
lean_inc_ref(v_post_416_);
lean_inc_ref(v_pre_414_);
v___x_457_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_414_, v_post_416_, v_body_453_, v___y_417_, v___y_418_, v___y_419_);
if (lean_obj_tag(v___x_457_) == 0)
{
lean_object* v_a_458_; size_t v___x_459_; size_t v___x_460_; uint8_t v___x_461_; 
v_a_458_ = lean_ctor_get(v___x_457_, 0);
lean_inc(v_a_458_);
lean_dec_ref_known(v___x_457_, 1);
v___x_459_ = lean_ptr_addr(v_binderType_452_);
v___x_460_ = lean_ptr_addr(v_a_456_);
v___x_461_ = lean_usize_dec_eq(v___x_459_, v___x_460_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; lean_object* v___x_463_; 
lean_inc(v_binderName_451_);
lean_dec_ref_known(v___y_428_, 3);
v___x_462_ = l_Lean_Expr_lam___override(v_binderName_451_, v_a_456_, v_a_458_, v_binderInfo_454_);
v___x_463_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_414_, v_post_416_, v___x_462_, v___y_417_, v___y_418_, v___y_419_);
return v___x_463_;
}
else
{
size_t v___x_464_; size_t v___x_465_; uint8_t v___x_466_; 
v___x_464_ = lean_ptr_addr(v_body_453_);
v___x_465_ = lean_ptr_addr(v_a_458_);
v___x_466_ = lean_usize_dec_eq(v___x_464_, v___x_465_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; lean_object* v___x_468_; 
lean_inc(v_binderName_451_);
lean_dec_ref_known(v___y_428_, 3);
v___x_467_ = l_Lean_Expr_lam___override(v_binderName_451_, v_a_456_, v_a_458_, v_binderInfo_454_);
v___x_468_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_414_, v_post_416_, v___x_467_, v___y_417_, v___y_418_, v___y_419_);
return v___x_468_;
}
else
{
uint8_t v___x_469_; 
v___x_469_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_454_, v_binderInfo_454_);
if (v___x_469_ == 0)
{
lean_object* v___x_470_; lean_object* v___x_471_; 
lean_inc(v_binderName_451_);
lean_dec_ref_known(v___y_428_, 3);
v___x_470_ = l_Lean_Expr_lam___override(v_binderName_451_, v_a_456_, v_a_458_, v_binderInfo_454_);
v___x_471_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_414_, v_post_416_, v___x_470_, v___y_417_, v___y_418_, v___y_419_);
return v___x_471_;
}
else
{
lean_object* v___x_472_; 
lean_dec(v_a_458_);
lean_dec(v_a_456_);
v___x_472_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_414_, v_post_416_, v___y_428_, v___y_417_, v___y_418_, v___y_419_);
return v___x_472_;
}
}
}
}
else
{
lean_dec(v_a_456_);
lean_dec_ref_known(v___y_428_, 3);
lean_dec_ref(v_post_416_);
lean_dec_ref(v_pre_414_);
return v___x_457_;
}
}
else
{
lean_dec_ref_known(v___y_428_, 3);
lean_dec_ref(v_post_416_);
lean_dec_ref(v_pre_414_);
return v___x_455_;
}
}
case 8:
{
lean_object* v_declName_473_; lean_object* v_type_474_; lean_object* v_value_475_; lean_object* v_body_476_; uint8_t v_nondep_477_; lean_object* v___x_478_; 
v_declName_473_ = lean_ctor_get(v___y_428_, 0);
v_type_474_ = lean_ctor_get(v___y_428_, 1);
v_value_475_ = lean_ctor_get(v___y_428_, 2);
v_body_476_ = lean_ctor_get(v___y_428_, 3);
v_nondep_477_ = lean_ctor_get_uint8(v___y_428_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_474_);
lean_inc_ref(v_post_416_);
lean_inc_ref(v_pre_414_);
v___x_478_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_414_, v_post_416_, v_type_474_, v___y_417_, v___y_418_, v___y_419_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v_a_479_; lean_object* v___x_480_; 
v_a_479_ = lean_ctor_get(v___x_478_, 0);
lean_inc(v_a_479_);
lean_dec_ref_known(v___x_478_, 1);
lean_inc_ref(v_value_475_);
lean_inc_ref(v_post_416_);
lean_inc_ref(v_pre_414_);
v___x_480_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_414_, v_post_416_, v_value_475_, v___y_417_, v___y_418_, v___y_419_);
if (lean_obj_tag(v___x_480_) == 0)
{
lean_object* v_a_481_; lean_object* v___x_482_; 
v_a_481_ = lean_ctor_get(v___x_480_, 0);
lean_inc(v_a_481_);
lean_dec_ref_known(v___x_480_, 1);
lean_inc_ref(v_body_476_);
lean_inc_ref(v_post_416_);
lean_inc_ref(v_pre_414_);
v___x_482_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_414_, v_post_416_, v_body_476_, v___y_417_, v___y_418_, v___y_419_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v_a_483_; size_t v___x_484_; size_t v___x_485_; uint8_t v___x_486_; 
v_a_483_ = lean_ctor_get(v___x_482_, 0);
lean_inc(v_a_483_);
lean_dec_ref_known(v___x_482_, 1);
v___x_484_ = lean_ptr_addr(v_type_474_);
v___x_485_ = lean_ptr_addr(v_a_479_);
v___x_486_ = lean_usize_dec_eq(v___x_484_, v___x_485_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; lean_object* v___x_488_; 
lean_inc(v_declName_473_);
lean_dec_ref_known(v___y_428_, 4);
v___x_487_ = l_Lean_Expr_letE___override(v_declName_473_, v_a_479_, v_a_481_, v_a_483_, v_nondep_477_);
v___x_488_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_414_, v_post_416_, v___x_487_, v___y_417_, v___y_418_, v___y_419_);
return v___x_488_;
}
else
{
size_t v___x_489_; size_t v___x_490_; uint8_t v___x_491_; 
v___x_489_ = lean_ptr_addr(v_value_475_);
v___x_490_ = lean_ptr_addr(v_a_481_);
v___x_491_ = lean_usize_dec_eq(v___x_489_, v___x_490_);
if (v___x_491_ == 0)
{
lean_object* v___x_492_; lean_object* v___x_493_; 
lean_inc(v_declName_473_);
lean_dec_ref_known(v___y_428_, 4);
v___x_492_ = l_Lean_Expr_letE___override(v_declName_473_, v_a_479_, v_a_481_, v_a_483_, v_nondep_477_);
v___x_493_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_414_, v_post_416_, v___x_492_, v___y_417_, v___y_418_, v___y_419_);
return v___x_493_;
}
else
{
size_t v___x_494_; size_t v___x_495_; uint8_t v___x_496_; 
v___x_494_ = lean_ptr_addr(v_body_476_);
v___x_495_ = lean_ptr_addr(v_a_483_);
v___x_496_ = lean_usize_dec_eq(v___x_494_, v___x_495_);
if (v___x_496_ == 0)
{
lean_object* v___x_497_; lean_object* v___x_498_; 
lean_inc(v_declName_473_);
lean_dec_ref_known(v___y_428_, 4);
v___x_497_ = l_Lean_Expr_letE___override(v_declName_473_, v_a_479_, v_a_481_, v_a_483_, v_nondep_477_);
v___x_498_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_414_, v_post_416_, v___x_497_, v___y_417_, v___y_418_, v___y_419_);
return v___x_498_;
}
else
{
lean_object* v___x_499_; 
lean_dec(v_a_483_);
lean_dec(v_a_481_);
lean_dec(v_a_479_);
v___x_499_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_414_, v_post_416_, v___y_428_, v___y_417_, v___y_418_, v___y_419_);
return v___x_499_;
}
}
}
}
else
{
lean_dec(v_a_481_);
lean_dec(v_a_479_);
lean_dec_ref_known(v___y_428_, 4);
lean_dec_ref(v_post_416_);
lean_dec_ref(v_pre_414_);
return v___x_482_;
}
}
else
{
lean_dec(v_a_479_);
lean_dec_ref_known(v___y_428_, 4);
lean_dec_ref(v_post_416_);
lean_dec_ref(v_pre_414_);
return v___x_480_;
}
}
else
{
lean_dec_ref_known(v___y_428_, 4);
lean_dec_ref(v_post_416_);
lean_dec_ref(v_pre_414_);
return v___x_478_;
}
}
case 5:
{
lean_object* v_dummy_500_; lean_object* v_nargs_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v_dummy_500_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0);
v_nargs_501_ = l_Lean_Expr_getAppNumArgs(v___y_428_);
lean_inc(v_nargs_501_);
v___x_502_ = lean_mk_array(v_nargs_501_, v_dummy_500_);
v___x_503_ = lean_unsigned_to_nat(1u);
v___x_504_ = lean_nat_sub(v_nargs_501_, v___x_503_);
lean_dec(v_nargs_501_);
v___x_505_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4(v_pre_414_, v_post_416_, v___y_428_, v___x_502_, v___x_504_, v___y_417_, v___y_418_, v___y_419_);
return v___x_505_;
}
case 10:
{
lean_object* v_data_506_; lean_object* v_expr_507_; lean_object* v___x_508_; 
v_data_506_ = lean_ctor_get(v___y_428_, 0);
v_expr_507_ = lean_ctor_get(v___y_428_, 1);
lean_inc_ref(v_expr_507_);
lean_inc_ref(v_post_416_);
lean_inc_ref(v_pre_414_);
v___x_508_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_414_, v_post_416_, v_expr_507_, v___y_417_, v___y_418_, v___y_419_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v_a_509_; size_t v___x_510_; size_t v___x_511_; uint8_t v___x_512_; 
v_a_509_ = lean_ctor_get(v___x_508_, 0);
lean_inc(v_a_509_);
lean_dec_ref_known(v___x_508_, 1);
v___x_510_ = lean_ptr_addr(v_expr_507_);
v___x_511_ = lean_ptr_addr(v_a_509_);
v___x_512_ = lean_usize_dec_eq(v___x_510_, v___x_511_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; lean_object* v___x_514_; 
lean_inc(v_data_506_);
lean_dec_ref_known(v___y_428_, 2);
v___x_513_ = l_Lean_Expr_mdata___override(v_data_506_, v_a_509_);
v___x_514_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_414_, v_post_416_, v___x_513_, v___y_417_, v___y_418_, v___y_419_);
return v___x_514_;
}
else
{
lean_object* v___x_515_; 
lean_dec(v_a_509_);
v___x_515_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_414_, v_post_416_, v___y_428_, v___y_417_, v___y_418_, v___y_419_);
return v___x_515_;
}
}
else
{
lean_dec_ref_known(v___y_428_, 2);
lean_dec_ref(v_post_416_);
lean_dec_ref(v_pre_414_);
return v___x_508_;
}
}
case 11:
{
lean_object* v_typeName_516_; lean_object* v_idx_517_; lean_object* v_struct_518_; lean_object* v___x_519_; 
v_typeName_516_ = lean_ctor_get(v___y_428_, 0);
v_idx_517_ = lean_ctor_get(v___y_428_, 1);
v_struct_518_ = lean_ctor_get(v___y_428_, 2);
lean_inc_ref(v_struct_518_);
lean_inc_ref(v_post_416_);
lean_inc_ref(v_pre_414_);
v___x_519_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_414_, v_post_416_, v_struct_518_, v___y_417_, v___y_418_, v___y_419_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v_a_520_; size_t v___x_521_; size_t v___x_522_; uint8_t v___x_523_; 
v_a_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_a_520_);
lean_dec_ref_known(v___x_519_, 1);
v___x_521_ = lean_ptr_addr(v_struct_518_);
v___x_522_ = lean_ptr_addr(v_a_520_);
v___x_523_ = lean_usize_dec_eq(v___x_521_, v___x_522_);
if (v___x_523_ == 0)
{
lean_object* v___x_524_; lean_object* v___x_525_; 
lean_inc(v_idx_517_);
lean_inc(v_typeName_516_);
lean_dec_ref_known(v___y_428_, 3);
v___x_524_ = l_Lean_Expr_proj___override(v_typeName_516_, v_idx_517_, v_a_520_);
v___x_525_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_414_, v_post_416_, v___x_524_, v___y_417_, v___y_418_, v___y_419_);
return v___x_525_;
}
else
{
lean_object* v___x_526_; 
lean_dec(v_a_520_);
v___x_526_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_414_, v_post_416_, v___y_428_, v___y_417_, v___y_418_, v___y_419_);
return v___x_526_;
}
}
else
{
lean_dec_ref_known(v___y_428_, 3);
lean_dec_ref(v_post_416_);
lean_dec_ref(v_pre_414_);
return v___x_519_;
}
}
default: 
{
lean_object* v___x_527_; 
v___x_527_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_414_, v_post_416_, v___y_428_, v___y_417_, v___y_418_, v___y_419_);
return v___x_527_;
}
}
}
}
}
else
{
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_546_; 
lean_dec_ref(v_post_416_);
lean_dec_ref(v_e_415_);
lean_dec_ref(v_pre_414_);
v_a_539_ = lean_ctor_get(v___x_422_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_546_ == 0)
{
v___x_541_ = v___x_422_;
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_422_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_542_ == 0)
{
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_a_539_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
}
else
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
lean_dec_ref(v_post_416_);
lean_dec_ref(v_e_415_);
lean_dec_ref(v_pre_414_);
v_a_547_ = lean_ctor_get(v___x_421_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_554_ == 0)
{
v___x_549_ = v___x_421_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_421_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_a_547_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___boxed(lean_object* v___x_555_, lean_object* v_pre_556_, lean_object* v_e_557_, lean_object* v_post_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1(v___x_555_, v_pre_556_, v_e_557_, v_post_558_, v___y_559_, v___y_560_, v___y_561_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
lean_dec(v___y_559_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(lean_object* v_pre_564_, lean_object* v_post_565_, lean_object* v_e_566_, lean_object* v_a_567_, lean_object* v___y_568_, lean_object* v___y_569_){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; 
lean_inc(v_a_567_);
v___x_571_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_571_, 0, lean_box(0));
lean_closure_set(v___x_571_, 1, lean_box(0));
lean_closure_set(v___x_571_, 2, v_a_567_);
v___x_572_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(lean_box(0), v___x_571_, v___y_568_, v___y_569_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_604_; 
v_a_573_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_604_ == 0)
{
v___x_575_ = v___x_572_;
v_isShared_576_ = v_isSharedCheck_604_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_dec(v___x_572_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_604_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_577_; 
v___x_577_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(v_a_573_, v_e_566_);
lean_dec(v_a_573_);
if (lean_obj_tag(v___x_577_) == 0)
{
lean_object* v___x_578_; lean_object* v___f_579_; lean_object* v___x_580_; 
lean_del_object(v___x_575_);
v___x_578_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___closed__0));
lean_inc_ref(v_e_566_);
v___f_579_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___boxed), 8, 4);
lean_closure_set(v___f_579_, 0, v___x_578_);
lean_closure_set(v___f_579_, 1, v_pre_564_);
lean_closure_set(v___f_579_, 2, v_e_566_);
lean_closure_set(v___f_579_, 3, v_post_565_);
v___x_580_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(v___f_579_, v_a_567_, v___y_568_, v___y_569_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v_a_581_; lean_object* v___f_582_; lean_object* v___x_583_; 
v_a_581_ = lean_ctor_get(v___x_580_, 0);
lean_inc_n(v_a_581_, 2);
lean_dec_ref_known(v___x_580_, 1);
lean_inc(v_a_567_);
v___f_582_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_582_, 0, v_a_567_);
lean_closure_set(v___f_582_, 1, v_e_566_);
lean_closure_set(v___f_582_, 2, v_a_581_);
v___x_583_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(lean_box(0), v___f_582_, v___y_568_, v___y_569_);
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_590_; 
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_590_ == 0)
{
lean_object* v_unused_591_; 
v_unused_591_ = lean_ctor_get(v___x_583_, 0);
lean_dec(v_unused_591_);
v___x_585_ = v___x_583_;
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
else
{
lean_dec(v___x_583_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_588_; 
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 0, v_a_581_);
v___x_588_ = v___x_585_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_581_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
else
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_599_; 
lean_dec(v_a_581_);
v_a_592_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_599_ == 0)
{
v___x_594_ = v___x_583_;
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_583_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_a_592_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
}
else
{
lean_dec_ref(v_e_566_);
return v___x_580_;
}
}
else
{
lean_object* v_val_600_; lean_object* v___x_602_; 
lean_dec_ref(v_e_566_);
lean_dec_ref(v_post_565_);
lean_dec_ref(v_pre_564_);
v_val_600_ = lean_ctor_get(v___x_577_, 0);
lean_inc(v_val_600_);
lean_dec_ref_known(v___x_577_, 1);
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 0, v_val_600_);
v___x_602_ = v___x_575_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_val_600_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
}
else
{
lean_object* v_a_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_612_; 
lean_dec_ref(v_e_566_);
lean_dec_ref(v_post_565_);
lean_dec_ref(v_pre_564_);
v_a_605_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_612_ == 0)
{
v___x_607_ = v___x_572_;
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_a_605_);
lean_dec(v___x_572_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_610_; 
if (v_isShared_608_ == 0)
{
v___x_610_ = v___x_607_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_a_605_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(lean_object* v_pre_613_, lean_object* v_post_614_, lean_object* v_e_615_, lean_object* v_a_616_, lean_object* v___y_617_, lean_object* v___y_618_){
_start:
{
lean_object* v___x_620_; 
lean_inc_ref(v_post_614_);
lean_inc(v___y_618_);
lean_inc_ref(v___y_617_);
lean_inc_ref(v_e_615_);
v___x_620_ = lean_apply_4(v_post_614_, v_e_615_, v___y_617_, v___y_618_, lean_box(0));
if (lean_obj_tag(v___x_620_) == 0)
{
lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_639_; 
v_a_621_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_639_ == 0)
{
v___x_623_ = v___x_620_;
v_isShared_624_ = v_isSharedCheck_639_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_dec(v___x_620_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_639_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
switch(lean_obj_tag(v_a_621_))
{
case 0:
{
lean_object* v_e_625_; lean_object* v___x_627_; 
lean_dec_ref(v_e_615_);
lean_dec_ref(v_post_614_);
lean_dec_ref(v_pre_613_);
v_e_625_ = lean_ctor_get(v_a_621_, 0);
lean_inc_ref(v_e_625_);
lean_dec_ref_known(v_a_621_, 1);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 0, v_e_625_);
v___x_627_ = v___x_623_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_e_625_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
case 1:
{
lean_object* v_e_629_; lean_object* v___x_630_; 
lean_del_object(v___x_623_);
lean_dec_ref(v_e_615_);
v_e_629_ = lean_ctor_get(v_a_621_, 0);
lean_inc_ref(v_e_629_);
lean_dec_ref_known(v_a_621_, 1);
v___x_630_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_613_, v_post_614_, v_e_629_, v_a_616_, v___y_617_, v___y_618_);
return v___x_630_;
}
default: 
{
lean_object* v_e_x3f_631_; 
lean_dec_ref(v_post_614_);
lean_dec_ref(v_pre_613_);
v_e_x3f_631_ = lean_ctor_get(v_a_621_, 0);
lean_inc(v_e_x3f_631_);
lean_dec_ref_known(v_a_621_, 1);
if (lean_obj_tag(v_e_x3f_631_) == 0)
{
lean_object* v___x_633_; 
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 0, v_e_615_);
v___x_633_ = v___x_623_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_e_615_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
else
{
lean_object* v_val_635_; lean_object* v___x_637_; 
lean_dec_ref(v_e_615_);
v_val_635_ = lean_ctor_get(v_e_x3f_631_, 0);
lean_inc(v_val_635_);
lean_dec_ref_known(v_e_x3f_631_, 1);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 0, v_val_635_);
v___x_637_ = v___x_623_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_val_635_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
}
}
}
else
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
lean_dec_ref(v_e_615_);
lean_dec_ref(v_post_614_);
lean_dec_ref(v_pre_613_);
v_a_640_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_647_ == 0)
{
v___x_642_ = v___x_620_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_620_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_640_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_648_, lean_object* v_post_649_, lean_object* v_e_650_, lean_object* v_a_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_648_, v_post_649_, v_e_650_, v_a_651_, v___y_652_, v___y_653_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec(v_a_651_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_656_, lean_object* v_post_657_, lean_object* v_sz_658_, lean_object* v_i_659_, lean_object* v_bs_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
size_t v_sz_boxed_665_; size_t v_i_boxed_666_; lean_object* v_res_667_; 
v_sz_boxed_665_ = lean_unbox_usize(v_sz_658_);
lean_dec(v_sz_658_);
v_i_boxed_666_ = lean_unbox_usize(v_i_659_);
lean_dec(v_i_659_);
v_res_667_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1(v_pre_656_, v_post_657_, v_sz_boxed_665_, v_i_boxed_666_, v_bs_660_, v___y_661_, v___y_662_, v___y_663_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_668_, lean_object* v_post_669_, lean_object* v_x_670_, lean_object* v_x_671_, lean_object* v_x_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4(v_pre_668_, v_post_669_, v_x_670_, v_x_671_, v_x_672_, v___y_673_, v___y_674_, v___y_675_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v___y_673_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___boxed(lean_object* v_pre_678_, lean_object* v_post_679_, lean_object* v_e_680_, lean_object* v_a_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_678_, v_post_679_, v_e_680_, v_a_681_, v___y_682_, v___y_683_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v_a_681_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(lean_object* v_00_u03b1_686_, lean_object* v_x_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_691_ = lean_apply_1(v_x_687_, lean_box(0));
v___x_692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0___boxed(lean_object* v_00_u03b1_693_, lean_object* v_x_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(v_00_u03b1_693_, v_x_694_, v___y_695_, v___y_696_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
return v_res_698_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0(void){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_699_ = lean_box(0);
v___x_700_ = lean_unsigned_to_nat(16u);
v___x_701_ = lean_mk_array(v___x_700_, v___x_699_);
return v___x_701_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1(void){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_702_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0);
v___x_703_ = lean_unsigned_to_nat(0u);
v___x_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
lean_ctor_set(v___x_704_, 1, v___x_702_);
return v___x_704_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2(void){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1, &l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1);
v___x_706_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_706_, 0, lean_box(0));
lean_closure_set(v___x_706_, 1, lean_box(0));
lean_closure_set(v___x_706_, 2, v___x_705_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0(lean_object* v_input_707_, lean_object* v_pre_708_, lean_object* v_post_709_, lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v_a_715_; lean_object* v___x_716_; 
v___x_713_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2);
v___x_714_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(lean_box(0), v___x_713_, v___y_710_, v___y_711_);
v_a_715_ = lean_ctor_get(v___x_714_, 0);
lean_inc(v_a_715_);
lean_dec_ref(v___x_714_);
v___x_716_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_708_, v_post_709_, v_input_707_, v_a_715_, v___y_710_, v___y_711_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v_a_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_726_; 
v_a_717_ = lean_ctor_get(v___x_716_, 0);
lean_inc(v_a_717_);
lean_dec_ref_known(v___x_716_, 1);
v___x_718_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_718_, 0, lean_box(0));
lean_closure_set(v___x_718_, 1, lean_box(0));
lean_closure_set(v___x_718_, 2, v_a_715_);
v___x_719_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(lean_box(0), v___x_718_, v___y_710_, v___y_711_);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_726_ == 0)
{
lean_object* v_unused_727_; 
v_unused_727_ = lean_ctor_get(v___x_719_, 0);
lean_dec(v_unused_727_);
v___x_721_ = v___x_719_;
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
else
{
lean_dec(v___x_719_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_724_; 
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 0, v_a_717_);
v___x_724_ = v___x_721_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_a_717_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
else
{
lean_dec(v_a_715_);
return v___x_716_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___boxed(lean_object* v_input_728_, lean_object* v_pre_729_, lean_object* v_post_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0(v_input_728_, v_pre_729_, v_post_730_, v___y_731_, v___y_732_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam(lean_object* v_type_737_, lean_object* v_a_738_, lean_object* v_a_739_){
_start:
{
lean_object* v___f_741_; lean_object* v___f_742_; lean_object* v___x_743_; 
v___f_741_ = ((lean_object*)(l_Lean_Meta_elimOptParam___closed__0));
v___f_742_ = ((lean_object*)(l_Lean_Meta_elimOptParam___closed__1));
v___x_743_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0(v_type_737_, v___f_741_, v___f_742_, v_a_738_, v_a_739_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam___boxed(lean_object* v_type_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_Lean_Meta_elimOptParam(v_type_744_, v_a_745_, v_a_746_);
lean_dec(v_a_746_);
lean_dec_ref(v_a_745_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_749_, lean_object* v_m_750_, lean_object* v_a_751_){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(v_m_750_, v_a_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_753_, lean_object* v_m_754_, lean_object* v_a_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(v_00_u03b2_753_, v_m_754_, v_a_755_);
lean_dec_ref(v_a_755_);
lean_dec_ref(v_m_754_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_757_, lean_object* v_ref_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_758_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_763_, lean_object* v_ref_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_763_, v_ref_764_, v___y_765_, v___y_766_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8(lean_object* v_00_u03b1_769_, lean_object* v___y_770_, lean_object* v___y_771_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg();
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___boxed(lean_object* v_00_u03b1_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_774_, v___y_775_, v___y_776_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_779_, lean_object* v_x_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(v_x_780_, v___y_781_, v___y_782_, v___y_783_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_786_, lean_object* v_x_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5(v_00_u03b1_786_, v_x_787_, v___y_788_, v___y_789_, v___y_790_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v___y_788_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_793_, lean_object* v_m_794_, lean_object* v_a_795_, lean_object* v_b_796_){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6___redArg(v_m_794_, v_a_795_, v_b_796_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_798_, lean_object* v_a_799_, lean_object* v_x_800_){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(v_a_799_, v_x_800_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_802_, lean_object* v_a_803_, lean_object* v_x_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_802_, v_a_803_, v_x_804_);
lean_dec(v_x_804_);
lean_dec_ref(v_a_803_);
return v_res_805_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_806_, lean_object* v_a_807_, lean_object* v_x_808_){
_start:
{
uint8_t v___x_809_; 
v___x_809_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___redArg(v_a_807_, v_x_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___boxed(lean_object* v_00_u03b2_810_, lean_object* v_a_811_, lean_object* v_x_812_){
_start:
{
uint8_t v_res_813_; lean_object* v_r_814_; 
v_res_813_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_810_, v_a_811_, v_x_812_);
lean_dec(v_x_812_);
lean_dec_ref(v_a_811_);
v_r_814_ = lean_box(v_res_813_);
return v_r_814_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_815_, lean_object* v_data_816_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11___redArg(v_data_816_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__12(lean_object* v_00_u03b2_818_, lean_object* v_a_819_, lean_object* v_b_820_, lean_object* v_x_821_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__12___redArg(v_a_819_, v_b_820_, v_x_821_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12(lean_object* v_00_u03b2_823_, lean_object* v_i_824_, lean_object* v_source_825_, lean_object* v_target_826_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v_i_824_, v_source_825_, v_target_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_828_, lean_object* v_x_829_, lean_object* v_x_830_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_x_829_, v_x_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0(uint8_t v_skipIfPropOrEq_832_, lean_object* v_as_833_, size_t v_sz_834_, size_t v_i_835_, lean_object* v_b_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
lean_object* v_a_843_; uint8_t v___x_847_; 
v___x_847_ = lean_usize_dec_lt(v_i_835_, v_sz_834_);
if (v___x_847_ == 0)
{
lean_object* v___x_848_; 
v___x_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_848_, 0, v_b_836_);
return v___x_848_;
}
else
{
lean_object* v_snd_849_; lean_object* v_fst_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_928_; 
v_snd_849_ = lean_ctor_get(v_b_836_, 1);
v_fst_850_ = lean_ctor_get(v_b_836_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v_b_836_);
if (v_isSharedCheck_928_ == 0)
{
v___x_852_ = v_b_836_;
v_isShared_853_ = v_isSharedCheck_928_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_snd_849_);
lean_inc(v_fst_850_);
lean_dec(v_b_836_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_928_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v_array_854_; lean_object* v_start_855_; lean_object* v_stop_856_; uint8_t v___x_857_; 
v_array_854_ = lean_ctor_get(v_snd_849_, 0);
v_start_855_ = lean_ctor_get(v_snd_849_, 1);
v_stop_856_ = lean_ctor_get(v_snd_849_, 2);
v___x_857_ = lean_nat_dec_lt(v_start_855_, v_stop_856_);
if (v___x_857_ == 0)
{
lean_object* v___x_859_; 
if (v_isShared_853_ == 0)
{
v___x_859_ = v___x_852_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_fst_850_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v_snd_849_);
v___x_859_ = v_reuseFailAlloc_861_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
lean_object* v___x_860_; 
v___x_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_860_, 0, v___x_859_);
return v___x_860_;
}
}
else
{
lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_924_; 
lean_inc(v_stop_856_);
lean_inc(v_start_855_);
lean_inc_ref(v_array_854_);
v_isSharedCheck_924_ = !lean_is_exclusive(v_snd_849_);
if (v_isSharedCheck_924_ == 0)
{
lean_object* v_unused_925_; lean_object* v_unused_926_; lean_object* v_unused_927_; 
v_unused_925_ = lean_ctor_get(v_snd_849_, 2);
lean_dec(v_unused_925_);
v_unused_926_ = lean_ctor_get(v_snd_849_, 1);
lean_dec(v_unused_926_);
v_unused_927_ = lean_ctor_get(v_snd_849_, 0);
lean_dec(v_unused_927_);
v___x_863_ = v_snd_849_;
v_isShared_864_ = v_isSharedCheck_924_;
goto v_resetjp_862_;
}
else
{
lean_dec(v_snd_849_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_924_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v_a_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_870_; 
v_a_865_ = lean_array_uget_borrowed(v_as_833_, v_i_835_);
v___x_866_ = lean_array_fget(v_array_854_, v_start_855_);
v___x_867_ = lean_unsigned_to_nat(1u);
v___x_868_ = lean_nat_add(v_start_855_, v___x_867_);
lean_dec(v_start_855_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 1, v___x_868_);
v___x_870_ = v___x_863_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_array_854_);
lean_ctor_set(v_reuseFailAlloc_923_, 1, v___x_868_);
lean_ctor_set(v_reuseFailAlloc_923_, 2, v_stop_856_);
v___x_870_ = v_reuseFailAlloc_923_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
lean_object* v___x_871_; 
lean_inc(v___y_840_);
lean_inc_ref(v___y_839_);
lean_inc(v___y_838_);
lean_inc_ref(v___y_837_);
lean_inc(v_a_865_);
v___x_871_ = lean_infer_type(v_a_865_, v___y_837_, v___y_838_, v___y_839_, v___y_840_);
if (lean_obj_tag(v___x_871_) == 0)
{
if (v_skipIfPropOrEq_832_ == 0)
{
lean_object* v___x_872_; 
lean_dec_ref_known(v___x_871_, 1);
lean_inc(v_a_865_);
v___x_872_ = l_Lean_Meta_mkEqHEq(v_a_865_, v___x_866_, v___y_837_, v___y_838_, v___y_839_, v___y_840_);
if (lean_obj_tag(v___x_872_) == 0)
{
lean_object* v_a_873_; lean_object* v___x_874_; lean_object* v___x_876_; 
v_a_873_ = lean_ctor_get(v___x_872_, 0);
lean_inc(v_a_873_);
lean_dec_ref_known(v___x_872_, 1);
v___x_874_ = lean_array_push(v_fst_850_, v_a_873_);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 1, v___x_870_);
lean_ctor_set(v___x_852_, 0, v___x_874_);
v___x_876_ = v___x_852_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_874_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v___x_870_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
v_a_843_ = v___x_876_;
goto v___jp_842_;
}
}
else
{
lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_885_; 
lean_dec_ref(v___x_870_);
lean_del_object(v___x_852_);
lean_dec(v_fst_850_);
v_a_878_ = lean_ctor_get(v___x_872_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_885_ == 0)
{
v___x_880_ = v___x_872_;
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_dec(v___x_872_);
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
else
{
lean_object* v_a_886_; lean_object* v___x_887_; 
v_a_886_ = lean_ctor_get(v___x_871_, 0);
lean_inc(v_a_886_);
lean_dec_ref_known(v___x_871_, 1);
v___x_887_ = l_Lean_Meta_isProp(v_a_886_, v___y_837_, v___y_838_, v___y_839_, v___y_840_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v_a_888_; uint8_t v___x_893_; 
v_a_888_ = lean_ctor_get(v___x_887_, 0);
lean_inc(v_a_888_);
lean_dec_ref_known(v___x_887_, 1);
v___x_893_ = lean_unbox(v_a_888_);
lean_dec(v_a_888_);
if (v___x_893_ == 0)
{
uint8_t v___x_894_; 
v___x_894_ = lean_expr_eqv(v_a_865_, v___x_866_);
if (v___x_894_ == 0)
{
lean_object* v___x_895_; 
lean_del_object(v___x_852_);
lean_inc(v_a_865_);
v___x_895_ = l_Lean_Meta_mkEqHEq(v_a_865_, v___x_866_, v___y_837_, v___y_838_, v___y_839_, v___y_840_);
if (lean_obj_tag(v___x_895_) == 0)
{
lean_object* v_a_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v_a_896_ = lean_ctor_get(v___x_895_, 0);
lean_inc(v_a_896_);
lean_dec_ref_known(v___x_895_, 1);
v___x_897_ = lean_array_push(v_fst_850_, v_a_896_);
v___x_898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_897_);
lean_ctor_set(v___x_898_, 1, v___x_870_);
v_a_843_ = v___x_898_;
goto v___jp_842_;
}
else
{
lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_906_; 
lean_dec_ref(v___x_870_);
lean_dec(v_fst_850_);
v_a_899_ = lean_ctor_get(v___x_895_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_906_ == 0)
{
v___x_901_ = v___x_895_;
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v___x_895_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_904_; 
if (v_isShared_902_ == 0)
{
v___x_904_ = v___x_901_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_a_899_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
}
else
{
lean_dec(v___x_866_);
goto v___jp_889_;
}
}
else
{
lean_dec(v___x_866_);
goto v___jp_889_;
}
v___jp_889_:
{
lean_object* v___x_891_; 
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 1, v___x_870_);
v___x_891_ = v___x_852_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_fst_850_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v___x_870_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
v_a_843_ = v___x_891_;
goto v___jp_842_;
}
}
}
else
{
lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_914_; 
lean_dec_ref(v___x_870_);
lean_dec(v___x_866_);
lean_del_object(v___x_852_);
lean_dec(v_fst_850_);
v_a_907_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_914_ == 0)
{
v___x_909_ = v___x_887_;
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_887_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_912_; 
if (v_isShared_910_ == 0)
{
v___x_912_ = v___x_909_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_a_907_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
}
}
else
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_922_; 
lean_dec_ref(v___x_870_);
lean_dec(v___x_866_);
lean_del_object(v___x_852_);
lean_dec(v_fst_850_);
v_a_915_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_922_ == 0)
{
v___x_917_ = v___x_871_;
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_871_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_920_; 
if (v_isShared_918_ == 0)
{
v___x_920_ = v___x_917_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_a_915_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
}
}
}
}
v___jp_842_:
{
size_t v___x_844_; size_t v___x_845_; 
v___x_844_ = ((size_t)1ULL);
v___x_845_ = lean_usize_add(v_i_835_, v___x_844_);
v_i_835_ = v___x_845_;
v_b_836_ = v_a_843_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0___boxed(lean_object* v_skipIfPropOrEq_929_, lean_object* v_as_930_, lean_object* v_sz_931_, lean_object* v_i_932_, lean_object* v_b_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
uint8_t v_skipIfPropOrEq_boxed_939_; size_t v_sz_boxed_940_; size_t v_i_boxed_941_; lean_object* v_res_942_; 
v_skipIfPropOrEq_boxed_939_ = lean_unbox(v_skipIfPropOrEq_929_);
v_sz_boxed_940_ = lean_unbox_usize(v_sz_931_);
lean_dec(v_sz_931_);
v_i_boxed_941_ = lean_unbox_usize(v_i_932_);
lean_dec(v_i_932_);
v_res_942_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0(v_skipIfPropOrEq_boxed_939_, v_as_930_, v_sz_boxed_940_, v_i_boxed_941_, v_b_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec_ref(v_as_930_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(lean_object* v_args1_945_, lean_object* v_args2_946_, uint8_t v_skipIfPropOrEq_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_){
_start:
{
lean_object* v___x_953_; lean_object* v_eqs_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; size_t v_sz_958_; size_t v___x_959_; lean_object* v___x_960_; 
v___x_953_ = lean_unsigned_to_nat(0u);
v_eqs_954_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_955_ = lean_array_get_size(v_args2_946_);
v___x_956_ = l_Array_toSubarray___redArg(v_args2_946_, v___x_953_, v___x_955_);
v___x_957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_957_, 0, v_eqs_954_);
lean_ctor_set(v___x_957_, 1, v___x_956_);
v_sz_958_ = lean_array_size(v_args1_945_);
v___x_959_ = ((size_t)0ULL);
v___x_960_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0(v_skipIfPropOrEq_947_, v_args1_945_, v_sz_958_, v___x_959_, v___x_957_, v_a_948_, v_a_949_, v_a_950_, v_a_951_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_969_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_969_ == 0)
{
v___x_963_ = v___x_960_;
v_isShared_964_ = v_isSharedCheck_969_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_960_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_969_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v_fst_965_; lean_object* v___x_967_; 
v_fst_965_ = lean_ctor_get(v_a_961_, 0);
lean_inc(v_fst_965_);
lean_dec(v_a_961_);
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 0, v_fst_965_);
v___x_967_ = v___x_963_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_fst_965_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
}
else
{
lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_977_; 
v_a_970_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_977_ == 0)
{
v___x_972_ = v___x_960_;
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_960_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_975_; 
if (v_isShared_973_ == 0)
{
v___x_975_ = v___x_972_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_a_970_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___boxed(lean_object* v_args1_978_, lean_object* v_args2_979_, lean_object* v_skipIfPropOrEq_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_){
_start:
{
uint8_t v_skipIfPropOrEq_boxed_986_; lean_object* v_res_987_; 
v_skipIfPropOrEq_boxed_986_ = lean_unbox(v_skipIfPropOrEq_980_);
v_res_987_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v_args1_978_, v_args2_979_, v_skipIfPropOrEq_boxed_986_, v_a_981_, v_a_982_, v_a_983_, v_a_984_);
lean_dec(v_a_984_);
lean_dec_ref(v_a_983_);
lean_dec(v_a_982_);
lean_dec_ref(v_a_981_);
lean_dec_ref(v_args1_978_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0(lean_object* v_k_988_, lean_object* v_b_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
lean_object* v___x_995_; 
lean_inc(v___y_993_);
lean_inc_ref(v___y_992_);
lean_inc(v___y_991_);
lean_inc_ref(v___y_990_);
v___x_995_ = lean_apply_6(v_k_988_, v_b_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, lean_box(0));
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0___boxed(lean_object* v_k_996_, lean_object* v_b_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0(v_k_996_, v_b_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(lean_object* v_name_1004_, uint8_t v_bi_1005_, lean_object* v_type_1006_, lean_object* v_k_1007_, uint8_t v_kind_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
lean_object* v___f_1014_; lean_object* v___x_1015_; 
v___f_1014_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1014_, 0, v_k_1007_);
v___x_1015_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1004_, v_bi_1005_, v_type_1006_, v___f_1014_, v_kind_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_);
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1023_; 
v_a_1016_ = lean_ctor_get(v___x_1015_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1018_ = v___x_1015_;
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_dec(v___x_1015_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1021_; 
if (v_isShared_1019_ == 0)
{
v___x_1021_ = v___x_1018_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_a_1016_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
else
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1031_; 
v_a_1024_ = lean_ctor_get(v___x_1015_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1026_ = v___x_1015_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_1015_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1029_; 
if (v_isShared_1027_ == 0)
{
v___x_1029_ = v___x_1026_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_a_1024_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___boxed(lean_object* v_name_1032_, lean_object* v_bi_1033_, lean_object* v_type_1034_, lean_object* v_k_1035_, lean_object* v_kind_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_){
_start:
{
uint8_t v_bi_boxed_1042_; uint8_t v_kind_boxed_1043_; lean_object* v_res_1044_; 
v_bi_boxed_1042_ = lean_unbox(v_bi_1033_);
v_kind_boxed_1043_ = lean_unbox(v_kind_1036_);
v_res_1044_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_name_1032_, v_bi_boxed_1042_, v_type_1034_, v_k_1035_, v_kind_boxed_1043_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0(lean_object* v_00_u03b1_1045_, lean_object* v_name_1046_, uint8_t v_bi_1047_, lean_object* v_type_1048_, lean_object* v_k_1049_, uint8_t v_kind_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v___x_1056_; 
v___x_1056_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_name_1046_, v_bi_1047_, v_type_1048_, v_k_1049_, v_kind_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___boxed(lean_object* v_00_u03b1_1057_, lean_object* v_name_1058_, lean_object* v_bi_1059_, lean_object* v_type_1060_, lean_object* v_k_1061_, lean_object* v_kind_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_){
_start:
{
uint8_t v_bi_boxed_1068_; uint8_t v_kind_boxed_1069_; lean_object* v_res_1070_; 
v_bi_boxed_1068_ = lean_unbox(v_bi_1059_);
v_kind_boxed_1069_ = lean_unbox(v_kind_1062_);
v_res_1070_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0(v_00_u03b1_1057_, v_name_1058_, v_bi_boxed_1068_, v_type_1060_, v_k_1061_, v_kind_boxed_1069_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
lean_dec(v___y_1066_);
lean_dec_ref(v___y_1065_);
lean_dec(v___y_1064_);
lean_dec_ref(v___y_1063_);
return v_res_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(lean_object* v_msgData_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v___x_1077_; lean_object* v_env_1078_; lean_object* v___x_1079_; lean_object* v_toCold_1080_; lean_object* v_mctx_1081_; lean_object* v_lctx_1082_; lean_object* v_options_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1077_ = lean_st_ref_get(v___y_1075_);
v_env_1078_ = lean_ctor_get(v___x_1077_, 0);
lean_inc_ref(v_env_1078_);
lean_dec(v___x_1077_);
v___x_1079_ = lean_st_ref_get(v___y_1073_);
v_toCold_1080_ = lean_ctor_get(v___y_1074_, 0);
v_mctx_1081_ = lean_ctor_get(v___x_1079_, 0);
lean_inc_ref(v_mctx_1081_);
lean_dec(v___x_1079_);
v_lctx_1082_ = lean_ctor_get(v___y_1072_, 2);
v_options_1083_ = lean_ctor_get(v_toCold_1080_, 2);
lean_inc_ref(v_options_1083_);
lean_inc_ref(v_lctx_1082_);
v___x_1084_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1084_, 0, v_env_1078_);
lean_ctor_set(v___x_1084_, 1, v_mctx_1081_);
lean_ctor_set(v___x_1084_, 2, v_lctx_1082_);
lean_ctor_set(v___x_1084_, 3, v_options_1083_);
v___x_1085_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1084_);
lean_ctor_set(v___x_1085_, 1, v_msgData_1071_);
v___x_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1085_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1___boxed(lean_object* v_msgData_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_){
_start:
{
lean_object* v_res_1093_; 
v_res_1093_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msgData_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(lean_object* v_msg_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v_ref_1100_; lean_object* v___x_1101_; lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1110_; 
v_ref_1100_ = lean_ctor_get(v___y_1097_, 2);
v___x_1101_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msg_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_);
v_a_1102_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1104_ = v___x_1101_;
v_isShared_1105_ = v_isSharedCheck_1110_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1101_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1110_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1106_; lean_object* v___x_1108_; 
lean_inc(v_ref_1100_);
v___x_1106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1106_, 0, v_ref_1100_);
lean_ctor_set(v___x_1106_, 1, v_a_1102_);
if (v_isShared_1105_ == 0)
{
lean_ctor_set_tag(v___x_1104_, 1);
lean_ctor_set(v___x_1104_, 0, v___x_1106_);
v___x_1108_ = v___x_1104_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v___x_1106_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg___boxed(lean_object* v_msg_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v_msg_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0___boxed(lean_object* v_i_1118_, lean_object* v_body_1119_, lean_object* v_args2_1120_, lean_object* v_args2New_1121_, lean_object* v_ctorVal_1122_, lean_object* v_useEq_1123_, lean_object* v_args1_1124_, lean_object* v_resultType_1125_, lean_object* v_k_1126_, lean_object* v_arg2_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
uint8_t v_useEq_boxed_1133_; lean_object* v_res_1134_; 
v_useEq_boxed_1133_ = lean_unbox(v_useEq_1123_);
v_res_1134_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0(v_i_1118_, v_body_1119_, v_args2_1120_, v_args2New_1121_, v_ctorVal_1122_, v_useEq_boxed_1133_, v_args1_1124_, v_resultType_1125_, v_k_1126_, v_arg2_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec_ref(v_body_1119_);
lean_dec(v_i_1118_);
return v_res_1134_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1(void){
_start:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1136_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__0));
v___x_1137_ = l_Lean_stringToMessageData(v___x_1136_);
return v___x_1137_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3(void){
_start:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1139_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__2));
v___x_1140_ = l_Lean_stringToMessageData(v___x_1139_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(lean_object* v_ctorVal_1141_, uint8_t v_useEq_1142_, lean_object* v_args1_1143_, lean_object* v_resultType_1144_, lean_object* v_k_1145_, lean_object* v_i_1146_, lean_object* v_type_1147_, lean_object* v_args2_1148_, lean_object* v_args2New_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_){
_start:
{
lean_object* v___x_1155_; uint8_t v___x_1156_; 
v___x_1155_ = lean_array_get_size(v_args1_1143_);
v___x_1156_ = lean_nat_dec_lt(v_i_1146_, v___x_1155_);
if (v___x_1156_ == 0)
{
lean_object* v___x_1157_; 
lean_dec_ref(v_type_1147_);
lean_dec(v_i_1146_);
lean_dec_ref(v_resultType_1144_);
lean_dec_ref(v_args1_1143_);
lean_dec_ref(v_ctorVal_1141_);
lean_inc(v_a_1153_);
lean_inc_ref(v_a_1152_);
lean_inc(v_a_1151_);
lean_inc_ref(v_a_1150_);
v___x_1157_ = lean_apply_7(v_k_1145_, v_args2_1148_, v_args2New_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, lean_box(0));
return v___x_1157_;
}
else
{
lean_object* v___x_1158_; 
lean_inc(v_a_1153_);
lean_inc_ref(v_a_1152_);
lean_inc(v_a_1151_);
lean_inc_ref(v_a_1150_);
v___x_1158_ = lean_whnf(v_type_1147_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; 
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
lean_inc(v_a_1159_);
lean_dec_ref_known(v___x_1158_, 1);
if (lean_obj_tag(v_a_1159_) == 7)
{
lean_object* v_binderName_1160_; lean_object* v_binderType_1161_; lean_object* v_body_1162_; lean_object* v_lctx_1163_; lean_object* v___x_1164_; uint8_t v___x_1165_; 
v_binderName_1160_ = lean_ctor_get(v_a_1159_, 0);
lean_inc(v_binderName_1160_);
v_binderType_1161_ = lean_ctor_get(v_a_1159_, 1);
lean_inc_ref(v_binderType_1161_);
v_body_1162_ = lean_ctor_get(v_a_1159_, 2);
lean_inc_ref(v_body_1162_);
lean_dec_ref_known(v_a_1159_, 3);
v_lctx_1163_ = lean_ctor_get(v_a_1150_, 2);
v___x_1164_ = lean_array_fget_borrowed(v_args1_1143_, v_i_1146_);
lean_inc(v___x_1164_);
lean_inc_ref(v_lctx_1163_);
v___x_1165_ = l_Lean_Meta_occursOrInType(v_lctx_1163_, v___x_1164_, v_resultType_1144_);
if (v___x_1165_ == 0)
{
lean_object* v___x_1166_; lean_object* v___f_1167_; uint8_t v___y_1169_; 
v___x_1166_ = lean_box(v_useEq_1142_);
v___f_1167_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0___boxed), 15, 9);
lean_closure_set(v___f_1167_, 0, v_i_1146_);
lean_closure_set(v___f_1167_, 1, v_body_1162_);
lean_closure_set(v___f_1167_, 2, v_args2_1148_);
lean_closure_set(v___f_1167_, 3, v_args2New_1149_);
lean_closure_set(v___f_1167_, 4, v_ctorVal_1141_);
lean_closure_set(v___f_1167_, 5, v___x_1166_);
lean_closure_set(v___f_1167_, 6, v_args1_1143_);
lean_closure_set(v___f_1167_, 7, v_resultType_1144_);
lean_closure_set(v___f_1167_, 8, v_k_1145_);
if (v_useEq_1142_ == 0)
{
uint8_t v___x_1172_; 
v___x_1172_ = 1;
v___y_1169_ = v___x_1172_;
goto v___jp_1168_;
}
else
{
uint8_t v___x_1173_; 
v___x_1173_ = 0;
v___y_1169_ = v___x_1173_;
goto v___jp_1168_;
}
v___jp_1168_:
{
uint8_t v___x_1170_; lean_object* v___x_1171_; 
v___x_1170_ = 0;
v___x_1171_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_binderName_1160_, v___y_1169_, v_binderType_1161_, v___f_1167_, v___x_1170_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_);
return v___x_1171_;
}
}
else
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
lean_dec_ref(v_binderType_1161_);
lean_dec(v_binderName_1160_);
v___x_1174_ = lean_unsigned_to_nat(1u);
v___x_1175_ = lean_nat_add(v_i_1146_, v___x_1174_);
lean_dec(v_i_1146_);
v___x_1176_ = lean_expr_instantiate1(v_body_1162_, v___x_1164_);
lean_dec_ref(v_body_1162_);
lean_inc(v___x_1164_);
v___x_1177_ = lean_array_push(v_args2_1148_, v___x_1164_);
v_i_1146_ = v___x_1175_;
v_type_1147_ = v___x_1176_;
v_args2_1148_ = v___x_1177_;
goto _start;
}
}
else
{
lean_object* v_toConstantVal_1179_; lean_object* v_name_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
lean_dec(v_a_1159_);
lean_dec_ref(v_args2New_1149_);
lean_dec_ref(v_args2_1148_);
lean_dec(v_i_1146_);
lean_dec_ref(v_k_1145_);
lean_dec_ref(v_resultType_1144_);
lean_dec_ref(v_args1_1143_);
v_toConstantVal_1179_ = lean_ctor_get(v_ctorVal_1141_, 0);
lean_inc_ref(v_toConstantVal_1179_);
lean_dec_ref(v_ctorVal_1141_);
v_name_1180_ = lean_ctor_get(v_toConstantVal_1179_, 0);
lean_inc(v_name_1180_);
lean_dec_ref(v_toConstantVal_1179_);
v___x_1181_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1);
v___x_1182_ = l_Lean_MessageData_ofName(v_name_1180_);
v___x_1183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1181_);
lean_ctor_set(v___x_1183_, 1, v___x_1182_);
v___x_1184_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_1185_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1183_);
lean_ctor_set(v___x_1185_, 1, v___x_1184_);
v___x_1186_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_1185_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_);
return v___x_1186_;
}
}
else
{
lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1194_; 
lean_dec_ref(v_args2New_1149_);
lean_dec_ref(v_args2_1148_);
lean_dec(v_i_1146_);
lean_dec_ref(v_k_1145_);
lean_dec_ref(v_resultType_1144_);
lean_dec_ref(v_args1_1143_);
lean_dec_ref(v_ctorVal_1141_);
v_a_1187_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1189_ = v___x_1158_;
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1158_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1192_; 
if (v_isShared_1190_ == 0)
{
v___x_1192_ = v___x_1189_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_a_1187_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0(lean_object* v_i_1195_, lean_object* v_body_1196_, lean_object* v_args2_1197_, lean_object* v_args2New_1198_, lean_object* v_ctorVal_1199_, uint8_t v_useEq_1200_, lean_object* v_args1_1201_, lean_object* v_resultType_1202_, lean_object* v_k_1203_, lean_object* v_arg2_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1210_ = lean_unsigned_to_nat(1u);
v___x_1211_ = lean_nat_add(v_i_1195_, v___x_1210_);
v___x_1212_ = lean_expr_instantiate1(v_body_1196_, v_arg2_1204_);
lean_inc_ref(v_arg2_1204_);
v___x_1213_ = lean_array_push(v_args2_1197_, v_arg2_1204_);
v___x_1214_ = lean_array_push(v_args2New_1198_, v_arg2_1204_);
v___x_1215_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(v_ctorVal_1199_, v_useEq_1200_, v_args1_1201_, v_resultType_1202_, v_k_1203_, v___x_1211_, v___x_1212_, v___x_1213_, v___x_1214_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___boxed(lean_object* v_ctorVal_1216_, lean_object* v_useEq_1217_, lean_object* v_args1_1218_, lean_object* v_resultType_1219_, lean_object* v_k_1220_, lean_object* v_i_1221_, lean_object* v_type_1222_, lean_object* v_args2_1223_, lean_object* v_args2New_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_){
_start:
{
uint8_t v_useEq_boxed_1230_; lean_object* v_res_1231_; 
v_useEq_boxed_1230_ = lean_unbox(v_useEq_1217_);
v_res_1231_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(v_ctorVal_1216_, v_useEq_boxed_1230_, v_args1_1218_, v_resultType_1219_, v_k_1220_, v_i_1221_, v_type_1222_, v_args2_1223_, v_args2New_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_);
lean_dec(v_a_1228_);
lean_dec_ref(v_a_1227_);
lean_dec(v_a_1226_);
lean_dec_ref(v_a_1225_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1(lean_object* v_00_u03b1_1232_, lean_object* v_msg_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
lean_object* v___x_1239_; 
v___x_1239_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v_msg_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_);
return v___x_1239_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___boxed(lean_object* v_00_u03b1_1240_, lean_object* v_msg_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1(v_00_u03b1_1240_, v_msg_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_match__1_splitter___redArg(lean_object* v_____x_1248_, lean_object* v_h__1_1249_, lean_object* v_h__2_1250_){
_start:
{
if (lean_obj_tag(v_____x_1248_) == 7)
{
lean_object* v_binderName_1251_; lean_object* v_binderType_1252_; lean_object* v_body_1253_; uint8_t v_binderInfo_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
lean_dec(v_h__2_1250_);
v_binderName_1251_ = lean_ctor_get(v_____x_1248_, 0);
lean_inc(v_binderName_1251_);
v_binderType_1252_ = lean_ctor_get(v_____x_1248_, 1);
lean_inc_ref(v_binderType_1252_);
v_body_1253_ = lean_ctor_get(v_____x_1248_, 2);
lean_inc_ref(v_body_1253_);
v_binderInfo_1254_ = lean_ctor_get_uint8(v_____x_1248_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_____x_1248_, 3);
v___x_1255_ = lean_box(v_binderInfo_1254_);
v___x_1256_ = lean_apply_4(v_h__1_1249_, v_binderName_1251_, v_binderType_1252_, v_body_1253_, v___x_1255_);
return v___x_1256_;
}
else
{
lean_object* v___x_1257_; 
lean_dec(v_h__1_1249_);
v___x_1257_ = lean_apply_2(v_h__2_1250_, v_____x_1248_, lean_box(0));
return v___x_1257_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_match__1_splitter(lean_object* v_motive_1258_, lean_object* v_____x_1259_, lean_object* v_h__1_1260_, lean_object* v_h__2_1261_){
_start:
{
if (lean_obj_tag(v_____x_1259_) == 7)
{
lean_object* v_binderName_1262_; lean_object* v_binderType_1263_; lean_object* v_body_1264_; uint8_t v_binderInfo_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
lean_dec(v_h__2_1261_);
v_binderName_1262_ = lean_ctor_get(v_____x_1259_, 0);
lean_inc(v_binderName_1262_);
v_binderType_1263_ = lean_ctor_get(v_____x_1259_, 1);
lean_inc_ref(v_binderType_1263_);
v_body_1264_ = lean_ctor_get(v_____x_1259_, 2);
lean_inc_ref(v_body_1264_);
v_binderInfo_1265_ = lean_ctor_get_uint8(v_____x_1259_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_____x_1259_, 3);
v___x_1266_ = lean_box(v_binderInfo_1265_);
v___x_1267_ = lean_apply_4(v_h__1_1260_, v_binderName_1262_, v_binderType_1263_, v_body_1264_, v___x_1266_);
return v___x_1267_;
}
else
{
lean_object* v___x_1268_; 
lean_dec(v_h__1_1260_);
v___x_1268_ = lean_apply_2(v_h__2_1261_, v_____x_1259_, lean_box(0));
return v___x_1268_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0(lean_object* v_k_1269_, lean_object* v_b_1270_, lean_object* v_c_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_){
_start:
{
lean_object* v___x_1277_; 
lean_inc(v___y_1275_);
lean_inc_ref(v___y_1274_);
lean_inc(v___y_1273_);
lean_inc_ref(v___y_1272_);
v___x_1277_ = lean_apply_7(v_k_1269_, v_b_1270_, v_c_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, lean_box(0));
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed(lean_object* v_k_1278_, lean_object* v_b_1279_, lean_object* v_c_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0(v_k_1278_, v_b_1279_, v_c_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(lean_object* v_type_1287_, lean_object* v_k_1288_, uint8_t v_cleanupAnnotations_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
lean_object* v___f_1295_; uint8_t v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___f_1295_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1295_, 0, v_k_1288_);
v___x_1296_ = 0;
v___x_1297_ = lean_box(0);
v___x_1298_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_1296_, v___x_1297_, v_type_1287_, v___f_1295_, v_cleanupAnnotations_1289_, v___x_1296_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
if (lean_obj_tag(v___x_1298_) == 0)
{
lean_object* v_a_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1306_; 
v_a_1299_ = lean_ctor_get(v___x_1298_, 0);
v_isSharedCheck_1306_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1301_ = v___x_1298_;
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_a_1299_);
lean_dec(v___x_1298_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1304_; 
if (v_isShared_1302_ == 0)
{
v___x_1304_ = v___x_1301_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_a_1299_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
}
else
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1314_; 
v_a_1307_ = lean_ctor_get(v___x_1298_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1309_ = v___x_1298_;
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v___x_1298_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1312_; 
if (v_isShared_1310_ == 0)
{
v___x_1312_ = v___x_1309_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_a_1307_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___boxed(lean_object* v_type_1315_, lean_object* v_k_1316_, lean_object* v_cleanupAnnotations_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1323_; lean_object* v_res_1324_; 
v_cleanupAnnotations_boxed_1323_ = lean_unbox(v_cleanupAnnotations_1317_);
v_res_1324_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_type_1315_, v_k_1316_, v_cleanupAnnotations_boxed_1323_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2(lean_object* v_00_u03b1_1325_, lean_object* v_type_1326_, lean_object* v_k_1327_, uint8_t v_cleanupAnnotations_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
lean_object* v___x_1334_; 
v___x_1334_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_type_1326_, v_k_1327_, v_cleanupAnnotations_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___boxed(lean_object* v_00_u03b1_1335_, lean_object* v_type_1336_, lean_object* v_k_1337_, lean_object* v_cleanupAnnotations_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1344_; lean_object* v_res_1345_; 
v_cleanupAnnotations_boxed_1344_ = lean_unbox(v_cleanupAnnotations_1338_);
v_res_1345_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2(v_00_u03b1_1335_, v_type_1336_, v_k_1337_, v_cleanupAnnotations_boxed_1344_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(lean_object* v_type_1346_, lean_object* v_maxFVars_x3f_1347_, lean_object* v_k_1348_, uint8_t v_cleanupAnnotations_1349_, uint8_t v_whnfType_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_){
_start:
{
lean_object* v___f_1356_; lean_object* v___x_1357_; 
v___f_1356_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1356_, 0, v_k_1348_);
v___x_1357_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_1346_, v_maxFVars_x3f_1347_, v___f_1356_, v_cleanupAnnotations_1349_, v_whnfType_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1365_; 
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1360_ = v___x_1357_;
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1357_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1363_; 
if (v_isShared_1361_ == 0)
{
v___x_1363_ = v___x_1360_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_a_1358_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
}
else
{
lean_object* v_a_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1373_; 
v_a_1366_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1368_ = v___x_1357_;
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_a_1366_);
lean_dec(v___x_1357_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v___x_1371_; 
if (v_isShared_1369_ == 0)
{
v___x_1371_ = v___x_1368_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_a_1366_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg___boxed(lean_object* v_type_1374_, lean_object* v_maxFVars_x3f_1375_, lean_object* v_k_1376_, lean_object* v_cleanupAnnotations_1377_, lean_object* v_whnfType_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1384_; uint8_t v_whnfType_boxed_1385_; lean_object* v_res_1386_; 
v_cleanupAnnotations_boxed_1384_ = lean_unbox(v_cleanupAnnotations_1377_);
v_whnfType_boxed_1385_ = lean_unbox(v_whnfType_1378_);
v_res_1386_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(v_type_1374_, v_maxFVars_x3f_1375_, v_k_1376_, v_cleanupAnnotations_boxed_1384_, v_whnfType_boxed_1385_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec(v___y_1380_);
lean_dec_ref(v___y_1379_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3(lean_object* v_00_u03b1_1387_, lean_object* v_type_1388_, lean_object* v_maxFVars_x3f_1389_, lean_object* v_k_1390_, uint8_t v_cleanupAnnotations_1391_, uint8_t v_whnfType_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v___x_1398_; 
v___x_1398_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(v_type_1388_, v_maxFVars_x3f_1389_, v_k_1390_, v_cleanupAnnotations_1391_, v_whnfType_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___boxed(lean_object* v_00_u03b1_1399_, lean_object* v_type_1400_, lean_object* v_maxFVars_x3f_1401_, lean_object* v_k_1402_, lean_object* v_cleanupAnnotations_1403_, lean_object* v_whnfType_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1410_; uint8_t v_whnfType_boxed_1411_; lean_object* v_res_1412_; 
v_cleanupAnnotations_boxed_1410_ = lean_unbox(v_cleanupAnnotations_1403_);
v_whnfType_boxed_1411_ = lean_unbox(v_whnfType_1404_);
v_res_1412_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3(v_00_u03b1_1399_, v_type_1400_, v_maxFVars_x3f_1401_, v_k_1402_, v_cleanupAnnotations_boxed_1410_, v_whnfType_boxed_1411_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0(lean_object* v_name_1413_, lean_object* v_us_1414_, lean_object* v_params_1415_, lean_object* v_args1_1416_, uint8_t v_useEq_1417_, lean_object* v_args2_1418_, lean_object* v_args2New_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1425_ = l_Lean_mkConst(v_name_1413_, v_us_1414_);
v___x_1426_ = l_Lean_mkAppN(v___x_1425_, v_params_1415_);
lean_inc_ref(v___x_1426_);
v___x_1427_ = l_Lean_mkAppN(v___x_1426_, v_args1_1416_);
v___x_1428_ = l_Lean_mkAppN(v___x_1426_, v_args2_1418_);
v___x_1429_ = l_Lean_Meta_mkEq(v___x_1427_, v___x_1428_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v_a_1430_; uint8_t v___x_1431_; lean_object* v_result_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v___x_1478_; 
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
lean_inc(v_a_1430_);
lean_dec_ref_known(v___x_1429_, 1);
v___x_1431_ = 1;
v___x_1478_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v_args1_1416_, v_args2_1418_, v___x_1431_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1510_; 
v_a_1479_ = lean_ctor_get(v___x_1478_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1481_ = v___x_1478_;
v_isShared_1482_ = v_isSharedCheck_1510_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v___x_1478_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1510_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1483_; 
v___x_1483_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f(v_a_1479_);
if (lean_obj_tag(v___x_1483_) == 1)
{
lean_del_object(v___x_1481_);
if (v_useEq_1417_ == 0)
{
lean_object* v_val_1484_; lean_object* v___x_1485_; 
v_val_1484_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_val_1484_);
lean_dec_ref_known(v___x_1483_, 1);
v___x_1485_ = l_Lean_mkArrow(v_a_1430_, v_val_1484_, v___y_1422_, v___y_1423_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v_a_1486_; 
v_a_1486_ = lean_ctor_get(v___x_1485_, 0);
lean_inc(v_a_1486_);
lean_dec_ref_known(v___x_1485_, 1);
v_result_1433_ = v_a_1486_;
v___y_1434_ = v___y_1420_;
v___y_1435_ = v___y_1421_;
v___y_1436_ = v___y_1422_;
v___y_1437_ = v___y_1423_;
goto v___jp_1432_;
}
else
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1494_; 
v_a_1487_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1489_ = v___x_1485_;
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1485_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1492_; 
if (v_isShared_1490_ == 0)
{
v___x_1492_ = v___x_1489_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_a_1487_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
}
else
{
lean_object* v_val_1495_; lean_object* v___x_1496_; 
v_val_1495_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_val_1495_);
lean_dec_ref_known(v___x_1483_, 1);
v___x_1496_ = l_Lean_Meta_mkEq(v_a_1430_, v_val_1495_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v_a_1497_; 
v_a_1497_ = lean_ctor_get(v___x_1496_, 0);
lean_inc(v_a_1497_);
lean_dec_ref_known(v___x_1496_, 1);
v_result_1433_ = v_a_1497_;
v___y_1434_ = v___y_1420_;
v___y_1435_ = v___y_1421_;
v___y_1436_ = v___y_1422_;
v___y_1437_ = v___y_1423_;
goto v___jp_1432_;
}
else
{
lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1505_; 
v_a_1498_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1500_ = v___x_1496_;
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_a_1498_);
lean_dec(v___x_1496_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1503_; 
if (v_isShared_1501_ == 0)
{
v___x_1503_ = v___x_1500_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_a_1498_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
}
}
else
{
lean_object* v___x_1506_; lean_object* v___x_1508_; 
lean_dec(v___x_1483_);
lean_dec(v_a_1430_);
v___x_1506_ = lean_box(0);
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 0, v___x_1506_);
v___x_1508_ = v___x_1481_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v___x_1506_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
}
}
else
{
lean_object* v_a_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1518_; 
lean_dec(v_a_1430_);
v_a_1511_ = lean_ctor_get(v___x_1478_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1513_ = v___x_1478_;
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_a_1511_);
lean_dec(v___x_1478_);
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
v___jp_1432_:
{
uint8_t v___x_1438_; uint8_t v___x_1439_; lean_object* v___x_1440_; 
v___x_1438_ = 0;
v___x_1439_ = 1;
v___x_1440_ = l_Lean_Meta_mkForallFVars(v_args2New_1419_, v_result_1433_, v___x_1438_, v___x_1431_, v___x_1431_, v___x_1439_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_object* v_a_1441_; lean_object* v___x_1442_; 
v_a_1441_ = lean_ctor_get(v___x_1440_, 0);
lean_inc(v_a_1441_);
lean_dec_ref_known(v___x_1440_, 1);
v___x_1442_ = l_Lean_Meta_mkForallFVars(v_args1_1416_, v_a_1441_, v___x_1438_, v___x_1431_, v___x_1431_, v___x_1439_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_);
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_object* v_a_1443_; lean_object* v___x_1444_; 
v_a_1443_ = lean_ctor_get(v___x_1442_, 0);
lean_inc(v_a_1443_);
lean_dec_ref_known(v___x_1442_, 1);
v___x_1444_ = l_Lean_Meta_mkForallFVars(v_params_1415_, v_a_1443_, v___x_1438_, v___x_1431_, v___x_1431_, v___x_1439_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_);
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_object* v_a_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1453_; 
v_a_1445_ = lean_ctor_get(v___x_1444_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1447_ = v___x_1444_;
v_isShared_1448_ = v_isSharedCheck_1453_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_a_1445_);
lean_dec(v___x_1444_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1453_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1449_; lean_object* v___x_1451_; 
v___x_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1449_, 0, v_a_1445_);
if (v_isShared_1448_ == 0)
{
lean_ctor_set(v___x_1447_, 0, v___x_1449_);
v___x_1451_ = v___x_1447_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1449_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
else
{
lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1461_; 
v_a_1454_ = lean_ctor_get(v___x_1444_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1456_ = v___x_1444_;
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_a_1454_);
lean_dec(v___x_1444_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1459_; 
if (v_isShared_1457_ == 0)
{
v___x_1459_ = v___x_1456_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_a_1454_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
}
}
else
{
lean_object* v_a_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1469_; 
v_a_1462_ = lean_ctor_get(v___x_1442_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1464_ = v___x_1442_;
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_a_1462_);
lean_dec(v___x_1442_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1467_; 
if (v_isShared_1465_ == 0)
{
v___x_1467_ = v___x_1464_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_a_1462_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
}
else
{
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1477_; 
v_a_1470_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1472_ = v___x_1440_;
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___x_1440_);
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
}
else
{
lean_object* v_a_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1526_; 
lean_dec_ref(v_args2_1418_);
v_a_1519_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1521_ = v___x_1429_;
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_a_1519_);
lean_dec(v___x_1429_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1524_; 
if (v_isShared_1522_ == 0)
{
v___x_1524_ = v___x_1521_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_a_1519_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0___boxed(lean_object* v_name_1527_, lean_object* v_us_1528_, lean_object* v_params_1529_, lean_object* v_args1_1530_, lean_object* v_useEq_1531_, lean_object* v_args2_1532_, lean_object* v_args2New_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
uint8_t v_useEq_boxed_1539_; lean_object* v_res_1540_; 
v_useEq_boxed_1539_ = lean_unbox(v_useEq_1531_);
v_res_1540_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0(v_name_1527_, v_us_1528_, v_params_1529_, v_args1_1530_, v_useEq_boxed_1539_, v_args2_1532_, v_args2New_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
lean_dec_ref(v_args2New_1533_);
lean_dec_ref(v_args1_1530_);
lean_dec_ref(v_params_1529_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1(size_t v_sz_1541_, size_t v_i_1542_, lean_object* v_bs_1543_){
_start:
{
uint8_t v___x_1544_; 
v___x_1544_ = lean_usize_dec_lt(v_i_1542_, v_sz_1541_);
if (v___x_1544_ == 0)
{
return v_bs_1543_;
}
else
{
lean_object* v_v_1545_; lean_object* v___x_1546_; lean_object* v_bs_x27_1547_; lean_object* v___x_1548_; uint8_t v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; size_t v___x_1552_; size_t v___x_1553_; lean_object* v___x_1554_; 
v_v_1545_ = lean_array_uget(v_bs_1543_, v_i_1542_);
v___x_1546_ = lean_unsigned_to_nat(0u);
v_bs_x27_1547_ = lean_array_uset(v_bs_1543_, v_i_1542_, v___x_1546_);
v___x_1548_ = l_Lean_Expr_fvarId_x21(v_v_1545_);
lean_dec(v_v_1545_);
v___x_1549_ = 1;
v___x_1550_ = lean_box(v___x_1549_);
v___x_1551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1548_);
lean_ctor_set(v___x_1551_, 1, v___x_1550_);
v___x_1552_ = ((size_t)1ULL);
v___x_1553_ = lean_usize_add(v_i_1542_, v___x_1552_);
v___x_1554_ = lean_array_uset(v_bs_x27_1547_, v_i_1542_, v___x_1551_);
v_i_1542_ = v___x_1553_;
v_bs_1543_ = v___x_1554_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1___boxed(lean_object* v_sz_1556_, lean_object* v_i_1557_, lean_object* v_bs_1558_){
_start:
{
size_t v_sz_boxed_1559_; size_t v_i_boxed_1560_; lean_object* v_res_1561_; 
v_sz_boxed_1559_ = lean_unbox_usize(v_sz_1556_);
lean_dec(v_sz_1556_);
v_i_boxed_1560_ = lean_unbox_usize(v_i_1557_);
lean_dec(v_i_1557_);
v_res_1561_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1(v_sz_boxed_1559_, v_i_boxed_1560_, v_bs_1558_);
return v_res_1561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(lean_object* v_bs_1562_, lean_object* v_k_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_){
_start:
{
lean_object* v___x_1569_; 
v___x_1569_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_box(0), v_bs_1562_, v_k_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v_a_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1577_; 
v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1577_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1572_ = v___x_1569_;
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_a_1570_);
lean_dec(v___x_1569_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1575_; 
if (v_isShared_1573_ == 0)
{
v___x_1575_ = v___x_1572_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_a_1570_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
}
else
{
lean_object* v_a_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1585_; 
v_a_1578_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1580_ = v___x_1569_;
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_a_1578_);
lean_dec(v___x_1569_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1583_; 
if (v_isShared_1581_ == 0)
{
v___x_1583_ = v___x_1580_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_a_1578_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_bs_1586_, lean_object* v_k_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(v_bs_1586_, v_k_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec_ref(v_bs_1586_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(lean_object* v_bs_1594_, lean_object* v_k_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_){
_start:
{
size_t v_sz_1601_; size_t v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
v_sz_1601_ = lean_array_size(v_bs_1594_);
v___x_1602_ = ((size_t)0ULL);
v___x_1603_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1(v_sz_1601_, v___x_1602_, v_bs_1594_);
v___x_1604_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(v___x_1603_, v_k_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_);
lean_dec_ref(v___x_1603_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg___boxed(lean_object* v_bs_1605_, lean_object* v_k_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_){
_start:
{
lean_object* v_res_1612_; 
v_res_1612_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v_bs_1605_, v_k_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
lean_dec(v___y_1610_);
lean_dec_ref(v___y_1609_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1(lean_object* v_name_1613_, lean_object* v_us_1614_, lean_object* v_params_1615_, uint8_t v_useEq_1616_, lean_object* v_ctorVal_1617_, lean_object* v_type_1618_, lean_object* v_args1_1619_, lean_object* v_resultType_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_){
_start:
{
lean_object* v___x_1626_; lean_object* v___f_1627_; 
v___x_1626_ = lean_box(v_useEq_1616_);
lean_inc_ref(v_args1_1619_);
lean_inc_ref(v_params_1615_);
v___f_1627_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1627_, 0, v_name_1613_);
lean_closure_set(v___f_1627_, 1, v_us_1614_);
lean_closure_set(v___f_1627_, 2, v_params_1615_);
lean_closure_set(v___f_1627_, 3, v_args1_1619_);
lean_closure_set(v___f_1627_, 4, v___x_1626_);
if (v_useEq_1616_ == 0)
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1628_ = l_Array_append___redArg(v_params_1615_, v_args1_1619_);
v___x_1629_ = lean_unsigned_to_nat(0u);
v___x_1630_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_1631_ = lean_box(v_useEq_1616_);
v___x_1632_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___boxed), 14, 9);
lean_closure_set(v___x_1632_, 0, v_ctorVal_1617_);
lean_closure_set(v___x_1632_, 1, v___x_1631_);
lean_closure_set(v___x_1632_, 2, v_args1_1619_);
lean_closure_set(v___x_1632_, 3, v_resultType_1620_);
lean_closure_set(v___x_1632_, 4, v___f_1627_);
lean_closure_set(v___x_1632_, 5, v___x_1629_);
lean_closure_set(v___x_1632_, 6, v_type_1618_);
lean_closure_set(v___x_1632_, 7, v___x_1630_);
lean_closure_set(v___x_1632_, 8, v___x_1630_);
v___x_1633_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v___x_1628_, v___x_1632_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
return v___x_1633_;
}
else
{
lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
lean_dec_ref(v_params_1615_);
v___x_1634_ = lean_unsigned_to_nat(0u);
v___x_1635_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_1636_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(v_ctorVal_1617_, v_useEq_1616_, v_args1_1619_, v_resultType_1620_, v___f_1627_, v___x_1634_, v_type_1618_, v___x_1635_, v___x_1635_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
return v___x_1636_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1___boxed(lean_object* v_name_1637_, lean_object* v_us_1638_, lean_object* v_params_1639_, lean_object* v_useEq_1640_, lean_object* v_ctorVal_1641_, lean_object* v_type_1642_, lean_object* v_args1_1643_, lean_object* v_resultType_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
uint8_t v_useEq_boxed_1650_; lean_object* v_res_1651_; 
v_useEq_boxed_1650_ = lean_unbox(v_useEq_1640_);
v_res_1651_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1(v_name_1637_, v_us_1638_, v_params_1639_, v_useEq_boxed_1650_, v_ctorVal_1641_, v_type_1642_, v_args1_1643_, v_resultType_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_);
lean_dec(v___y_1648_);
lean_dec_ref(v___y_1647_);
lean_dec(v___y_1646_);
lean_dec_ref(v___y_1645_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2(lean_object* v_name_1652_, lean_object* v_us_1653_, uint8_t v_useEq_1654_, lean_object* v_ctorVal_1655_, lean_object* v_params_1656_, lean_object* v_type_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v___x_1663_; lean_object* v___f_1664_; uint8_t v___x_1665_; lean_object* v___x_1666_; 
v___x_1663_ = lean_box(v_useEq_1654_);
lean_inc_ref(v_type_1657_);
v___f_1664_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1___boxed), 13, 6);
lean_closure_set(v___f_1664_, 0, v_name_1652_);
lean_closure_set(v___f_1664_, 1, v_us_1653_);
lean_closure_set(v___f_1664_, 2, v_params_1656_);
lean_closure_set(v___f_1664_, 3, v___x_1663_);
lean_closure_set(v___f_1664_, 4, v_ctorVal_1655_);
lean_closure_set(v___f_1664_, 5, v_type_1657_);
v___x_1665_ = 0;
v___x_1666_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_type_1657_, v___f_1664_, v___x_1665_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2___boxed(lean_object* v_name_1667_, lean_object* v_us_1668_, lean_object* v_useEq_1669_, lean_object* v_ctorVal_1670_, lean_object* v_params_1671_, lean_object* v_type_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
uint8_t v_useEq_boxed_1678_; lean_object* v_res_1679_; 
v_useEq_boxed_1678_ = lean_unbox(v_useEq_1669_);
v_res_1679_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2(v_name_1667_, v_us_1668_, v_useEq_boxed_1678_, v_ctorVal_1670_, v_params_1671_, v_type_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(lean_object* v_a_1680_, lean_object* v_a_1681_){
_start:
{
if (lean_obj_tag(v_a_1680_) == 0)
{
lean_object* v___x_1682_; 
v___x_1682_ = l_List_reverse___redArg(v_a_1681_);
return v___x_1682_;
}
else
{
lean_object* v_head_1683_; lean_object* v_tail_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1693_; 
v_head_1683_ = lean_ctor_get(v_a_1680_, 0);
v_tail_1684_ = lean_ctor_get(v_a_1680_, 1);
v_isSharedCheck_1693_ = !lean_is_exclusive(v_a_1680_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1686_ = v_a_1680_;
v_isShared_1687_ = v_isSharedCheck_1693_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_tail_1684_);
lean_inc(v_head_1683_);
lean_dec(v_a_1680_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1693_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1688_; lean_object* v___x_1690_; 
v___x_1688_ = l_Lean_mkLevelParam(v_head_1683_);
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 1, v_a_1681_);
lean_ctor_set(v___x_1686_, 0, v___x_1688_);
v___x_1690_ = v___x_1686_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v___x_1688_);
lean_ctor_set(v_reuseFailAlloc_1692_, 1, v_a_1681_);
v___x_1690_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
v_a_1680_ = v_tail_1684_;
v_a_1681_ = v___x_1690_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(lean_object* v_ctorVal_1694_, uint8_t v_useEq_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_){
_start:
{
lean_object* v_toConstantVal_1701_; lean_object* v_numParams_1702_; lean_object* v_name_1703_; lean_object* v_levelParams_1704_; lean_object* v_type_1705_; lean_object* v___x_1706_; lean_object* v_us_1707_; lean_object* v___x_1708_; lean_object* v___f_1709_; lean_object* v___x_1710_; 
v_toConstantVal_1701_ = lean_ctor_get(v_ctorVal_1694_, 0);
v_numParams_1702_ = lean_ctor_get(v_ctorVal_1694_, 3);
lean_inc(v_numParams_1702_);
v_name_1703_ = lean_ctor_get(v_toConstantVal_1701_, 0);
lean_inc(v_name_1703_);
v_levelParams_1704_ = lean_ctor_get(v_toConstantVal_1701_, 1);
v_type_1705_ = lean_ctor_get(v_toConstantVal_1701_, 2);
lean_inc_ref(v_type_1705_);
v___x_1706_ = lean_box(0);
lean_inc(v_levelParams_1704_);
v_us_1707_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(v_levelParams_1704_, v___x_1706_);
v___x_1708_ = lean_box(v_useEq_1695_);
v___f_1709_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2___boxed), 11, 4);
lean_closure_set(v___f_1709_, 0, v_name_1703_);
lean_closure_set(v___f_1709_, 1, v_us_1707_);
lean_closure_set(v___f_1709_, 2, v___x_1708_);
lean_closure_set(v___f_1709_, 3, v_ctorVal_1694_);
v___x_1710_ = l_Lean_Meta_elimOptParam(v_type_1705_, v_a_1698_, v_a_1699_);
if (lean_obj_tag(v___x_1710_) == 0)
{
lean_object* v_a_1711_; lean_object* v___x_1712_; uint8_t v___x_1713_; lean_object* v___x_1714_; 
v_a_1711_ = lean_ctor_get(v___x_1710_, 0);
lean_inc(v_a_1711_);
lean_dec_ref_known(v___x_1710_, 1);
v___x_1712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1712_, 0, v_numParams_1702_);
v___x_1713_ = 0;
v___x_1714_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(v_a_1711_, v___x_1712_, v___f_1709_, v___x_1713_, v___x_1713_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_);
return v___x_1714_;
}
else
{
lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1722_; 
lean_dec_ref(v___f_1709_);
lean_dec(v_numParams_1702_);
v_a_1715_ = lean_ctor_get(v___x_1710_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1717_ = v___x_1710_;
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_a_1715_);
lean_dec(v___x_1710_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1720_; 
if (v_isShared_1718_ == 0)
{
v___x_1720_ = v___x_1717_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_a_1715_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___boxed(lean_object* v_ctorVal_1723_, lean_object* v_useEq_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_){
_start:
{
uint8_t v_useEq_boxed_1730_; lean_object* v_res_1731_; 
v_useEq_boxed_1730_ = lean_unbox(v_useEq_1724_);
v_res_1731_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(v_ctorVal_1723_, v_useEq_boxed_1730_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_);
lean_dec(v_a_1728_);
lean_dec_ref(v_a_1727_);
lean_dec(v_a_1726_);
lean_dec_ref(v_a_1725_);
return v_res_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2(lean_object* v_00_u03b1_1732_, lean_object* v_bs_1733_, lean_object* v_k_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
lean_object* v___x_1740_; 
v___x_1740_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(v_bs_1733_, v_k_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1741_, lean_object* v_bs_1742_, lean_object* v_k_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2(v_00_u03b1_1741_, v_bs_1742_, v_k_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_);
lean_dec(v___y_1747_);
lean_dec_ref(v___y_1746_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1744_);
lean_dec_ref(v_bs_1742_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1(lean_object* v_00_u03b1_1750_, lean_object* v_bs_1751_, lean_object* v_k_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_){
_start:
{
lean_object* v___x_1758_; 
v___x_1758_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v_bs_1751_, v_k_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___boxed(lean_object* v_00_u03b1_1759_, lean_object* v_bs_1760_, lean_object* v_k_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_){
_start:
{
lean_object* v_res_1767_; 
v_res_1767_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1(v_00_u03b1_1759_, v_bs_1760_, v_k_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_);
lean_dec(v___y_1765_);
lean_dec_ref(v___y_1764_);
lean_dec(v___y_1763_);
lean_dec_ref(v___y_1762_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(lean_object* v_ctorVal_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_){
_start:
{
uint8_t v___x_1774_; lean_object* v___x_1775_; 
v___x_1774_ = 0;
v___x_1775_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(v_ctorVal_1768_, v___x_1774_, v_a_1769_, v_a_1770_, v_a_1771_, v_a_1772_);
return v___x_1775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f___boxed(lean_object* v_ctorVal_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_){
_start:
{
lean_object* v_res_1782_; 
v_res_1782_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
lean_dec(v_a_1780_);
lean_dec_ref(v_a_1779_);
lean_dec(v_a_1778_);
lean_dec_ref(v_a_1777_);
return v_res_1782_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1(void){
_start:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1784_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__0));
v___x_1785_ = l_Lean_stringToMessageData(v___x_1784_);
return v___x_1785_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3(void){
_start:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1787_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__2));
v___x_1788_ = l_Lean_stringToMessageData(v___x_1787_);
return v___x_1788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(lean_object* v_ctorName_1789_){
_start:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1790_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1);
v___x_1791_ = l_Lean_MessageData_ofName(v_ctorName_1789_);
v___x_1792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1792_, 0, v___x_1790_);
lean_ctor_set(v___x_1792_, 1, v___x_1791_);
v___x_1793_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3);
v___x_1794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1792_);
lean_ctor_set(v___x_1794_, 1, v___x_1793_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(lean_object* v_ctorName_1795_, lean_object* v_mvarId_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_){
_start:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1802_ = l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(v_ctorName_1795_);
v___x_1803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1803_, 0, v_mvarId_1796_);
v___x_1804_ = l_Lean_indentD(v___x_1803_);
v___x_1805_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1802_);
lean_ctor_set(v___x_1805_, 1, v___x_1804_);
v___x_1806_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_1805_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg___boxed(lean_object* v_ctorName_1807_, lean_object* v_mvarId_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_){
_start:
{
lean_object* v_res_1814_; 
v_res_1814_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(v_ctorName_1807_, v_mvarId_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_);
lean_dec(v_a_1812_);
lean_dec_ref(v_a_1811_);
lean_dec(v_a_1810_);
lean_dec_ref(v_a_1809_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure(lean_object* v_00_u03b1_1815_, lean_object* v_ctorName_1816_, lean_object* v_mvarId_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_){
_start:
{
lean_object* v___x_1823_; 
v___x_1823_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(v_ctorName_1816_, v_mvarId_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___boxed(lean_object* v_00_u03b1_1824_, lean_object* v_ctorName_1825_, lean_object* v_mvarId_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_){
_start:
{
lean_object* v_res_1832_; 
v_res_1832_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure(v_00_u03b1_1824_, v_ctorName_1825_, v_mvarId_1826_, v_a_1827_, v_a_1828_, v_a_1829_, v_a_1830_);
lean_dec(v_a_1830_);
lean_dec_ref(v_a_1829_);
lean_dec(v_a_1828_);
lean_dec_ref(v_a_1827_);
return v_res_1832_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0(lean_object* v_ctorName_1833_, lean_object* v_as_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_){
_start:
{
if (lean_obj_tag(v_as_1834_) == 0)
{
lean_object* v___x_1840_; lean_object* v___x_1841_; 
lean_dec(v_ctorName_1833_);
v___x_1840_ = lean_box(0);
v___x_1841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1840_);
return v___x_1841_;
}
else
{
lean_object* v_head_1842_; lean_object* v_tail_1843_; lean_object* v___x_1844_; 
v_head_1842_ = lean_ctor_get(v_as_1834_, 0);
lean_inc_n(v_head_1842_, 2);
v_tail_1843_ = lean_ctor_get(v_as_1834_, 1);
lean_inc(v_tail_1843_);
lean_dec_ref_known(v_as_1834_, 2);
v___x_1844_ = l_Lean_MVarId_assumptionCore(v_head_1842_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_);
if (lean_obj_tag(v___x_1844_) == 0)
{
lean_object* v_a_1845_; uint8_t v___x_1846_; 
v_a_1845_ = lean_ctor_get(v___x_1844_, 0);
lean_inc(v_a_1845_);
lean_dec_ref_known(v___x_1844_, 1);
v___x_1846_ = lean_unbox(v_a_1845_);
lean_dec(v_a_1845_);
if (v___x_1846_ == 0)
{
lean_object* v___x_1847_; 
lean_dec(v_tail_1843_);
v___x_1847_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(v_ctorName_1833_, v_head_1842_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_);
return v___x_1847_;
}
else
{
lean_dec(v_head_1842_);
v_as_1834_ = v_tail_1843_;
goto _start;
}
}
else
{
lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1856_; 
lean_dec(v_tail_1843_);
lean_dec(v_head_1842_);
lean_dec(v_ctorName_1833_);
v_a_1849_ = lean_ctor_get(v___x_1844_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1851_ = v___x_1844_;
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v___x_1844_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1854_; 
if (v_isShared_1852_ == 0)
{
v___x_1854_ = v___x_1851_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_a_1849_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0___boxed(lean_object* v_ctorName_1857_, lean_object* v_as_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0(v_ctorName_1857_, v_as_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(lean_object* v_mvarId_1865_, lean_object* v_ctorName_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_){
_start:
{
lean_object* v___x_1872_; 
v___x_1872_ = l_Lean_MVarId_splitAndCore(v_mvarId_1865_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_a_1873_; lean_object* v___x_1874_; 
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
lean_inc(v_a_1873_);
lean_dec_ref_known(v___x_1872_, 1);
v___x_1874_ = l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0(v_ctorName_1866_, v_a_1873_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_);
return v___x_1874_;
}
else
{
lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1882_; 
lean_dec(v_ctorName_1866_);
v_a_1875_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1877_ = v___x_1872_;
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_dec(v___x_1872_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1880_; 
if (v_isShared_1878_ == 0)
{
v___x_1880_ = v___x_1877_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_a_1875_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption___boxed(lean_object* v_mvarId_1883_, lean_object* v_ctorName_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_){
_start:
{
lean_object* v_res_1890_; 
v_res_1890_ = l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(v_mvarId_1883_, v_ctorName_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_);
lean_dec(v_a_1888_);
lean_dec_ref(v_a_1887_);
lean_dec(v_a_1886_);
lean_dec_ref(v_a_1885_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0(lean_object* v_msg_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_){
_start:
{
lean_object* v___f_1898_; lean_object* v___x_922__overap_1899_; lean_object* v___x_1900_; 
v___f_1898_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0___closed__0));
v___x_922__overap_1899_ = lean_panic_fn_borrowed(v___f_1898_, v_msg_1892_);
lean_inc(v___y_1896_);
lean_inc_ref(v___y_1895_);
lean_inc(v___y_1894_);
lean_inc_ref(v___y_1893_);
v___x_1900_ = lean_apply_5(v___x_922__overap_1899_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, lean_box(0));
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0___boxed(lean_object* v_msg_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_){
_start:
{
lean_object* v_res_1907_; 
v_res_1907_ = l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0(v_msg_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
return v_res_1907_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1908_; double v___x_1909_; 
v___x_1908_ = lean_unsigned_to_nat(0u);
v___x_1909_ = lean_float_of_nat(v___x_1908_);
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(lean_object* v_cls_1913_, lean_object* v_msg_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_){
_start:
{
lean_object* v_ref_1920_; lean_object* v___x_1921_; lean_object* v_a_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1967_; 
v_ref_1920_ = lean_ctor_get(v___y_1917_, 2);
v___x_1921_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msg_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_);
v_a_1922_ = lean_ctor_get(v___x_1921_, 0);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___x_1921_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1924_ = v___x_1921_;
v_isShared_1925_ = v_isSharedCheck_1967_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_a_1922_);
lean_dec(v___x_1921_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1967_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1926_; lean_object* v_traceState_1927_; lean_object* v_env_1928_; lean_object* v_nextMacroScope_1929_; lean_object* v_ngen_1930_; lean_object* v_auxDeclNGen_1931_; lean_object* v_cache_1932_; lean_object* v_recordedDeps_1933_; lean_object* v_messages_1934_; lean_object* v_infoState_1935_; lean_object* v_snapshotTasks_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1966_; 
v___x_1926_ = lean_st_ref_take(v___y_1918_);
v_traceState_1927_ = lean_ctor_get(v___x_1926_, 4);
v_env_1928_ = lean_ctor_get(v___x_1926_, 0);
v_nextMacroScope_1929_ = lean_ctor_get(v___x_1926_, 1);
v_ngen_1930_ = lean_ctor_get(v___x_1926_, 2);
v_auxDeclNGen_1931_ = lean_ctor_get(v___x_1926_, 3);
v_cache_1932_ = lean_ctor_get(v___x_1926_, 5);
v_recordedDeps_1933_ = lean_ctor_get(v___x_1926_, 6);
v_messages_1934_ = lean_ctor_get(v___x_1926_, 7);
v_infoState_1935_ = lean_ctor_get(v___x_1926_, 8);
v_snapshotTasks_1936_ = lean_ctor_get(v___x_1926_, 9);
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1926_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1938_ = v___x_1926_;
v_isShared_1939_ = v_isSharedCheck_1966_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_snapshotTasks_1936_);
lean_inc(v_infoState_1935_);
lean_inc(v_messages_1934_);
lean_inc(v_recordedDeps_1933_);
lean_inc(v_cache_1932_);
lean_inc(v_traceState_1927_);
lean_inc(v_auxDeclNGen_1931_);
lean_inc(v_ngen_1930_);
lean_inc(v_nextMacroScope_1929_);
lean_inc(v_env_1928_);
lean_dec(v___x_1926_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1966_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
uint64_t v_tid_1940_; lean_object* v_traces_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1965_; 
v_tid_1940_ = lean_ctor_get_uint64(v_traceState_1927_, sizeof(void*)*1);
v_traces_1941_ = lean_ctor_get(v_traceState_1927_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v_traceState_1927_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1943_ = v_traceState_1927_;
v_isShared_1944_ = v_isSharedCheck_1965_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_traces_1941_);
lean_dec(v_traceState_1927_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1965_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1945_; lean_object* v___x_1946_; double v___x_1947_; uint8_t v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1956_; 
v___x_1945_ = lean_box(0);
v___x_1946_ = lean_box(0);
v___x_1947_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0);
v___x_1948_ = 0;
v___x_1949_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_1950_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1950_, 0, v_cls_1913_);
lean_ctor_set(v___x_1950_, 1, v___x_1946_);
lean_ctor_set(v___x_1950_, 2, v___x_1949_);
lean_ctor_set_float(v___x_1950_, sizeof(void*)*3, v___x_1947_);
lean_ctor_set_float(v___x_1950_, sizeof(void*)*3 + 8, v___x_1947_);
lean_ctor_set_uint8(v___x_1950_, sizeof(void*)*3 + 16, v___x_1948_);
v___x_1951_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__2));
v___x_1952_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1950_);
lean_ctor_set(v___x_1952_, 1, v_a_1922_);
lean_ctor_set(v___x_1952_, 2, v___x_1951_);
lean_inc(v_ref_1920_);
v___x_1953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1953_, 0, v_ref_1920_);
lean_ctor_set(v___x_1953_, 1, v___x_1952_);
v___x_1954_ = l_Lean_PersistentArray_push___redArg(v_traces_1941_, v___x_1953_);
if (v_isShared_1944_ == 0)
{
lean_ctor_set(v___x_1943_, 0, v___x_1954_);
v___x_1956_ = v___x_1943_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v___x_1954_);
lean_ctor_set_uint64(v_reuseFailAlloc_1964_, sizeof(void*)*1, v_tid_1940_);
v___x_1956_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
lean_object* v___x_1958_; 
if (v_isShared_1939_ == 0)
{
lean_ctor_set(v___x_1938_, 4, v___x_1956_);
v___x_1958_ = v___x_1938_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_env_1928_);
lean_ctor_set(v_reuseFailAlloc_1963_, 1, v_nextMacroScope_1929_);
lean_ctor_set(v_reuseFailAlloc_1963_, 2, v_ngen_1930_);
lean_ctor_set(v_reuseFailAlloc_1963_, 3, v_auxDeclNGen_1931_);
lean_ctor_set(v_reuseFailAlloc_1963_, 4, v___x_1956_);
lean_ctor_set(v_reuseFailAlloc_1963_, 5, v_cache_1932_);
lean_ctor_set(v_reuseFailAlloc_1963_, 6, v_recordedDeps_1933_);
lean_ctor_set(v_reuseFailAlloc_1963_, 7, v_messages_1934_);
lean_ctor_set(v_reuseFailAlloc_1963_, 8, v_infoState_1935_);
lean_ctor_set(v_reuseFailAlloc_1963_, 9, v_snapshotTasks_1936_);
v___x_1958_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
lean_object* v___x_1959_; lean_object* v___x_1961_; 
v___x_1959_ = lean_st_ref_put(v___y_1918_, v___x_1958_);
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 0, v___x_1945_);
v___x_1961_ = v___x_1924_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v___x_1945_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___boxed(lean_object* v_cls_1968_, lean_object* v_msg_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
lean_object* v_res_1975_; 
v_res_1975_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_1968_, v_msg_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
return v_res_1975_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3(void){
_start:
{
lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___x_1979_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__2));
v___x_1980_ = lean_unsigned_to_nat(30u);
v___x_1981_ = lean_unsigned_to_nat(96u);
v___x_1982_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__1));
v___x_1983_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__0));
v___x_1984_ = l_mkPanicMessageWithDecl(v___x_1983_, v___x_1982_, v___x_1981_, v___x_1980_, v___x_1979_);
return v___x_1984_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9(void){
_start:
{
lean_object* v_cls_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
v_cls_1993_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_1994_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__8));
v___x_1995_ = l_Lean_Name_append(v___x_1994_, v_cls_1993_);
return v___x_1995_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11(void){
_start:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1997_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__10));
v___x_1998_ = l_Lean_stringToMessageData(v___x_1997_);
return v___x_1998_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13(void){
_start:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_2000_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__12));
v___x_2001_ = l_Lean_stringToMessageData(v___x_2000_);
return v___x_2001_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15(void){
_start:
{
lean_object* v___x_2003_; lean_object* v___x_2004_; 
v___x_2003_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__14));
v___x_2004_ = l_Lean_stringToMessageData(v___x_2003_);
return v___x_2004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(lean_object* v_ctorName_2005_, lean_object* v_mvarId_2006_, lean_object* v_h_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_){
_start:
{
lean_object* v___y_2014_; lean_object* v___y_2015_; lean_object* v___y_2016_; lean_object* v___y_2017_; lean_object* v_toCold_2033_; lean_object* v_options_2034_; uint8_t v_hasTrace_2035_; 
v_toCold_2033_ = lean_ctor_get(v_a_2010_, 0);
v_options_2034_ = lean_ctor_get(v_toCold_2033_, 2);
v_hasTrace_2035_ = lean_ctor_get_uint8(v_options_2034_, sizeof(void*)*1);
if (v_hasTrace_2035_ == 0)
{
v___y_2014_ = v_a_2008_;
v___y_2015_ = v_a_2009_;
v___y_2016_ = v_a_2010_;
v___y_2017_ = v_a_2011_;
goto v___jp_2013_;
}
else
{
lean_object* v_inheritedTraceOptions_2036_; lean_object* v_cls_2037_; lean_object* v___x_2038_; uint8_t v___x_2039_; 
v_inheritedTraceOptions_2036_ = lean_ctor_get(v_toCold_2033_, 11);
v_cls_2037_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_2038_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_2039_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2036_, v_options_2034_, v___x_2038_);
if (v___x_2039_ == 0)
{
v___y_2014_ = v_a_2008_;
v___y_2015_ = v_a_2009_;
v___y_2016_ = v_a_2010_;
v___y_2017_ = v_a_2011_;
goto v___jp_2013_;
}
else
{
lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2040_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11);
lean_inc(v_ctorName_2005_);
v___x_2041_ = l_Lean_MessageData_ofName(v_ctorName_2005_);
v___x_2042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2042_, 0, v___x_2040_);
lean_ctor_set(v___x_2042_, 1, v___x_2041_);
v___x_2043_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13);
v___x_2044_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2042_);
lean_ctor_set(v___x_2044_, 1, v___x_2043_);
lean_inc(v_h_2007_);
v___x_2045_ = l_Lean_mkFVar(v_h_2007_);
v___x_2046_ = l_Lean_MessageData_ofExpr(v___x_2045_);
v___x_2047_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2044_);
lean_ctor_set(v___x_2047_, 1, v___x_2046_);
v___x_2048_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15);
v___x_2049_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2047_);
lean_ctor_set(v___x_2049_, 1, v___x_2048_);
lean_inc(v_mvarId_2006_);
v___x_2050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2050_, 0, v_mvarId_2006_);
v___x_2051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2049_);
lean_ctor_set(v___x_2051_, 1, v___x_2050_);
v___x_2052_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2037_, v___x_2051_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_);
if (lean_obj_tag(v___x_2052_) == 0)
{
lean_dec_ref_known(v___x_2052_, 1);
v___y_2014_ = v_a_2008_;
v___y_2015_ = v_a_2009_;
v___y_2016_ = v_a_2010_;
v___y_2017_ = v_a_2011_;
goto v___jp_2013_;
}
else
{
lean_dec(v_h_2007_);
lean_dec(v_mvarId_2006_);
lean_dec(v_ctorName_2005_);
return v___x_2052_;
}
}
}
v___jp_2013_:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2018_ = lean_box(0);
v___x_2019_ = l_Lean_Meta_injection(v_mvarId_2006_, v_h_2007_, v___x_2018_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v_a_2020_; 
v_a_2020_ = lean_ctor_get(v___x_2019_, 0);
lean_inc(v_a_2020_);
lean_dec_ref_known(v___x_2019_, 1);
if (lean_obj_tag(v_a_2020_) == 0)
{
lean_object* v___x_2021_; lean_object* v___x_2022_; 
lean_dec(v_ctorName_2005_);
v___x_2021_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3);
v___x_2022_ = l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0(v___x_2021_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
return v___x_2022_;
}
else
{
lean_object* v_mvarId_2023_; lean_object* v___x_2024_; 
v_mvarId_2023_ = lean_ctor_get(v_a_2020_, 0);
lean_inc(v_mvarId_2023_);
lean_dec_ref_known(v_a_2020_, 3);
v___x_2024_ = l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(v_mvarId_2023_, v_ctorName_2005_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
return v___x_2024_;
}
}
else
{
lean_object* v_a_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2032_; 
lean_dec(v_ctorName_2005_);
v_a_2025_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2027_ = v___x_2019_;
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_a_2025_);
lean_dec(v___x_2019_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2030_; 
if (v_isShared_2028_ == 0)
{
v___x_2030_ = v___x_2027_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_a_2025_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___boxed(lean_object* v_ctorName_2053_, lean_object* v_mvarId_2054_, lean_object* v_h_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(v_ctorName_2053_, v_mvarId_2054_, v_h_2055_, v_a_2056_, v_a_2057_, v_a_2058_, v_a_2059_);
lean_dec(v_a_2059_);
lean_dec_ref(v_a_2058_);
lean_dec(v_a_2057_);
lean_dec_ref(v_a_2056_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(lean_object* v_type_2062_, lean_object* v_k_2063_, uint8_t v_cleanupAnnotations_2064_, uint8_t v_whnfType_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_){
_start:
{
lean_object* v___f_2071_; lean_object* v___x_2072_; 
v___f_2071_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2071_, 0, v_k_2063_);
v___x_2072_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_2062_, v___f_2071_, v_cleanupAnnotations_2064_, v_whnfType_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2080_; 
v_a_2073_ = lean_ctor_get(v___x_2072_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2075_ = v___x_2072_;
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_2072_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2078_; 
if (v_isShared_2076_ == 0)
{
v___x_2078_ = v___x_2075_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_a_2073_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
else
{
lean_object* v_a_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2088_; 
v_a_2081_ = lean_ctor_get(v___x_2072_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2083_ = v___x_2072_;
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_a_2081_);
lean_dec(v___x_2072_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2086_; 
if (v_isShared_2084_ == 0)
{
v___x_2086_ = v___x_2083_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_a_2081_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg___boxed(lean_object* v_type_2089_, lean_object* v_k_2090_, lean_object* v_cleanupAnnotations_2091_, lean_object* v_whnfType_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2098_; uint8_t v_whnfType_boxed_2099_; lean_object* v_res_2100_; 
v_cleanupAnnotations_boxed_2098_ = lean_unbox(v_cleanupAnnotations_2091_);
v_whnfType_boxed_2099_ = lean_unbox(v_whnfType_2092_);
v_res_2100_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_type_2089_, v_k_2090_, v_cleanupAnnotations_boxed_2098_, v_whnfType_boxed_2099_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
return v_res_2100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0(lean_object* v_00_u03b1_2101_, lean_object* v_type_2102_, lean_object* v_k_2103_, uint8_t v_cleanupAnnotations_2104_, uint8_t v_whnfType_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_){
_start:
{
lean_object* v___x_2111_; 
v___x_2111_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_type_2102_, v_k_2103_, v_cleanupAnnotations_2104_, v_whnfType_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_);
return v___x_2111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___boxed(lean_object* v_00_u03b1_2112_, lean_object* v_type_2113_, lean_object* v_k_2114_, lean_object* v_cleanupAnnotations_2115_, lean_object* v_whnfType_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2122_; uint8_t v_whnfType_boxed_2123_; lean_object* v_res_2124_; 
v_cleanupAnnotations_boxed_2122_ = lean_unbox(v_cleanupAnnotations_2115_);
v_whnfType_boxed_2123_ = lean_unbox(v_whnfType_2116_);
v_res_2124_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0(v_00_u03b1_2112_, v_type_2113_, v_k_2114_, v_cleanupAnnotations_boxed_2122_, v_whnfType_boxed_2123_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2117_);
return v_res_2124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0(lean_object* v___x_2125_, lean_object* v_ctorName_2126_, lean_object* v_xs_2127_, lean_object* v_type_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2134_ = lean_box(0);
v___x_2135_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_2128_, v___x_2134_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_a_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; 
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_a_2136_);
lean_dec_ref_known(v___x_2135_, 1);
v___x_2137_ = l_Lean_Expr_mvarId_x21(v_a_2136_);
v___x_2138_ = lean_array_get_size(v_xs_2127_);
v___x_2139_ = lean_unsigned_to_nat(1u);
v___x_2140_ = lean_nat_sub(v___x_2138_, v___x_2139_);
v___x_2141_ = lean_array_get_borrowed(v___x_2125_, v_xs_2127_, v___x_2140_);
lean_dec(v___x_2140_);
v___x_2142_ = l_Lean_Expr_fvarId_x21(v___x_2141_);
v___x_2143_ = l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(v_ctorName_2126_, v___x_2137_, v___x_2142_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
if (lean_obj_tag(v___x_2143_) == 0)
{
uint8_t v___x_2144_; uint8_t v___x_2145_; uint8_t v___x_2146_; lean_object* v___x_2147_; 
lean_dec_ref_known(v___x_2143_, 1);
v___x_2144_ = 0;
v___x_2145_ = 1;
v___x_2146_ = 1;
v___x_2147_ = l_Lean_Meta_mkLambdaFVars(v_xs_2127_, v_a_2136_, v___x_2144_, v___x_2145_, v___x_2144_, v___x_2145_, v___x_2146_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
return v___x_2147_;
}
else
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
lean_dec(v_a_2136_);
v_a_2148_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2143_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2143_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2153_; 
if (v_isShared_2151_ == 0)
{
v___x_2153_ = v___x_2150_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_a_2148_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
}
else
{
lean_dec(v_ctorName_2126_);
return v___x_2135_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0___boxed(lean_object* v___x_2156_, lean_object* v_ctorName_2157_, lean_object* v_xs_2158_, lean_object* v_type_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_){
_start:
{
lean_object* v_res_2165_; 
v_res_2165_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0(v___x_2156_, v_ctorName_2157_, v_xs_2158_, v_type_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2160_);
lean_dec_ref(v_xs_2158_);
lean_dec_ref(v___x_2156_);
return v_res_2165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(lean_object* v_ctorName_2166_, lean_object* v_targetType_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_){
_start:
{
lean_object* v___x_2173_; lean_object* v___f_2174_; uint8_t v___x_2175_; lean_object* v___x_2176_; 
v___x_2173_ = l_Lean_instInhabitedExpr;
v___f_2174_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2174_, 0, v___x_2173_);
lean_closure_set(v___f_2174_, 1, v_ctorName_2166_);
v___x_2175_ = 0;
v___x_2176_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_targetType_2167_, v___f_2174_, v___x_2175_, v___x_2175_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___boxed(lean_object* v_ctorName_2177_, lean_object* v_targetType_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_){
_start:
{
lean_object* v_res_2184_; 
v_res_2184_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_ctorName_2177_, v_targetType_2178_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_);
lean_dec(v_a_2182_);
lean_dec_ref(v_a_2181_);
lean_dec(v_a_2180_);
lean_dec_ref(v_a_2179_);
return v_res_2184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheoremNameFor(lean_object* v_ctorName_2188_){
_start:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2189_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheoremNameFor___closed__1));
v___x_2190_ = l_Lean_Name_append(v_ctorName_2188_, v___x_2189_);
return v___x_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(lean_object* v_e_2191_, lean_object* v___y_2192_){
_start:
{
uint8_t v___x_2194_; 
v___x_2194_ = l_Lean_Expr_hasMVar(v_e_2191_);
if (v___x_2194_ == 0)
{
lean_object* v___x_2195_; 
v___x_2195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2195_, 0, v_e_2191_);
return v___x_2195_;
}
else
{
lean_object* v___x_2196_; lean_object* v_mctx_2197_; lean_object* v___x_2198_; lean_object* v_fst_2199_; lean_object* v_snd_2200_; lean_object* v___x_2201_; lean_object* v_cache_2202_; lean_object* v_zetaDeltaFVarIds_2203_; lean_object* v_postponed_2204_; lean_object* v_diag_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2214_; 
v___x_2196_ = lean_st_ref_get(v___y_2192_);
v_mctx_2197_ = lean_ctor_get(v___x_2196_, 0);
lean_inc_ref(v_mctx_2197_);
lean_dec(v___x_2196_);
v___x_2198_ = l_Lean_instantiateMVarsCore(v_mctx_2197_, v_e_2191_);
v_fst_2199_ = lean_ctor_get(v___x_2198_, 0);
lean_inc(v_fst_2199_);
v_snd_2200_ = lean_ctor_get(v___x_2198_, 1);
lean_inc(v_snd_2200_);
lean_dec_ref(v___x_2198_);
v___x_2201_ = lean_st_ref_take(v___y_2192_);
v_cache_2202_ = lean_ctor_get(v___x_2201_, 1);
v_zetaDeltaFVarIds_2203_ = lean_ctor_get(v___x_2201_, 2);
v_postponed_2204_ = lean_ctor_get(v___x_2201_, 3);
v_diag_2205_ = lean_ctor_get(v___x_2201_, 4);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2214_ == 0)
{
lean_object* v_unused_2215_; 
v_unused_2215_ = lean_ctor_get(v___x_2201_, 0);
lean_dec(v_unused_2215_);
v___x_2207_ = v___x_2201_;
v_isShared_2208_ = v_isSharedCheck_2214_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_diag_2205_);
lean_inc(v_postponed_2204_);
lean_inc(v_zetaDeltaFVarIds_2203_);
lean_inc(v_cache_2202_);
lean_dec(v___x_2201_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2214_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2210_; 
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 0, v_snd_2200_);
v___x_2210_ = v___x_2207_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_snd_2200_);
lean_ctor_set(v_reuseFailAlloc_2213_, 1, v_cache_2202_);
lean_ctor_set(v_reuseFailAlloc_2213_, 2, v_zetaDeltaFVarIds_2203_);
lean_ctor_set(v_reuseFailAlloc_2213_, 3, v_postponed_2204_);
lean_ctor_set(v_reuseFailAlloc_2213_, 4, v_diag_2205_);
v___x_2210_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2211_ = lean_st_ref_put(v___y_2192_, v___x_2210_);
v___x_2212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2212_, 0, v_fst_2199_);
return v___x_2212_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg___boxed(lean_object* v_e_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_){
_start:
{
lean_object* v_res_2219_; 
v_res_2219_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_e_2216_, v___y_2217_);
lean_dec(v___y_2217_);
return v_res_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0(lean_object* v_e_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_){
_start:
{
lean_object* v___x_2226_; 
v___x_2226_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_e_2220_, v___y_2222_);
return v___x_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___boxed(lean_object* v_e_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
lean_object* v_res_2233_; 
v_res_2233_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0(v_e_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
return v_res_2233_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2234_ = lean_unsigned_to_nat(32u);
v___x_2235_ = lean_mk_empty_array_with_capacity(v___x_2234_);
v___x_2236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2236_, 0, v___x_2235_);
return v___x_2236_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2237_ = ((size_t)5ULL);
v___x_2238_ = lean_unsigned_to_nat(0u);
v___x_2239_ = lean_unsigned_to_nat(32u);
v___x_2240_ = lean_mk_empty_array_with_capacity(v___x_2239_);
v___x_2241_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0);
v___x_2242_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2242_, 0, v___x_2241_);
lean_ctor_set(v___x_2242_, 1, v___x_2240_);
lean_ctor_set(v___x_2242_, 2, v___x_2238_);
lean_ctor_set(v___x_2242_, 3, v___x_2238_);
lean_ctor_set_usize(v___x_2242_, 4, v___x_2237_);
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(lean_object* v___y_2243_){
_start:
{
lean_object* v___x_2245_; lean_object* v_traceState_2246_; lean_object* v_traces_2247_; lean_object* v___x_2248_; lean_object* v_traceState_2249_; lean_object* v_env_2250_; lean_object* v_nextMacroScope_2251_; lean_object* v_ngen_2252_; lean_object* v_auxDeclNGen_2253_; lean_object* v_cache_2254_; lean_object* v_recordedDeps_2255_; lean_object* v_messages_2256_; lean_object* v_infoState_2257_; lean_object* v_snapshotTasks_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2277_; 
v___x_2245_ = lean_st_ref_get(v___y_2243_);
v_traceState_2246_ = lean_ctor_get(v___x_2245_, 4);
lean_inc_ref(v_traceState_2246_);
lean_dec(v___x_2245_);
v_traces_2247_ = lean_ctor_get(v_traceState_2246_, 0);
lean_inc_ref(v_traces_2247_);
lean_dec_ref(v_traceState_2246_);
v___x_2248_ = lean_st_ref_take(v___y_2243_);
v_traceState_2249_ = lean_ctor_get(v___x_2248_, 4);
v_env_2250_ = lean_ctor_get(v___x_2248_, 0);
v_nextMacroScope_2251_ = lean_ctor_get(v___x_2248_, 1);
v_ngen_2252_ = lean_ctor_get(v___x_2248_, 2);
v_auxDeclNGen_2253_ = lean_ctor_get(v___x_2248_, 3);
v_cache_2254_ = lean_ctor_get(v___x_2248_, 5);
v_recordedDeps_2255_ = lean_ctor_get(v___x_2248_, 6);
v_messages_2256_ = lean_ctor_get(v___x_2248_, 7);
v_infoState_2257_ = lean_ctor_get(v___x_2248_, 8);
v_snapshotTasks_2258_ = lean_ctor_get(v___x_2248_, 9);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2248_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2260_ = v___x_2248_;
v_isShared_2261_ = v_isSharedCheck_2277_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_snapshotTasks_2258_);
lean_inc(v_infoState_2257_);
lean_inc(v_messages_2256_);
lean_inc(v_recordedDeps_2255_);
lean_inc(v_cache_2254_);
lean_inc(v_traceState_2249_);
lean_inc(v_auxDeclNGen_2253_);
lean_inc(v_ngen_2252_);
lean_inc(v_nextMacroScope_2251_);
lean_inc(v_env_2250_);
lean_dec(v___x_2248_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2277_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
uint64_t v_tid_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2275_; 
v_tid_2262_ = lean_ctor_get_uint64(v_traceState_2249_, sizeof(void*)*1);
v_isSharedCheck_2275_ = !lean_is_exclusive(v_traceState_2249_);
if (v_isSharedCheck_2275_ == 0)
{
lean_object* v_unused_2276_; 
v_unused_2276_ = lean_ctor_get(v_traceState_2249_, 0);
lean_dec(v_unused_2276_);
v___x_2264_ = v_traceState_2249_;
v_isShared_2265_ = v_isSharedCheck_2275_;
goto v_resetjp_2263_;
}
else
{
lean_dec(v_traceState_2249_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2275_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2266_; lean_object* v___x_2268_; 
v___x_2266_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1);
if (v_isShared_2265_ == 0)
{
lean_ctor_set(v___x_2264_, 0, v___x_2266_);
v___x_2268_ = v___x_2264_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v___x_2266_);
lean_ctor_set_uint64(v_reuseFailAlloc_2274_, sizeof(void*)*1, v_tid_2262_);
v___x_2268_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
lean_object* v___x_2270_; 
if (v_isShared_2261_ == 0)
{
lean_ctor_set(v___x_2260_, 4, v___x_2268_);
v___x_2270_ = v___x_2260_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v_env_2250_);
lean_ctor_set(v_reuseFailAlloc_2273_, 1, v_nextMacroScope_2251_);
lean_ctor_set(v_reuseFailAlloc_2273_, 2, v_ngen_2252_);
lean_ctor_set(v_reuseFailAlloc_2273_, 3, v_auxDeclNGen_2253_);
lean_ctor_set(v_reuseFailAlloc_2273_, 4, v___x_2268_);
lean_ctor_set(v_reuseFailAlloc_2273_, 5, v_cache_2254_);
lean_ctor_set(v_reuseFailAlloc_2273_, 6, v_recordedDeps_2255_);
lean_ctor_set(v_reuseFailAlloc_2273_, 7, v_messages_2256_);
lean_ctor_set(v_reuseFailAlloc_2273_, 8, v_infoState_2257_);
lean_ctor_set(v_reuseFailAlloc_2273_, 9, v_snapshotTasks_2258_);
v___x_2270_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; 
v___x_2271_ = lean_st_ref_put(v___y_2243_, v___x_2270_);
v___x_2272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2272_, 0, v_traces_2247_);
return v___x_2272_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___boxed(lean_object* v___y_2278_, lean_object* v___y_2279_){
_start:
{
lean_object* v_res_2280_; 
v_res_2280_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v___y_2278_);
lean_dec(v___y_2278_);
return v_res_2280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1(lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_){
_start:
{
lean_object* v___x_2286_; 
v___x_2286_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v___y_2284_);
return v___x_2286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___boxed(lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_){
_start:
{
lean_object* v_res_2292_; 
v_res_2292_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1(v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec(v___y_2288_);
lean_dec_ref(v___y_2287_);
return v_res_2292_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(lean_object* v_opts_2293_, lean_object* v_opt_2294_){
_start:
{
lean_object* v_name_2295_; lean_object* v_defValue_2296_; lean_object* v_map_2297_; lean_object* v___x_2298_; 
v_name_2295_ = lean_ctor_get(v_opt_2294_, 0);
v_defValue_2296_ = lean_ctor_get(v_opt_2294_, 1);
v_map_2297_ = lean_ctor_get(v_opts_2293_, 0);
v___x_2298_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2297_, v_name_2295_);
if (lean_obj_tag(v___x_2298_) == 0)
{
uint8_t v___x_2299_; 
v___x_2299_ = lean_unbox(v_defValue_2296_);
return v___x_2299_;
}
else
{
lean_object* v_val_2300_; 
v_val_2300_ = lean_ctor_get(v___x_2298_, 0);
lean_inc(v_val_2300_);
lean_dec_ref_known(v___x_2298_, 1);
if (lean_obj_tag(v_val_2300_) == 1)
{
uint8_t v_v_2301_; 
v_v_2301_ = lean_ctor_get_uint8(v_val_2300_, 0);
lean_dec_ref_known(v_val_2300_, 0);
return v_v_2301_;
}
else
{
uint8_t v___x_2302_; 
lean_dec(v_val_2300_);
v___x_2302_ = lean_unbox(v_defValue_2296_);
return v___x_2302_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2___boxed(lean_object* v_opts_2303_, lean_object* v_opt_2304_){
_start:
{
uint8_t v_res_2305_; lean_object* v_r_2306_; 
v_res_2305_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_opts_2303_, v_opt_2304_);
lean_dec_ref(v_opt_2304_);
lean_dec_ref(v_opts_2303_);
v_r_2306_ = lean_box(v_res_2305_);
return v_r_2306_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2308_; lean_object* v___x_2309_; 
v___x_2308_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__0));
v___x_2309_ = l_Lean_stringToMessageData(v___x_2308_);
return v___x_2309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0(lean_object* v_name_2310_, lean_object* v_x_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_){
_start:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2317_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1);
v___x_2318_ = l_Lean_MessageData_ofName(v_name_2310_);
v___x_2319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2319_, 0, v___x_2317_);
lean_ctor_set(v___x_2319_, 1, v___x_2318_);
v___x_2320_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_2321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2319_);
lean_ctor_set(v___x_2321_, 1, v___x_2320_);
v___x_2322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2321_);
return v___x_2322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed(lean_object* v_name_2323_, lean_object* v_x_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_){
_start:
{
lean_object* v_res_2330_; 
v_res_2330_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0(v_name_2323_, v_x_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
lean_dec_ref(v_x_2324_);
return v_res_2330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(lean_object* v_name_2331_, lean_object* v_val_2332_, lean_object* v_name_2333_, lean_object* v_levelParams_2334_, uint8_t v___x_2335_, lean_object* v_____r_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_){
_start:
{
lean_object* v___x_2342_; 
lean_inc_ref(v_val_2332_);
v___x_2342_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2331_, v_val_2332_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_object* v_a_2343_; lean_object* v___x_2344_; lean_object* v_a_2345_; lean_object* v___x_2346_; lean_object* v_a_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2359_; 
v_a_2343_ = lean_ctor_get(v___x_2342_, 0);
lean_inc(v_a_2343_);
lean_dec_ref_known(v___x_2342_, 1);
v___x_2344_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2332_, v___y_2338_);
v_a_2345_ = lean_ctor_get(v___x_2344_, 0);
lean_inc(v_a_2345_);
lean_dec_ref(v___x_2344_);
v___x_2346_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2343_, v___y_2338_);
v_a_2347_ = lean_ctor_get(v___x_2346_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2346_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2349_ = v___x_2346_;
v_isShared_2350_ = v_isSharedCheck_2359_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_a_2347_);
lean_dec(v___x_2346_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2359_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2356_; 
lean_inc(v_name_2333_);
v___x_2351_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2351_, 0, v_name_2333_);
lean_ctor_set(v___x_2351_, 1, v_levelParams_2334_);
lean_ctor_set(v___x_2351_, 2, v_a_2345_);
v___x_2352_ = lean_box(0);
v___x_2353_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2353_, 0, v_name_2333_);
lean_ctor_set(v___x_2353_, 1, v___x_2352_);
v___x_2354_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2354_, 0, v___x_2351_);
lean_ctor_set(v___x_2354_, 1, v_a_2347_);
lean_ctor_set(v___x_2354_, 2, v___x_2353_);
if (v_isShared_2350_ == 0)
{
lean_ctor_set_tag(v___x_2349_, 2);
lean_ctor_set(v___x_2349_, 0, v___x_2354_);
v___x_2356_ = v___x_2349_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v___x_2354_);
v___x_2356_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
lean_object* v___x_2357_; 
v___x_2357_ = l_Lean_addDecl(v___x_2356_, v___x_2335_, v___y_2339_, v___y_2340_);
return v___x_2357_;
}
}
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2367_; 
lean_dec(v_levelParams_2334_);
lean_dec(v_name_2333_);
lean_dec_ref(v_val_2332_);
v_a_2360_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2362_ = v___x_2342_;
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2342_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2365_; 
if (v_isShared_2363_ == 0)
{
v___x_2365_ = v___x_2362_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_a_2360_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1___boxed(lean_object* v_name_2368_, lean_object* v_val_2369_, lean_object* v_name_2370_, lean_object* v_levelParams_2371_, lean_object* v___x_2372_, lean_object* v_____r_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_){
_start:
{
uint8_t v___x_12478__boxed_2379_; lean_object* v_res_2380_; 
v___x_12478__boxed_2379_ = lean_unbox(v___x_2372_);
v_res_2380_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(v_name_2368_, v_val_2369_, v_name_2370_, v_levelParams_2371_, v___x_12478__boxed_2379_, v_____r_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
return v_res_2380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(lean_object* v_name_2381_, lean_object* v_val_2382_, lean_object* v_name_2383_, lean_object* v_levelParams_2384_, lean_object* v_____r_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_){
_start:
{
lean_object* v___x_2391_; 
lean_inc_ref(v_val_2382_);
v___x_2391_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2381_, v_val_2382_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_);
if (lean_obj_tag(v___x_2391_) == 0)
{
lean_object* v_a_2392_; lean_object* v___x_2393_; lean_object* v_a_2394_; lean_object* v___x_2395_; lean_object* v_a_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2409_; 
v_a_2392_ = lean_ctor_get(v___x_2391_, 0);
lean_inc(v_a_2392_);
lean_dec_ref_known(v___x_2391_, 1);
v___x_2393_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2382_, v___y_2387_);
v_a_2394_ = lean_ctor_get(v___x_2393_, 0);
lean_inc(v_a_2394_);
lean_dec_ref(v___x_2393_);
v___x_2395_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2392_, v___y_2387_);
v_a_2396_ = lean_ctor_get(v___x_2395_, 0);
v_isSharedCheck_2409_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2398_ = v___x_2395_;
v_isShared_2399_ = v_isSharedCheck_2409_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_a_2396_);
lean_dec(v___x_2395_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2409_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2405_; 
lean_inc(v_name_2383_);
v___x_2400_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2400_, 0, v_name_2383_);
lean_ctor_set(v___x_2400_, 1, v_levelParams_2384_);
lean_ctor_set(v___x_2400_, 2, v_a_2394_);
v___x_2401_ = lean_box(0);
v___x_2402_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2402_, 0, v_name_2383_);
lean_ctor_set(v___x_2402_, 1, v___x_2401_);
v___x_2403_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2403_, 0, v___x_2400_);
lean_ctor_set(v___x_2403_, 1, v_a_2396_);
lean_ctor_set(v___x_2403_, 2, v___x_2402_);
if (v_isShared_2399_ == 0)
{
lean_ctor_set_tag(v___x_2398_, 2);
lean_ctor_set(v___x_2398_, 0, v___x_2403_);
v___x_2405_ = v___x_2398_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v___x_2403_);
v___x_2405_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
uint8_t v___x_2406_; lean_object* v___x_2407_; 
v___x_2406_ = 0;
v___x_2407_ = l_Lean_addDecl(v___x_2405_, v___x_2406_, v___y_2388_, v___y_2389_);
return v___x_2407_;
}
}
}
else
{
lean_object* v_a_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2417_; 
lean_dec(v_levelParams_2384_);
lean_dec(v_name_2383_);
lean_dec_ref(v_val_2382_);
v_a_2410_ = lean_ctor_get(v___x_2391_, 0);
v_isSharedCheck_2417_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2417_ == 0)
{
v___x_2412_ = v___x_2391_;
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_a_2410_);
lean_dec(v___x_2391_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2415_; 
if (v_isShared_2413_ == 0)
{
v___x_2415_ = v___x_2412_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v_a_2410_);
v___x_2415_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
return v___x_2415_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2___boxed(lean_object* v_name_2418_, lean_object* v_val_2419_, lean_object* v_name_2420_, lean_object* v_levelParams_2421_, lean_object* v_____r_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_){
_start:
{
lean_object* v_res_2428_; 
v_res_2428_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(v_name_2418_, v_val_2419_, v_name_2420_, v_levelParams_2421_, v_____r_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_);
lean_dec(v___y_2426_);
lean_dec_ref(v___y_2425_);
lean_dec(v___y_2424_);
lean_dec_ref(v___y_2423_);
return v_res_2428_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3_spec__4(size_t v_sz_2429_, size_t v_i_2430_, lean_object* v_bs_2431_){
_start:
{
uint8_t v___x_2432_; 
v___x_2432_ = lean_usize_dec_lt(v_i_2430_, v_sz_2429_);
if (v___x_2432_ == 0)
{
return v_bs_2431_;
}
else
{
lean_object* v_v_2433_; lean_object* v_msg_2434_; lean_object* v___x_2435_; lean_object* v_bs_x27_2436_; size_t v___x_2437_; size_t v___x_2438_; lean_object* v___x_2439_; 
v_v_2433_ = lean_array_uget_borrowed(v_bs_2431_, v_i_2430_);
v_msg_2434_ = lean_ctor_get(v_v_2433_, 1);
lean_inc_ref(v_msg_2434_);
v___x_2435_ = lean_unsigned_to_nat(0u);
v_bs_x27_2436_ = lean_array_uset(v_bs_2431_, v_i_2430_, v___x_2435_);
v___x_2437_ = ((size_t)1ULL);
v___x_2438_ = lean_usize_add(v_i_2430_, v___x_2437_);
v___x_2439_ = lean_array_uset(v_bs_x27_2436_, v_i_2430_, v_msg_2434_);
v_i_2430_ = v___x_2438_;
v_bs_2431_ = v___x_2439_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_2441_, lean_object* v_i_2442_, lean_object* v_bs_2443_){
_start:
{
size_t v_sz_boxed_2444_; size_t v_i_boxed_2445_; lean_object* v_res_2446_; 
v_sz_boxed_2444_ = lean_unbox_usize(v_sz_2441_);
lean_dec(v_sz_2441_);
v_i_boxed_2445_ = lean_unbox_usize(v_i_2442_);
lean_dec(v_i_2442_);
v_res_2446_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3_spec__4(v_sz_boxed_2444_, v_i_boxed_2445_, v_bs_2443_);
return v_res_2446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(lean_object* v_oldTraces_2447_, lean_object* v_data_2448_, lean_object* v_ref_2449_, lean_object* v_msg_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_){
_start:
{
lean_object* v_toCold_2456_; lean_object* v_currRecDepth_2457_; lean_object* v_ref_2458_; uint16_t v_optionFlags_2459_; uint8_t v_suppressElabErrors_2460_; uint8_t v_isRecordingDeps_2461_; lean_object* v_ref_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v_traceState_2465_; lean_object* v_traces_2466_; lean_object* v___x_2467_; size_t v_sz_2468_; size_t v___x_2469_; lean_object* v___x_2470_; lean_object* v_msg_2471_; lean_object* v___x_2472_; lean_object* v_a_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2511_; 
v_toCold_2456_ = lean_ctor_get(v___y_2453_, 0);
v_currRecDepth_2457_ = lean_ctor_get(v___y_2453_, 1);
v_ref_2458_ = lean_ctor_get(v___y_2453_, 2);
v_optionFlags_2459_ = lean_ctor_get_uint16(v___y_2453_, sizeof(void*)*3);
v_suppressElabErrors_2460_ = lean_ctor_get_uint8(v___y_2453_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2461_ = lean_ctor_get_uint8(v___y_2453_, sizeof(void*)*3 + 3);
v_ref_2462_ = l_Lean_replaceRef(v_ref_2449_, v_ref_2458_);
lean_inc(v_currRecDepth_2457_);
lean_inc_ref(v_toCold_2456_);
v___x_2463_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2463_, 0, v_toCold_2456_);
lean_ctor_set(v___x_2463_, 1, v_currRecDepth_2457_);
lean_ctor_set(v___x_2463_, 2, v_ref_2462_);
lean_ctor_set_uint16(v___x_2463_, sizeof(void*)*3, v_optionFlags_2459_);
lean_ctor_set_uint8(v___x_2463_, sizeof(void*)*3 + 2, v_suppressElabErrors_2460_);
lean_ctor_set_uint8(v___x_2463_, sizeof(void*)*3 + 3, v_isRecordingDeps_2461_);
v___x_2464_ = lean_st_ref_get(v___y_2454_);
v_traceState_2465_ = lean_ctor_get(v___x_2464_, 4);
lean_inc_ref(v_traceState_2465_);
lean_dec(v___x_2464_);
v_traces_2466_ = lean_ctor_get(v_traceState_2465_, 0);
lean_inc_ref(v_traces_2466_);
lean_dec_ref(v_traceState_2465_);
v___x_2467_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2466_);
lean_dec_ref(v_traces_2466_);
v_sz_2468_ = lean_array_size(v___x_2467_);
v___x_2469_ = ((size_t)0ULL);
v___x_2470_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3_spec__4(v_sz_2468_, v___x_2469_, v___x_2467_);
v_msg_2471_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2471_, 0, v_data_2448_);
lean_ctor_set(v_msg_2471_, 1, v_msg_2450_);
lean_ctor_set(v_msg_2471_, 2, v___x_2470_);
v___x_2472_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msg_2471_, v___y_2451_, v___y_2452_, v___x_2463_, v___y_2454_);
lean_dec_ref_known(v___x_2463_, 3);
v_a_2473_ = lean_ctor_get(v___x_2472_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2472_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2475_ = v___x_2472_;
v_isShared_2476_ = v_isSharedCheck_2511_;
goto v_resetjp_2474_;
}
else
{
lean_inc(v_a_2473_);
lean_dec(v___x_2472_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2511_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
lean_object* v___x_2477_; lean_object* v_traceState_2478_; lean_object* v_env_2479_; lean_object* v_nextMacroScope_2480_; lean_object* v_ngen_2481_; lean_object* v_auxDeclNGen_2482_; lean_object* v_cache_2483_; lean_object* v_recordedDeps_2484_; lean_object* v_messages_2485_; lean_object* v_infoState_2486_; lean_object* v_snapshotTasks_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2510_; 
v___x_2477_ = lean_st_ref_take(v___y_2454_);
v_traceState_2478_ = lean_ctor_get(v___x_2477_, 4);
v_env_2479_ = lean_ctor_get(v___x_2477_, 0);
v_nextMacroScope_2480_ = lean_ctor_get(v___x_2477_, 1);
v_ngen_2481_ = lean_ctor_get(v___x_2477_, 2);
v_auxDeclNGen_2482_ = lean_ctor_get(v___x_2477_, 3);
v_cache_2483_ = lean_ctor_get(v___x_2477_, 5);
v_recordedDeps_2484_ = lean_ctor_get(v___x_2477_, 6);
v_messages_2485_ = lean_ctor_get(v___x_2477_, 7);
v_infoState_2486_ = lean_ctor_get(v___x_2477_, 8);
v_snapshotTasks_2487_ = lean_ctor_get(v___x_2477_, 9);
v_isSharedCheck_2510_ = !lean_is_exclusive(v___x_2477_);
if (v_isSharedCheck_2510_ == 0)
{
v___x_2489_ = v___x_2477_;
v_isShared_2490_ = v_isSharedCheck_2510_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_snapshotTasks_2487_);
lean_inc(v_infoState_2486_);
lean_inc(v_messages_2485_);
lean_inc(v_recordedDeps_2484_);
lean_inc(v_cache_2483_);
lean_inc(v_traceState_2478_);
lean_inc(v_auxDeclNGen_2482_);
lean_inc(v_ngen_2481_);
lean_inc(v_nextMacroScope_2480_);
lean_inc(v_env_2479_);
lean_dec(v___x_2477_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2510_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
uint64_t v_tid_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2508_; 
v_tid_2491_ = lean_ctor_get_uint64(v_traceState_2478_, sizeof(void*)*1);
v_isSharedCheck_2508_ = !lean_is_exclusive(v_traceState_2478_);
if (v_isSharedCheck_2508_ == 0)
{
lean_object* v_unused_2509_; 
v_unused_2509_ = lean_ctor_get(v_traceState_2478_, 0);
lean_dec(v_unused_2509_);
v___x_2493_ = v_traceState_2478_;
v_isShared_2494_ = v_isSharedCheck_2508_;
goto v_resetjp_2492_;
}
else
{
lean_dec(v_traceState_2478_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2508_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2499_; 
v___x_2495_ = lean_box(0);
v___x_2496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2496_, 0, v_ref_2449_);
lean_ctor_set(v___x_2496_, 1, v_a_2473_);
v___x_2497_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2447_, v___x_2496_);
if (v_isShared_2494_ == 0)
{
lean_ctor_set(v___x_2493_, 0, v___x_2497_);
v___x_2499_ = v___x_2493_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v___x_2497_);
lean_ctor_set_uint64(v_reuseFailAlloc_2507_, sizeof(void*)*1, v_tid_2491_);
v___x_2499_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
lean_object* v___x_2501_; 
if (v_isShared_2490_ == 0)
{
lean_ctor_set(v___x_2489_, 4, v___x_2499_);
v___x_2501_ = v___x_2489_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v_env_2479_);
lean_ctor_set(v_reuseFailAlloc_2506_, 1, v_nextMacroScope_2480_);
lean_ctor_set(v_reuseFailAlloc_2506_, 2, v_ngen_2481_);
lean_ctor_set(v_reuseFailAlloc_2506_, 3, v_auxDeclNGen_2482_);
lean_ctor_set(v_reuseFailAlloc_2506_, 4, v___x_2499_);
lean_ctor_set(v_reuseFailAlloc_2506_, 5, v_cache_2483_);
lean_ctor_set(v_reuseFailAlloc_2506_, 6, v_recordedDeps_2484_);
lean_ctor_set(v_reuseFailAlloc_2506_, 7, v_messages_2485_);
lean_ctor_set(v_reuseFailAlloc_2506_, 8, v_infoState_2486_);
lean_ctor_set(v_reuseFailAlloc_2506_, 9, v_snapshotTasks_2487_);
v___x_2501_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
lean_object* v___x_2502_; lean_object* v___x_2504_; 
v___x_2502_ = lean_st_ref_put(v___y_2454_, v___x_2501_);
if (v_isShared_2476_ == 0)
{
lean_ctor_set(v___x_2475_, 0, v___x_2495_);
v___x_2504_ = v___x_2475_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v___x_2495_);
v___x_2504_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
return v___x_2504_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3___boxed(lean_object* v_oldTraces_2512_, lean_object* v_data_2513_, lean_object* v_ref_2514_, lean_object* v_msg_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_){
_start:
{
lean_object* v_res_2521_; 
v_res_2521_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(v_oldTraces_2512_, v_data_2513_, v_ref_2514_, v_msg_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
return v_res_2521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(lean_object* v_opts_2522_, lean_object* v_opt_2523_){
_start:
{
lean_object* v_name_2524_; lean_object* v_defValue_2525_; lean_object* v_map_2526_; lean_object* v___x_2527_; 
v_name_2524_ = lean_ctor_get(v_opt_2523_, 0);
v_defValue_2525_ = lean_ctor_get(v_opt_2523_, 1);
v_map_2526_ = lean_ctor_get(v_opts_2522_, 0);
v___x_2527_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2526_, v_name_2524_);
if (lean_obj_tag(v___x_2527_) == 0)
{
lean_inc(v_defValue_2525_);
return v_defValue_2525_;
}
else
{
lean_object* v_val_2528_; 
v_val_2528_ = lean_ctor_get(v___x_2527_, 0);
lean_inc(v_val_2528_);
lean_dec_ref_known(v___x_2527_, 1);
if (lean_obj_tag(v_val_2528_) == 3)
{
lean_object* v_v_2529_; 
v_v_2529_ = lean_ctor_get(v_val_2528_, 0);
lean_inc(v_v_2529_);
lean_dec_ref_known(v_val_2528_, 1);
return v_v_2529_;
}
else
{
lean_dec(v_val_2528_);
lean_inc(v_defValue_2525_);
return v_defValue_2525_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6___boxed(lean_object* v_opts_2530_, lean_object* v_opt_2531_){
_start:
{
lean_object* v_res_2532_; 
v_res_2532_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(v_opts_2530_, v_opt_2531_);
lean_dec_ref(v_opt_2531_);
lean_dec_ref(v_opts_2530_);
return v_res_2532_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5(lean_object* v_e_2533_){
_start:
{
if (lean_obj_tag(v_e_2533_) == 0)
{
uint8_t v___x_2534_; 
v___x_2534_ = 2;
return v___x_2534_;
}
else
{
uint8_t v___x_2535_; 
v___x_2535_ = 0;
return v___x_2535_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___boxed(lean_object* v_e_2536_){
_start:
{
uint8_t v_res_2537_; lean_object* v_r_2538_; 
v_res_2537_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5(v_e_2536_);
lean_dec_ref(v_e_2536_);
v_r_2538_ = lean_box(v_res_2537_);
return v_r_2538_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg(lean_object* v_x_2539_){
_start:
{
if (lean_obj_tag(v_x_2539_) == 0)
{
lean_object* v_a_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2548_; 
v_a_2541_ = lean_ctor_get(v_x_2539_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v_x_2539_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2543_ = v_x_2539_;
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_a_2541_);
lean_dec(v_x_2539_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2546_; 
if (v_isShared_2544_ == 0)
{
lean_ctor_set_tag(v___x_2543_, 1);
v___x_2546_ = v___x_2543_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_a_2541_);
v___x_2546_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
return v___x_2546_;
}
}
}
else
{
lean_object* v_a_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2556_; 
v_a_2549_ = lean_ctor_get(v_x_2539_, 0);
v_isSharedCheck_2556_ = !lean_is_exclusive(v_x_2539_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2551_ = v_x_2539_;
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_a_2549_);
lean_dec(v_x_2539_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2554_; 
if (v_isShared_2552_ == 0)
{
lean_ctor_set_tag(v___x_2551_, 0);
v___x_2554_ = v___x_2551_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v_a_2549_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
return v___x_2554_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg___boxed(lean_object* v_x_2557_, lean_object* v___y_2558_){
_start:
{
lean_object* v_res_2559_; 
v_res_2559_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg(v_x_2557_);
return v_res_2559_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2561_; lean_object* v___x_2562_; 
v___x_2561_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__0));
v___x_2562_ = l_Lean_stringToMessageData(v___x_2561_);
return v___x_2562_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2563_; double v___x_2564_; 
v___x_2563_ = lean_unsigned_to_nat(1000u);
v___x_2564_ = lean_float_of_nat(v___x_2563_);
return v___x_2564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(lean_object* v_cls_2565_, uint8_t v_collapsed_2566_, lean_object* v_tag_2567_, lean_object* v_opts_2568_, uint8_t v_clsEnabled_2569_, lean_object* v_oldTraces_2570_, lean_object* v_msg_2571_, lean_object* v_resStartStop_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_){
_start:
{
lean_object* v_fst_2578_; lean_object* v_snd_2579_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v_data_2583_; lean_object* v_fst_2586_; lean_object* v_snd_2587_; lean_object* v___x_2588_; uint8_t v___x_2589_; lean_object* v___y_2591_; lean_object* v_a_2592_; uint8_t v___y_2607_; double v___y_2639_; 
v_fst_2578_ = lean_ctor_get(v_resStartStop_2572_, 0);
lean_inc(v_fst_2578_);
v_snd_2579_ = lean_ctor_get(v_resStartStop_2572_, 1);
lean_inc(v_snd_2579_);
lean_dec_ref(v_resStartStop_2572_);
v_fst_2586_ = lean_ctor_get(v_snd_2579_, 0);
lean_inc(v_fst_2586_);
v_snd_2587_ = lean_ctor_get(v_snd_2579_, 1);
lean_inc(v_snd_2587_);
lean_dec(v_snd_2579_);
v___x_2588_ = l_Lean_trace_profiler;
v___x_2589_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_opts_2568_, v___x_2588_);
if (v___x_2589_ == 0)
{
v___y_2607_ = v___x_2589_;
goto v___jp_2606_;
}
else
{
lean_object* v___x_2644_; uint8_t v___x_2645_; 
v___x_2644_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2645_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_opts_2568_, v___x_2644_);
if (v___x_2645_ == 0)
{
lean_object* v___x_2646_; lean_object* v___x_2647_; double v___x_2648_; double v___x_2649_; double v___x_2650_; 
v___x_2646_ = l_Lean_trace_profiler_threshold;
v___x_2647_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(v_opts_2568_, v___x_2646_);
v___x_2648_ = lean_float_of_nat(v___x_2647_);
v___x_2649_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2);
v___x_2650_ = lean_float_div(v___x_2648_, v___x_2649_);
v___y_2639_ = v___x_2650_;
goto v___jp_2638_;
}
else
{
lean_object* v___x_2651_; lean_object* v___x_2652_; double v___x_2653_; 
v___x_2651_ = l_Lean_trace_profiler_threshold;
v___x_2652_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(v_opts_2568_, v___x_2651_);
v___x_2653_ = lean_float_of_nat(v___x_2652_);
v___y_2639_ = v___x_2653_;
goto v___jp_2638_;
}
}
v___jp_2580_:
{
lean_object* v___x_2584_; 
lean_inc(v___y_2582_);
v___x_2584_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(v_oldTraces_2570_, v_data_2583_, v___y_2582_, v___y_2581_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_);
if (lean_obj_tag(v___x_2584_) == 0)
{
lean_object* v___x_2585_; 
lean_dec_ref_known(v___x_2584_, 1);
v___x_2585_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg(v_fst_2578_);
return v___x_2585_;
}
else
{
lean_dec(v_fst_2578_);
return v___x_2584_;
}
}
v___jp_2590_:
{
uint8_t v_result_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; double v___x_2596_; lean_object* v_data_2597_; 
v_result_2593_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5(v_fst_2578_);
v___x_2594_ = lean_box(v_result_2593_);
v___x_2595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2595_, 0, v___x_2594_);
v___x_2596_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0);
lean_inc_ref(v_tag_2567_);
lean_inc_ref(v___x_2595_);
lean_inc(v_cls_2565_);
v_data_2597_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2597_, 0, v_cls_2565_);
lean_ctor_set(v_data_2597_, 1, v___x_2595_);
lean_ctor_set(v_data_2597_, 2, v_tag_2567_);
lean_ctor_set_float(v_data_2597_, sizeof(void*)*3, v___x_2596_);
lean_ctor_set_float(v_data_2597_, sizeof(void*)*3 + 8, v___x_2596_);
lean_ctor_set_uint8(v_data_2597_, sizeof(void*)*3 + 16, v_collapsed_2566_);
if (v___x_2589_ == 0)
{
lean_dec_ref_known(v___x_2595_, 1);
lean_dec(v_snd_2587_);
lean_dec(v_fst_2586_);
lean_dec_ref(v_tag_2567_);
lean_dec(v_cls_2565_);
v___y_2581_ = v_a_2592_;
v___y_2582_ = v___y_2591_;
v_data_2583_ = v_data_2597_;
goto v___jp_2580_;
}
else
{
lean_object* v_data_2598_; double v___x_2599_; double v___x_2600_; 
lean_dec_ref_known(v_data_2597_, 3);
v_data_2598_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2598_, 0, v_cls_2565_);
lean_ctor_set(v_data_2598_, 1, v___x_2595_);
lean_ctor_set(v_data_2598_, 2, v_tag_2567_);
v___x_2599_ = lean_unbox_float(v_fst_2586_);
lean_dec(v_fst_2586_);
lean_ctor_set_float(v_data_2598_, sizeof(void*)*3, v___x_2599_);
v___x_2600_ = lean_unbox_float(v_snd_2587_);
lean_dec(v_snd_2587_);
lean_ctor_set_float(v_data_2598_, sizeof(void*)*3 + 8, v___x_2600_);
lean_ctor_set_uint8(v_data_2598_, sizeof(void*)*3 + 16, v_collapsed_2566_);
v___y_2581_ = v_a_2592_;
v___y_2582_ = v___y_2591_;
v_data_2583_ = v_data_2598_;
goto v___jp_2580_;
}
}
v___jp_2601_:
{
lean_object* v_ref_2602_; lean_object* v___x_2603_; 
v_ref_2602_ = lean_ctor_get(v___y_2575_, 2);
lean_inc(v___y_2576_);
lean_inc_ref(v___y_2575_);
lean_inc(v___y_2574_);
lean_inc_ref(v___y_2573_);
lean_inc(v_fst_2578_);
v___x_2603_ = lean_apply_6(v_msg_2571_, v_fst_2578_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, lean_box(0));
if (lean_obj_tag(v___x_2603_) == 0)
{
lean_object* v_a_2604_; 
v_a_2604_ = lean_ctor_get(v___x_2603_, 0);
lean_inc(v_a_2604_);
lean_dec_ref_known(v___x_2603_, 1);
v___y_2591_ = v_ref_2602_;
v_a_2592_ = v_a_2604_;
goto v___jp_2590_;
}
else
{
lean_object* v___x_2605_; 
lean_dec_ref_known(v___x_2603_, 1);
v___x_2605_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1);
v___y_2591_ = v_ref_2602_;
v_a_2592_ = v___x_2605_;
goto v___jp_2590_;
}
}
v___jp_2606_:
{
if (v_clsEnabled_2569_ == 0)
{
if (v___y_2607_ == 0)
{
lean_object* v___x_2608_; lean_object* v_traceState_2609_; lean_object* v_env_2610_; lean_object* v_nextMacroScope_2611_; lean_object* v_ngen_2612_; lean_object* v_auxDeclNGen_2613_; lean_object* v_cache_2614_; lean_object* v_recordedDeps_2615_; lean_object* v_messages_2616_; lean_object* v_infoState_2617_; lean_object* v_snapshotTasks_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2637_; 
lean_dec(v_snd_2587_);
lean_dec(v_fst_2586_);
lean_dec_ref(v_msg_2571_);
lean_dec_ref(v_tag_2567_);
lean_dec(v_cls_2565_);
v___x_2608_ = lean_st_ref_take(v___y_2576_);
v_traceState_2609_ = lean_ctor_get(v___x_2608_, 4);
v_env_2610_ = lean_ctor_get(v___x_2608_, 0);
v_nextMacroScope_2611_ = lean_ctor_get(v___x_2608_, 1);
v_ngen_2612_ = lean_ctor_get(v___x_2608_, 2);
v_auxDeclNGen_2613_ = lean_ctor_get(v___x_2608_, 3);
v_cache_2614_ = lean_ctor_get(v___x_2608_, 5);
v_recordedDeps_2615_ = lean_ctor_get(v___x_2608_, 6);
v_messages_2616_ = lean_ctor_get(v___x_2608_, 7);
v_infoState_2617_ = lean_ctor_get(v___x_2608_, 8);
v_snapshotTasks_2618_ = lean_ctor_get(v___x_2608_, 9);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2620_ = v___x_2608_;
v_isShared_2621_ = v_isSharedCheck_2637_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_snapshotTasks_2618_);
lean_inc(v_infoState_2617_);
lean_inc(v_messages_2616_);
lean_inc(v_recordedDeps_2615_);
lean_inc(v_cache_2614_);
lean_inc(v_traceState_2609_);
lean_inc(v_auxDeclNGen_2613_);
lean_inc(v_ngen_2612_);
lean_inc(v_nextMacroScope_2611_);
lean_inc(v_env_2610_);
lean_dec(v___x_2608_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2637_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
uint64_t v_tid_2622_; lean_object* v_traces_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2636_; 
v_tid_2622_ = lean_ctor_get_uint64(v_traceState_2609_, sizeof(void*)*1);
v_traces_2623_ = lean_ctor_get(v_traceState_2609_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v_traceState_2609_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2625_ = v_traceState_2609_;
v_isShared_2626_ = v_isSharedCheck_2636_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_traces_2623_);
lean_dec(v_traceState_2609_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2636_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v___x_2627_; lean_object* v___x_2629_; 
v___x_2627_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2570_, v_traces_2623_);
lean_dec_ref(v_traces_2623_);
if (v_isShared_2626_ == 0)
{
lean_ctor_set(v___x_2625_, 0, v___x_2627_);
v___x_2629_ = v___x_2625_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v___x_2627_);
lean_ctor_set_uint64(v_reuseFailAlloc_2635_, sizeof(void*)*1, v_tid_2622_);
v___x_2629_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
lean_object* v___x_2631_; 
if (v_isShared_2621_ == 0)
{
lean_ctor_set(v___x_2620_, 4, v___x_2629_);
v___x_2631_ = v___x_2620_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v_env_2610_);
lean_ctor_set(v_reuseFailAlloc_2634_, 1, v_nextMacroScope_2611_);
lean_ctor_set(v_reuseFailAlloc_2634_, 2, v_ngen_2612_);
lean_ctor_set(v_reuseFailAlloc_2634_, 3, v_auxDeclNGen_2613_);
lean_ctor_set(v_reuseFailAlloc_2634_, 4, v___x_2629_);
lean_ctor_set(v_reuseFailAlloc_2634_, 5, v_cache_2614_);
lean_ctor_set(v_reuseFailAlloc_2634_, 6, v_recordedDeps_2615_);
lean_ctor_set(v_reuseFailAlloc_2634_, 7, v_messages_2616_);
lean_ctor_set(v_reuseFailAlloc_2634_, 8, v_infoState_2617_);
lean_ctor_set(v_reuseFailAlloc_2634_, 9, v_snapshotTasks_2618_);
v___x_2631_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
lean_object* v___x_2632_; lean_object* v___x_2633_; 
v___x_2632_ = lean_st_ref_put(v___y_2576_, v___x_2631_);
v___x_2633_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg(v_fst_2578_);
return v___x_2633_;
}
}
}
}
}
else
{
goto v___jp_2601_;
}
}
else
{
goto v___jp_2601_;
}
}
v___jp_2638_:
{
double v___x_2640_; double v___x_2641_; double v___x_2642_; uint8_t v___x_2643_; 
v___x_2640_ = lean_unbox_float(v_snd_2587_);
v___x_2641_ = lean_unbox_float(v_fst_2586_);
v___x_2642_ = lean_float_sub(v___x_2640_, v___x_2641_);
v___x_2643_ = lean_float_decLt(v___y_2639_, v___x_2642_);
v___y_2607_ = v___x_2643_;
goto v___jp_2606_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___boxed(lean_object* v_cls_2654_, lean_object* v_collapsed_2655_, lean_object* v_tag_2656_, lean_object* v_opts_2657_, lean_object* v_clsEnabled_2658_, lean_object* v_oldTraces_2659_, lean_object* v_msg_2660_, lean_object* v_resStartStop_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_){
_start:
{
uint8_t v_collapsed_boxed_2667_; uint8_t v_clsEnabled_boxed_2668_; lean_object* v_res_2669_; 
v_collapsed_boxed_2667_ = lean_unbox(v_collapsed_2655_);
v_clsEnabled_boxed_2668_ = lean_unbox(v_clsEnabled_2658_);
v_res_2669_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_2654_, v_collapsed_boxed_2667_, v_tag_2656_, v_opts_2657_, v_clsEnabled_boxed_2668_, v_oldTraces_2659_, v_msg_2660_, v_resStartStop_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_);
lean_dec(v___y_2665_);
lean_dec_ref(v___y_2664_);
lean_dec(v___y_2663_);
lean_dec_ref(v___y_2662_);
lean_dec_ref(v_opts_2657_);
return v_res_2669_;
}
}
static double _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0(void){
_start:
{
lean_object* v___x_2670_; double v___x_2671_; 
v___x_2670_ = lean_unsigned_to_nat(1000000000u);
v___x_2671_ = lean_float_of_nat(v___x_2670_);
return v___x_2671_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2(void){
_start:
{
lean_object* v___x_2673_; lean_object* v___x_2674_; 
v___x_2673_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1));
v___x_2674_ = l_Lean_stringToMessageData(v___x_2673_);
return v___x_2674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(lean_object* v_ctorVal_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_){
_start:
{
lean_object* v_toConstantVal_2681_; lean_object* v_toCold_2682_; lean_object* v_options_2683_; lean_object* v_name_2684_; lean_object* v_levelParams_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2896_; 
v_toConstantVal_2681_ = lean_ctor_get(v_ctorVal_2675_, 0);
lean_inc_ref(v_toConstantVal_2681_);
v_toCold_2682_ = lean_ctor_get(v_a_2678_, 0);
v_options_2683_ = lean_ctor_get(v_toCold_2682_, 2);
v_name_2684_ = lean_ctor_get(v_toConstantVal_2681_, 0);
v_levelParams_2685_ = lean_ctor_get(v_toConstantVal_2681_, 1);
v_isSharedCheck_2896_ = !lean_is_exclusive(v_toConstantVal_2681_);
if (v_isSharedCheck_2896_ == 0)
{
lean_object* v_unused_2897_; 
v_unused_2897_ = lean_ctor_get(v_toConstantVal_2681_, 2);
lean_dec(v_unused_2897_);
v___x_2687_ = v_toConstantVal_2681_;
v_isShared_2688_ = v_isSharedCheck_2896_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_levelParams_2685_);
lean_inc(v_name_2684_);
lean_dec(v_toConstantVal_2681_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2896_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v_inheritedTraceOptions_2689_; uint8_t v_hasTrace_2690_; lean_object* v_name_2691_; 
v_inheritedTraceOptions_2689_ = lean_ctor_get(v_toCold_2682_, 11);
v_hasTrace_2690_ = lean_ctor_get_uint8(v_options_2683_, sizeof(void*)*1);
lean_inc(v_name_2684_);
v_name_2691_ = l_Lean_Meta_mkInjectiveTheoremNameFor(v_name_2684_);
if (v_hasTrace_2690_ == 0)
{
lean_object* v___x_2692_; 
v___x_2692_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2675_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_);
if (lean_obj_tag(v___x_2692_) == 0)
{
lean_object* v_a_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2730_; 
v_a_2693_ = lean_ctor_get(v___x_2692_, 0);
v_isSharedCheck_2730_ = !lean_is_exclusive(v___x_2692_);
if (v_isSharedCheck_2730_ == 0)
{
v___x_2695_ = v___x_2692_;
v_isShared_2696_ = v_isSharedCheck_2730_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_a_2693_);
lean_dec(v___x_2692_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2730_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
if (lean_obj_tag(v_a_2693_) == 1)
{
lean_object* v_val_2697_; lean_object* v___x_2698_; 
lean_del_object(v___x_2695_);
v_val_2697_ = lean_ctor_get(v_a_2693_, 0);
lean_inc_n(v_val_2697_, 2);
lean_dec_ref_known(v_a_2693_, 1);
v___x_2698_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2684_, v_val_2697_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_);
if (lean_obj_tag(v___x_2698_) == 0)
{
lean_object* v_a_2699_; lean_object* v___x_2700_; lean_object* v_a_2701_; lean_object* v___x_2702_; lean_object* v_a_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2717_; 
v_a_2699_ = lean_ctor_get(v___x_2698_, 0);
lean_inc(v_a_2699_);
lean_dec_ref_known(v___x_2698_, 1);
v___x_2700_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2697_, v_a_2677_);
v_a_2701_ = lean_ctor_get(v___x_2700_, 0);
lean_inc(v_a_2701_);
lean_dec_ref(v___x_2700_);
v___x_2702_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2699_, v_a_2677_);
v_a_2703_ = lean_ctor_get(v___x_2702_, 0);
v_isSharedCheck_2717_ = !lean_is_exclusive(v___x_2702_);
if (v_isSharedCheck_2717_ == 0)
{
v___x_2705_ = v___x_2702_;
v_isShared_2706_ = v_isSharedCheck_2717_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_a_2703_);
lean_dec(v___x_2702_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2717_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2708_; 
lean_inc(v_name_2691_);
if (v_isShared_2688_ == 0)
{
lean_ctor_set(v___x_2687_, 2, v_a_2701_);
lean_ctor_set(v___x_2687_, 0, v_name_2691_);
v___x_2708_ = v___x_2687_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v_name_2691_);
lean_ctor_set(v_reuseFailAlloc_2716_, 1, v_levelParams_2685_);
lean_ctor_set(v_reuseFailAlloc_2716_, 2, v_a_2701_);
v___x_2708_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2713_; 
v___x_2709_ = lean_box(0);
v___x_2710_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2710_, 0, v_name_2691_);
lean_ctor_set(v___x_2710_, 1, v___x_2709_);
v___x_2711_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2708_);
lean_ctor_set(v___x_2711_, 1, v_a_2703_);
lean_ctor_set(v___x_2711_, 2, v___x_2710_);
if (v_isShared_2706_ == 0)
{
lean_ctor_set_tag(v___x_2705_, 2);
lean_ctor_set(v___x_2705_, 0, v___x_2711_);
v___x_2713_ = v___x_2705_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v___x_2711_);
v___x_2713_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
lean_object* v___x_2714_; 
v___x_2714_ = l_Lean_addDecl(v___x_2713_, v_hasTrace_2690_, v_a_2678_, v_a_2679_);
return v___x_2714_;
}
}
}
}
else
{
lean_object* v_a_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2725_; 
lean_dec(v_val_2697_);
lean_dec(v_name_2691_);
lean_del_object(v___x_2687_);
lean_dec(v_levelParams_2685_);
v_a_2718_ = lean_ctor_get(v___x_2698_, 0);
v_isSharedCheck_2725_ = !lean_is_exclusive(v___x_2698_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2720_ = v___x_2698_;
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_a_2718_);
lean_dec(v___x_2698_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v___x_2723_; 
if (v_isShared_2721_ == 0)
{
v___x_2723_ = v___x_2720_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v_a_2718_);
v___x_2723_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
return v___x_2723_;
}
}
}
}
else
{
lean_object* v___x_2726_; lean_object* v___x_2728_; 
lean_dec(v_a_2693_);
lean_dec(v_name_2691_);
lean_del_object(v___x_2687_);
lean_dec(v_levelParams_2685_);
lean_dec(v_name_2684_);
v___x_2726_ = lean_box(0);
if (v_isShared_2696_ == 0)
{
lean_ctor_set(v___x_2695_, 0, v___x_2726_);
v___x_2728_ = v___x_2695_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v___x_2726_);
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
else
{
lean_object* v_a_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2738_; 
lean_dec(v_name_2691_);
lean_del_object(v___x_2687_);
lean_dec(v_levelParams_2685_);
lean_dec(v_name_2684_);
v_a_2731_ = lean_ctor_get(v___x_2692_, 0);
v_isSharedCheck_2738_ = !lean_is_exclusive(v___x_2692_);
if (v_isSharedCheck_2738_ == 0)
{
v___x_2733_ = v___x_2692_;
v_isShared_2734_ = v_isSharedCheck_2738_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_a_2731_);
lean_dec(v___x_2692_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2738_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v___x_2736_; 
if (v_isShared_2734_ == 0)
{
v___x_2736_ = v___x_2733_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v_a_2731_);
v___x_2736_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
return v___x_2736_;
}
}
}
}
else
{
lean_object* v___f_2739_; lean_object* v_cls_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; uint8_t v___x_2743_; lean_object* v___y_2745_; lean_object* v___y_2746_; lean_object* v_a_2747_; lean_object* v___y_2757_; lean_object* v___y_2758_; lean_object* v_a_2759_; lean_object* v___y_2762_; lean_object* v___y_2763_; lean_object* v_a_2764_; lean_object* v___y_2767_; lean_object* v___y_2768_; lean_object* v___y_2769_; lean_object* v___y_2773_; lean_object* v___y_2774_; lean_object* v_a_2775_; lean_object* v___y_2788_; lean_object* v___y_2789_; lean_object* v_a_2790_; lean_object* v___y_2793_; lean_object* v___y_2794_; lean_object* v_a_2795_; lean_object* v___y_2798_; lean_object* v___y_2799_; lean_object* v___y_2800_; 
lean_inc(v_name_2691_);
v___f_2739_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2739_, 0, v_name_2691_);
v_cls_2740_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_2741_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_2742_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_2743_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2689_, v_options_2683_, v___x_2742_);
if (v___x_2743_ == 0)
{
lean_object* v___x_2838_; uint8_t v___x_2839_; 
v___x_2838_ = l_Lean_trace_profiler;
v___x_2839_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_2683_, v___x_2838_);
if (v___x_2839_ == 0)
{
lean_object* v___x_2840_; 
lean_dec_ref(v___f_2739_);
v___x_2840_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2675_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_);
if (lean_obj_tag(v___x_2840_) == 0)
{
lean_object* v_a_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2887_; 
v_a_2841_ = lean_ctor_get(v___x_2840_, 0);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2843_ = v___x_2840_;
v_isShared_2844_ = v_isSharedCheck_2887_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_a_2841_);
lean_dec(v___x_2840_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2887_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
if (lean_obj_tag(v_a_2841_) == 1)
{
lean_object* v_val_2845_; lean_object* v___y_2847_; lean_object* v___y_2848_; lean_object* v___y_2849_; lean_object* v___y_2850_; 
lean_del_object(v___x_2843_);
v_val_2845_ = lean_ctor_get(v_a_2841_, 0);
lean_inc(v_val_2845_);
lean_dec_ref_known(v_a_2841_, 1);
if (v___x_2743_ == 0)
{
v___y_2847_ = v_a_2676_;
v___y_2848_ = v_a_2677_;
v___y_2849_ = v_a_2678_;
v___y_2850_ = v_a_2679_;
goto v___jp_2846_;
}
else
{
lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; 
v___x_2879_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
lean_inc(v_val_2845_);
v___x_2880_ = l_Lean_MessageData_ofExpr(v_val_2845_);
v___x_2881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2881_, 0, v___x_2879_);
lean_ctor_set(v___x_2881_, 1, v___x_2880_);
v___x_2882_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2740_, v___x_2881_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_);
if (lean_obj_tag(v___x_2882_) == 0)
{
lean_dec_ref_known(v___x_2882_, 1);
v___y_2847_ = v_a_2676_;
v___y_2848_ = v_a_2677_;
v___y_2849_ = v_a_2678_;
v___y_2850_ = v_a_2679_;
goto v___jp_2846_;
}
else
{
lean_dec(v_val_2845_);
lean_dec(v_name_2691_);
lean_del_object(v___x_2687_);
lean_dec(v_levelParams_2685_);
lean_dec(v_name_2684_);
return v___x_2882_;
}
}
v___jp_2846_:
{
lean_object* v___x_2851_; 
lean_inc(v_val_2845_);
v___x_2851_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2684_, v_val_2845_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_);
if (lean_obj_tag(v___x_2851_) == 0)
{
lean_object* v_a_2852_; lean_object* v___x_2853_; lean_object* v_a_2854_; lean_object* v___x_2855_; lean_object* v_a_2856_; lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2870_; 
v_a_2852_ = lean_ctor_get(v___x_2851_, 0);
lean_inc(v_a_2852_);
lean_dec_ref_known(v___x_2851_, 1);
v___x_2853_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2845_, v___y_2848_);
v_a_2854_ = lean_ctor_get(v___x_2853_, 0);
lean_inc(v_a_2854_);
lean_dec_ref(v___x_2853_);
v___x_2855_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2852_, v___y_2848_);
v_a_2856_ = lean_ctor_get(v___x_2855_, 0);
v_isSharedCheck_2870_ = !lean_is_exclusive(v___x_2855_);
if (v_isSharedCheck_2870_ == 0)
{
v___x_2858_ = v___x_2855_;
v_isShared_2859_ = v_isSharedCheck_2870_;
goto v_resetjp_2857_;
}
else
{
lean_inc(v_a_2856_);
lean_dec(v___x_2855_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2870_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
lean_object* v___x_2861_; 
lean_inc(v_name_2691_);
if (v_isShared_2688_ == 0)
{
lean_ctor_set(v___x_2687_, 2, v_a_2854_);
lean_ctor_set(v___x_2687_, 0, v_name_2691_);
v___x_2861_ = v___x_2687_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v_name_2691_);
lean_ctor_set(v_reuseFailAlloc_2869_, 1, v_levelParams_2685_);
lean_ctor_set(v_reuseFailAlloc_2869_, 2, v_a_2854_);
v___x_2861_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2866_; 
v___x_2862_ = lean_box(0);
v___x_2863_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2863_, 0, v_name_2691_);
lean_ctor_set(v___x_2863_, 1, v___x_2862_);
v___x_2864_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2864_, 0, v___x_2861_);
lean_ctor_set(v___x_2864_, 1, v_a_2856_);
lean_ctor_set(v___x_2864_, 2, v___x_2863_);
if (v_isShared_2859_ == 0)
{
lean_ctor_set_tag(v___x_2858_, 2);
lean_ctor_set(v___x_2858_, 0, v___x_2864_);
v___x_2866_ = v___x_2858_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v___x_2864_);
v___x_2866_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
lean_object* v___x_2867_; 
v___x_2867_ = l_Lean_addDecl(v___x_2866_, v___x_2839_, v___y_2849_, v___y_2850_);
return v___x_2867_;
}
}
}
}
else
{
lean_object* v_a_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2878_; 
lean_dec(v_val_2845_);
lean_dec(v_name_2691_);
lean_del_object(v___x_2687_);
lean_dec(v_levelParams_2685_);
v_a_2871_ = lean_ctor_get(v___x_2851_, 0);
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2851_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2873_ = v___x_2851_;
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
else
{
lean_inc(v_a_2871_);
lean_dec(v___x_2851_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v___x_2876_; 
if (v_isShared_2874_ == 0)
{
v___x_2876_ = v___x_2873_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_a_2871_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
return v___x_2876_;
}
}
}
}
}
else
{
lean_object* v___x_2883_; lean_object* v___x_2885_; 
lean_dec(v_a_2841_);
lean_dec(v_name_2691_);
lean_del_object(v___x_2687_);
lean_dec(v_levelParams_2685_);
lean_dec(v_name_2684_);
v___x_2883_ = lean_box(0);
if (v_isShared_2844_ == 0)
{
lean_ctor_set(v___x_2843_, 0, v___x_2883_);
v___x_2885_ = v___x_2843_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v___x_2883_);
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
else
{
lean_object* v_a_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2895_; 
lean_dec(v_name_2691_);
lean_del_object(v___x_2687_);
lean_dec(v_levelParams_2685_);
lean_dec(v_name_2684_);
v_a_2888_ = lean_ctor_get(v___x_2840_, 0);
v_isSharedCheck_2895_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2890_ = v___x_2840_;
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_a_2888_);
lean_dec(v___x_2840_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v___x_2893_; 
if (v_isShared_2891_ == 0)
{
v___x_2893_ = v___x_2890_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v_a_2888_);
v___x_2893_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
return v___x_2893_;
}
}
}
}
else
{
lean_del_object(v___x_2687_);
goto v___jp_2803_;
}
}
else
{
lean_del_object(v___x_2687_);
goto v___jp_2803_;
}
v___jp_2744_:
{
lean_object* v___x_2748_; double v___x_2749_; double v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; 
v___x_2748_ = lean_io_get_num_heartbeats();
v___x_2749_ = lean_float_of_nat(v___y_2745_);
v___x_2750_ = lean_float_of_nat(v___x_2748_);
v___x_2751_ = lean_box_float(v___x_2749_);
v___x_2752_ = lean_box_float(v___x_2750_);
v___x_2753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2751_);
lean_ctor_set(v___x_2753_, 1, v___x_2752_);
v___x_2754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2754_, 0, v_a_2747_);
lean_ctor_set(v___x_2754_, 1, v___x_2753_);
v___x_2755_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_2740_, v_hasTrace_2690_, v___x_2741_, v_options_2683_, v___x_2743_, v___y_2746_, v___f_2739_, v___x_2754_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_);
return v___x_2755_;
}
v___jp_2756_:
{
lean_object* v___x_2760_; 
v___x_2760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2760_, 0, v_a_2759_);
v___y_2745_ = v___y_2757_;
v___y_2746_ = v___y_2758_;
v_a_2747_ = v___x_2760_;
goto v___jp_2744_;
}
v___jp_2761_:
{
lean_object* v___x_2765_; 
v___x_2765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2765_, 0, v_a_2764_);
v___y_2745_ = v___y_2762_;
v___y_2746_ = v___y_2763_;
v_a_2747_ = v___x_2765_;
goto v___jp_2744_;
}
v___jp_2766_:
{
if (lean_obj_tag(v___y_2769_) == 0)
{
lean_object* v_a_2770_; 
v_a_2770_ = lean_ctor_get(v___y_2769_, 0);
lean_inc(v_a_2770_);
lean_dec_ref_known(v___y_2769_, 1);
v___y_2762_ = v___y_2767_;
v___y_2763_ = v___y_2768_;
v_a_2764_ = v_a_2770_;
goto v___jp_2761_;
}
else
{
lean_object* v_a_2771_; 
v_a_2771_ = lean_ctor_get(v___y_2769_, 0);
lean_inc(v_a_2771_);
lean_dec_ref_known(v___y_2769_, 1);
v___y_2757_ = v___y_2767_;
v___y_2758_ = v___y_2768_;
v_a_2759_ = v_a_2771_;
goto v___jp_2756_;
}
}
v___jp_2772_:
{
lean_object* v___x_2776_; double v___x_2777_; double v___x_2778_; double v___x_2779_; double v___x_2780_; double v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; 
v___x_2776_ = lean_io_mono_nanos_now();
v___x_2777_ = lean_float_of_nat(v___y_2774_);
v___x_2778_ = lean_float_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0);
v___x_2779_ = lean_float_div(v___x_2777_, v___x_2778_);
v___x_2780_ = lean_float_of_nat(v___x_2776_);
v___x_2781_ = lean_float_div(v___x_2780_, v___x_2778_);
v___x_2782_ = lean_box_float(v___x_2779_);
v___x_2783_ = lean_box_float(v___x_2781_);
v___x_2784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2784_, 0, v___x_2782_);
lean_ctor_set(v___x_2784_, 1, v___x_2783_);
v___x_2785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2785_, 0, v_a_2775_);
lean_ctor_set(v___x_2785_, 1, v___x_2784_);
v___x_2786_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_2740_, v_hasTrace_2690_, v___x_2741_, v_options_2683_, v___x_2743_, v___y_2773_, v___f_2739_, v___x_2785_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_);
return v___x_2786_;
}
v___jp_2787_:
{
lean_object* v___x_2791_; 
v___x_2791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2791_, 0, v_a_2790_);
v___y_2773_ = v___y_2788_;
v___y_2774_ = v___y_2789_;
v_a_2775_ = v___x_2791_;
goto v___jp_2772_;
}
v___jp_2792_:
{
lean_object* v___x_2796_; 
v___x_2796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2796_, 0, v_a_2795_);
v___y_2773_ = v___y_2793_;
v___y_2774_ = v___y_2794_;
v_a_2775_ = v___x_2796_;
goto v___jp_2772_;
}
v___jp_2797_:
{
if (lean_obj_tag(v___y_2800_) == 0)
{
lean_object* v_a_2801_; 
v_a_2801_ = lean_ctor_get(v___y_2800_, 0);
lean_inc(v_a_2801_);
lean_dec_ref_known(v___y_2800_, 1);
v___y_2788_ = v___y_2798_;
v___y_2789_ = v___y_2799_;
v_a_2790_ = v_a_2801_;
goto v___jp_2787_;
}
else
{
lean_object* v_a_2802_; 
v_a_2802_ = lean_ctor_get(v___y_2800_, 0);
lean_inc(v_a_2802_);
lean_dec_ref_known(v___y_2800_, 1);
v___y_2793_ = v___y_2798_;
v___y_2794_ = v___y_2799_;
v_a_2795_ = v_a_2802_;
goto v___jp_2792_;
}
}
v___jp_2803_:
{
lean_object* v___x_2804_; lean_object* v_a_2805_; lean_object* v___x_2806_; uint8_t v___x_2807_; 
v___x_2804_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v_a_2679_);
v_a_2805_ = lean_ctor_get(v___x_2804_, 0);
lean_inc(v_a_2805_);
lean_dec_ref(v___x_2804_);
v___x_2806_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2807_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_2683_, v___x_2806_);
if (v___x_2807_ == 0)
{
lean_object* v___x_2808_; lean_object* v___x_2809_; 
v___x_2808_ = lean_io_mono_nanos_now();
v___x_2809_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2675_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_);
if (lean_obj_tag(v___x_2809_) == 0)
{
lean_object* v_a_2810_; 
v_a_2810_ = lean_ctor_get(v___x_2809_, 0);
lean_inc(v_a_2810_);
lean_dec_ref_known(v___x_2809_, 1);
if (lean_obj_tag(v_a_2810_) == 1)
{
if (v___x_2743_ == 0)
{
lean_object* v_val_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; 
v_val_2811_ = lean_ctor_get(v_a_2810_, 0);
lean_inc(v_val_2811_);
lean_dec_ref_known(v_a_2810_, 1);
v___x_2812_ = lean_box(0);
v___x_2813_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(v_name_2684_, v_val_2811_, v_name_2691_, v_levelParams_2685_, v___x_2807_, v___x_2812_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_);
v___y_2798_ = v_a_2805_;
v___y_2799_ = v___x_2808_;
v___y_2800_ = v___x_2813_;
goto v___jp_2797_;
}
else
{
lean_object* v_val_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; 
v_val_2814_ = lean_ctor_get(v_a_2810_, 0);
lean_inc_n(v_val_2814_, 2);
lean_dec_ref_known(v_a_2810_, 1);
v___x_2815_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_2816_ = l_Lean_MessageData_ofExpr(v_val_2814_);
v___x_2817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2817_, 0, v___x_2815_);
lean_ctor_set(v___x_2817_, 1, v___x_2816_);
v___x_2818_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2740_, v___x_2817_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_);
if (lean_obj_tag(v___x_2818_) == 0)
{
lean_object* v_a_2819_; lean_object* v___x_2820_; 
v_a_2819_ = lean_ctor_get(v___x_2818_, 0);
lean_inc(v_a_2819_);
lean_dec_ref_known(v___x_2818_, 1);
v___x_2820_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(v_name_2684_, v_val_2814_, v_name_2691_, v_levelParams_2685_, v___x_2807_, v_a_2819_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_);
v___y_2798_ = v_a_2805_;
v___y_2799_ = v___x_2808_;
v___y_2800_ = v___x_2820_;
goto v___jp_2797_;
}
else
{
lean_dec(v_val_2814_);
lean_dec(v_name_2691_);
lean_dec(v_levelParams_2685_);
lean_dec(v_name_2684_);
v___y_2798_ = v_a_2805_;
v___y_2799_ = v___x_2808_;
v___y_2800_ = v___x_2818_;
goto v___jp_2797_;
}
}
}
else
{
lean_object* v___x_2821_; 
lean_dec(v_a_2810_);
lean_dec(v_name_2691_);
lean_dec(v_levelParams_2685_);
lean_dec(v_name_2684_);
v___x_2821_ = lean_box(0);
v___y_2788_ = v_a_2805_;
v___y_2789_ = v___x_2808_;
v_a_2790_ = v___x_2821_;
goto v___jp_2787_;
}
}
else
{
lean_object* v_a_2822_; 
lean_dec(v_name_2691_);
lean_dec(v_levelParams_2685_);
lean_dec(v_name_2684_);
v_a_2822_ = lean_ctor_get(v___x_2809_, 0);
lean_inc(v_a_2822_);
lean_dec_ref_known(v___x_2809_, 1);
v___y_2793_ = v_a_2805_;
v___y_2794_ = v___x_2808_;
v_a_2795_ = v_a_2822_;
goto v___jp_2792_;
}
}
else
{
lean_object* v___x_2823_; lean_object* v___x_2824_; 
v___x_2823_ = lean_io_get_num_heartbeats();
v___x_2824_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2675_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_);
if (lean_obj_tag(v___x_2824_) == 0)
{
lean_object* v_a_2825_; 
v_a_2825_ = lean_ctor_get(v___x_2824_, 0);
lean_inc(v_a_2825_);
lean_dec_ref_known(v___x_2824_, 1);
if (lean_obj_tag(v_a_2825_) == 1)
{
if (v___x_2743_ == 0)
{
lean_object* v_val_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; 
v_val_2826_ = lean_ctor_get(v_a_2825_, 0);
lean_inc(v_val_2826_);
lean_dec_ref_known(v_a_2825_, 1);
v___x_2827_ = lean_box(0);
v___x_2828_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(v_name_2684_, v_val_2826_, v_name_2691_, v_levelParams_2685_, v___x_2827_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_);
v___y_2767_ = v___x_2823_;
v___y_2768_ = v_a_2805_;
v___y_2769_ = v___x_2828_;
goto v___jp_2766_;
}
else
{
lean_object* v_val_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; 
v_val_2829_ = lean_ctor_get(v_a_2825_, 0);
lean_inc_n(v_val_2829_, 2);
lean_dec_ref_known(v_a_2825_, 1);
v___x_2830_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_2831_ = l_Lean_MessageData_ofExpr(v_val_2829_);
v___x_2832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2832_, 0, v___x_2830_);
lean_ctor_set(v___x_2832_, 1, v___x_2831_);
v___x_2833_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2740_, v___x_2832_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_);
if (lean_obj_tag(v___x_2833_) == 0)
{
lean_object* v_a_2834_; lean_object* v___x_2835_; 
v_a_2834_ = lean_ctor_get(v___x_2833_, 0);
lean_inc(v_a_2834_);
lean_dec_ref_known(v___x_2833_, 1);
v___x_2835_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(v_name_2684_, v_val_2829_, v_name_2691_, v_levelParams_2685_, v_a_2834_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_);
v___y_2767_ = v___x_2823_;
v___y_2768_ = v_a_2805_;
v___y_2769_ = v___x_2835_;
goto v___jp_2766_;
}
else
{
lean_dec(v_val_2829_);
lean_dec(v_name_2691_);
lean_dec(v_levelParams_2685_);
lean_dec(v_name_2684_);
v___y_2767_ = v___x_2823_;
v___y_2768_ = v_a_2805_;
v___y_2769_ = v___x_2833_;
goto v___jp_2766_;
}
}
}
else
{
lean_object* v___x_2836_; 
lean_dec(v_a_2825_);
lean_dec(v_name_2691_);
lean_dec(v_levelParams_2685_);
lean_dec(v_name_2684_);
v___x_2836_ = lean_box(0);
v___y_2762_ = v___x_2823_;
v___y_2763_ = v_a_2805_;
v_a_2764_ = v___x_2836_;
goto v___jp_2761_;
}
}
else
{
lean_object* v_a_2837_; 
lean_dec(v_name_2691_);
lean_dec(v_levelParams_2685_);
lean_dec(v_name_2684_);
v_a_2837_ = lean_ctor_get(v___x_2824_, 0);
lean_inc(v_a_2837_);
lean_dec_ref_known(v___x_2824_, 1);
v___y_2757_ = v___x_2823_;
v___y_2758_ = v_a_2805_;
v_a_2759_ = v_a_2837_;
goto v___jp_2756_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___boxed(lean_object* v_ctorVal_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_){
_start:
{
lean_object* v_res_2904_; 
v_res_2904_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(v_ctorVal_2898_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_);
lean_dec(v_a_2902_);
lean_dec_ref(v_a_2901_);
lean_dec(v_a_2900_);
lean_dec_ref(v_a_2899_);
return v_res_2904_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4(lean_object* v_00_u03b1_2905_, lean_object* v_x_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_){
_start:
{
lean_object* v___x_2912_; 
v___x_2912_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg(v_x_2906_);
return v___x_2912_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2913_, lean_object* v_x_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_){
_start:
{
lean_object* v_res_2920_; 
v_res_2920_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4(v_00_u03b1_2913_, v_x_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_);
lean_dec(v___y_2918_);
lean_dec_ref(v___y_2917_);
lean_dec(v___y_2916_);
lean_dec_ref(v___y_2915_);
return v_res_2920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveEqTheoremNameFor(lean_object* v_ctorName_2924_){
_start:
{
lean_object* v___x_2925_; lean_object* v___x_2926_; 
v___x_2925_ = ((lean_object*)(l_Lean_Meta_mkInjectiveEqTheoremNameFor___closed__1));
v___x_2926_ = l_Lean_Name_append(v_ctorName_2924_, v___x_2925_);
return v___x_2926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(lean_object* v_ctorVal_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_){
_start:
{
uint8_t v___x_2933_; lean_object* v___x_2934_; 
v___x_2933_ = 1;
v___x_2934_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(v_ctorVal_2927_, v___x_2933_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_);
return v___x_2934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f___boxed(lean_object* v_ctorVal_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_){
_start:
{
lean_object* v_res_2941_; 
v_res_2941_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_2935_, v_a_2936_, v_a_2937_, v_a_2938_, v_a_2939_);
lean_dec(v_a_2939_);
lean_dec_ref(v_a_2938_);
lean_dec(v_a_2937_);
lean_dec_ref(v_a_2936_);
return v_res_2941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(lean_object* v_e_2942_, lean_object* v_t_2943_, lean_object* v_acc_2944_, lean_object* v_a_2945_){
_start:
{
lean_object* v___x_2950_; 
v___x_2950_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_t_2943_, v_a_2945_);
if (lean_obj_tag(v___x_2950_) == 0)
{
lean_object* v_a_2951_; lean_object* v___x_2952_; uint8_t v___x_2953_; 
v_a_2951_ = lean_ctor_get(v___x_2950_, 0);
lean_inc(v_a_2951_);
lean_dec_ref_known(v___x_2950_, 1);
v___x_2952_ = l_Lean_Expr_cleanupAnnotations(v_a_2951_);
v___x_2953_ = l_Lean_Expr_isApp(v___x_2952_);
if (v___x_2953_ == 0)
{
lean_dec_ref(v___x_2952_);
goto v___jp_2947_;
}
else
{
lean_object* v_arg_2954_; lean_object* v___x_2955_; uint8_t v___x_2956_; 
v_arg_2954_ = lean_ctor_get(v___x_2952_, 1);
lean_inc_ref(v_arg_2954_);
v___x_2955_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2952_);
v___x_2956_ = l_Lean_Expr_isApp(v___x_2955_);
if (v___x_2956_ == 0)
{
lean_dec_ref(v___x_2955_);
lean_dec_ref(v_arg_2954_);
goto v___jp_2947_;
}
else
{
lean_object* v_arg_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; uint8_t v___x_2960_; 
v_arg_2957_ = lean_ctor_get(v___x_2955_, 1);
lean_inc_ref(v_arg_2957_);
v___x_2958_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2955_);
v___x_2959_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__1));
v___x_2960_ = l_Lean_Expr_isConstOf(v___x_2958_, v___x_2959_);
lean_dec_ref(v___x_2958_);
if (v___x_2960_ == 0)
{
lean_dec_ref(v_arg_2957_);
lean_dec_ref(v_arg_2954_);
goto v___jp_2947_;
}
else
{
lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2961_ = lean_unsigned_to_nat(0u);
v___x_2962_ = l_Lean_mkProj(v___x_2959_, v___x_2961_, v_e_2942_);
lean_inc_ref(v___x_2962_);
v___x_2963_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v___x_2962_, v_arg_2957_, v_acc_2944_, v_a_2945_);
if (lean_obj_tag(v___x_2963_) == 0)
{
lean_object* v_a_2964_; 
v_a_2964_ = lean_ctor_get(v___x_2963_, 0);
lean_inc(v_a_2964_);
lean_dec_ref_known(v___x_2963_, 1);
v_e_2942_ = v___x_2962_;
v_t_2943_ = v_arg_2954_;
v_acc_2944_ = v_a_2964_;
goto _start;
}
else
{
lean_dec_ref(v___x_2962_);
lean_dec_ref(v_arg_2954_);
return v___x_2963_;
}
}
}
}
}
else
{
lean_object* v_a_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2973_; 
lean_dec_ref(v_acc_2944_);
lean_dec_ref(v_e_2942_);
v_a_2966_ = lean_ctor_get(v___x_2950_, 0);
v_isSharedCheck_2973_ = !lean_is_exclusive(v___x_2950_);
if (v_isSharedCheck_2973_ == 0)
{
v___x_2968_ = v___x_2950_;
v_isShared_2969_ = v_isSharedCheck_2973_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_a_2966_);
lean_dec(v___x_2950_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_2973_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v___x_2971_; 
if (v_isShared_2969_ == 0)
{
v___x_2971_ = v___x_2968_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v_a_2966_);
v___x_2971_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
return v___x_2971_;
}
}
}
v___jp_2947_:
{
lean_object* v___x_2948_; lean_object* v___x_2949_; 
v___x_2948_ = lean_array_push(v_acc_2944_, v_e_2942_);
v___x_2949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2949_, 0, v___x_2948_);
return v___x_2949_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg___boxed(lean_object* v_e_2974_, lean_object* v_t_2975_, lean_object* v_acc_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_){
_start:
{
lean_object* v_res_2979_; 
v_res_2979_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v_e_2974_, v_t_2975_, v_acc_2976_, v_a_2977_);
lean_dec(v_a_2977_);
return v_res_2979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go(lean_object* v_e_2980_, lean_object* v_t_2981_, lean_object* v_acc_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_){
_start:
{
lean_object* v___x_2988_; 
v___x_2988_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v_e_2980_, v_t_2981_, v_acc_2982_, v_a_2984_);
return v___x_2988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___boxed(lean_object* v_e_2989_, lean_object* v_t_2990_, lean_object* v_acc_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_){
_start:
{
lean_object* v_res_2997_; 
v_res_2997_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go(v_e_2989_, v_t_2990_, v_acc_2991_, v_a_2992_, v_a_2993_, v_a_2994_, v_a_2995_);
lean_dec(v_a_2995_);
lean_dec_ref(v_a_2994_);
lean_dec(v_a_2993_);
lean_dec_ref(v_a_2992_);
return v_res_2997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections(lean_object* v_e_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_){
_start:
{
lean_object* v___x_3004_; 
lean_inc(v_a_3002_);
lean_inc_ref(v_a_3001_);
lean_inc(v_a_3000_);
lean_inc_ref(v_a_2999_);
lean_inc_ref(v_e_2998_);
v___x_3004_ = lean_infer_type(v_e_2998_, v_a_2999_, v_a_3000_, v_a_3001_, v_a_3002_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_object* v_a_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; 
v_a_3005_ = lean_ctor_get(v___x_3004_, 0);
lean_inc(v_a_3005_);
lean_dec_ref_known(v___x_3004_, 1);
v___x_3006_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_3007_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v_e_2998_, v_a_3005_, v___x_3006_, v_a_3000_);
return v___x_3007_;
}
else
{
lean_object* v_a_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3015_; 
lean_dec_ref(v_e_2998_);
v_a_3008_ = lean_ctor_get(v___x_3004_, 0);
v_isSharedCheck_3015_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3015_ == 0)
{
v___x_3010_ = v___x_3004_;
v_isShared_3011_ = v_isSharedCheck_3015_;
goto v_resetjp_3009_;
}
else
{
lean_inc(v_a_3008_);
lean_dec(v___x_3004_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3015_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
lean_object* v___x_3013_; 
if (v_isShared_3011_ == 0)
{
v___x_3013_ = v___x_3010_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3014_; 
v_reuseFailAlloc_3014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3014_, 0, v_a_3008_);
v___x_3013_ = v_reuseFailAlloc_3014_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
return v___x_3013_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections___boxed(lean_object* v_e_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_){
_start:
{
lean_object* v_res_3022_; 
v_res_3022_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections(v_e_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_);
lean_dec(v_a_3020_);
lean_dec_ref(v_a_3019_);
lean_dec(v_a_3018_);
lean_dec_ref(v_a_3017_);
return v_res_3022_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_x_3023_, lean_object* v_x_3024_, lean_object* v_x_3025_, lean_object* v_x_3026_){
_start:
{
lean_object* v_ks_3027_; lean_object* v_vs_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3052_; 
v_ks_3027_ = lean_ctor_get(v_x_3023_, 0);
v_vs_3028_ = lean_ctor_get(v_x_3023_, 1);
v_isSharedCheck_3052_ = !lean_is_exclusive(v_x_3023_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_3030_ = v_x_3023_;
v_isShared_3031_ = v_isSharedCheck_3052_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_vs_3028_);
lean_inc(v_ks_3027_);
lean_dec(v_x_3023_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3052_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___x_3032_; uint8_t v___x_3033_; 
v___x_3032_ = lean_array_get_size(v_ks_3027_);
v___x_3033_ = lean_nat_dec_lt(v_x_3024_, v___x_3032_);
if (v___x_3033_ == 0)
{
lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3037_; 
lean_dec(v_x_3024_);
v___x_3034_ = lean_array_push(v_ks_3027_, v_x_3025_);
v___x_3035_ = lean_array_push(v_vs_3028_, v_x_3026_);
if (v_isShared_3031_ == 0)
{
lean_ctor_set(v___x_3030_, 1, v___x_3035_);
lean_ctor_set(v___x_3030_, 0, v___x_3034_);
v___x_3037_ = v___x_3030_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v___x_3034_);
lean_ctor_set(v_reuseFailAlloc_3038_, 1, v___x_3035_);
v___x_3037_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
return v___x_3037_;
}
}
else
{
lean_object* v_k_x27_3039_; uint8_t v___x_3040_; 
v_k_x27_3039_ = lean_array_fget_borrowed(v_ks_3027_, v_x_3024_);
v___x_3040_ = l_Lean_instBEqMVarId_beq(v_x_3025_, v_k_x27_3039_);
if (v___x_3040_ == 0)
{
lean_object* v___x_3042_; 
if (v_isShared_3031_ == 0)
{
v___x_3042_ = v___x_3030_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v_ks_3027_);
lean_ctor_set(v_reuseFailAlloc_3046_, 1, v_vs_3028_);
v___x_3042_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
lean_object* v___x_3043_; lean_object* v___x_3044_; 
v___x_3043_ = lean_unsigned_to_nat(1u);
v___x_3044_ = lean_nat_add(v_x_3024_, v___x_3043_);
lean_dec(v_x_3024_);
v_x_3023_ = v___x_3042_;
v_x_3024_ = v___x_3044_;
goto _start;
}
}
else
{
lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3050_; 
v___x_3047_ = lean_array_fset(v_ks_3027_, v_x_3024_, v_x_3025_);
v___x_3048_ = lean_array_fset(v_vs_3028_, v_x_3024_, v_x_3026_);
lean_dec(v_x_3024_);
if (v_isShared_3031_ == 0)
{
lean_ctor_set(v___x_3030_, 1, v___x_3048_);
lean_ctor_set(v___x_3030_, 0, v___x_3047_);
v___x_3050_ = v___x_3030_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v___x_3047_);
lean_ctor_set(v_reuseFailAlloc_3051_, 1, v___x_3048_);
v___x_3050_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
return v___x_3050_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_n_3053_, lean_object* v_k_3054_, lean_object* v_v_3055_){
_start:
{
lean_object* v___x_3056_; lean_object* v___x_3057_; 
v___x_3056_ = lean_unsigned_to_nat(0u);
v___x_3057_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_n_3053_, v___x_3056_, v_k_3054_, v_v_3055_);
return v___x_3057_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_3058_; 
v___x_3058_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_3058_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(lean_object* v_x_3059_, size_t v_x_3060_, size_t v_x_3061_, lean_object* v_x_3062_, lean_object* v_x_3063_){
_start:
{
if (lean_obj_tag(v_x_3059_) == 0)
{
lean_object* v_es_3064_; size_t v___x_3065_; size_t v___x_3066_; lean_object* v_j_3067_; lean_object* v___x_3068_; uint8_t v___x_3069_; 
v_es_3064_ = lean_ctor_get(v_x_3059_, 0);
v___x_3065_ = ((size_t)31ULL);
v___x_3066_ = lean_usize_land(v_x_3060_, v___x_3065_);
v_j_3067_ = lean_usize_to_nat(v___x_3066_);
v___x_3068_ = lean_array_get_size(v_es_3064_);
v___x_3069_ = lean_nat_dec_lt(v_j_3067_, v___x_3068_);
if (v___x_3069_ == 0)
{
lean_dec(v_j_3067_);
lean_dec(v_x_3063_);
lean_dec(v_x_3062_);
return v_x_3059_;
}
else
{
lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3108_; 
lean_inc_ref(v_es_3064_);
v_isSharedCheck_3108_ = !lean_is_exclusive(v_x_3059_);
if (v_isSharedCheck_3108_ == 0)
{
lean_object* v_unused_3109_; 
v_unused_3109_ = lean_ctor_get(v_x_3059_, 0);
lean_dec(v_unused_3109_);
v___x_3071_ = v_x_3059_;
v_isShared_3072_ = v_isSharedCheck_3108_;
goto v_resetjp_3070_;
}
else
{
lean_dec(v_x_3059_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3108_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v_v_3073_; lean_object* v___x_3074_; lean_object* v_xs_x27_3075_; lean_object* v___y_3077_; 
v_v_3073_ = lean_array_fget(v_es_3064_, v_j_3067_);
v___x_3074_ = lean_box(0);
v_xs_x27_3075_ = lean_array_fset(v_es_3064_, v_j_3067_, v___x_3074_);
switch(lean_obj_tag(v_v_3073_))
{
case 0:
{
lean_object* v_key_3082_; lean_object* v_val_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3093_; 
v_key_3082_ = lean_ctor_get(v_v_3073_, 0);
v_val_3083_ = lean_ctor_get(v_v_3073_, 1);
v_isSharedCheck_3093_ = !lean_is_exclusive(v_v_3073_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_3085_ = v_v_3073_;
v_isShared_3086_ = v_isSharedCheck_3093_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_val_3083_);
lean_inc(v_key_3082_);
lean_dec(v_v_3073_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3093_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
uint8_t v___x_3087_; 
v___x_3087_ = l_Lean_instBEqMVarId_beq(v_x_3062_, v_key_3082_);
if (v___x_3087_ == 0)
{
lean_object* v___x_3088_; lean_object* v___x_3089_; 
lean_del_object(v___x_3085_);
v___x_3088_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3082_, v_val_3083_, v_x_3062_, v_x_3063_);
v___x_3089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3089_, 0, v___x_3088_);
v___y_3077_ = v___x_3089_;
goto v___jp_3076_;
}
else
{
lean_object* v___x_3091_; 
lean_dec(v_val_3083_);
lean_dec(v_key_3082_);
if (v_isShared_3086_ == 0)
{
lean_ctor_set(v___x_3085_, 1, v_x_3063_);
lean_ctor_set(v___x_3085_, 0, v_x_3062_);
v___x_3091_ = v___x_3085_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v_x_3062_);
lean_ctor_set(v_reuseFailAlloc_3092_, 1, v_x_3063_);
v___x_3091_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
v___y_3077_ = v___x_3091_;
goto v___jp_3076_;
}
}
}
}
case 1:
{
lean_object* v_node_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3106_; 
v_node_3094_ = lean_ctor_get(v_v_3073_, 0);
v_isSharedCheck_3106_ = !lean_is_exclusive(v_v_3073_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3096_ = v_v_3073_;
v_isShared_3097_ = v_isSharedCheck_3106_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_node_3094_);
lean_dec(v_v_3073_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3106_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
size_t v___x_3098_; size_t v___x_3099_; size_t v___x_3100_; size_t v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3104_; 
v___x_3098_ = ((size_t)5ULL);
v___x_3099_ = lean_usize_shift_right(v_x_3060_, v___x_3098_);
v___x_3100_ = ((size_t)1ULL);
v___x_3101_ = lean_usize_add(v_x_3061_, v___x_3100_);
v___x_3102_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_node_3094_, v___x_3099_, v___x_3101_, v_x_3062_, v_x_3063_);
if (v_isShared_3097_ == 0)
{
lean_ctor_set(v___x_3096_, 0, v___x_3102_);
v___x_3104_ = v___x_3096_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v___x_3102_);
v___x_3104_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
v___y_3077_ = v___x_3104_;
goto v___jp_3076_;
}
}
}
default: 
{
lean_object* v___x_3107_; 
v___x_3107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3107_, 0, v_x_3062_);
lean_ctor_set(v___x_3107_, 1, v_x_3063_);
v___y_3077_ = v___x_3107_;
goto v___jp_3076_;
}
}
v___jp_3076_:
{
lean_object* v___x_3078_; lean_object* v___x_3080_; 
v___x_3078_ = lean_array_fset(v_xs_x27_3075_, v_j_3067_, v___y_3077_);
lean_dec(v_j_3067_);
if (v_isShared_3072_ == 0)
{
lean_ctor_set(v___x_3071_, 0, v___x_3078_);
v___x_3080_ = v___x_3071_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v___x_3078_);
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
lean_object* v_ks_3110_; lean_object* v_vs_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3129_; 
v_ks_3110_ = lean_ctor_get(v_x_3059_, 0);
v_vs_3111_ = lean_ctor_get(v_x_3059_, 1);
v_isSharedCheck_3129_ = !lean_is_exclusive(v_x_3059_);
if (v_isSharedCheck_3129_ == 0)
{
v___x_3113_ = v_x_3059_;
v_isShared_3114_ = v_isSharedCheck_3129_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_vs_3111_);
lean_inc(v_ks_3110_);
lean_dec(v_x_3059_);
v___x_3113_ = lean_box(0);
v_isShared_3114_ = v_isSharedCheck_3129_;
goto v_resetjp_3112_;
}
v_resetjp_3112_:
{
lean_object* v___x_3116_; 
if (v_isShared_3114_ == 0)
{
v___x_3116_ = v___x_3113_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v_ks_3110_);
lean_ctor_set(v_reuseFailAlloc_3128_, 1, v_vs_3111_);
v___x_3116_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3115_;
}
v_reusejp_3115_:
{
lean_object* v_newNode_3117_; size_t v___x_3118_; uint8_t v___x_3119_; 
v_newNode_3117_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(v___x_3116_, v_x_3062_, v_x_3063_);
v___x_3118_ = ((size_t)7ULL);
v___x_3119_ = lean_usize_dec_le(v___x_3118_, v_x_3061_);
if (v___x_3119_ == 0)
{
lean_object* v___x_3120_; lean_object* v___x_3121_; uint8_t v___x_3122_; 
v___x_3120_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3117_);
v___x_3121_ = lean_unsigned_to_nat(4u);
v___x_3122_ = lean_nat_dec_lt(v___x_3120_, v___x_3121_);
lean_dec(v___x_3120_);
if (v___x_3122_ == 0)
{
lean_object* v_ks_3123_; lean_object* v_vs_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; 
v_ks_3123_ = lean_ctor_get(v_newNode_3117_, 0);
lean_inc_ref(v_ks_3123_);
v_vs_3124_ = lean_ctor_get(v_newNode_3117_, 1);
lean_inc_ref(v_vs_3124_);
lean_dec_ref(v_newNode_3117_);
v___x_3125_ = lean_unsigned_to_nat(0u);
v___x_3126_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_3127_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(v_x_3061_, v_ks_3123_, v_vs_3124_, v___x_3125_, v___x_3126_);
lean_dec_ref(v_vs_3124_);
lean_dec_ref(v_ks_3123_);
return v___x_3127_;
}
else
{
return v_newNode_3117_;
}
}
else
{
return v_newNode_3117_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(size_t v_depth_3130_, lean_object* v_keys_3131_, lean_object* v_vals_3132_, lean_object* v_i_3133_, lean_object* v_entries_3134_){
_start:
{
lean_object* v___x_3135_; uint8_t v___x_3136_; 
v___x_3135_ = lean_array_get_size(v_keys_3131_);
v___x_3136_ = lean_nat_dec_lt(v_i_3133_, v___x_3135_);
if (v___x_3136_ == 0)
{
lean_dec(v_i_3133_);
return v_entries_3134_;
}
else
{
lean_object* v_k_3137_; lean_object* v_v_3138_; uint64_t v___x_3139_; size_t v_h_3140_; size_t v___x_3141_; lean_object* v___x_3142_; size_t v___x_3143_; size_t v___x_3144_; size_t v___x_3145_; size_t v_h_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; 
v_k_3137_ = lean_array_fget_borrowed(v_keys_3131_, v_i_3133_);
v_v_3138_ = lean_array_fget_borrowed(v_vals_3132_, v_i_3133_);
v___x_3139_ = l_Lean_instHashableMVarId_hash(v_k_3137_);
v_h_3140_ = lean_uint64_to_usize(v___x_3139_);
v___x_3141_ = ((size_t)5ULL);
v___x_3142_ = lean_unsigned_to_nat(1u);
v___x_3143_ = ((size_t)1ULL);
v___x_3144_ = lean_usize_sub(v_depth_3130_, v___x_3143_);
v___x_3145_ = lean_usize_mul(v___x_3141_, v___x_3144_);
v_h_3146_ = lean_usize_shift_right(v_h_3140_, v___x_3145_);
v___x_3147_ = lean_nat_add(v_i_3133_, v___x_3142_);
lean_dec(v_i_3133_);
lean_inc(v_v_3138_);
lean_inc(v_k_3137_);
v___x_3148_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_entries_3134_, v_h_3146_, v_depth_3130_, v_k_3137_, v_v_3138_);
v_i_3133_ = v___x_3147_;
v_entries_3134_ = v___x_3148_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_depth_3150_, lean_object* v_keys_3151_, lean_object* v_vals_3152_, lean_object* v_i_3153_, lean_object* v_entries_3154_){
_start:
{
size_t v_depth_boxed_3155_; lean_object* v_res_3156_; 
v_depth_boxed_3155_ = lean_unbox_usize(v_depth_3150_);
lean_dec(v_depth_3150_);
v_res_3156_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_boxed_3155_, v_keys_3151_, v_vals_3152_, v_i_3153_, v_entries_3154_);
lean_dec_ref(v_vals_3152_);
lean_dec_ref(v_keys_3151_);
return v_res_3156_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_3157_, lean_object* v_x_3158_, lean_object* v_x_3159_, lean_object* v_x_3160_, lean_object* v_x_3161_){
_start:
{
size_t v_x_4992__boxed_3162_; size_t v_x_4993__boxed_3163_; lean_object* v_res_3164_; 
v_x_4992__boxed_3162_ = lean_unbox_usize(v_x_3158_);
lean_dec(v_x_3158_);
v_x_4993__boxed_3163_ = lean_unbox_usize(v_x_3159_);
lean_dec(v_x_3159_);
v_res_3164_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_x_3157_, v_x_4992__boxed_3162_, v_x_4993__boxed_3163_, v_x_3160_, v_x_3161_);
return v_res_3164_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(lean_object* v_x_3165_, lean_object* v_x_3166_, lean_object* v_x_3167_){
_start:
{
uint64_t v___x_3168_; size_t v___x_3169_; size_t v___x_3170_; lean_object* v___x_3171_; 
v___x_3168_ = l_Lean_instHashableMVarId_hash(v_x_3166_);
v___x_3169_ = lean_uint64_to_usize(v___x_3168_);
v___x_3170_ = ((size_t)1ULL);
v___x_3171_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_x_3165_, v___x_3169_, v___x_3170_, v_x_3166_, v_x_3167_);
return v___x_3171_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(lean_object* v_mvarId_3172_, lean_object* v_val_3173_, lean_object* v___y_3174_){
_start:
{
lean_object* v___x_3176_; lean_object* v_mctx_3177_; lean_object* v_cache_3178_; lean_object* v_zetaDeltaFVarIds_3179_; lean_object* v_postponed_3180_; lean_object* v_diag_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3210_; 
v___x_3176_ = lean_st_ref_take(v___y_3174_);
v_mctx_3177_ = lean_ctor_get(v___x_3176_, 0);
v_cache_3178_ = lean_ctor_get(v___x_3176_, 1);
v_zetaDeltaFVarIds_3179_ = lean_ctor_get(v___x_3176_, 2);
v_postponed_3180_ = lean_ctor_get(v___x_3176_, 3);
v_diag_3181_ = lean_ctor_get(v___x_3176_, 4);
v_isSharedCheck_3210_ = !lean_is_exclusive(v___x_3176_);
if (v_isSharedCheck_3210_ == 0)
{
v___x_3183_ = v___x_3176_;
v_isShared_3184_ = v_isSharedCheck_3210_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_diag_3181_);
lean_inc(v_postponed_3180_);
lean_inc(v_zetaDeltaFVarIds_3179_);
lean_inc(v_cache_3178_);
lean_inc(v_mctx_3177_);
lean_dec(v___x_3176_);
v___x_3183_ = lean_box(0);
v_isShared_3184_ = v_isSharedCheck_3210_;
goto v_resetjp_3182_;
}
v_resetjp_3182_:
{
lean_object* v_depth_3185_; lean_object* v_levelAssignDepth_3186_; lean_object* v_lmvarCounter_3187_; lean_object* v_mvarCounter_3188_; lean_object* v_lDecls_3189_; lean_object* v_decls_3190_; lean_object* v_userNames_3191_; lean_object* v_lAssignment_3192_; lean_object* v_eAssignment_3193_; lean_object* v_dAssignment_3194_; lean_object* v_instanceTypedMVars_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3209_; 
v_depth_3185_ = lean_ctor_get(v_mctx_3177_, 0);
v_levelAssignDepth_3186_ = lean_ctor_get(v_mctx_3177_, 1);
v_lmvarCounter_3187_ = lean_ctor_get(v_mctx_3177_, 2);
v_mvarCounter_3188_ = lean_ctor_get(v_mctx_3177_, 3);
v_lDecls_3189_ = lean_ctor_get(v_mctx_3177_, 4);
v_decls_3190_ = lean_ctor_get(v_mctx_3177_, 5);
v_userNames_3191_ = lean_ctor_get(v_mctx_3177_, 6);
v_lAssignment_3192_ = lean_ctor_get(v_mctx_3177_, 7);
v_eAssignment_3193_ = lean_ctor_get(v_mctx_3177_, 8);
v_dAssignment_3194_ = lean_ctor_get(v_mctx_3177_, 9);
v_instanceTypedMVars_3195_ = lean_ctor_get(v_mctx_3177_, 10);
v_isSharedCheck_3209_ = !lean_is_exclusive(v_mctx_3177_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3197_ = v_mctx_3177_;
v_isShared_3198_ = v_isSharedCheck_3209_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_instanceTypedMVars_3195_);
lean_inc(v_dAssignment_3194_);
lean_inc(v_eAssignment_3193_);
lean_inc(v_lAssignment_3192_);
lean_inc(v_userNames_3191_);
lean_inc(v_decls_3190_);
lean_inc(v_lDecls_3189_);
lean_inc(v_mvarCounter_3188_);
lean_inc(v_lmvarCounter_3187_);
lean_inc(v_levelAssignDepth_3186_);
lean_inc(v_depth_3185_);
lean_dec(v_mctx_3177_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3209_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3202_; 
v___x_3199_ = lean_box(0);
v___x_3200_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(v_eAssignment_3193_, v_mvarId_3172_, v_val_3173_);
if (v_isShared_3198_ == 0)
{
lean_ctor_set(v___x_3197_, 8, v___x_3200_);
v___x_3202_ = v___x_3197_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_depth_3185_);
lean_ctor_set(v_reuseFailAlloc_3208_, 1, v_levelAssignDepth_3186_);
lean_ctor_set(v_reuseFailAlloc_3208_, 2, v_lmvarCounter_3187_);
lean_ctor_set(v_reuseFailAlloc_3208_, 3, v_mvarCounter_3188_);
lean_ctor_set(v_reuseFailAlloc_3208_, 4, v_lDecls_3189_);
lean_ctor_set(v_reuseFailAlloc_3208_, 5, v_decls_3190_);
lean_ctor_set(v_reuseFailAlloc_3208_, 6, v_userNames_3191_);
lean_ctor_set(v_reuseFailAlloc_3208_, 7, v_lAssignment_3192_);
lean_ctor_set(v_reuseFailAlloc_3208_, 8, v___x_3200_);
lean_ctor_set(v_reuseFailAlloc_3208_, 9, v_dAssignment_3194_);
lean_ctor_set(v_reuseFailAlloc_3208_, 10, v_instanceTypedMVars_3195_);
v___x_3202_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
lean_object* v___x_3204_; 
if (v_isShared_3184_ == 0)
{
lean_ctor_set(v___x_3183_, 0, v___x_3202_);
v___x_3204_ = v___x_3183_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v___x_3202_);
lean_ctor_set(v_reuseFailAlloc_3207_, 1, v_cache_3178_);
lean_ctor_set(v_reuseFailAlloc_3207_, 2, v_zetaDeltaFVarIds_3179_);
lean_ctor_set(v_reuseFailAlloc_3207_, 3, v_postponed_3180_);
lean_ctor_set(v_reuseFailAlloc_3207_, 4, v_diag_3181_);
v___x_3204_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
lean_object* v___x_3205_; lean_object* v___x_3206_; 
v___x_3205_ = lean_st_ref_put(v___y_3174_, v___x_3204_);
v___x_3206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3206_, 0, v___x_3199_);
return v___x_3206_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg___boxed(lean_object* v_mvarId_3211_, lean_object* v_val_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_){
_start:
{
lean_object* v_res_3215_; 
v_res_3215_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(v_mvarId_3211_, v_val_3212_, v___y_3213_);
lean_dec(v___y_3213_);
return v_res_3215_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3217_; lean_object* v___x_3218_; 
v___x_3217_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1___closed__0));
v___x_3218_ = l_Lean_stringToMessageData(v___x_3217_);
return v___x_3218_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(lean_object* v___f_3219_, lean_object* v_a_3220_, lean_object* v_x_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_){
_start:
{
lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3227_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1___closed__1, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1___closed__1);
v___x_3228_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_3227_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_);
if (lean_obj_tag(v___x_3228_) == 0)
{
lean_object* v_a_3229_; lean_object* v___x_3230_; 
v_a_3229_ = lean_ctor_get(v___x_3228_, 0);
lean_inc(v_a_3229_);
lean_dec_ref_known(v___x_3228_, 1);
lean_inc(v___y_3225_);
lean_inc_ref(v___y_3224_);
lean_inc(v___y_3223_);
lean_inc_ref(v___y_3222_);
v___x_3230_ = lean_apply_7(v___f_3219_, v_a_3229_, v_a_3220_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_, lean_box(0));
return v___x_3230_;
}
else
{
lean_object* v_a_3231_; lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3238_; 
lean_dec(v_a_3220_);
lean_dec_ref(v___f_3219_);
v_a_3231_ = lean_ctor_get(v___x_3228_, 0);
v_isSharedCheck_3238_ = !lean_is_exclusive(v___x_3228_);
if (v_isSharedCheck_3238_ == 0)
{
v___x_3233_ = v___x_3228_;
v_isShared_3234_ = v_isSharedCheck_3238_;
goto v_resetjp_3232_;
}
else
{
lean_inc(v_a_3231_);
lean_dec(v___x_3228_);
v___x_3233_ = lean_box(0);
v_isShared_3234_ = v_isSharedCheck_3238_;
goto v_resetjp_3232_;
}
v_resetjp_3232_:
{
lean_object* v___x_3236_; 
if (v_isShared_3234_ == 0)
{
v___x_3236_ = v___x_3233_;
goto v_reusejp_3235_;
}
else
{
lean_object* v_reuseFailAlloc_3237_; 
v_reuseFailAlloc_3237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3237_, 0, v_a_3231_);
v___x_3236_ = v_reuseFailAlloc_3237_;
goto v_reusejp_3235_;
}
v_reusejp_3235_:
{
return v___x_3236_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1___boxed(lean_object* v___f_3239_, lean_object* v_a_3240_, lean_object* v_x_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_){
_start:
{
lean_object* v_res_3247_; 
v_res_3247_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(v___f_3239_, v_a_3240_, v_x_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec(v_x_3241_);
return v_res_3247_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(lean_object* v___f_3248_, lean_object* v_a_3249_, lean_object* v_x_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_){
_start:
{
lean_object* v___x_3256_; lean_object* v___x_3257_; 
v___x_3256_ = lean_box(0);
lean_inc(v___y_3254_);
lean_inc_ref(v___y_3253_);
lean_inc(v___y_3252_);
lean_inc_ref(v___y_3251_);
v___x_3257_ = lean_apply_7(v___f_3248_, v___x_3256_, v_a_3249_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, lean_box(0));
return v___x_3257_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___boxed(lean_object* v___f_3258_, lean_object* v_a_3259_, lean_object* v_x_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_){
_start:
{
lean_object* v_res_3266_; 
v_res_3266_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(v___f_3258_, v_a_3259_, v_x_3260_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_);
lean_dec(v___y_3264_);
lean_dec_ref(v___y_3263_);
lean_dec(v___y_3262_);
lean_dec_ref(v___y_3261_);
return v_res_3266_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0(uint8_t v___x_3267_, lean_object* v_____r_3268_, lean_object* v_mvarId_u2082_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_){
_start:
{
lean_object* v___x_3275_; 
v___x_3275_ = l_Lean_Meta_introSubstEq(v_mvarId_u2082_3269_, v___x_3267_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_);
if (lean_obj_tag(v___x_3275_) == 0)
{
lean_object* v_a_3276_; lean_object* v___x_3278_; uint8_t v_isShared_3279_; uint8_t v_isSharedCheck_3285_; 
v_a_3276_ = lean_ctor_get(v___x_3275_, 0);
v_isSharedCheck_3285_ = !lean_is_exclusive(v___x_3275_);
if (v_isSharedCheck_3285_ == 0)
{
v___x_3278_ = v___x_3275_;
v_isShared_3279_ = v_isSharedCheck_3285_;
goto v_resetjp_3277_;
}
else
{
lean_inc(v_a_3276_);
lean_dec(v___x_3275_);
v___x_3278_ = lean_box(0);
v_isShared_3279_ = v_isSharedCheck_3285_;
goto v_resetjp_3277_;
}
v_resetjp_3277_:
{
lean_object* v_snd_3280_; lean_object* v___x_3281_; lean_object* v___x_3283_; 
v_snd_3280_ = lean_ctor_get(v_a_3276_, 1);
lean_inc(v_snd_3280_);
lean_dec(v_a_3276_);
v___x_3281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3281_, 0, v_snd_3280_);
if (v_isShared_3279_ == 0)
{
lean_ctor_set(v___x_3278_, 0, v___x_3281_);
v___x_3283_ = v___x_3278_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3284_; 
v_reuseFailAlloc_3284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3284_, 0, v___x_3281_);
v___x_3283_ = v_reuseFailAlloc_3284_;
goto v_reusejp_3282_;
}
v_reusejp_3282_:
{
return v___x_3283_;
}
}
}
else
{
lean_object* v_a_3286_; lean_object* v___x_3288_; uint8_t v_isShared_3289_; uint8_t v_isSharedCheck_3293_; 
v_a_3286_ = lean_ctor_get(v___x_3275_, 0);
v_isSharedCheck_3293_ = !lean_is_exclusive(v___x_3275_);
if (v_isSharedCheck_3293_ == 0)
{
v___x_3288_ = v___x_3275_;
v_isShared_3289_ = v_isSharedCheck_3293_;
goto v_resetjp_3287_;
}
else
{
lean_inc(v_a_3286_);
lean_dec(v___x_3275_);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0___boxed(lean_object* v___x_3294_, lean_object* v_____r_3295_, lean_object* v_mvarId_u2082_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_){
_start:
{
uint8_t v___x_5280__boxed_3302_; lean_object* v_res_3303_; 
v___x_5280__boxed_3302_ = lean_unbox(v___x_3294_);
v_res_3303_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0(v___x_5280__boxed_3302_, v_____r_3295_, v_mvarId_u2082_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_);
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3299_);
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3297_);
return v_res_3303_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; 
v___x_3312_ = lean_box(0);
v___x_3313_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__3));
v___x_3314_ = l_Lean_mkConst(v___x_3313_, v___x_3312_);
return v___x_3314_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg(lean_object* v_a_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_){
_start:
{
lean_object* v___y_3322_; uint8_t v___x_3342_; lean_object* v___f_3343_; uint8_t v___x_3344_; lean_object* v___x_3345_; 
v___x_3342_ = 0;
v___f_3343_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__0));
v___x_3344_ = 1;
lean_inc(v_a_3315_);
v___x_3345_ = l_Lean_MVarId_getType(v_a_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_);
if (lean_obj_tag(v___x_3345_) == 0)
{
lean_object* v_a_3346_; lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3403_; 
v_a_3346_ = lean_ctor_get(v___x_3345_, 0);
v_isSharedCheck_3403_ = !lean_is_exclusive(v___x_3345_);
if (v_isSharedCheck_3403_ == 0)
{
v___x_3348_ = v___x_3345_;
v_isShared_3349_ = v_isSharedCheck_3403_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_a_3346_);
lean_dec(v___x_3345_);
v___x_3348_ = lean_box(0);
v_isShared_3349_ = v_isSharedCheck_3403_;
goto v_resetjp_3347_;
}
v_resetjp_3347_:
{
if (lean_obj_tag(v_a_3346_) == 7)
{
lean_object* v_binderType_3350_; lean_object* v_body_3351_; uint8_t v___x_3352_; 
v_binderType_3350_ = lean_ctor_get(v_a_3346_, 1);
lean_inc_ref(v_binderType_3350_);
v_body_3351_ = lean_ctor_get(v_a_3346_, 2);
lean_inc_ref(v_body_3351_);
lean_dec_ref_known(v_a_3346_, 3);
v___x_3352_ = l_Lean_Expr_hasLooseBVars(v_body_3351_);
if (v___x_3352_ == 0)
{
lean_object* v___x_3353_; 
lean_del_object(v___x_3348_);
v___x_3353_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_3350_, v___y_3317_);
if (lean_obj_tag(v___x_3353_) == 0)
{
lean_object* v_a_3354_; lean_object* v___x_3355_; uint8_t v___x_3356_; 
v_a_3354_ = lean_ctor_get(v___x_3353_, 0);
lean_inc(v_a_3354_);
lean_dec_ref_known(v___x_3353_, 1);
v___x_3355_ = l_Lean_Expr_cleanupAnnotations(v_a_3354_);
v___x_3356_ = l_Lean_Expr_isApp(v___x_3355_);
if (v___x_3356_ == 0)
{
lean_object* v___x_3357_; lean_object* v___x_3358_; 
lean_dec_ref(v___x_3355_);
lean_dec_ref(v_body_3351_);
v___x_3357_ = lean_box(0);
v___x_3358_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(v___f_3343_, v_a_3315_, v___x_3357_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_);
v___y_3322_ = v___x_3358_;
goto v___jp_3321_;
}
else
{
lean_object* v_arg_3359_; lean_object* v___x_3360_; uint8_t v___x_3361_; 
v_arg_3359_ = lean_ctor_get(v___x_3355_, 1);
lean_inc_ref(v_arg_3359_);
v___x_3360_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3355_);
v___x_3361_ = l_Lean_Expr_isApp(v___x_3360_);
if (v___x_3361_ == 0)
{
lean_object* v___x_3362_; lean_object* v___x_3363_; 
lean_dec_ref(v___x_3360_);
lean_dec_ref(v_arg_3359_);
lean_dec_ref(v_body_3351_);
v___x_3362_ = lean_box(0);
v___x_3363_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(v___f_3343_, v_a_3315_, v___x_3362_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_);
v___y_3322_ = v___x_3363_;
goto v___jp_3321_;
}
else
{
lean_object* v_arg_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; uint8_t v___x_3367_; 
v_arg_3364_ = lean_ctor_get(v___x_3360_, 1);
lean_inc_ref(v_arg_3364_);
v___x_3365_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3360_);
v___x_3366_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__1));
v___x_3367_ = l_Lean_Expr_isConstOf(v___x_3365_, v___x_3366_);
lean_dec_ref(v___x_3365_);
if (v___x_3367_ == 0)
{
lean_object* v___x_3368_; lean_object* v___x_3369_; 
lean_dec_ref(v_arg_3364_);
lean_dec_ref(v_arg_3359_);
lean_dec_ref(v_body_3351_);
v___x_3368_ = lean_box(0);
v___x_3369_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(v___f_3343_, v_a_3315_, v___x_3368_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_);
v___y_3322_ = v___x_3369_;
goto v___jp_3321_;
}
else
{
lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; 
v___x_3370_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__4, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__4_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__4);
v___x_3371_ = l_Lean_mkApp3(v___x_3370_, v_arg_3364_, v_arg_3359_, v_body_3351_);
v___x_3372_ = lean_unsigned_to_nat(1u);
lean_inc(v_a_3315_);
v___x_3373_ = l_Lean_MVarId_applyN(v_a_3315_, v___x_3371_, v___x_3372_, v___x_3344_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_);
if (lean_obj_tag(v___x_3373_) == 0)
{
lean_object* v_a_3374_; 
v_a_3374_ = lean_ctor_get(v___x_3373_, 0);
lean_inc(v_a_3374_);
lean_dec_ref_known(v___x_3373_, 1);
if (lean_obj_tag(v_a_3374_) == 1)
{
lean_object* v_tail_3375_; 
v_tail_3375_ = lean_ctor_get(v_a_3374_, 1);
if (lean_obj_tag(v_tail_3375_) == 0)
{
lean_object* v_head_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
lean_dec(v_a_3315_);
v_head_3376_ = lean_ctor_get(v_a_3374_, 0);
lean_inc(v_head_3376_);
lean_dec_ref_known(v_a_3374_, 2);
v___x_3377_ = lean_box(0);
v___x_3378_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0(v___x_3342_, v___x_3377_, v_head_3376_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_);
v___y_3322_ = v___x_3378_;
goto v___jp_3321_;
}
else
{
lean_object* v___x_3379_; 
v___x_3379_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(v___f_3343_, v_a_3315_, v_a_3374_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_);
lean_dec_ref_known(v_a_3374_, 2);
v___y_3322_ = v___x_3379_;
goto v___jp_3321_;
}
}
else
{
lean_object* v___x_3380_; 
v___x_3380_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(v___f_3343_, v_a_3315_, v_a_3374_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_);
lean_dec(v_a_3374_);
v___y_3322_ = v___x_3380_;
goto v___jp_3321_;
}
}
else
{
lean_object* v_a_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3388_; 
lean_dec(v_a_3315_);
v_a_3381_ = lean_ctor_get(v___x_3373_, 0);
v_isSharedCheck_3388_ = !lean_is_exclusive(v___x_3373_);
if (v_isSharedCheck_3388_ == 0)
{
v___x_3383_ = v___x_3373_;
v_isShared_3384_ = v_isSharedCheck_3388_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_a_3381_);
lean_dec(v___x_3373_);
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
}
}
else
{
lean_object* v_a_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3396_; 
lean_dec_ref(v_body_3351_);
lean_dec(v_a_3315_);
v_a_3389_ = lean_ctor_get(v___x_3353_, 0);
v_isSharedCheck_3396_ = !lean_is_exclusive(v___x_3353_);
if (v_isSharedCheck_3396_ == 0)
{
v___x_3391_ = v___x_3353_;
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
else
{
lean_inc(v_a_3389_);
lean_dec(v___x_3353_);
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
else
{
lean_object* v___x_3398_; 
lean_dec_ref(v_body_3351_);
lean_dec_ref(v_binderType_3350_);
if (v_isShared_3349_ == 0)
{
lean_ctor_set(v___x_3348_, 0, v_a_3315_);
v___x_3398_ = v___x_3348_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3399_; 
v_reuseFailAlloc_3399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3399_, 0, v_a_3315_);
v___x_3398_ = v_reuseFailAlloc_3399_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
return v___x_3398_;
}
}
}
else
{
lean_object* v___x_3401_; 
lean_dec(v_a_3346_);
if (v_isShared_3349_ == 0)
{
lean_ctor_set(v___x_3348_, 0, v_a_3315_);
v___x_3401_ = v___x_3348_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v_a_3315_);
v___x_3401_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
return v___x_3401_;
}
}
}
}
else
{
lean_object* v_a_3404_; lean_object* v___x_3406_; uint8_t v_isShared_3407_; uint8_t v_isSharedCheck_3411_; 
lean_dec(v_a_3315_);
v_a_3404_ = lean_ctor_get(v___x_3345_, 0);
v_isSharedCheck_3411_ = !lean_is_exclusive(v___x_3345_);
if (v_isSharedCheck_3411_ == 0)
{
v___x_3406_ = v___x_3345_;
v_isShared_3407_ = v_isSharedCheck_3411_;
goto v_resetjp_3405_;
}
else
{
lean_inc(v_a_3404_);
lean_dec(v___x_3345_);
v___x_3406_ = lean_box(0);
v_isShared_3407_ = v_isSharedCheck_3411_;
goto v_resetjp_3405_;
}
v_resetjp_3405_:
{
lean_object* v___x_3409_; 
if (v_isShared_3407_ == 0)
{
v___x_3409_ = v___x_3406_;
goto v_reusejp_3408_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v_a_3404_);
v___x_3409_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3408_;
}
v_reusejp_3408_:
{
return v___x_3409_;
}
}
}
v___jp_3321_:
{
if (lean_obj_tag(v___y_3322_) == 0)
{
lean_object* v_a_3323_; lean_object* v___x_3325_; uint8_t v_isShared_3326_; uint8_t v_isSharedCheck_3333_; 
v_a_3323_ = lean_ctor_get(v___y_3322_, 0);
v_isSharedCheck_3333_ = !lean_is_exclusive(v___y_3322_);
if (v_isSharedCheck_3333_ == 0)
{
v___x_3325_ = v___y_3322_;
v_isShared_3326_ = v_isSharedCheck_3333_;
goto v_resetjp_3324_;
}
else
{
lean_inc(v_a_3323_);
lean_dec(v___y_3322_);
v___x_3325_ = lean_box(0);
v_isShared_3326_ = v_isSharedCheck_3333_;
goto v_resetjp_3324_;
}
v_resetjp_3324_:
{
if (lean_obj_tag(v_a_3323_) == 0)
{
lean_object* v_a_3327_; lean_object* v___x_3329_; 
v_a_3327_ = lean_ctor_get(v_a_3323_, 0);
lean_inc(v_a_3327_);
lean_dec_ref_known(v_a_3323_, 1);
if (v_isShared_3326_ == 0)
{
lean_ctor_set(v___x_3325_, 0, v_a_3327_);
v___x_3329_ = v___x_3325_;
goto v_reusejp_3328_;
}
else
{
lean_object* v_reuseFailAlloc_3330_; 
v_reuseFailAlloc_3330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3330_, 0, v_a_3327_);
v___x_3329_ = v_reuseFailAlloc_3330_;
goto v_reusejp_3328_;
}
v_reusejp_3328_:
{
return v___x_3329_;
}
}
else
{
lean_object* v_a_3331_; 
lean_del_object(v___x_3325_);
v_a_3331_ = lean_ctor_get(v_a_3323_, 0);
lean_inc(v_a_3331_);
lean_dec_ref_known(v_a_3323_, 1);
v_a_3315_ = v_a_3331_;
goto _start;
}
}
}
else
{
lean_object* v_a_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3341_; 
v_a_3334_ = lean_ctor_get(v___y_3322_, 0);
v_isSharedCheck_3341_ = !lean_is_exclusive(v___y_3322_);
if (v_isSharedCheck_3341_ == 0)
{
v___x_3336_ = v___y_3322_;
v_isShared_3337_ = v_isSharedCheck_3341_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_a_3334_);
lean_dec(v___y_3322_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3341_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
lean_object* v___x_3339_; 
if (v_isShared_3337_ == 0)
{
v___x_3339_ = v___x_3336_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v_a_3334_);
v___x_3339_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
return v___x_3339_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___boxed(lean_object* v_a_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_){
_start:
{
lean_object* v_res_3418_; 
v_res_3418_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg(v_a_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_);
lean_dec(v___y_3416_);
lean_dec_ref(v___y_3415_);
lean_dec(v___y_3414_);
lean_dec_ref(v___y_3413_);
return v_res_3418_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3420_; lean_object* v___x_3421_; 
v___x_3420_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__0));
v___x_3421_ = l_Lean_stringToMessageData(v___x_3420_);
return v___x_3421_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; 
v___x_3427_ = lean_box(0);
v___x_3428_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__4));
v___x_3429_ = l_Lean_mkConst(v___x_3428_, v___x_3427_);
return v___x_3429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0(lean_object* v_ctorVal_3434_, lean_object* v_xs_3435_, lean_object* v_type_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_){
_start:
{
lean_object* v___x_3451_; lean_object* v___x_3452_; 
v___x_3451_ = lean_box(0);
v___x_3452_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_3436_, v___x_3451_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_);
if (lean_obj_tag(v___x_3452_) == 0)
{
lean_object* v_a_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; uint8_t v___x_3457_; uint8_t v___x_3458_; lean_object* v___y_3460_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; 
v_a_3453_ = lean_ctor_get(v___x_3452_, 0);
lean_inc(v_a_3453_);
lean_dec_ref_known(v___x_3452_, 1);
v___x_3454_ = l_Lean_Expr_mvarId_x21(v_a_3453_);
v___x_3455_ = lean_box(0);
v___x_3456_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__5, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__5_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__5);
v___x_3457_ = 1;
v___x_3458_ = 0;
v___x_3471_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6));
v___x_3472_ = lean_box(0);
v___x_3473_ = l_Lean_MVarId_apply(v___x_3454_, v___x_3456_, v___x_3471_, v___x_3472_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_);
if (lean_obj_tag(v___x_3473_) == 0)
{
lean_object* v_a_3474_; 
v_a_3474_ = lean_ctor_get(v___x_3473_, 0);
lean_inc(v_a_3474_);
lean_dec_ref_known(v___x_3473_, 1);
if (lean_obj_tag(v_a_3474_) == 1)
{
lean_object* v_tail_3475_; 
v_tail_3475_ = lean_ctor_get(v_a_3474_, 1);
lean_inc(v_tail_3475_);
if (lean_obj_tag(v_tail_3475_) == 1)
{
lean_object* v_tail_3476_; 
v_tail_3476_ = lean_ctor_get(v_tail_3475_, 1);
if (lean_obj_tag(v_tail_3476_) == 0)
{
lean_object* v_toConstantVal_3477_; lean_object* v_head_3478_; lean_object* v_head_3479_; lean_object* v_name_3480_; lean_object* v_levelParams_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; 
v_toConstantVal_3477_ = lean_ctor_get(v_ctorVal_3434_, 0);
lean_inc_ref(v_toConstantVal_3477_);
lean_dec_ref(v_ctorVal_3434_);
v_head_3478_ = lean_ctor_get(v_a_3474_, 0);
lean_inc(v_head_3478_);
lean_dec_ref_known(v_a_3474_, 2);
v_head_3479_ = lean_ctor_get(v_tail_3475_, 0);
lean_inc(v_head_3479_);
lean_dec_ref_known(v_tail_3475_, 2);
v_name_3480_ = lean_ctor_get(v_toConstantVal_3477_, 0);
lean_inc_n(v_name_3480_, 2);
v_levelParams_3481_ = lean_ctor_get(v_toConstantVal_3477_, 1);
lean_inc(v_levelParams_3481_);
lean_dec_ref(v_toConstantVal_3477_);
v___x_3482_ = l_Lean_Meta_mkInjectiveTheoremNameFor(v_name_3480_);
v___x_3483_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(v_levelParams_3481_, v___x_3455_);
v___x_3484_ = l_Lean_mkConst(v___x_3482_, v___x_3483_);
v___x_3485_ = l_Lean_mkAppN(v___x_3484_, v_xs_3435_);
v___x_3486_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(v_head_3478_, v___x_3485_, v___y_3438_);
lean_dec_ref(v___x_3486_);
v___x_3487_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg(v_head_3479_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_);
if (lean_obj_tag(v___x_3487_) == 0)
{
lean_object* v_a_3488_; lean_object* v___x_3489_; 
v_a_3488_ = lean_ctor_get(v___x_3487_, 0);
lean_inc(v_a_3488_);
lean_dec_ref_known(v___x_3487_, 1);
v___x_3489_ = l_Lean_MVarId_refl(v_a_3488_, v___x_3457_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_);
if (lean_obj_tag(v___x_3489_) == 0)
{
lean_dec(v_name_3480_);
v___y_3460_ = v___x_3489_;
goto v___jp_3459_;
}
else
{
lean_object* v_a_3490_; uint8_t v___y_3492_; uint8_t v___x_3495_; 
v_a_3490_ = lean_ctor_get(v___x_3489_, 0);
lean_inc(v_a_3490_);
v___x_3495_ = l_Lean_Exception_isInterrupt(v_a_3490_);
if (v___x_3495_ == 0)
{
uint8_t v___x_3496_; 
v___x_3496_ = l_Lean_Exception_isRuntime(v_a_3490_);
v___y_3492_ = v___x_3496_;
goto v___jp_3491_;
}
else
{
lean_dec(v_a_3490_);
v___y_3492_ = v___x_3495_;
goto v___jp_3491_;
}
v___jp_3491_:
{
if (v___y_3492_ == 0)
{
lean_object* v___x_3493_; lean_object* v___x_3494_; 
lean_dec_ref_known(v___x_3489_, 1);
v___x_3493_ = l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(v_name_3480_);
v___x_3494_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_3493_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_);
v___y_3460_ = v___x_3494_;
goto v___jp_3459_;
}
else
{
lean_dec(v_name_3480_);
v___y_3460_ = v___x_3489_;
goto v___jp_3459_;
}
}
}
}
else
{
lean_object* v_a_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3504_; 
lean_dec(v_name_3480_);
lean_dec(v_a_3453_);
v_a_3497_ = lean_ctor_get(v___x_3487_, 0);
v_isSharedCheck_3504_ = !lean_is_exclusive(v___x_3487_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3499_ = v___x_3487_;
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_a_3497_);
lean_dec(v___x_3487_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
lean_object* v___x_3502_; 
if (v_isShared_3500_ == 0)
{
v___x_3502_ = v___x_3499_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_a_3497_);
v___x_3502_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
return v___x_3502_;
}
}
}
}
else
{
lean_dec_ref_known(v_tail_3475_, 2);
lean_dec_ref_known(v_a_3474_, 2);
lean_dec(v_a_3453_);
goto v___jp_3442_;
}
}
else
{
lean_dec(v_tail_3475_);
lean_dec_ref_known(v_a_3474_, 2);
lean_dec(v_a_3453_);
goto v___jp_3442_;
}
}
else
{
lean_dec(v_a_3474_);
lean_dec(v_a_3453_);
goto v___jp_3442_;
}
}
else
{
lean_object* v_a_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3512_; 
lean_dec(v_a_3453_);
lean_dec_ref(v_ctorVal_3434_);
v_a_3505_ = lean_ctor_get(v___x_3473_, 0);
v_isSharedCheck_3512_ = !lean_is_exclusive(v___x_3473_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_3507_ = v___x_3473_;
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_a_3505_);
lean_dec(v___x_3473_);
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
v___jp_3459_:
{
if (lean_obj_tag(v___y_3460_) == 0)
{
uint8_t v___x_3461_; lean_object* v___x_3462_; 
lean_dec_ref_known(v___y_3460_, 1);
v___x_3461_ = 1;
v___x_3462_ = l_Lean_Meta_mkLambdaFVars(v_xs_3435_, v_a_3453_, v___x_3458_, v___x_3457_, v___x_3458_, v___x_3457_, v___x_3461_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_);
return v___x_3462_;
}
else
{
lean_object* v_a_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3470_; 
lean_dec(v_a_3453_);
v_a_3463_ = lean_ctor_get(v___y_3460_, 0);
v_isSharedCheck_3470_ = !lean_is_exclusive(v___y_3460_);
if (v_isSharedCheck_3470_ == 0)
{
v___x_3465_ = v___y_3460_;
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_a_3463_);
lean_dec(v___y_3460_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
lean_object* v___x_3468_; 
if (v_isShared_3466_ == 0)
{
v___x_3468_ = v___x_3465_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_a_3463_);
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
}
else
{
lean_dec_ref(v_ctorVal_3434_);
return v___x_3452_;
}
v___jp_3442_:
{
lean_object* v_toConstantVal_3443_; lean_object* v_name_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; 
v_toConstantVal_3443_ = lean_ctor_get(v_ctorVal_3434_, 0);
lean_inc_ref(v_toConstantVal_3443_);
lean_dec_ref(v_ctorVal_3434_);
v_name_3444_ = lean_ctor_get(v_toConstantVal_3443_, 0);
lean_inc(v_name_3444_);
lean_dec_ref(v_toConstantVal_3443_);
v___x_3445_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__1);
v___x_3446_ = l_Lean_MessageData_ofName(v_name_3444_);
v___x_3447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3447_, 0, v___x_3445_);
lean_ctor_set(v___x_3447_, 1, v___x_3446_);
v___x_3448_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_3449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3449_, 0, v___x_3447_);
lean_ctor_set(v___x_3449_, 1, v___x_3448_);
v___x_3450_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_3449_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_);
return v___x_3450_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___boxed(lean_object* v_ctorVal_3513_, lean_object* v_xs_3514_, lean_object* v_type_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_){
_start:
{
lean_object* v_res_3521_; 
v_res_3521_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0(v_ctorVal_3513_, v_xs_3514_, v_type_3515_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_);
lean_dec(v___y_3519_);
lean_dec_ref(v___y_3518_);
lean_dec(v___y_3517_);
lean_dec_ref(v___y_3516_);
lean_dec_ref(v_xs_3514_);
return v_res_3521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(lean_object* v_ctorVal_3522_, lean_object* v_targetType_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_){
_start:
{
lean_object* v___f_3529_; uint8_t v___x_3530_; lean_object* v___x_3531_; 
v___f_3529_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3529_, 0, v_ctorVal_3522_);
v___x_3530_ = 0;
v___x_3531_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_targetType_3523_, v___f_3529_, v___x_3530_, v___x_3530_, v_a_3524_, v_a_3525_, v_a_3526_, v_a_3527_);
return v___x_3531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___boxed(lean_object* v_ctorVal_3532_, lean_object* v_targetType_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_){
_start:
{
lean_object* v_res_3539_; 
v_res_3539_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3532_, v_targetType_3533_, v_a_3534_, v_a_3535_, v_a_3536_, v_a_3537_);
lean_dec(v_a_3537_);
lean_dec_ref(v_a_3536_);
lean_dec(v_a_3535_);
lean_dec_ref(v_a_3534_);
return v_res_3539_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0(lean_object* v_mvarId_3540_, lean_object* v_val_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_){
_start:
{
lean_object* v___x_3547_; 
v___x_3547_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(v_mvarId_3540_, v_val_3541_, v___y_3543_);
return v___x_3547_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___boxed(lean_object* v_mvarId_3548_, lean_object* v_val_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_){
_start:
{
lean_object* v_res_3555_; 
v_res_3555_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0(v_mvarId_3548_, v_val_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_);
lean_dec(v___y_3553_);
lean_dec_ref(v___y_3552_);
lean_dec(v___y_3551_);
lean_dec_ref(v___y_3550_);
return v_res_3555_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1(lean_object* v_inst_3556_, lean_object* v_a_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_){
_start:
{
lean_object* v___x_3563_; 
v___x_3563_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg(v_a_3557_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_);
return v___x_3563_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___boxed(lean_object* v_inst_3564_, lean_object* v_a_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_){
_start:
{
lean_object* v_res_3571_; 
v_res_3571_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1(v_inst_3564_, v_a_3565_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_);
lean_dec(v___y_3569_);
lean_dec_ref(v___y_3568_);
lean_dec(v___y_3567_);
lean_dec_ref(v___y_3566_);
return v_res_3571_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0(lean_object* v_00_u03b2_3572_, lean_object* v_x_3573_, lean_object* v_x_3574_, lean_object* v_x_3575_){
_start:
{
lean_object* v___x_3576_; 
v___x_3576_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(v_x_3573_, v_x_3574_, v_x_3575_);
return v___x_3576_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3577_, lean_object* v_x_3578_, size_t v_x_3579_, size_t v_x_3580_, lean_object* v_x_3581_, lean_object* v_x_3582_){
_start:
{
lean_object* v___x_3583_; 
v___x_3583_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_x_3578_, v_x_3579_, v_x_3580_, v_x_3581_, v_x_3582_);
return v___x_3583_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3584_, lean_object* v_x_3585_, lean_object* v_x_3586_, lean_object* v_x_3587_, lean_object* v_x_3588_, lean_object* v_x_3589_){
_start:
{
size_t v_x_5833__boxed_3590_; size_t v_x_5834__boxed_3591_; lean_object* v_res_3592_; 
v_x_5833__boxed_3590_ = lean_unbox_usize(v_x_3586_);
lean_dec(v_x_3586_);
v_x_5834__boxed_3591_ = lean_unbox_usize(v_x_3587_);
lean_dec(v_x_3587_);
v_res_3592_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1(v_00_u03b2_3584_, v_x_3585_, v_x_5833__boxed_3590_, v_x_5834__boxed_3591_, v_x_3588_, v_x_3589_);
return v_res_3592_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_3593_, lean_object* v_n_3594_, lean_object* v_k_3595_, lean_object* v_v_3596_){
_start:
{
lean_object* v___x_3597_; 
v___x_3597_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(v_n_3594_, v_k_3595_, v_v_3596_);
return v___x_3597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_3598_, size_t v_depth_3599_, lean_object* v_keys_3600_, lean_object* v_vals_3601_, lean_object* v_heq_3602_, lean_object* v_i_3603_, lean_object* v_entries_3604_){
_start:
{
lean_object* v___x_3605_; 
v___x_3605_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_3599_, v_keys_3600_, v_vals_3601_, v_i_3603_, v_entries_3604_);
return v___x_3605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_3606_, lean_object* v_depth_3607_, lean_object* v_keys_3608_, lean_object* v_vals_3609_, lean_object* v_heq_3610_, lean_object* v_i_3611_, lean_object* v_entries_3612_){
_start:
{
size_t v_depth_boxed_3613_; lean_object* v_res_3614_; 
v_depth_boxed_3613_ = lean_unbox_usize(v_depth_3607_);
lean_dec(v_depth_3607_);
v_res_3614_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_3606_, v_depth_boxed_3613_, v_keys_3608_, v_vals_3609_, v_heq_3610_, v_i_3611_, v_entries_3612_);
lean_dec_ref(v_vals_3609_);
lean_dec_ref(v_keys_3608_);
return v_res_3614_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_3615_, lean_object* v_x_3616_, lean_object* v_x_3617_, lean_object* v_x_3618_, lean_object* v_x_3619_){
_start:
{
lean_object* v___x_3620_; 
v___x_3620_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_x_3616_, v_x_3617_, v_x_3618_, v_x_3619_);
return v___x_3620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(lean_object* v_ctorVal_3621_, lean_object* v_val_3622_, lean_object* v_name_3623_, lean_object* v_levelParams_3624_, uint8_t v___x_3625_, uint8_t v_hasTrace_3626_, lean_object* v_____r_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_){
_start:
{
lean_object* v___x_3633_; 
lean_inc_ref(v_val_3622_);
v___x_3633_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3621_, v_val_3622_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_);
if (lean_obj_tag(v___x_3633_) == 0)
{
lean_object* v_a_3634_; lean_object* v___x_3635_; lean_object* v_a_3636_; lean_object* v___x_3637_; lean_object* v_a_3638_; lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3654_; 
v_a_3634_ = lean_ctor_get(v___x_3633_, 0);
lean_inc(v_a_3634_);
lean_dec_ref_known(v___x_3633_, 1);
v___x_3635_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3622_, v___y_3629_);
v_a_3636_ = lean_ctor_get(v___x_3635_, 0);
lean_inc(v_a_3636_);
lean_dec_ref(v___x_3635_);
v___x_3637_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3634_, v___y_3629_);
v_a_3638_ = lean_ctor_get(v___x_3637_, 0);
v_isSharedCheck_3654_ = !lean_is_exclusive(v___x_3637_);
if (v_isSharedCheck_3654_ == 0)
{
v___x_3640_ = v___x_3637_;
v_isShared_3641_ = v_isSharedCheck_3654_;
goto v_resetjp_3639_;
}
else
{
lean_inc(v_a_3638_);
lean_dec(v___x_3637_);
v___x_3640_ = lean_box(0);
v_isShared_3641_ = v_isSharedCheck_3654_;
goto v_resetjp_3639_;
}
v_resetjp_3639_:
{
lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3647_; 
lean_inc_n(v_name_3623_, 2);
v___x_3642_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3642_, 0, v_name_3623_);
lean_ctor_set(v___x_3642_, 1, v_levelParams_3624_);
lean_ctor_set(v___x_3642_, 2, v_a_3636_);
v___x_3643_ = lean_box(0);
v___x_3644_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3644_, 0, v_name_3623_);
lean_ctor_set(v___x_3644_, 1, v___x_3643_);
v___x_3645_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3645_, 0, v___x_3642_);
lean_ctor_set(v___x_3645_, 1, v_a_3638_);
lean_ctor_set(v___x_3645_, 2, v___x_3644_);
if (v_isShared_3641_ == 0)
{
lean_ctor_set_tag(v___x_3640_, 2);
lean_ctor_set(v___x_3640_, 0, v___x_3645_);
v___x_3647_ = v___x_3640_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3653_; 
v_reuseFailAlloc_3653_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3653_, 0, v___x_3645_);
v___x_3647_ = v_reuseFailAlloc_3653_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
lean_object* v___x_3648_; 
v___x_3648_ = l_Lean_addDecl(v___x_3647_, v___x_3625_, v___y_3630_, v___y_3631_);
if (lean_obj_tag(v___x_3648_) == 0)
{
lean_object* v___x_3649_; uint8_t v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; 
lean_dec_ref_known(v___x_3648_, 1);
v___x_3649_ = l_Lean_Meta_simpExtension;
v___x_3650_ = 0;
v___x_3651_ = lean_unsigned_to_nat(1000u);
v___x_3652_ = l_Lean_Meta_addSimpTheorem(v___x_3649_, v_name_3623_, v_hasTrace_3626_, v___x_3625_, v___x_3650_, v___x_3651_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_);
return v___x_3652_;
}
else
{
lean_dec(v_name_3623_);
return v___x_3648_;
}
}
}
}
else
{
lean_object* v_a_3655_; lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3662_; 
lean_dec(v_levelParams_3624_);
lean_dec(v_name_3623_);
lean_dec_ref(v_val_3622_);
v_a_3655_ = lean_ctor_get(v___x_3633_, 0);
v_isSharedCheck_3662_ = !lean_is_exclusive(v___x_3633_);
if (v_isSharedCheck_3662_ == 0)
{
v___x_3657_ = v___x_3633_;
v_isShared_3658_ = v_isSharedCheck_3662_;
goto v_resetjp_3656_;
}
else
{
lean_inc(v_a_3655_);
lean_dec(v___x_3633_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1___boxed(lean_object* v_ctorVal_3663_, lean_object* v_val_3664_, lean_object* v_name_3665_, lean_object* v_levelParams_3666_, lean_object* v___x_3667_, lean_object* v_hasTrace_3668_, lean_object* v_____r_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_){
_start:
{
uint8_t v___x_8728__boxed_3675_; uint8_t v_hasTrace_boxed_3676_; lean_object* v_res_3677_; 
v___x_8728__boxed_3675_ = lean_unbox(v___x_3667_);
v_hasTrace_boxed_3676_ = lean_unbox(v_hasTrace_3668_);
v_res_3677_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(v_ctorVal_3663_, v_val_3664_, v_name_3665_, v_levelParams_3666_, v___x_8728__boxed_3675_, v_hasTrace_boxed_3676_, v_____r_3669_, v___y_3670_, v___y_3671_, v___y_3672_, v___y_3673_);
lean_dec(v___y_3673_);
lean_dec_ref(v___y_3672_);
lean_dec(v___y_3671_);
lean_dec_ref(v___y_3670_);
return v_res_3677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(lean_object* v_ctorVal_3678_, lean_object* v_val_3679_, lean_object* v_name_3680_, lean_object* v_levelParams_3681_, uint8_t v___x_3682_, lean_object* v_____r_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_){
_start:
{
lean_object* v___x_3689_; 
lean_inc_ref(v_val_3679_);
v___x_3689_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3678_, v_val_3679_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_);
if (lean_obj_tag(v___x_3689_) == 0)
{
lean_object* v_a_3690_; lean_object* v___x_3691_; lean_object* v_a_3692_; lean_object* v___x_3693_; lean_object* v_a_3694_; lean_object* v___x_3696_; uint8_t v_isShared_3697_; uint8_t v_isSharedCheck_3711_; 
v_a_3690_ = lean_ctor_get(v___x_3689_, 0);
lean_inc(v_a_3690_);
lean_dec_ref_known(v___x_3689_, 1);
v___x_3691_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3679_, v___y_3685_);
v_a_3692_ = lean_ctor_get(v___x_3691_, 0);
lean_inc(v_a_3692_);
lean_dec_ref(v___x_3691_);
v___x_3693_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3690_, v___y_3685_);
v_a_3694_ = lean_ctor_get(v___x_3693_, 0);
v_isSharedCheck_3711_ = !lean_is_exclusive(v___x_3693_);
if (v_isSharedCheck_3711_ == 0)
{
v___x_3696_ = v___x_3693_;
v_isShared_3697_ = v_isSharedCheck_3711_;
goto v_resetjp_3695_;
}
else
{
lean_inc(v_a_3694_);
lean_dec(v___x_3693_);
v___x_3696_ = lean_box(0);
v_isShared_3697_ = v_isSharedCheck_3711_;
goto v_resetjp_3695_;
}
v_resetjp_3695_:
{
lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3703_; 
lean_inc_n(v_name_3680_, 2);
v___x_3698_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3698_, 0, v_name_3680_);
lean_ctor_set(v___x_3698_, 1, v_levelParams_3681_);
lean_ctor_set(v___x_3698_, 2, v_a_3692_);
v___x_3699_ = lean_box(0);
v___x_3700_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3700_, 0, v_name_3680_);
lean_ctor_set(v___x_3700_, 1, v___x_3699_);
v___x_3701_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3701_, 0, v___x_3698_);
lean_ctor_set(v___x_3701_, 1, v_a_3694_);
lean_ctor_set(v___x_3701_, 2, v___x_3700_);
if (v_isShared_3697_ == 0)
{
lean_ctor_set_tag(v___x_3696_, 2);
lean_ctor_set(v___x_3696_, 0, v___x_3701_);
v___x_3703_ = v___x_3696_;
goto v_reusejp_3702_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v___x_3701_);
v___x_3703_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3702_;
}
v_reusejp_3702_:
{
uint8_t v___x_3704_; lean_object* v___x_3705_; 
v___x_3704_ = 0;
v___x_3705_ = l_Lean_addDecl(v___x_3703_, v___x_3704_, v___y_3686_, v___y_3687_);
if (lean_obj_tag(v___x_3705_) == 0)
{
lean_object* v___x_3706_; uint8_t v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; 
lean_dec_ref_known(v___x_3705_, 1);
v___x_3706_ = l_Lean_Meta_simpExtension;
v___x_3707_ = 0;
v___x_3708_ = lean_unsigned_to_nat(1000u);
v___x_3709_ = l_Lean_Meta_addSimpTheorem(v___x_3706_, v_name_3680_, v___x_3682_, v___x_3704_, v___x_3707_, v___x_3708_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_);
return v___x_3709_;
}
else
{
lean_dec(v_name_3680_);
return v___x_3705_;
}
}
}
}
else
{
lean_object* v_a_3712_; lean_object* v___x_3714_; uint8_t v_isShared_3715_; uint8_t v_isSharedCheck_3719_; 
lean_dec(v_levelParams_3681_);
lean_dec(v_name_3680_);
lean_dec_ref(v_val_3679_);
v_a_3712_ = lean_ctor_get(v___x_3689_, 0);
v_isSharedCheck_3719_ = !lean_is_exclusive(v___x_3689_);
if (v_isSharedCheck_3719_ == 0)
{
v___x_3714_ = v___x_3689_;
v_isShared_3715_ = v_isSharedCheck_3719_;
goto v_resetjp_3713_;
}
else
{
lean_inc(v_a_3712_);
lean_dec(v___x_3689_);
v___x_3714_ = lean_box(0);
v_isShared_3715_ = v_isSharedCheck_3719_;
goto v_resetjp_3713_;
}
v_resetjp_3713_:
{
lean_object* v___x_3717_; 
if (v_isShared_3715_ == 0)
{
v___x_3717_ = v___x_3714_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3718_; 
v_reuseFailAlloc_3718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3718_, 0, v_a_3712_);
v___x_3717_ = v_reuseFailAlloc_3718_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
return v___x_3717_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0___boxed(lean_object* v_ctorVal_3720_, lean_object* v_val_3721_, lean_object* v_name_3722_, lean_object* v_levelParams_3723_, lean_object* v___x_3724_, lean_object* v_____r_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_){
_start:
{
uint8_t v___x_8816__boxed_3731_; lean_object* v_res_3732_; 
v___x_8816__boxed_3731_ = lean_unbox(v___x_3724_);
v_res_3732_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(v_ctorVal_3720_, v_val_3721_, v_name_3722_, v_levelParams_3723_, v___x_8816__boxed_3731_, v_____r_3725_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_);
lean_dec(v___y_3729_);
lean_dec_ref(v___y_3728_);
lean_dec(v___y_3727_);
lean_dec_ref(v___y_3726_);
return v_res_3732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(lean_object* v_ctorVal_3733_, lean_object* v_a_3734_, lean_object* v_a_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_){
_start:
{
lean_object* v_toConstantVal_3739_; lean_object* v_toCold_3740_; lean_object* v_options_3741_; lean_object* v_name_3742_; lean_object* v_levelParams_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3963_; 
v_toConstantVal_3739_ = lean_ctor_get(v_ctorVal_3733_, 0);
lean_inc_ref(v_toConstantVal_3739_);
v_toCold_3740_ = lean_ctor_get(v_a_3736_, 0);
v_options_3741_ = lean_ctor_get(v_toCold_3740_, 2);
v_name_3742_ = lean_ctor_get(v_toConstantVal_3739_, 0);
v_levelParams_3743_ = lean_ctor_get(v_toConstantVal_3739_, 1);
v_isSharedCheck_3963_ = !lean_is_exclusive(v_toConstantVal_3739_);
if (v_isSharedCheck_3963_ == 0)
{
lean_object* v_unused_3964_; 
v_unused_3964_ = lean_ctor_get(v_toConstantVal_3739_, 2);
lean_dec(v_unused_3964_);
v___x_3745_ = v_toConstantVal_3739_;
v_isShared_3746_ = v_isSharedCheck_3963_;
goto v_resetjp_3744_;
}
else
{
lean_inc(v_levelParams_3743_);
lean_inc(v_name_3742_);
lean_dec(v_toConstantVal_3739_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3963_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
lean_object* v_inheritedTraceOptions_3747_; uint8_t v_hasTrace_3748_; lean_object* v_name_3749_; 
v_inheritedTraceOptions_3747_ = lean_ctor_get(v_toCold_3740_, 11);
v_hasTrace_3748_ = lean_ctor_get_uint8(v_options_3741_, sizeof(void*)*1);
v_name_3749_ = l_Lean_Meta_mkInjectiveEqTheoremNameFor(v_name_3742_);
if (v_hasTrace_3748_ == 0)
{
lean_object* v___x_3750_; 
lean_inc_ref(v_ctorVal_3733_);
v___x_3750_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3733_, v_a_3734_, v_a_3735_, v_a_3736_, v_a_3737_);
if (lean_obj_tag(v___x_3750_) == 0)
{
lean_object* v_a_3751_; lean_object* v___x_3753_; uint8_t v_isShared_3754_; uint8_t v_isSharedCheck_3793_; 
v_a_3751_ = lean_ctor_get(v___x_3750_, 0);
v_isSharedCheck_3793_ = !lean_is_exclusive(v___x_3750_);
if (v_isSharedCheck_3793_ == 0)
{
v___x_3753_ = v___x_3750_;
v_isShared_3754_ = v_isSharedCheck_3793_;
goto v_resetjp_3752_;
}
else
{
lean_inc(v_a_3751_);
lean_dec(v___x_3750_);
v___x_3753_ = lean_box(0);
v_isShared_3754_ = v_isSharedCheck_3793_;
goto v_resetjp_3752_;
}
v_resetjp_3752_:
{
if (lean_obj_tag(v_a_3751_) == 1)
{
lean_object* v_val_3755_; lean_object* v___x_3756_; 
lean_del_object(v___x_3753_);
v_val_3755_ = lean_ctor_get(v_a_3751_, 0);
lean_inc_n(v_val_3755_, 2);
lean_dec_ref_known(v_a_3751_, 1);
v___x_3756_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3733_, v_val_3755_, v_a_3734_, v_a_3735_, v_a_3736_, v_a_3737_);
if (lean_obj_tag(v___x_3756_) == 0)
{
lean_object* v_a_3757_; lean_object* v___x_3758_; lean_object* v_a_3759_; lean_object* v___x_3760_; lean_object* v_a_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3780_; 
v_a_3757_ = lean_ctor_get(v___x_3756_, 0);
lean_inc(v_a_3757_);
lean_dec_ref_known(v___x_3756_, 1);
v___x_3758_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3755_, v_a_3735_);
v_a_3759_ = lean_ctor_get(v___x_3758_, 0);
lean_inc(v_a_3759_);
lean_dec_ref(v___x_3758_);
v___x_3760_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3757_, v_a_3735_);
v_a_3761_ = lean_ctor_get(v___x_3760_, 0);
v_isSharedCheck_3780_ = !lean_is_exclusive(v___x_3760_);
if (v_isSharedCheck_3780_ == 0)
{
v___x_3763_ = v___x_3760_;
v_isShared_3764_ = v_isSharedCheck_3780_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_a_3761_);
lean_dec(v___x_3760_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3780_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v___x_3766_; 
lean_inc(v_name_3749_);
if (v_isShared_3746_ == 0)
{
lean_ctor_set(v___x_3745_, 2, v_a_3759_);
lean_ctor_set(v___x_3745_, 0, v_name_3749_);
v___x_3766_ = v___x_3745_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3779_; 
v_reuseFailAlloc_3779_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3779_, 0, v_name_3749_);
lean_ctor_set(v_reuseFailAlloc_3779_, 1, v_levelParams_3743_);
lean_ctor_set(v_reuseFailAlloc_3779_, 2, v_a_3759_);
v___x_3766_ = v_reuseFailAlloc_3779_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3771_; 
v___x_3767_ = lean_box(0);
lean_inc(v_name_3749_);
v___x_3768_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3768_, 0, v_name_3749_);
lean_ctor_set(v___x_3768_, 1, v___x_3767_);
v___x_3769_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3769_, 0, v___x_3766_);
lean_ctor_set(v___x_3769_, 1, v_a_3761_);
lean_ctor_set(v___x_3769_, 2, v___x_3768_);
if (v_isShared_3764_ == 0)
{
lean_ctor_set_tag(v___x_3763_, 2);
lean_ctor_set(v___x_3763_, 0, v___x_3769_);
v___x_3771_ = v___x_3763_;
goto v_reusejp_3770_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v___x_3769_);
v___x_3771_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3770_;
}
v_reusejp_3770_:
{
lean_object* v___x_3772_; 
v___x_3772_ = l_Lean_addDecl(v___x_3771_, v_hasTrace_3748_, v_a_3736_, v_a_3737_);
if (lean_obj_tag(v___x_3772_) == 0)
{
lean_object* v___x_3773_; uint8_t v___x_3774_; uint8_t v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; 
lean_dec_ref_known(v___x_3772_, 1);
v___x_3773_ = l_Lean_Meta_simpExtension;
v___x_3774_ = 1;
v___x_3775_ = 0;
v___x_3776_ = lean_unsigned_to_nat(1000u);
v___x_3777_ = l_Lean_Meta_addSimpTheorem(v___x_3773_, v_name_3749_, v___x_3774_, v_hasTrace_3748_, v___x_3775_, v___x_3776_, v_a_3734_, v_a_3735_, v_a_3736_, v_a_3737_);
return v___x_3777_;
}
else
{
lean_dec(v_name_3749_);
return v___x_3772_;
}
}
}
}
}
else
{
lean_object* v_a_3781_; lean_object* v___x_3783_; uint8_t v_isShared_3784_; uint8_t v_isSharedCheck_3788_; 
lean_dec(v_val_3755_);
lean_dec(v_name_3749_);
lean_del_object(v___x_3745_);
lean_dec(v_levelParams_3743_);
v_a_3781_ = lean_ctor_get(v___x_3756_, 0);
v_isSharedCheck_3788_ = !lean_is_exclusive(v___x_3756_);
if (v_isSharedCheck_3788_ == 0)
{
v___x_3783_ = v___x_3756_;
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
else
{
lean_inc(v_a_3781_);
lean_dec(v___x_3756_);
v___x_3783_ = lean_box(0);
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
v_resetjp_3782_:
{
lean_object* v___x_3786_; 
if (v_isShared_3784_ == 0)
{
v___x_3786_ = v___x_3783_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3787_; 
v_reuseFailAlloc_3787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3787_, 0, v_a_3781_);
v___x_3786_ = v_reuseFailAlloc_3787_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
return v___x_3786_;
}
}
}
}
else
{
lean_object* v___x_3789_; lean_object* v___x_3791_; 
lean_dec(v_a_3751_);
lean_dec(v_name_3749_);
lean_del_object(v___x_3745_);
lean_dec(v_levelParams_3743_);
lean_dec_ref(v_ctorVal_3733_);
v___x_3789_ = lean_box(0);
if (v_isShared_3754_ == 0)
{
lean_ctor_set(v___x_3753_, 0, v___x_3789_);
v___x_3791_ = v___x_3753_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v___x_3789_);
v___x_3791_ = v_reuseFailAlloc_3792_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
return v___x_3791_;
}
}
}
}
else
{
lean_object* v_a_3794_; lean_object* v___x_3796_; uint8_t v_isShared_3797_; uint8_t v_isSharedCheck_3801_; 
lean_dec(v_name_3749_);
lean_del_object(v___x_3745_);
lean_dec(v_levelParams_3743_);
lean_dec_ref(v_ctorVal_3733_);
v_a_3794_ = lean_ctor_get(v___x_3750_, 0);
v_isSharedCheck_3801_ = !lean_is_exclusive(v___x_3750_);
if (v_isSharedCheck_3801_ == 0)
{
v___x_3796_ = v___x_3750_;
v_isShared_3797_ = v_isSharedCheck_3801_;
goto v_resetjp_3795_;
}
else
{
lean_inc(v_a_3794_);
lean_dec(v___x_3750_);
v___x_3796_ = lean_box(0);
v_isShared_3797_ = v_isSharedCheck_3801_;
goto v_resetjp_3795_;
}
v_resetjp_3795_:
{
lean_object* v___x_3799_; 
if (v_isShared_3797_ == 0)
{
v___x_3799_ = v___x_3796_;
goto v_reusejp_3798_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v_a_3794_);
v___x_3799_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3798_;
}
v_reusejp_3798_:
{
return v___x_3799_;
}
}
}
}
else
{
lean_object* v___f_3802_; lean_object* v_cls_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; uint8_t v___x_3806_; lean_object* v___y_3808_; lean_object* v___y_3809_; lean_object* v_a_3810_; lean_object* v___y_3820_; lean_object* v___y_3821_; lean_object* v_a_3822_; lean_object* v___y_3825_; lean_object* v___y_3826_; lean_object* v_a_3827_; lean_object* v___y_3830_; lean_object* v___y_3831_; lean_object* v___y_3832_; lean_object* v___y_3836_; lean_object* v___y_3837_; lean_object* v_a_3838_; lean_object* v___y_3851_; lean_object* v___y_3852_; lean_object* v_a_3853_; lean_object* v___y_3856_; lean_object* v___y_3857_; lean_object* v_a_3858_; lean_object* v___y_3861_; lean_object* v___y_3862_; lean_object* v___y_3863_; 
lean_inc(v_name_3749_);
v___f_3802_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3802_, 0, v_name_3749_);
v_cls_3803_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_3804_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_3805_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_3806_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3747_, v_options_3741_, v___x_3805_);
if (v___x_3806_ == 0)
{
lean_object* v___x_3901_; uint8_t v___x_3902_; 
v___x_3901_ = l_Lean_trace_profiler;
v___x_3902_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_3741_, v___x_3901_);
if (v___x_3902_ == 0)
{
lean_object* v___x_3903_; 
lean_dec_ref(v___f_3802_);
lean_inc_ref(v_ctorVal_3733_);
v___x_3903_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3733_, v_a_3734_, v_a_3735_, v_a_3736_, v_a_3737_);
if (lean_obj_tag(v___x_3903_) == 0)
{
lean_object* v_a_3904_; lean_object* v___x_3906_; uint8_t v_isShared_3907_; uint8_t v_isSharedCheck_3954_; 
v_a_3904_ = lean_ctor_get(v___x_3903_, 0);
v_isSharedCheck_3954_ = !lean_is_exclusive(v___x_3903_);
if (v_isSharedCheck_3954_ == 0)
{
v___x_3906_ = v___x_3903_;
v_isShared_3907_ = v_isSharedCheck_3954_;
goto v_resetjp_3905_;
}
else
{
lean_inc(v_a_3904_);
lean_dec(v___x_3903_);
v___x_3906_ = lean_box(0);
v_isShared_3907_ = v_isSharedCheck_3954_;
goto v_resetjp_3905_;
}
v_resetjp_3905_:
{
if (lean_obj_tag(v_a_3904_) == 1)
{
lean_object* v_val_3908_; lean_object* v___y_3910_; lean_object* v___y_3911_; lean_object* v___y_3912_; lean_object* v___y_3913_; 
lean_del_object(v___x_3906_);
v_val_3908_ = lean_ctor_get(v_a_3904_, 0);
lean_inc(v_val_3908_);
lean_dec_ref_known(v_a_3904_, 1);
if (v___x_3806_ == 0)
{
v___y_3910_ = v_a_3734_;
v___y_3911_ = v_a_3735_;
v___y_3912_ = v_a_3736_;
v___y_3913_ = v_a_3737_;
goto v___jp_3909_;
}
else
{
lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; 
v___x_3946_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
lean_inc(v_val_3908_);
v___x_3947_ = l_Lean_MessageData_ofExpr(v_val_3908_);
v___x_3948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3948_, 0, v___x_3946_);
lean_ctor_set(v___x_3948_, 1, v___x_3947_);
v___x_3949_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_3803_, v___x_3948_, v_a_3734_, v_a_3735_, v_a_3736_, v_a_3737_);
if (lean_obj_tag(v___x_3949_) == 0)
{
lean_dec_ref_known(v___x_3949_, 1);
v___y_3910_ = v_a_3734_;
v___y_3911_ = v_a_3735_;
v___y_3912_ = v_a_3736_;
v___y_3913_ = v_a_3737_;
goto v___jp_3909_;
}
else
{
lean_dec(v_val_3908_);
lean_dec(v_name_3749_);
lean_del_object(v___x_3745_);
lean_dec(v_levelParams_3743_);
lean_dec_ref(v_ctorVal_3733_);
return v___x_3949_;
}
}
v___jp_3909_:
{
lean_object* v___x_3914_; 
lean_inc(v_val_3908_);
v___x_3914_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3733_, v_val_3908_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_);
if (lean_obj_tag(v___x_3914_) == 0)
{
lean_object* v_a_3915_; lean_object* v___x_3916_; lean_object* v_a_3917_; lean_object* v___x_3918_; lean_object* v_a_3919_; lean_object* v___x_3921_; uint8_t v_isShared_3922_; uint8_t v_isSharedCheck_3937_; 
v_a_3915_ = lean_ctor_get(v___x_3914_, 0);
lean_inc(v_a_3915_);
lean_dec_ref_known(v___x_3914_, 1);
v___x_3916_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3908_, v___y_3911_);
v_a_3917_ = lean_ctor_get(v___x_3916_, 0);
lean_inc(v_a_3917_);
lean_dec_ref(v___x_3916_);
v___x_3918_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3915_, v___y_3911_);
v_a_3919_ = lean_ctor_get(v___x_3918_, 0);
v_isSharedCheck_3937_ = !lean_is_exclusive(v___x_3918_);
if (v_isSharedCheck_3937_ == 0)
{
v___x_3921_ = v___x_3918_;
v_isShared_3922_ = v_isSharedCheck_3937_;
goto v_resetjp_3920_;
}
else
{
lean_inc(v_a_3919_);
lean_dec(v___x_3918_);
v___x_3921_ = lean_box(0);
v_isShared_3922_ = v_isSharedCheck_3937_;
goto v_resetjp_3920_;
}
v_resetjp_3920_:
{
lean_object* v___x_3924_; 
lean_inc(v_name_3749_);
if (v_isShared_3746_ == 0)
{
lean_ctor_set(v___x_3745_, 2, v_a_3917_);
lean_ctor_set(v___x_3745_, 0, v_name_3749_);
v___x_3924_ = v___x_3745_;
goto v_reusejp_3923_;
}
else
{
lean_object* v_reuseFailAlloc_3936_; 
v_reuseFailAlloc_3936_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3936_, 0, v_name_3749_);
lean_ctor_set(v_reuseFailAlloc_3936_, 1, v_levelParams_3743_);
lean_ctor_set(v_reuseFailAlloc_3936_, 2, v_a_3917_);
v___x_3924_ = v_reuseFailAlloc_3936_;
goto v_reusejp_3923_;
}
v_reusejp_3923_:
{
lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3929_; 
v___x_3925_ = lean_box(0);
lean_inc(v_name_3749_);
v___x_3926_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3926_, 0, v_name_3749_);
lean_ctor_set(v___x_3926_, 1, v___x_3925_);
v___x_3927_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3927_, 0, v___x_3924_);
lean_ctor_set(v___x_3927_, 1, v_a_3919_);
lean_ctor_set(v___x_3927_, 2, v___x_3926_);
if (v_isShared_3922_ == 0)
{
lean_ctor_set_tag(v___x_3921_, 2);
lean_ctor_set(v___x_3921_, 0, v___x_3927_);
v___x_3929_ = v___x_3921_;
goto v_reusejp_3928_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v___x_3927_);
v___x_3929_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3928_;
}
v_reusejp_3928_:
{
lean_object* v___x_3930_; 
v___x_3930_ = l_Lean_addDecl(v___x_3929_, v___x_3902_, v___y_3912_, v___y_3913_);
if (lean_obj_tag(v___x_3930_) == 0)
{
lean_object* v___x_3931_; uint8_t v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; 
lean_dec_ref_known(v___x_3930_, 1);
v___x_3931_ = l_Lean_Meta_simpExtension;
v___x_3932_ = 0;
v___x_3933_ = lean_unsigned_to_nat(1000u);
v___x_3934_ = l_Lean_Meta_addSimpTheorem(v___x_3931_, v_name_3749_, v_hasTrace_3748_, v___x_3902_, v___x_3932_, v___x_3933_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_);
return v___x_3934_;
}
else
{
lean_dec(v_name_3749_);
return v___x_3930_;
}
}
}
}
}
else
{
lean_object* v_a_3938_; lean_object* v___x_3940_; uint8_t v_isShared_3941_; uint8_t v_isSharedCheck_3945_; 
lean_dec(v_val_3908_);
lean_dec(v_name_3749_);
lean_del_object(v___x_3745_);
lean_dec(v_levelParams_3743_);
v_a_3938_ = lean_ctor_get(v___x_3914_, 0);
v_isSharedCheck_3945_ = !lean_is_exclusive(v___x_3914_);
if (v_isSharedCheck_3945_ == 0)
{
v___x_3940_ = v___x_3914_;
v_isShared_3941_ = v_isSharedCheck_3945_;
goto v_resetjp_3939_;
}
else
{
lean_inc(v_a_3938_);
lean_dec(v___x_3914_);
v___x_3940_ = lean_box(0);
v_isShared_3941_ = v_isSharedCheck_3945_;
goto v_resetjp_3939_;
}
v_resetjp_3939_:
{
lean_object* v___x_3943_; 
if (v_isShared_3941_ == 0)
{
v___x_3943_ = v___x_3940_;
goto v_reusejp_3942_;
}
else
{
lean_object* v_reuseFailAlloc_3944_; 
v_reuseFailAlloc_3944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3944_, 0, v_a_3938_);
v___x_3943_ = v_reuseFailAlloc_3944_;
goto v_reusejp_3942_;
}
v_reusejp_3942_:
{
return v___x_3943_;
}
}
}
}
}
else
{
lean_object* v___x_3950_; lean_object* v___x_3952_; 
lean_dec(v_a_3904_);
lean_dec(v_name_3749_);
lean_del_object(v___x_3745_);
lean_dec(v_levelParams_3743_);
lean_dec_ref(v_ctorVal_3733_);
v___x_3950_ = lean_box(0);
if (v_isShared_3907_ == 0)
{
lean_ctor_set(v___x_3906_, 0, v___x_3950_);
v___x_3952_ = v___x_3906_;
goto v_reusejp_3951_;
}
else
{
lean_object* v_reuseFailAlloc_3953_; 
v_reuseFailAlloc_3953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3953_, 0, v___x_3950_);
v___x_3952_ = v_reuseFailAlloc_3953_;
goto v_reusejp_3951_;
}
v_reusejp_3951_:
{
return v___x_3952_;
}
}
}
}
else
{
lean_object* v_a_3955_; lean_object* v___x_3957_; uint8_t v_isShared_3958_; uint8_t v_isSharedCheck_3962_; 
lean_dec(v_name_3749_);
lean_del_object(v___x_3745_);
lean_dec(v_levelParams_3743_);
lean_dec_ref(v_ctorVal_3733_);
v_a_3955_ = lean_ctor_get(v___x_3903_, 0);
v_isSharedCheck_3962_ = !lean_is_exclusive(v___x_3903_);
if (v_isSharedCheck_3962_ == 0)
{
v___x_3957_ = v___x_3903_;
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
else
{
lean_inc(v_a_3955_);
lean_dec(v___x_3903_);
v___x_3957_ = lean_box(0);
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
v_resetjp_3956_:
{
lean_object* v___x_3960_; 
if (v_isShared_3958_ == 0)
{
v___x_3960_ = v___x_3957_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v_a_3955_);
v___x_3960_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
return v___x_3960_;
}
}
}
}
else
{
lean_del_object(v___x_3745_);
goto v___jp_3866_;
}
}
else
{
lean_del_object(v___x_3745_);
goto v___jp_3866_;
}
v___jp_3807_:
{
lean_object* v___x_3811_; double v___x_3812_; double v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; 
v___x_3811_ = lean_io_get_num_heartbeats();
v___x_3812_ = lean_float_of_nat(v___y_3809_);
v___x_3813_ = lean_float_of_nat(v___x_3811_);
v___x_3814_ = lean_box_float(v___x_3812_);
v___x_3815_ = lean_box_float(v___x_3813_);
v___x_3816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3816_, 0, v___x_3814_);
lean_ctor_set(v___x_3816_, 1, v___x_3815_);
v___x_3817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3817_, 0, v_a_3810_);
lean_ctor_set(v___x_3817_, 1, v___x_3816_);
v___x_3818_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_3803_, v_hasTrace_3748_, v___x_3804_, v_options_3741_, v___x_3806_, v___y_3808_, v___f_3802_, v___x_3817_, v_a_3734_, v_a_3735_, v_a_3736_, v_a_3737_);
return v___x_3818_;
}
v___jp_3819_:
{
lean_object* v___x_3823_; 
v___x_3823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3823_, 0, v_a_3822_);
v___y_3808_ = v___y_3820_;
v___y_3809_ = v___y_3821_;
v_a_3810_ = v___x_3823_;
goto v___jp_3807_;
}
v___jp_3824_:
{
lean_object* v___x_3828_; 
v___x_3828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3828_, 0, v_a_3827_);
v___y_3808_ = v___y_3825_;
v___y_3809_ = v___y_3826_;
v_a_3810_ = v___x_3828_;
goto v___jp_3807_;
}
v___jp_3829_:
{
if (lean_obj_tag(v___y_3832_) == 0)
{
lean_object* v_a_3833_; 
v_a_3833_ = lean_ctor_get(v___y_3832_, 0);
lean_inc(v_a_3833_);
lean_dec_ref_known(v___y_3832_, 1);
v___y_3825_ = v___y_3830_;
v___y_3826_ = v___y_3831_;
v_a_3827_ = v_a_3833_;
goto v___jp_3824_;
}
else
{
lean_object* v_a_3834_; 
v_a_3834_ = lean_ctor_get(v___y_3832_, 0);
lean_inc(v_a_3834_);
lean_dec_ref_known(v___y_3832_, 1);
v___y_3820_ = v___y_3830_;
v___y_3821_ = v___y_3831_;
v_a_3822_ = v_a_3834_;
goto v___jp_3819_;
}
}
v___jp_3835_:
{
lean_object* v___x_3839_; double v___x_3840_; double v___x_3841_; double v___x_3842_; double v___x_3843_; double v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; 
v___x_3839_ = lean_io_mono_nanos_now();
v___x_3840_ = lean_float_of_nat(v___y_3837_);
v___x_3841_ = lean_float_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0);
v___x_3842_ = lean_float_div(v___x_3840_, v___x_3841_);
v___x_3843_ = lean_float_of_nat(v___x_3839_);
v___x_3844_ = lean_float_div(v___x_3843_, v___x_3841_);
v___x_3845_ = lean_box_float(v___x_3842_);
v___x_3846_ = lean_box_float(v___x_3844_);
v___x_3847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3847_, 0, v___x_3845_);
lean_ctor_set(v___x_3847_, 1, v___x_3846_);
v___x_3848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3848_, 0, v_a_3838_);
lean_ctor_set(v___x_3848_, 1, v___x_3847_);
v___x_3849_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_3803_, v_hasTrace_3748_, v___x_3804_, v_options_3741_, v___x_3806_, v___y_3836_, v___f_3802_, v___x_3848_, v_a_3734_, v_a_3735_, v_a_3736_, v_a_3737_);
return v___x_3849_;
}
v___jp_3850_:
{
lean_object* v___x_3854_; 
v___x_3854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3854_, 0, v_a_3853_);
v___y_3836_ = v___y_3851_;
v___y_3837_ = v___y_3852_;
v_a_3838_ = v___x_3854_;
goto v___jp_3835_;
}
v___jp_3855_:
{
lean_object* v___x_3859_; 
v___x_3859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3859_, 0, v_a_3858_);
v___y_3836_ = v___y_3856_;
v___y_3837_ = v___y_3857_;
v_a_3838_ = v___x_3859_;
goto v___jp_3835_;
}
v___jp_3860_:
{
if (lean_obj_tag(v___y_3863_) == 0)
{
lean_object* v_a_3864_; 
v_a_3864_ = lean_ctor_get(v___y_3863_, 0);
lean_inc(v_a_3864_);
lean_dec_ref_known(v___y_3863_, 1);
v___y_3851_ = v___y_3861_;
v___y_3852_ = v___y_3862_;
v_a_3853_ = v_a_3864_;
goto v___jp_3850_;
}
else
{
lean_object* v_a_3865_; 
v_a_3865_ = lean_ctor_get(v___y_3863_, 0);
lean_inc(v_a_3865_);
lean_dec_ref_known(v___y_3863_, 1);
v___y_3856_ = v___y_3861_;
v___y_3857_ = v___y_3862_;
v_a_3858_ = v_a_3865_;
goto v___jp_3855_;
}
}
v___jp_3866_:
{
lean_object* v___x_3867_; lean_object* v_a_3868_; lean_object* v___x_3869_; uint8_t v___x_3870_; 
v___x_3867_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v_a_3737_);
v_a_3868_ = lean_ctor_get(v___x_3867_, 0);
lean_inc(v_a_3868_);
lean_dec_ref(v___x_3867_);
v___x_3869_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3870_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_3741_, v___x_3869_);
if (v___x_3870_ == 0)
{
lean_object* v___x_3871_; lean_object* v___x_3872_; 
v___x_3871_ = lean_io_mono_nanos_now();
lean_inc_ref(v_ctorVal_3733_);
v___x_3872_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3733_, v_a_3734_, v_a_3735_, v_a_3736_, v_a_3737_);
if (lean_obj_tag(v___x_3872_) == 0)
{
lean_object* v_a_3873_; 
v_a_3873_ = lean_ctor_get(v___x_3872_, 0);
lean_inc(v_a_3873_);
lean_dec_ref_known(v___x_3872_, 1);
if (lean_obj_tag(v_a_3873_) == 1)
{
if (v___x_3806_ == 0)
{
lean_object* v_val_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; 
v_val_3874_ = lean_ctor_get(v_a_3873_, 0);
lean_inc(v_val_3874_);
lean_dec_ref_known(v_a_3873_, 1);
v___x_3875_ = lean_box(0);
v___x_3876_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(v_ctorVal_3733_, v_val_3874_, v_name_3749_, v_levelParams_3743_, v___x_3870_, v_hasTrace_3748_, v___x_3875_, v_a_3734_, v_a_3735_, v_a_3736_, v_a_3737_);
v___y_3861_ = v_a_3868_;
v___y_3862_ = v___x_3871_;
v___y_3863_ = v___x_3876_;
goto v___jp_3860_;
}
else
{
lean_object* v_val_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; 
v_val_3877_ = lean_ctor_get(v_a_3873_, 0);
lean_inc_n(v_val_3877_, 2);
lean_dec_ref_known(v_a_3873_, 1);
v___x_3878_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_3879_ = l_Lean_MessageData_ofExpr(v_val_3877_);
v___x_3880_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3880_, 0, v___x_3878_);
lean_ctor_set(v___x_3880_, 1, v___x_3879_);
v___x_3881_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_3803_, v___x_3880_, v_a_3734_, v_a_3735_, v_a_3736_, v_a_3737_);
if (lean_obj_tag(v___x_3881_) == 0)
{
lean_object* v_a_3882_; lean_object* v___x_3883_; 
v_a_3882_ = lean_ctor_get(v___x_3881_, 0);
lean_inc(v_a_3882_);
lean_dec_ref_known(v___x_3881_, 1);
v___x_3883_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(v_ctorVal_3733_, v_val_3877_, v_name_3749_, v_levelParams_3743_, v___x_3870_, v_hasTrace_3748_, v_a_3882_, v_a_3734_, v_a_3735_, v_a_3736_, v_a_3737_);
v___y_3861_ = v_a_3868_;
v___y_3862_ = v___x_3871_;
v___y_3863_ = v___x_3883_;
goto v___jp_3860_;
}
else
{
lean_dec(v_val_3877_);
lean_dec(v_name_3749_);
lean_dec(v_levelParams_3743_);
lean_dec_ref(v_ctorVal_3733_);
v___y_3861_ = v_a_3868_;
v___y_3862_ = v___x_3871_;
v___y_3863_ = v___x_3881_;
goto v___jp_3860_;
}
}
}
else
{
lean_object* v___x_3884_; 
lean_dec(v_a_3873_);
lean_dec(v_name_3749_);
lean_dec(v_levelParams_3743_);
lean_dec_ref(v_ctorVal_3733_);
v___x_3884_ = lean_box(0);
v___y_3851_ = v_a_3868_;
v___y_3852_ = v___x_3871_;
v_a_3853_ = v___x_3884_;
goto v___jp_3850_;
}
}
else
{
lean_object* v_a_3885_; 
lean_dec(v_name_3749_);
lean_dec(v_levelParams_3743_);
lean_dec_ref(v_ctorVal_3733_);
v_a_3885_ = lean_ctor_get(v___x_3872_, 0);
lean_inc(v_a_3885_);
lean_dec_ref_known(v___x_3872_, 1);
v___y_3856_ = v_a_3868_;
v___y_3857_ = v___x_3871_;
v_a_3858_ = v_a_3885_;
goto v___jp_3855_;
}
}
else
{
lean_object* v___x_3886_; lean_object* v___x_3887_; 
v___x_3886_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_ctorVal_3733_);
v___x_3887_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3733_, v_a_3734_, v_a_3735_, v_a_3736_, v_a_3737_);
if (lean_obj_tag(v___x_3887_) == 0)
{
lean_object* v_a_3888_; 
v_a_3888_ = lean_ctor_get(v___x_3887_, 0);
lean_inc(v_a_3888_);
lean_dec_ref_known(v___x_3887_, 1);
if (lean_obj_tag(v_a_3888_) == 1)
{
if (v___x_3806_ == 0)
{
lean_object* v_val_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; 
v_val_3889_ = lean_ctor_get(v_a_3888_, 0);
lean_inc(v_val_3889_);
lean_dec_ref_known(v_a_3888_, 1);
v___x_3890_ = lean_box(0);
v___x_3891_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(v_ctorVal_3733_, v_val_3889_, v_name_3749_, v_levelParams_3743_, v___x_3870_, v___x_3890_, v_a_3734_, v_a_3735_, v_a_3736_, v_a_3737_);
v___y_3830_ = v_a_3868_;
v___y_3831_ = v___x_3886_;
v___y_3832_ = v___x_3891_;
goto v___jp_3829_;
}
else
{
lean_object* v_val_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; 
v_val_3892_ = lean_ctor_get(v_a_3888_, 0);
lean_inc_n(v_val_3892_, 2);
lean_dec_ref_known(v_a_3888_, 1);
v___x_3893_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_3894_ = l_Lean_MessageData_ofExpr(v_val_3892_);
v___x_3895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3895_, 0, v___x_3893_);
lean_ctor_set(v___x_3895_, 1, v___x_3894_);
v___x_3896_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_3803_, v___x_3895_, v_a_3734_, v_a_3735_, v_a_3736_, v_a_3737_);
if (lean_obj_tag(v___x_3896_) == 0)
{
lean_object* v_a_3897_; lean_object* v___x_3898_; 
v_a_3897_ = lean_ctor_get(v___x_3896_, 0);
lean_inc(v_a_3897_);
lean_dec_ref_known(v___x_3896_, 1);
v___x_3898_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(v_ctorVal_3733_, v_val_3892_, v_name_3749_, v_levelParams_3743_, v___x_3870_, v_a_3897_, v_a_3734_, v_a_3735_, v_a_3736_, v_a_3737_);
v___y_3830_ = v_a_3868_;
v___y_3831_ = v___x_3886_;
v___y_3832_ = v___x_3898_;
goto v___jp_3829_;
}
else
{
lean_dec(v_val_3892_);
lean_dec(v_name_3749_);
lean_dec(v_levelParams_3743_);
lean_dec_ref(v_ctorVal_3733_);
v___y_3830_ = v_a_3868_;
v___y_3831_ = v___x_3886_;
v___y_3832_ = v___x_3896_;
goto v___jp_3829_;
}
}
}
else
{
lean_object* v___x_3899_; 
lean_dec(v_a_3888_);
lean_dec(v_name_3749_);
lean_dec(v_levelParams_3743_);
lean_dec_ref(v_ctorVal_3733_);
v___x_3899_ = lean_box(0);
v___y_3825_ = v_a_3868_;
v___y_3826_ = v___x_3886_;
v_a_3827_ = v___x_3899_;
goto v___jp_3824_;
}
}
else
{
lean_object* v_a_3900_; 
lean_dec(v_name_3749_);
lean_dec(v_levelParams_3743_);
lean_dec_ref(v_ctorVal_3733_);
v_a_3900_ = lean_ctor_get(v___x_3887_, 0);
lean_inc(v_a_3900_);
lean_dec_ref_known(v___x_3887_, 1);
v___y_3820_ = v_a_3868_;
v___y_3821_ = v___x_3886_;
v_a_3822_ = v_a_3900_;
goto v___jp_3819_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___boxed(lean_object* v_ctorVal_3965_, lean_object* v_a_3966_, lean_object* v_a_3967_, lean_object* v_a_3968_, lean_object* v_a_3969_, lean_object* v_a_3970_){
_start:
{
lean_object* v_res_3971_; 
v_res_3971_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(v_ctorVal_3965_, v_a_3966_, v_a_3967_, v_a_3968_, v_a_3969_);
lean_dec(v_a_3969_);
lean_dec_ref(v_a_3968_);
lean_dec(v_a_3967_);
lean_dec_ref(v_a_3966_);
return v_res_3971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(lean_object* v_name_3972_, lean_object* v_decl_3973_, lean_object* v_ref_3974_){
_start:
{
lean_object* v_defValue_3976_; lean_object* v_descr_3977_; lean_object* v_deprecation_x3f_3978_; lean_object* v___x_3979_; uint8_t v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; 
v_defValue_3976_ = lean_ctor_get(v_decl_3973_, 0);
v_descr_3977_ = lean_ctor_get(v_decl_3973_, 1);
v_deprecation_x3f_3978_ = lean_ctor_get(v_decl_3973_, 2);
v___x_3979_ = lean_alloc_ctor(1, 0, 1);
v___x_3980_ = lean_unbox(v_defValue_3976_);
lean_ctor_set_uint8(v___x_3979_, 0, v___x_3980_);
lean_inc(v_deprecation_x3f_3978_);
lean_inc_ref(v_descr_3977_);
lean_inc_n(v_name_3972_, 2);
v___x_3981_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3981_, 0, v_name_3972_);
lean_ctor_set(v___x_3981_, 1, v_ref_3974_);
lean_ctor_set(v___x_3981_, 2, v___x_3979_);
lean_ctor_set(v___x_3981_, 3, v_descr_3977_);
lean_ctor_set(v___x_3981_, 4, v_deprecation_x3f_3978_);
v___x_3982_ = lean_register_option(v_name_3972_, v___x_3981_);
if (lean_obj_tag(v___x_3982_) == 0)
{
lean_object* v___x_3984_; uint8_t v_isShared_3985_; uint8_t v_isSharedCheck_3990_; 
v_isSharedCheck_3990_ = !lean_is_exclusive(v___x_3982_);
if (v_isSharedCheck_3990_ == 0)
{
lean_object* v_unused_3991_; 
v_unused_3991_ = lean_ctor_get(v___x_3982_, 0);
lean_dec(v_unused_3991_);
v___x_3984_ = v___x_3982_;
v_isShared_3985_ = v_isSharedCheck_3990_;
goto v_resetjp_3983_;
}
else
{
lean_dec(v___x_3982_);
v___x_3984_ = lean_box(0);
v_isShared_3985_ = v_isSharedCheck_3990_;
goto v_resetjp_3983_;
}
v_resetjp_3983_:
{
lean_object* v___x_3986_; lean_object* v___x_3988_; 
lean_inc(v_defValue_3976_);
v___x_3986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3986_, 0, v_name_3972_);
lean_ctor_set(v___x_3986_, 1, v_defValue_3976_);
if (v_isShared_3985_ == 0)
{
lean_ctor_set(v___x_3984_, 0, v___x_3986_);
v___x_3988_ = v___x_3984_;
goto v_reusejp_3987_;
}
else
{
lean_object* v_reuseFailAlloc_3989_; 
v_reuseFailAlloc_3989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3989_, 0, v___x_3986_);
v___x_3988_ = v_reuseFailAlloc_3989_;
goto v_reusejp_3987_;
}
v_reusejp_3987_:
{
return v___x_3988_;
}
}
}
else
{
lean_object* v_a_3992_; lean_object* v___x_3994_; uint8_t v_isShared_3995_; uint8_t v_isSharedCheck_3999_; 
lean_dec(v_name_3972_);
v_a_3992_ = lean_ctor_get(v___x_3982_, 0);
v_isSharedCheck_3999_ = !lean_is_exclusive(v___x_3982_);
if (v_isSharedCheck_3999_ == 0)
{
v___x_3994_ = v___x_3982_;
v_isShared_3995_ = v_isSharedCheck_3999_;
goto v_resetjp_3993_;
}
else
{
lean_inc(v_a_3992_);
lean_dec(v___x_3982_);
v___x_3994_ = lean_box(0);
v_isShared_3995_ = v_isSharedCheck_3999_;
goto v_resetjp_3993_;
}
v_resetjp_3993_:
{
lean_object* v___x_3997_; 
if (v_isShared_3995_ == 0)
{
v___x_3997_ = v___x_3994_;
goto v_reusejp_3996_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v_a_3992_);
v___x_3997_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3996_;
}
v_reusejp_3996_:
{
return v___x_3997_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_4000_, lean_object* v_decl_4001_, lean_object* v_ref_4002_, lean_object* v_a_4003_){
_start:
{
lean_object* v_res_4004_; 
v_res_4004_ = l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(v_name_4000_, v_decl_4001_, v_ref_4002_);
lean_dec_ref(v_decl_4001_);
return v_res_4004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; 
v___x_4019_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_));
v___x_4020_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_));
v___x_4021_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_));
v___x_4022_ = l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(v___x_4019_, v___x_4020_, v___x_4021_);
return v___x_4022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4____boxed(lean_object* v_a_4023_){
_start:
{
lean_object* v_res_4024_; 
v_res_4024_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_();
return v_res_4024_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(lean_object* v___y_4025_, uint8_t v_isExporting_4026_, lean_object* v___x_4027_, lean_object* v___y_4028_, lean_object* v___x_4029_, lean_object* v_a_x3f_4030_){
_start:
{
lean_object* v___x_4032_; lean_object* v_env_4033_; lean_object* v_nextMacroScope_4034_; lean_object* v_ngen_4035_; lean_object* v_auxDeclNGen_4036_; lean_object* v_traceState_4037_; lean_object* v_recordedDeps_4038_; lean_object* v_messages_4039_; lean_object* v_infoState_4040_; lean_object* v_snapshotTasks_4041_; lean_object* v___x_4043_; uint8_t v_isShared_4044_; uint8_t v_isSharedCheck_4066_; 
v___x_4032_ = lean_st_ref_take(v___y_4025_);
v_env_4033_ = lean_ctor_get(v___x_4032_, 0);
v_nextMacroScope_4034_ = lean_ctor_get(v___x_4032_, 1);
v_ngen_4035_ = lean_ctor_get(v___x_4032_, 2);
v_auxDeclNGen_4036_ = lean_ctor_get(v___x_4032_, 3);
v_traceState_4037_ = lean_ctor_get(v___x_4032_, 4);
v_recordedDeps_4038_ = lean_ctor_get(v___x_4032_, 6);
v_messages_4039_ = lean_ctor_get(v___x_4032_, 7);
v_infoState_4040_ = lean_ctor_get(v___x_4032_, 8);
v_snapshotTasks_4041_ = lean_ctor_get(v___x_4032_, 9);
v_isSharedCheck_4066_ = !lean_is_exclusive(v___x_4032_);
if (v_isSharedCheck_4066_ == 0)
{
lean_object* v_unused_4067_; 
v_unused_4067_ = lean_ctor_get(v___x_4032_, 5);
lean_dec(v_unused_4067_);
v___x_4043_ = v___x_4032_;
v_isShared_4044_ = v_isSharedCheck_4066_;
goto v_resetjp_4042_;
}
else
{
lean_inc(v_snapshotTasks_4041_);
lean_inc(v_infoState_4040_);
lean_inc(v_messages_4039_);
lean_inc(v_recordedDeps_4038_);
lean_inc(v_traceState_4037_);
lean_inc(v_auxDeclNGen_4036_);
lean_inc(v_ngen_4035_);
lean_inc(v_nextMacroScope_4034_);
lean_inc(v_env_4033_);
lean_dec(v___x_4032_);
v___x_4043_ = lean_box(0);
v_isShared_4044_ = v_isSharedCheck_4066_;
goto v_resetjp_4042_;
}
v_resetjp_4042_:
{
lean_object* v___x_4045_; lean_object* v___x_4047_; 
v___x_4045_ = l_Lean_Environment_setExporting(v_env_4033_, v_isExporting_4026_);
if (v_isShared_4044_ == 0)
{
lean_ctor_set(v___x_4043_, 5, v___x_4027_);
lean_ctor_set(v___x_4043_, 0, v___x_4045_);
v___x_4047_ = v___x_4043_;
goto v_reusejp_4046_;
}
else
{
lean_object* v_reuseFailAlloc_4065_; 
v_reuseFailAlloc_4065_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4065_, 0, v___x_4045_);
lean_ctor_set(v_reuseFailAlloc_4065_, 1, v_nextMacroScope_4034_);
lean_ctor_set(v_reuseFailAlloc_4065_, 2, v_ngen_4035_);
lean_ctor_set(v_reuseFailAlloc_4065_, 3, v_auxDeclNGen_4036_);
lean_ctor_set(v_reuseFailAlloc_4065_, 4, v_traceState_4037_);
lean_ctor_set(v_reuseFailAlloc_4065_, 5, v___x_4027_);
lean_ctor_set(v_reuseFailAlloc_4065_, 6, v_recordedDeps_4038_);
lean_ctor_set(v_reuseFailAlloc_4065_, 7, v_messages_4039_);
lean_ctor_set(v_reuseFailAlloc_4065_, 8, v_infoState_4040_);
lean_ctor_set(v_reuseFailAlloc_4065_, 9, v_snapshotTasks_4041_);
v___x_4047_ = v_reuseFailAlloc_4065_;
goto v_reusejp_4046_;
}
v_reusejp_4046_:
{
lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v_mctx_4050_; lean_object* v_zetaDeltaFVarIds_4051_; lean_object* v_postponed_4052_; lean_object* v_diag_4053_; lean_object* v___x_4055_; uint8_t v_isShared_4056_; uint8_t v_isSharedCheck_4063_; 
v___x_4048_ = lean_st_ref_put(v___y_4025_, v___x_4047_);
v___x_4049_ = lean_st_ref_take(v___y_4028_);
v_mctx_4050_ = lean_ctor_get(v___x_4049_, 0);
v_zetaDeltaFVarIds_4051_ = lean_ctor_get(v___x_4049_, 2);
v_postponed_4052_ = lean_ctor_get(v___x_4049_, 3);
v_diag_4053_ = lean_ctor_get(v___x_4049_, 4);
v_isSharedCheck_4063_ = !lean_is_exclusive(v___x_4049_);
if (v_isSharedCheck_4063_ == 0)
{
lean_object* v_unused_4064_; 
v_unused_4064_ = lean_ctor_get(v___x_4049_, 1);
lean_dec(v_unused_4064_);
v___x_4055_ = v___x_4049_;
v_isShared_4056_ = v_isSharedCheck_4063_;
goto v_resetjp_4054_;
}
else
{
lean_inc(v_diag_4053_);
lean_inc(v_postponed_4052_);
lean_inc(v_zetaDeltaFVarIds_4051_);
lean_inc(v_mctx_4050_);
lean_dec(v___x_4049_);
v___x_4055_ = lean_box(0);
v_isShared_4056_ = v_isSharedCheck_4063_;
goto v_resetjp_4054_;
}
v_resetjp_4054_:
{
lean_object* v___x_4057_; lean_object* v___x_4059_; 
v___x_4057_ = lean_box(0);
if (v_isShared_4056_ == 0)
{
lean_ctor_set(v___x_4055_, 1, v___x_4029_);
v___x_4059_ = v___x_4055_;
goto v_reusejp_4058_;
}
else
{
lean_object* v_reuseFailAlloc_4062_; 
v_reuseFailAlloc_4062_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4062_, 0, v_mctx_4050_);
lean_ctor_set(v_reuseFailAlloc_4062_, 1, v___x_4029_);
lean_ctor_set(v_reuseFailAlloc_4062_, 2, v_zetaDeltaFVarIds_4051_);
lean_ctor_set(v_reuseFailAlloc_4062_, 3, v_postponed_4052_);
lean_ctor_set(v_reuseFailAlloc_4062_, 4, v_diag_4053_);
v___x_4059_ = v_reuseFailAlloc_4062_;
goto v_reusejp_4058_;
}
v_reusejp_4058_:
{
lean_object* v___x_4060_; lean_object* v___x_4061_; 
v___x_4060_ = lean_st_ref_put(v___y_4028_, v___x_4059_);
v___x_4061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4061_, 0, v___x_4057_);
return v___x_4061_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0___boxed(lean_object* v___y_4068_, lean_object* v_isExporting_4069_, lean_object* v___x_4070_, lean_object* v___y_4071_, lean_object* v___x_4072_, lean_object* v_a_x3f_4073_, lean_object* v___y_4074_){
_start:
{
uint8_t v_isExporting_boxed_4075_; lean_object* v_res_4076_; 
v_isExporting_boxed_4075_ = lean_unbox(v_isExporting_4069_);
v_res_4076_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(v___y_4068_, v_isExporting_boxed_4075_, v___x_4070_, v___y_4071_, v___x_4072_, v_a_x3f_4073_);
lean_dec(v_a_x3f_4073_);
lean_dec(v___y_4071_);
lean_dec(v___y_4068_);
return v_res_4076_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_4077_; 
v___x_4077_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_4077_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4078_; lean_object* v___x_4079_; 
v___x_4078_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0);
v___x_4079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4079_, 0, v___x_4078_);
return v___x_4079_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_4080_; lean_object* v___x_4081_; 
v___x_4080_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1);
v___x_4081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4081_, 0, v___x_4080_);
lean_ctor_set(v___x_4081_, 1, v___x_4080_);
return v___x_4081_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_4082_; lean_object* v___x_4083_; 
v___x_4082_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1);
v___x_4083_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4083_, 0, v___x_4082_);
lean_ctor_set(v___x_4083_, 1, v___x_4082_);
lean_ctor_set(v___x_4083_, 2, v___x_4082_);
lean_ctor_set(v___x_4083_, 3, v___x_4082_);
lean_ctor_set(v___x_4083_, 4, v___x_4082_);
lean_ctor_set(v___x_4083_, 5, v___x_4082_);
return v___x_4083_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(lean_object* v_x_4084_, uint8_t v_isExporting_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_){
_start:
{
lean_object* v___x_4091_; lean_object* v_env_4092_; lean_object* v___x_4093_; uint8_t v_isModule_4094_; 
v___x_4091_ = lean_st_ref_get(v___y_4089_);
v_env_4092_ = lean_ctor_get(v___x_4091_, 0);
lean_inc_ref(v_env_4092_);
lean_dec(v___x_4091_);
v___x_4093_ = l_Lean_Environment_header(v_env_4092_);
v_isModule_4094_ = lean_ctor_get_uint8(v___x_4093_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4093_);
if (v_isModule_4094_ == 0)
{
lean_object* v___x_4095_; 
lean_dec_ref(v_env_4092_);
lean_inc(v___y_4089_);
lean_inc_ref(v___y_4088_);
lean_inc(v___y_4087_);
lean_inc_ref(v___y_4086_);
v___x_4095_ = lean_apply_5(v_x_4084_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, lean_box(0));
return v___x_4095_;
}
else
{
uint8_t v_isExporting_4096_; 
v_isExporting_4096_ = lean_ctor_get_uint8(v_env_4092_, sizeof(void*)*8);
lean_dec_ref(v_env_4092_);
if (v_isExporting_4085_ == 0)
{
if (v_isExporting_4096_ == 0)
{
lean_object* v___x_4163_; 
lean_inc(v___y_4089_);
lean_inc_ref(v___y_4088_);
lean_inc(v___y_4087_);
lean_inc_ref(v___y_4086_);
v___x_4163_ = lean_apply_5(v_x_4084_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, lean_box(0));
return v___x_4163_;
}
else
{
goto v___jp_4097_;
}
}
else
{
if (v_isExporting_4096_ == 0)
{
goto v___jp_4097_;
}
else
{
lean_object* v___x_4164_; 
lean_inc(v___y_4089_);
lean_inc_ref(v___y_4088_);
lean_inc(v___y_4087_);
lean_inc_ref(v___y_4086_);
v___x_4164_ = lean_apply_5(v_x_4084_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, lean_box(0));
return v___x_4164_;
}
}
v___jp_4097_:
{
lean_object* v___x_4098_; lean_object* v_env_4099_; lean_object* v_nextMacroScope_4100_; lean_object* v_ngen_4101_; lean_object* v_auxDeclNGen_4102_; lean_object* v_traceState_4103_; lean_object* v_recordedDeps_4104_; lean_object* v_messages_4105_; lean_object* v_infoState_4106_; lean_object* v_snapshotTasks_4107_; lean_object* v___x_4109_; uint8_t v_isShared_4110_; uint8_t v_isSharedCheck_4161_; 
v___x_4098_ = lean_st_ref_take(v___y_4089_);
v_env_4099_ = lean_ctor_get(v___x_4098_, 0);
v_nextMacroScope_4100_ = lean_ctor_get(v___x_4098_, 1);
v_ngen_4101_ = lean_ctor_get(v___x_4098_, 2);
v_auxDeclNGen_4102_ = lean_ctor_get(v___x_4098_, 3);
v_traceState_4103_ = lean_ctor_get(v___x_4098_, 4);
v_recordedDeps_4104_ = lean_ctor_get(v___x_4098_, 6);
v_messages_4105_ = lean_ctor_get(v___x_4098_, 7);
v_infoState_4106_ = lean_ctor_get(v___x_4098_, 8);
v_snapshotTasks_4107_ = lean_ctor_get(v___x_4098_, 9);
v_isSharedCheck_4161_ = !lean_is_exclusive(v___x_4098_);
if (v_isSharedCheck_4161_ == 0)
{
lean_object* v_unused_4162_; 
v_unused_4162_ = lean_ctor_get(v___x_4098_, 5);
lean_dec(v_unused_4162_);
v___x_4109_ = v___x_4098_;
v_isShared_4110_ = v_isSharedCheck_4161_;
goto v_resetjp_4108_;
}
else
{
lean_inc(v_snapshotTasks_4107_);
lean_inc(v_infoState_4106_);
lean_inc(v_messages_4105_);
lean_inc(v_recordedDeps_4104_);
lean_inc(v_traceState_4103_);
lean_inc(v_auxDeclNGen_4102_);
lean_inc(v_ngen_4101_);
lean_inc(v_nextMacroScope_4100_);
lean_inc(v_env_4099_);
lean_dec(v___x_4098_);
v___x_4109_ = lean_box(0);
v_isShared_4110_ = v_isSharedCheck_4161_;
goto v_resetjp_4108_;
}
v_resetjp_4108_:
{
lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4114_; 
v___x_4111_ = l_Lean_Environment_setExporting(v_env_4099_, v_isExporting_4085_);
v___x_4112_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2);
if (v_isShared_4110_ == 0)
{
lean_ctor_set(v___x_4109_, 5, v___x_4112_);
lean_ctor_set(v___x_4109_, 0, v___x_4111_);
v___x_4114_ = v___x_4109_;
goto v_reusejp_4113_;
}
else
{
lean_object* v_reuseFailAlloc_4160_; 
v_reuseFailAlloc_4160_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4160_, 0, v___x_4111_);
lean_ctor_set(v_reuseFailAlloc_4160_, 1, v_nextMacroScope_4100_);
lean_ctor_set(v_reuseFailAlloc_4160_, 2, v_ngen_4101_);
lean_ctor_set(v_reuseFailAlloc_4160_, 3, v_auxDeclNGen_4102_);
lean_ctor_set(v_reuseFailAlloc_4160_, 4, v_traceState_4103_);
lean_ctor_set(v_reuseFailAlloc_4160_, 5, v___x_4112_);
lean_ctor_set(v_reuseFailAlloc_4160_, 6, v_recordedDeps_4104_);
lean_ctor_set(v_reuseFailAlloc_4160_, 7, v_messages_4105_);
lean_ctor_set(v_reuseFailAlloc_4160_, 8, v_infoState_4106_);
lean_ctor_set(v_reuseFailAlloc_4160_, 9, v_snapshotTasks_4107_);
v___x_4114_ = v_reuseFailAlloc_4160_;
goto v_reusejp_4113_;
}
v_reusejp_4113_:
{
lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v_mctx_4117_; lean_object* v_zetaDeltaFVarIds_4118_; lean_object* v_postponed_4119_; lean_object* v_diag_4120_; lean_object* v___x_4122_; uint8_t v_isShared_4123_; uint8_t v_isSharedCheck_4158_; 
v___x_4115_ = lean_st_ref_put(v___y_4089_, v___x_4114_);
v___x_4116_ = lean_st_ref_take(v___y_4087_);
v_mctx_4117_ = lean_ctor_get(v___x_4116_, 0);
v_zetaDeltaFVarIds_4118_ = lean_ctor_get(v___x_4116_, 2);
v_postponed_4119_ = lean_ctor_get(v___x_4116_, 3);
v_diag_4120_ = lean_ctor_get(v___x_4116_, 4);
v_isSharedCheck_4158_ = !lean_is_exclusive(v___x_4116_);
if (v_isSharedCheck_4158_ == 0)
{
lean_object* v_unused_4159_; 
v_unused_4159_ = lean_ctor_get(v___x_4116_, 1);
lean_dec(v_unused_4159_);
v___x_4122_ = v___x_4116_;
v_isShared_4123_ = v_isSharedCheck_4158_;
goto v_resetjp_4121_;
}
else
{
lean_inc(v_diag_4120_);
lean_inc(v_postponed_4119_);
lean_inc(v_zetaDeltaFVarIds_4118_);
lean_inc(v_mctx_4117_);
lean_dec(v___x_4116_);
v___x_4122_ = lean_box(0);
v_isShared_4123_ = v_isSharedCheck_4158_;
goto v_resetjp_4121_;
}
v_resetjp_4121_:
{
lean_object* v___x_4124_; lean_object* v___x_4126_; 
v___x_4124_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3);
if (v_isShared_4123_ == 0)
{
lean_ctor_set(v___x_4122_, 1, v___x_4124_);
v___x_4126_ = v___x_4122_;
goto v_reusejp_4125_;
}
else
{
lean_object* v_reuseFailAlloc_4157_; 
v_reuseFailAlloc_4157_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4157_, 0, v_mctx_4117_);
lean_ctor_set(v_reuseFailAlloc_4157_, 1, v___x_4124_);
lean_ctor_set(v_reuseFailAlloc_4157_, 2, v_zetaDeltaFVarIds_4118_);
lean_ctor_set(v_reuseFailAlloc_4157_, 3, v_postponed_4119_);
lean_ctor_set(v_reuseFailAlloc_4157_, 4, v_diag_4120_);
v___x_4126_ = v_reuseFailAlloc_4157_;
goto v_reusejp_4125_;
}
v_reusejp_4125_:
{
lean_object* v___x_4127_; lean_object* v_r_4128_; 
v___x_4127_ = lean_st_ref_put(v___y_4087_, v___x_4126_);
lean_inc(v___y_4089_);
lean_inc_ref(v___y_4088_);
lean_inc(v___y_4087_);
lean_inc_ref(v___y_4086_);
v_r_4128_ = lean_apply_5(v_x_4084_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, lean_box(0));
if (lean_obj_tag(v_r_4128_) == 0)
{
lean_object* v_a_4129_; lean_object* v___x_4131_; uint8_t v_isShared_4132_; uint8_t v_isSharedCheck_4145_; 
v_a_4129_ = lean_ctor_get(v_r_4128_, 0);
v_isSharedCheck_4145_ = !lean_is_exclusive(v_r_4128_);
if (v_isSharedCheck_4145_ == 0)
{
v___x_4131_ = v_r_4128_;
v_isShared_4132_ = v_isSharedCheck_4145_;
goto v_resetjp_4130_;
}
else
{
lean_inc(v_a_4129_);
lean_dec(v_r_4128_);
v___x_4131_ = lean_box(0);
v_isShared_4132_ = v_isSharedCheck_4145_;
goto v_resetjp_4130_;
}
v_resetjp_4130_:
{
lean_object* v___x_4134_; 
lean_inc(v_a_4129_);
if (v_isShared_4132_ == 0)
{
lean_ctor_set_tag(v___x_4131_, 1);
v___x_4134_ = v___x_4131_;
goto v_reusejp_4133_;
}
else
{
lean_object* v_reuseFailAlloc_4144_; 
v_reuseFailAlloc_4144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4144_, 0, v_a_4129_);
v___x_4134_ = v_reuseFailAlloc_4144_;
goto v_reusejp_4133_;
}
v_reusejp_4133_:
{
lean_object* v___x_4135_; lean_object* v___x_4137_; uint8_t v_isShared_4138_; uint8_t v_isSharedCheck_4142_; 
v___x_4135_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(v___y_4089_, v_isExporting_4096_, v___x_4112_, v___y_4087_, v___x_4124_, v___x_4134_);
lean_dec_ref(v___x_4134_);
v_isSharedCheck_4142_ = !lean_is_exclusive(v___x_4135_);
if (v_isSharedCheck_4142_ == 0)
{
lean_object* v_unused_4143_; 
v_unused_4143_ = lean_ctor_get(v___x_4135_, 0);
lean_dec(v_unused_4143_);
v___x_4137_ = v___x_4135_;
v_isShared_4138_ = v_isSharedCheck_4142_;
goto v_resetjp_4136_;
}
else
{
lean_dec(v___x_4135_);
v___x_4137_ = lean_box(0);
v_isShared_4138_ = v_isSharedCheck_4142_;
goto v_resetjp_4136_;
}
v_resetjp_4136_:
{
lean_object* v___x_4140_; 
if (v_isShared_4138_ == 0)
{
lean_ctor_set(v___x_4137_, 0, v_a_4129_);
v___x_4140_ = v___x_4137_;
goto v_reusejp_4139_;
}
else
{
lean_object* v_reuseFailAlloc_4141_; 
v_reuseFailAlloc_4141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4141_, 0, v_a_4129_);
v___x_4140_ = v_reuseFailAlloc_4141_;
goto v_reusejp_4139_;
}
v_reusejp_4139_:
{
return v___x_4140_;
}
}
}
}
}
else
{
lean_object* v_a_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4150_; uint8_t v_isShared_4151_; uint8_t v_isSharedCheck_4155_; 
v_a_4146_ = lean_ctor_get(v_r_4128_, 0);
lean_inc(v_a_4146_);
lean_dec_ref_known(v_r_4128_, 1);
v___x_4147_ = lean_box(0);
v___x_4148_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(v___y_4089_, v_isExporting_4096_, v___x_4112_, v___y_4087_, v___x_4124_, v___x_4147_);
v_isSharedCheck_4155_ = !lean_is_exclusive(v___x_4148_);
if (v_isSharedCheck_4155_ == 0)
{
lean_object* v_unused_4156_; 
v_unused_4156_ = lean_ctor_get(v___x_4148_, 0);
lean_dec(v_unused_4156_);
v___x_4150_ = v___x_4148_;
v_isShared_4151_ = v_isSharedCheck_4155_;
goto v_resetjp_4149_;
}
else
{
lean_dec(v___x_4148_);
v___x_4150_ = lean_box(0);
v_isShared_4151_ = v_isSharedCheck_4155_;
goto v_resetjp_4149_;
}
v_resetjp_4149_:
{
lean_object* v___x_4153_; 
if (v_isShared_4151_ == 0)
{
lean_ctor_set_tag(v___x_4150_, 1);
lean_ctor_set(v___x_4150_, 0, v_a_4146_);
v___x_4153_ = v___x_4150_;
goto v_reusejp_4152_;
}
else
{
lean_object* v_reuseFailAlloc_4154_; 
v_reuseFailAlloc_4154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4154_, 0, v_a_4146_);
v___x_4153_ = v_reuseFailAlloc_4154_;
goto v_reusejp_4152_;
}
v_reusejp_4152_:
{
return v___x_4153_;
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___boxed(lean_object* v_x_4165_, lean_object* v_isExporting_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_){
_start:
{
uint8_t v_isExporting_boxed_4172_; lean_object* v_res_4173_; 
v_isExporting_boxed_4172_ = lean_unbox(v_isExporting_4166_);
v_res_4173_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(v_x_4165_, v_isExporting_boxed_4172_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_);
lean_dec(v___y_4170_);
lean_dec_ref(v___y_4169_);
lean_dec(v___y_4168_);
lean_dec_ref(v___y_4167_);
return v_res_4173_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2(lean_object* v_00_u03b1_4174_, lean_object* v_x_4175_, uint8_t v_isExporting_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_){
_start:
{
lean_object* v___x_4182_; 
v___x_4182_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(v_x_4175_, v_isExporting_4176_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_);
return v___x_4182_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___boxed(lean_object* v_00_u03b1_4183_, lean_object* v_x_4184_, lean_object* v_isExporting_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_){
_start:
{
uint8_t v_isExporting_boxed_4191_; lean_object* v_res_4192_; 
v_isExporting_boxed_4191_ = lean_unbox(v_isExporting_4185_);
v_res_4192_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2(v_00_u03b1_4183_, v_x_4184_, v_isExporting_boxed_4191_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_);
lean_dec(v___y_4189_);
lean_dec_ref(v___y_4188_);
lean_dec(v___y_4187_);
lean_dec_ref(v___y_4186_);
return v_res_4192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(lean_object* v_lctx_4193_, lean_object* v_localInsts_4194_, lean_object* v_x_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_){
_start:
{
lean_object* v___x_4201_; 
v___x_4201_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_4193_, v_localInsts_4194_, v_x_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_);
if (lean_obj_tag(v___x_4201_) == 0)
{
lean_object* v_a_4202_; lean_object* v___x_4204_; uint8_t v_isShared_4205_; uint8_t v_isSharedCheck_4209_; 
v_a_4202_ = lean_ctor_get(v___x_4201_, 0);
v_isSharedCheck_4209_ = !lean_is_exclusive(v___x_4201_);
if (v_isSharedCheck_4209_ == 0)
{
v___x_4204_ = v___x_4201_;
v_isShared_4205_ = v_isSharedCheck_4209_;
goto v_resetjp_4203_;
}
else
{
lean_inc(v_a_4202_);
lean_dec(v___x_4201_);
v___x_4204_ = lean_box(0);
v_isShared_4205_ = v_isSharedCheck_4209_;
goto v_resetjp_4203_;
}
v_resetjp_4203_:
{
lean_object* v___x_4207_; 
if (v_isShared_4205_ == 0)
{
v___x_4207_ = v___x_4204_;
goto v_reusejp_4206_;
}
else
{
lean_object* v_reuseFailAlloc_4208_; 
v_reuseFailAlloc_4208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4208_, 0, v_a_4202_);
v___x_4207_ = v_reuseFailAlloc_4208_;
goto v_reusejp_4206_;
}
v_reusejp_4206_:
{
return v___x_4207_;
}
}
}
else
{
lean_object* v_a_4210_; lean_object* v___x_4212_; uint8_t v_isShared_4213_; uint8_t v_isSharedCheck_4217_; 
v_a_4210_ = lean_ctor_get(v___x_4201_, 0);
v_isSharedCheck_4217_ = !lean_is_exclusive(v___x_4201_);
if (v_isSharedCheck_4217_ == 0)
{
v___x_4212_ = v___x_4201_;
v_isShared_4213_ = v_isSharedCheck_4217_;
goto v_resetjp_4211_;
}
else
{
lean_inc(v_a_4210_);
lean_dec(v___x_4201_);
v___x_4212_ = lean_box(0);
v_isShared_4213_ = v_isSharedCheck_4217_;
goto v_resetjp_4211_;
}
v_resetjp_4211_:
{
lean_object* v___x_4215_; 
if (v_isShared_4213_ == 0)
{
v___x_4215_ = v___x_4212_;
goto v_reusejp_4214_;
}
else
{
lean_object* v_reuseFailAlloc_4216_; 
v_reuseFailAlloc_4216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4216_, 0, v_a_4210_);
v___x_4215_ = v_reuseFailAlloc_4216_;
goto v_reusejp_4214_;
}
v_reusejp_4214_:
{
return v___x_4215_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg___boxed(lean_object* v_lctx_4218_, lean_object* v_localInsts_4219_, lean_object* v_x_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_){
_start:
{
lean_object* v_res_4226_; 
v_res_4226_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v_lctx_4218_, v_localInsts_4219_, v_x_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_);
lean_dec(v___y_4224_);
lean_dec_ref(v___y_4223_);
lean_dec(v___y_4222_);
lean_dec_ref(v___y_4221_);
return v_res_4226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4(lean_object* v_00_u03b1_4227_, lean_object* v_lctx_4228_, lean_object* v_localInsts_4229_, lean_object* v_x_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_){
_start:
{
lean_object* v___x_4236_; 
v___x_4236_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v_lctx_4228_, v_localInsts_4229_, v_x_4230_, v___y_4231_, v___y_4232_, v___y_4233_, v___y_4234_);
return v___x_4236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___boxed(lean_object* v_00_u03b1_4237_, lean_object* v_lctx_4238_, lean_object* v_localInsts_4239_, lean_object* v_x_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_){
_start:
{
lean_object* v_res_4246_; 
v_res_4246_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4(v_00_u03b1_4237_, v_lctx_4238_, v_localInsts_4239_, v_x_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_);
lean_dec(v___y_4244_);
lean_dec_ref(v___y_4243_);
lean_dec(v___y_4242_);
lean_dec_ref(v___y_4241_);
return v_res_4246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__0(lean_object* v_declName_4247_, lean_object* v_x_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_){
_start:
{
lean_object* v___x_4254_; lean_object* v___x_4255_; 
v___x_4254_ = l_Lean_MessageData_ofName(v_declName_4247_);
v___x_4255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4255_, 0, v___x_4254_);
return v___x_4255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__0___boxed(lean_object* v_declName_4256_, lean_object* v_x_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_){
_start:
{
lean_object* v_res_4263_; 
v_res_4263_ = l_Lean_Meta_mkInjectiveTheorems___lam__0(v_declName_4256_, v_x_4257_, v___y_4258_, v___y_4259_, v___y_4260_, v___y_4261_);
lean_dec(v___y_4261_);
lean_dec_ref(v___y_4260_);
lean_dec(v___y_4259_);
lean_dec_ref(v___y_4258_);
lean_dec_ref(v_x_4257_);
return v_res_4263_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_4264_; 
v___x_4264_ = l_instMonadEIO___redArg();
return v___x_4264_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(lean_object* v_msg_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_){
_start:
{
lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v_toApplicative_4277_; lean_object* v___x_4279_; uint8_t v_isShared_4280_; uint8_t v_isSharedCheck_4338_; 
v___x_4275_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0);
v___x_4276_ = l_StateRefT_x27_instMonad___redArg(v___x_4275_);
v_toApplicative_4277_ = lean_ctor_get(v___x_4276_, 0);
v_isSharedCheck_4338_ = !lean_is_exclusive(v___x_4276_);
if (v_isSharedCheck_4338_ == 0)
{
lean_object* v_unused_4339_; 
v_unused_4339_ = lean_ctor_get(v___x_4276_, 1);
lean_dec(v_unused_4339_);
v___x_4279_ = v___x_4276_;
v_isShared_4280_ = v_isSharedCheck_4338_;
goto v_resetjp_4278_;
}
else
{
lean_inc(v_toApplicative_4277_);
lean_dec(v___x_4276_);
v___x_4279_ = lean_box(0);
v_isShared_4280_ = v_isSharedCheck_4338_;
goto v_resetjp_4278_;
}
v_resetjp_4278_:
{
lean_object* v_toFunctor_4281_; lean_object* v_toSeq_4282_; lean_object* v_toSeqLeft_4283_; lean_object* v_toSeqRight_4284_; lean_object* v___x_4286_; uint8_t v_isShared_4287_; uint8_t v_isSharedCheck_4336_; 
v_toFunctor_4281_ = lean_ctor_get(v_toApplicative_4277_, 0);
v_toSeq_4282_ = lean_ctor_get(v_toApplicative_4277_, 2);
v_toSeqLeft_4283_ = lean_ctor_get(v_toApplicative_4277_, 3);
v_toSeqRight_4284_ = lean_ctor_get(v_toApplicative_4277_, 4);
v_isSharedCheck_4336_ = !lean_is_exclusive(v_toApplicative_4277_);
if (v_isSharedCheck_4336_ == 0)
{
lean_object* v_unused_4337_; 
v_unused_4337_ = lean_ctor_get(v_toApplicative_4277_, 1);
lean_dec(v_unused_4337_);
v___x_4286_ = v_toApplicative_4277_;
v_isShared_4287_ = v_isSharedCheck_4336_;
goto v_resetjp_4285_;
}
else
{
lean_inc(v_toSeqRight_4284_);
lean_inc(v_toSeqLeft_4283_);
lean_inc(v_toSeq_4282_);
lean_inc(v_toFunctor_4281_);
lean_dec(v_toApplicative_4277_);
v___x_4286_ = lean_box(0);
v_isShared_4287_ = v_isSharedCheck_4336_;
goto v_resetjp_4285_;
}
v_resetjp_4285_:
{
lean_object* v___f_4288_; lean_object* v___f_4289_; lean_object* v___f_4290_; lean_object* v___f_4291_; lean_object* v___x_4292_; lean_object* v___f_4293_; lean_object* v___f_4294_; lean_object* v___f_4295_; lean_object* v___x_4297_; 
v___f_4288_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__1));
v___f_4289_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__2));
lean_inc_ref(v_toFunctor_4281_);
v___f_4290_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4290_, 0, v_toFunctor_4281_);
v___f_4291_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4291_, 0, v_toFunctor_4281_);
v___x_4292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4292_, 0, v___f_4290_);
lean_ctor_set(v___x_4292_, 1, v___f_4291_);
v___f_4293_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4293_, 0, v_toSeqRight_4284_);
v___f_4294_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4294_, 0, v_toSeqLeft_4283_);
v___f_4295_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4295_, 0, v_toSeq_4282_);
if (v_isShared_4287_ == 0)
{
lean_ctor_set(v___x_4286_, 4, v___f_4293_);
lean_ctor_set(v___x_4286_, 3, v___f_4294_);
lean_ctor_set(v___x_4286_, 2, v___f_4295_);
lean_ctor_set(v___x_4286_, 1, v___f_4288_);
lean_ctor_set(v___x_4286_, 0, v___x_4292_);
v___x_4297_ = v___x_4286_;
goto v_reusejp_4296_;
}
else
{
lean_object* v_reuseFailAlloc_4335_; 
v_reuseFailAlloc_4335_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4335_, 0, v___x_4292_);
lean_ctor_set(v_reuseFailAlloc_4335_, 1, v___f_4288_);
lean_ctor_set(v_reuseFailAlloc_4335_, 2, v___f_4295_);
lean_ctor_set(v_reuseFailAlloc_4335_, 3, v___f_4294_);
lean_ctor_set(v_reuseFailAlloc_4335_, 4, v___f_4293_);
v___x_4297_ = v_reuseFailAlloc_4335_;
goto v_reusejp_4296_;
}
v_reusejp_4296_:
{
lean_object* v___x_4299_; 
if (v_isShared_4280_ == 0)
{
lean_ctor_set(v___x_4279_, 1, v___f_4289_);
lean_ctor_set(v___x_4279_, 0, v___x_4297_);
v___x_4299_ = v___x_4279_;
goto v_reusejp_4298_;
}
else
{
lean_object* v_reuseFailAlloc_4334_; 
v_reuseFailAlloc_4334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4334_, 0, v___x_4297_);
lean_ctor_set(v_reuseFailAlloc_4334_, 1, v___f_4289_);
v___x_4299_ = v_reuseFailAlloc_4334_;
goto v_reusejp_4298_;
}
v_reusejp_4298_:
{
lean_object* v___x_4300_; lean_object* v_toApplicative_4301_; lean_object* v___x_4303_; uint8_t v_isShared_4304_; uint8_t v_isSharedCheck_4332_; 
v___x_4300_ = l_StateRefT_x27_instMonad___redArg(v___x_4299_);
v_toApplicative_4301_ = lean_ctor_get(v___x_4300_, 0);
v_isSharedCheck_4332_ = !lean_is_exclusive(v___x_4300_);
if (v_isSharedCheck_4332_ == 0)
{
lean_object* v_unused_4333_; 
v_unused_4333_ = lean_ctor_get(v___x_4300_, 1);
lean_dec(v_unused_4333_);
v___x_4303_ = v___x_4300_;
v_isShared_4304_ = v_isSharedCheck_4332_;
goto v_resetjp_4302_;
}
else
{
lean_inc(v_toApplicative_4301_);
lean_dec(v___x_4300_);
v___x_4303_ = lean_box(0);
v_isShared_4304_ = v_isSharedCheck_4332_;
goto v_resetjp_4302_;
}
v_resetjp_4302_:
{
lean_object* v_toFunctor_4305_; lean_object* v_toSeq_4306_; lean_object* v_toSeqLeft_4307_; lean_object* v_toSeqRight_4308_; lean_object* v___x_4310_; uint8_t v_isShared_4311_; uint8_t v_isSharedCheck_4330_; 
v_toFunctor_4305_ = lean_ctor_get(v_toApplicative_4301_, 0);
v_toSeq_4306_ = lean_ctor_get(v_toApplicative_4301_, 2);
v_toSeqLeft_4307_ = lean_ctor_get(v_toApplicative_4301_, 3);
v_toSeqRight_4308_ = lean_ctor_get(v_toApplicative_4301_, 4);
v_isSharedCheck_4330_ = !lean_is_exclusive(v_toApplicative_4301_);
if (v_isSharedCheck_4330_ == 0)
{
lean_object* v_unused_4331_; 
v_unused_4331_ = lean_ctor_get(v_toApplicative_4301_, 1);
lean_dec(v_unused_4331_);
v___x_4310_ = v_toApplicative_4301_;
v_isShared_4311_ = v_isSharedCheck_4330_;
goto v_resetjp_4309_;
}
else
{
lean_inc(v_toSeqRight_4308_);
lean_inc(v_toSeqLeft_4307_);
lean_inc(v_toSeq_4306_);
lean_inc(v_toFunctor_4305_);
lean_dec(v_toApplicative_4301_);
v___x_4310_ = lean_box(0);
v_isShared_4311_ = v_isSharedCheck_4330_;
goto v_resetjp_4309_;
}
v_resetjp_4309_:
{
lean_object* v___f_4312_; lean_object* v___f_4313_; lean_object* v___f_4314_; lean_object* v___f_4315_; lean_object* v___x_4316_; lean_object* v___f_4317_; lean_object* v___f_4318_; lean_object* v___f_4319_; lean_object* v___x_4321_; 
v___f_4312_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__3));
v___f_4313_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__4));
lean_inc_ref(v_toFunctor_4305_);
v___f_4314_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4314_, 0, v_toFunctor_4305_);
v___f_4315_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4315_, 0, v_toFunctor_4305_);
v___x_4316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4316_, 0, v___f_4314_);
lean_ctor_set(v___x_4316_, 1, v___f_4315_);
v___f_4317_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4317_, 0, v_toSeqRight_4308_);
v___f_4318_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4318_, 0, v_toSeqLeft_4307_);
v___f_4319_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4319_, 0, v_toSeq_4306_);
if (v_isShared_4311_ == 0)
{
lean_ctor_set(v___x_4310_, 4, v___f_4317_);
lean_ctor_set(v___x_4310_, 3, v___f_4318_);
lean_ctor_set(v___x_4310_, 2, v___f_4319_);
lean_ctor_set(v___x_4310_, 1, v___f_4312_);
lean_ctor_set(v___x_4310_, 0, v___x_4316_);
v___x_4321_ = v___x_4310_;
goto v_reusejp_4320_;
}
else
{
lean_object* v_reuseFailAlloc_4329_; 
v_reuseFailAlloc_4329_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4329_, 0, v___x_4316_);
lean_ctor_set(v_reuseFailAlloc_4329_, 1, v___f_4312_);
lean_ctor_set(v_reuseFailAlloc_4329_, 2, v___f_4319_);
lean_ctor_set(v_reuseFailAlloc_4329_, 3, v___f_4318_);
lean_ctor_set(v_reuseFailAlloc_4329_, 4, v___f_4317_);
v___x_4321_ = v_reuseFailAlloc_4329_;
goto v_reusejp_4320_;
}
v_reusejp_4320_:
{
lean_object* v___x_4323_; 
if (v_isShared_4304_ == 0)
{
lean_ctor_set(v___x_4303_, 1, v___f_4313_);
lean_ctor_set(v___x_4303_, 0, v___x_4321_);
v___x_4323_ = v___x_4303_;
goto v_reusejp_4322_;
}
else
{
lean_object* v_reuseFailAlloc_4328_; 
v_reuseFailAlloc_4328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4328_, 0, v___x_4321_);
lean_ctor_set(v_reuseFailAlloc_4328_, 1, v___f_4313_);
v___x_4323_ = v_reuseFailAlloc_4328_;
goto v_reusejp_4322_;
}
v_reusejp_4322_:
{
lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_15720__overap_4326_; lean_object* v___x_4327_; 
v___x_4324_ = lean_box(0);
v___x_4325_ = l_instInhabitedOfMonad___redArg(v___x_4323_, v___x_4324_);
v___x_15720__overap_4326_ = lean_panic_fn_borrowed(v___x_4325_, v_msg_4269_);
lean_dec(v___x_4325_);
lean_inc(v___y_4273_);
lean_inc_ref(v___y_4272_);
lean_inc(v___y_4271_);
lean_inc_ref(v___y_4270_);
v___x_4327_ = lean_apply_5(v___x_15720__overap_4326_, v___y_4270_, v___y_4271_, v___y_4272_, v___y_4273_, lean_box(0));
return v___x_4327_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___boxed(lean_object* v_msg_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_){
_start:
{
lean_object* v_res_4346_; 
v_res_4346_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(v_msg_4340_, v___y_4341_, v___y_4342_, v___y_4343_, v___y_4344_);
lean_dec(v___y_4344_);
lean_dec_ref(v___y_4343_);
lean_dec(v___y_4342_);
lean_dec_ref(v___y_4341_);
return v_res_4346_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1(void){
_start:
{
lean_object* v___x_4348_; lean_object* v___x_4349_; 
v___x_4348_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__0));
v___x_4349_ = l_Lean_stringToMessageData(v___x_4348_);
return v___x_4349_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4(void){
_start:
{
lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; 
v___x_4352_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__2));
v___x_4353_ = lean_unsigned_to_nat(11u);
v___x_4354_ = lean_unsigned_to_nat(122u);
v___x_4355_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__3));
v___x_4356_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__2));
v___x_4357_ = l_mkPanicMessageWithDecl(v___x_4356_, v___x_4355_, v___x_4354_, v___x_4353_, v___x_4352_);
return v___x_4357_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(lean_object* v_constName_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_){
_start:
{
lean_object* v___x_4372_; lean_object* v_env_4373_; uint8_t v___x_4374_; lean_object* v___x_4375_; 
v___x_4372_ = lean_st_ref_get(v___y_4362_);
v_env_4373_ = lean_ctor_get(v___x_4372_, 0);
lean_inc_ref(v_env_4373_);
lean_dec(v___x_4372_);
v___x_4374_ = 0;
lean_inc(v_constName_4358_);
v___x_4375_ = l_Lean_Environment_findAsync_x3f(v_env_4373_, v_constName_4358_, v___x_4374_);
if (lean_obj_tag(v___x_4375_) == 1)
{
lean_object* v_val_4376_; uint8_t v_kind_4377_; 
v_val_4376_ = lean_ctor_get(v___x_4375_, 0);
lean_inc(v_val_4376_);
lean_dec_ref_known(v___x_4375_, 1);
v_kind_4377_ = lean_ctor_get_uint8(v_val_4376_, sizeof(void*)*3);
if (v_kind_4377_ == 6)
{
lean_object* v___x_4378_; 
v___x_4378_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_4376_);
if (lean_obj_tag(v___x_4378_) == 6)
{
lean_object* v_val_4379_; lean_object* v___x_4381_; uint8_t v_isShared_4382_; uint8_t v_isSharedCheck_4386_; 
lean_dec(v_constName_4358_);
v_val_4379_ = lean_ctor_get(v___x_4378_, 0);
v_isSharedCheck_4386_ = !lean_is_exclusive(v___x_4378_);
if (v_isSharedCheck_4386_ == 0)
{
v___x_4381_ = v___x_4378_;
v_isShared_4382_ = v_isSharedCheck_4386_;
goto v_resetjp_4380_;
}
else
{
lean_inc(v_val_4379_);
lean_dec(v___x_4378_);
v___x_4381_ = lean_box(0);
v_isShared_4382_ = v_isSharedCheck_4386_;
goto v_resetjp_4380_;
}
v_resetjp_4380_:
{
lean_object* v___x_4384_; 
if (v_isShared_4382_ == 0)
{
lean_ctor_set_tag(v___x_4381_, 0);
v___x_4384_ = v___x_4381_;
goto v_reusejp_4383_;
}
else
{
lean_object* v_reuseFailAlloc_4385_; 
v_reuseFailAlloc_4385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4385_, 0, v_val_4379_);
v___x_4384_ = v_reuseFailAlloc_4385_;
goto v_reusejp_4383_;
}
v_reusejp_4383_:
{
return v___x_4384_;
}
}
}
else
{
lean_object* v___x_4387_; lean_object* v___x_4388_; 
lean_dec_ref(v___x_4378_);
v___x_4387_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4);
v___x_4388_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(v___x_4387_, v___y_4359_, v___y_4360_, v___y_4361_, v___y_4362_);
if (lean_obj_tag(v___x_4388_) == 0)
{
lean_object* v_a_4389_; lean_object* v___x_4391_; uint8_t v_isShared_4392_; uint8_t v_isSharedCheck_4397_; 
v_a_4389_ = lean_ctor_get(v___x_4388_, 0);
v_isSharedCheck_4397_ = !lean_is_exclusive(v___x_4388_);
if (v_isSharedCheck_4397_ == 0)
{
v___x_4391_ = v___x_4388_;
v_isShared_4392_ = v_isSharedCheck_4397_;
goto v_resetjp_4390_;
}
else
{
lean_inc(v_a_4389_);
lean_dec(v___x_4388_);
v___x_4391_ = lean_box(0);
v_isShared_4392_ = v_isSharedCheck_4397_;
goto v_resetjp_4390_;
}
v_resetjp_4390_:
{
if (lean_obj_tag(v_a_4389_) == 0)
{
lean_del_object(v___x_4391_);
goto v___jp_4364_;
}
else
{
lean_object* v_val_4393_; lean_object* v___x_4395_; 
lean_dec(v_constName_4358_);
v_val_4393_ = lean_ctor_get(v_a_4389_, 0);
lean_inc(v_val_4393_);
lean_dec_ref_known(v_a_4389_, 1);
if (v_isShared_4392_ == 0)
{
lean_ctor_set(v___x_4391_, 0, v_val_4393_);
v___x_4395_ = v___x_4391_;
goto v_reusejp_4394_;
}
else
{
lean_object* v_reuseFailAlloc_4396_; 
v_reuseFailAlloc_4396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4396_, 0, v_val_4393_);
v___x_4395_ = v_reuseFailAlloc_4396_;
goto v_reusejp_4394_;
}
v_reusejp_4394_:
{
return v___x_4395_;
}
}
}
}
else
{
lean_object* v_a_4398_; lean_object* v___x_4400_; uint8_t v_isShared_4401_; uint8_t v_isSharedCheck_4405_; 
lean_dec(v_constName_4358_);
v_a_4398_ = lean_ctor_get(v___x_4388_, 0);
v_isSharedCheck_4405_ = !lean_is_exclusive(v___x_4388_);
if (v_isSharedCheck_4405_ == 0)
{
v___x_4400_ = v___x_4388_;
v_isShared_4401_ = v_isSharedCheck_4405_;
goto v_resetjp_4399_;
}
else
{
lean_inc(v_a_4398_);
lean_dec(v___x_4388_);
v___x_4400_ = lean_box(0);
v_isShared_4401_ = v_isSharedCheck_4405_;
goto v_resetjp_4399_;
}
v_resetjp_4399_:
{
lean_object* v___x_4403_; 
if (v_isShared_4401_ == 0)
{
v___x_4403_ = v___x_4400_;
goto v_reusejp_4402_;
}
else
{
lean_object* v_reuseFailAlloc_4404_; 
v_reuseFailAlloc_4404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4404_, 0, v_a_4398_);
v___x_4403_ = v_reuseFailAlloc_4404_;
goto v_reusejp_4402_;
}
v_reusejp_4402_:
{
return v___x_4403_;
}
}
}
}
}
else
{
lean_dec(v_val_4376_);
goto v___jp_4364_;
}
}
else
{
lean_dec(v___x_4375_);
goto v___jp_4364_;
}
v___jp_4364_:
{
lean_object* v___x_4365_; uint8_t v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; 
v___x_4365_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_4366_ = 0;
v___x_4367_ = l_Lean_MessageData_ofConstName(v_constName_4358_, v___x_4366_);
v___x_4368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4368_, 0, v___x_4365_);
lean_ctor_set(v___x_4368_, 1, v___x_4367_);
v___x_4369_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1);
v___x_4370_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4370_, 0, v___x_4368_);
lean_ctor_set(v___x_4370_, 1, v___x_4369_);
v___x_4371_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_4370_, v___y_4359_, v___y_4360_, v___y_4361_, v___y_4362_);
return v___x_4371_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___boxed(lean_object* v_constName_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_){
_start:
{
lean_object* v_res_4412_; 
v_res_4412_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(v_constName_4406_, v___y_4407_, v___y_4408_, v___y_4409_, v___y_4410_);
lean_dec(v___y_4410_);
lean_dec_ref(v___y_4409_);
lean_dec(v___y_4408_);
lean_dec_ref(v___y_4407_);
return v_res_4412_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0(lean_object* v_head_4413_, lean_object* v___x_4414_, lean_object* v___x_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_){
_start:
{
lean_object* v___x_4421_; 
v___x_4421_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(v_head_4413_, v___y_4416_, v___y_4417_, v___y_4418_, v___y_4419_);
if (lean_obj_tag(v___x_4421_) == 0)
{
lean_object* v_a_4422_; lean_object* v___x_4424_; uint8_t v_isShared_4425_; uint8_t v_isSharedCheck_4433_; 
v_a_4422_ = lean_ctor_get(v___x_4421_, 0);
v_isSharedCheck_4433_ = !lean_is_exclusive(v___x_4421_);
if (v_isSharedCheck_4433_ == 0)
{
v___x_4424_ = v___x_4421_;
v_isShared_4425_ = v_isSharedCheck_4433_;
goto v_resetjp_4423_;
}
else
{
lean_inc(v_a_4422_);
lean_dec(v___x_4421_);
v___x_4424_ = lean_box(0);
v_isShared_4425_ = v_isSharedCheck_4433_;
goto v_resetjp_4423_;
}
v_resetjp_4423_:
{
lean_object* v_numFields_4426_; uint8_t v___x_4427_; 
v_numFields_4426_ = lean_ctor_get(v_a_4422_, 4);
v___x_4427_ = lean_nat_dec_lt(v___x_4414_, v_numFields_4426_);
if (v___x_4427_ == 0)
{
lean_object* v___x_4429_; 
lean_dec(v_a_4422_);
if (v_isShared_4425_ == 0)
{
lean_ctor_set(v___x_4424_, 0, v___x_4415_);
v___x_4429_ = v___x_4424_;
goto v_reusejp_4428_;
}
else
{
lean_object* v_reuseFailAlloc_4430_; 
v_reuseFailAlloc_4430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4430_, 0, v___x_4415_);
v___x_4429_ = v_reuseFailAlloc_4430_;
goto v_reusejp_4428_;
}
v_reusejp_4428_:
{
return v___x_4429_;
}
}
else
{
lean_object* v___x_4431_; 
lean_del_object(v___x_4424_);
lean_inc(v_a_4422_);
v___x_4431_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(v_a_4422_, v___y_4416_, v___y_4417_, v___y_4418_, v___y_4419_);
if (lean_obj_tag(v___x_4431_) == 0)
{
lean_object* v___x_4432_; 
lean_dec_ref_known(v___x_4431_, 1);
v___x_4432_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(v_a_4422_, v___y_4416_, v___y_4417_, v___y_4418_, v___y_4419_);
return v___x_4432_;
}
else
{
lean_dec(v_a_4422_);
return v___x_4431_;
}
}
}
}
else
{
lean_object* v_a_4434_; lean_object* v___x_4436_; uint8_t v_isShared_4437_; uint8_t v_isSharedCheck_4441_; 
v_a_4434_ = lean_ctor_get(v___x_4421_, 0);
v_isSharedCheck_4441_ = !lean_is_exclusive(v___x_4421_);
if (v_isSharedCheck_4441_ == 0)
{
v___x_4436_ = v___x_4421_;
v_isShared_4437_ = v_isSharedCheck_4441_;
goto v_resetjp_4435_;
}
else
{
lean_inc(v_a_4434_);
lean_dec(v___x_4421_);
v___x_4436_ = lean_box(0);
v_isShared_4437_ = v_isSharedCheck_4441_;
goto v_resetjp_4435_;
}
v_resetjp_4435_:
{
lean_object* v___x_4439_; 
if (v_isShared_4437_ == 0)
{
v___x_4439_ = v___x_4436_;
goto v_reusejp_4438_;
}
else
{
lean_object* v_reuseFailAlloc_4440_; 
v_reuseFailAlloc_4440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4440_, 0, v_a_4434_);
v___x_4439_ = v_reuseFailAlloc_4440_;
goto v_reusejp_4438_;
}
v_reusejp_4438_:
{
return v___x_4439_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0___boxed(lean_object* v_head_4442_, lean_object* v___x_4443_, lean_object* v___x_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_){
_start:
{
lean_object* v_res_4450_; 
v_res_4450_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0(v_head_4442_, v___x_4443_, v___x_4444_, v___y_4445_, v___y_4446_, v___y_4447_, v___y_4448_);
lean_dec(v___y_4448_);
lean_dec_ref(v___y_4447_);
lean_dec(v___y_4446_);
lean_dec_ref(v___y_4445_);
lean_dec(v___x_4443_);
return v_res_4450_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(uint8_t v___y_4451_, uint8_t v___x_4452_, lean_object* v_as_x27_4453_, lean_object* v_b_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_){
_start:
{
if (lean_obj_tag(v_as_x27_4453_) == 0)
{
lean_object* v___x_4460_; 
v___x_4460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4460_, 0, v_b_4454_);
return v___x_4460_;
}
else
{
lean_object* v_head_4461_; lean_object* v_tail_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___f_4465_; uint8_t v___y_4467_; uint8_t v___x_4470_; 
v_head_4461_ = lean_ctor_get(v_as_x27_4453_, 0);
v_tail_4462_ = lean_ctor_get(v_as_x27_4453_, 1);
v___x_4463_ = lean_unsigned_to_nat(0u);
v___x_4464_ = lean_box(0);
lean_inc(v_head_4461_);
v___f_4465_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4465_, 0, v_head_4461_);
lean_closure_set(v___f_4465_, 1, v___x_4463_);
lean_closure_set(v___f_4465_, 2, v___x_4464_);
v___x_4470_ = l_Lean_isPrivateName(v_head_4461_);
if (v___x_4470_ == 0)
{
v___y_4467_ = v___y_4451_;
goto v___jp_4466_;
}
else
{
v___y_4467_ = v___x_4452_;
goto v___jp_4466_;
}
v___jp_4466_:
{
lean_object* v___x_4468_; 
v___x_4468_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(v___f_4465_, v___y_4467_, v___y_4455_, v___y_4456_, v___y_4457_, v___y_4458_);
if (lean_obj_tag(v___x_4468_) == 0)
{
lean_dec_ref_known(v___x_4468_, 1);
v_as_x27_4453_ = v_tail_4462_;
v_b_4454_ = v___x_4464_;
goto _start;
}
else
{
return v___x_4468_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___boxed(lean_object* v___y_4471_, lean_object* v___x_4472_, lean_object* v_as_x27_4473_, lean_object* v_b_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_){
_start:
{
uint8_t v___y_16840__boxed_4480_; uint8_t v___x_16841__boxed_4481_; lean_object* v_res_4482_; 
v___y_16840__boxed_4480_ = lean_unbox(v___y_4471_);
v___x_16841__boxed_4481_ = lean_unbox(v___x_4472_);
v_res_4482_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___y_16840__boxed_4480_, v___x_16841__boxed_4481_, v_as_x27_4473_, v_b_4474_, v___y_4475_, v___y_4476_, v___y_4477_, v___y_4478_);
lean_dec(v___y_4478_);
lean_dec_ref(v___y_4477_);
lean_dec(v___y_4476_);
lean_dec_ref(v___y_4475_);
lean_dec(v_as_x27_4473_);
return v_res_4482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__1(uint8_t v___y_4483_, uint8_t v_isUnsafe_4484_, lean_object* v_ctors_4485_, lean_object* v___x_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_){
_start:
{
lean_object* v___x_4492_; 
v___x_4492_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___y_4483_, v_isUnsafe_4484_, v_ctors_4485_, v___x_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_);
if (lean_obj_tag(v___x_4492_) == 0)
{
lean_object* v___x_4494_; uint8_t v_isShared_4495_; uint8_t v_isSharedCheck_4499_; 
v_isSharedCheck_4499_ = !lean_is_exclusive(v___x_4492_);
if (v_isSharedCheck_4499_ == 0)
{
lean_object* v_unused_4500_; 
v_unused_4500_ = lean_ctor_get(v___x_4492_, 0);
lean_dec(v_unused_4500_);
v___x_4494_ = v___x_4492_;
v_isShared_4495_ = v_isSharedCheck_4499_;
goto v_resetjp_4493_;
}
else
{
lean_dec(v___x_4492_);
v___x_4494_ = lean_box(0);
v_isShared_4495_ = v_isSharedCheck_4499_;
goto v_resetjp_4493_;
}
v_resetjp_4493_:
{
lean_object* v___x_4497_; 
if (v_isShared_4495_ == 0)
{
lean_ctor_set(v___x_4494_, 0, v___x_4486_);
v___x_4497_ = v___x_4494_;
goto v_reusejp_4496_;
}
else
{
lean_object* v_reuseFailAlloc_4498_; 
v_reuseFailAlloc_4498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4498_, 0, v___x_4486_);
v___x_4497_ = v_reuseFailAlloc_4498_;
goto v_reusejp_4496_;
}
v_reusejp_4496_:
{
return v___x_4497_;
}
}
}
else
{
return v___x_4492_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed(lean_object* v___y_4501_, lean_object* v_isUnsafe_4502_, lean_object* v_ctors_4503_, lean_object* v___x_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_){
_start:
{
uint8_t v___y_16885__boxed_4510_; uint8_t v_isUnsafe_boxed_4511_; lean_object* v_res_4512_; 
v___y_16885__boxed_4510_ = lean_unbox(v___y_4501_);
v_isUnsafe_boxed_4511_ = lean_unbox(v_isUnsafe_4502_);
v_res_4512_ = l_Lean_Meta_mkInjectiveTheorems___lam__1(v___y_16885__boxed_4510_, v_isUnsafe_boxed_4511_, v_ctors_4503_, v___x_4504_, v___y_4505_, v___y_4506_, v___y_4507_, v___y_4508_);
lean_dec(v___y_4508_);
lean_dec_ref(v___y_4507_);
lean_dec(v___y_4506_);
lean_dec_ref(v___y_4505_);
lean_dec(v_ctors_4503_);
return v_res_4512_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4514_; lean_object* v___x_4515_; 
v___x_4514_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__0));
v___x_4515_ = l_Lean_stringToMessageData(v___x_4514_);
return v___x_4515_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(lean_object* v_constName_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_){
_start:
{
lean_object* v___x_4522_; lean_object* v_env_4523_; lean_object* v___x_4524_; 
v___x_4522_ = lean_st_ref_get(v___y_4520_);
v_env_4523_ = lean_ctor_get(v___x_4522_, 0);
lean_inc_ref(v_env_4523_);
lean_dec(v___x_4522_);
lean_inc(v_constName_4516_);
v___x_4524_ = l_Lean_isInductiveCore_x3f(v_env_4523_, v_constName_4516_);
if (lean_obj_tag(v___x_4524_) == 0)
{
lean_object* v___x_4525_; uint8_t v___x_4526_; lean_object* v___x_4527_; lean_object* v___x_4528_; lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; 
v___x_4525_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_4526_ = 0;
v___x_4527_ = l_Lean_MessageData_ofConstName(v_constName_4516_, v___x_4526_);
v___x_4528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4528_, 0, v___x_4525_);
lean_ctor_set(v___x_4528_, 1, v___x_4527_);
v___x_4529_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1);
v___x_4530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4530_, 0, v___x_4528_);
lean_ctor_set(v___x_4530_, 1, v___x_4529_);
v___x_4531_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_4530_, v___y_4517_, v___y_4518_, v___y_4519_, v___y_4520_);
return v___x_4531_;
}
else
{
lean_object* v_val_4532_; lean_object* v___x_4534_; uint8_t v_isShared_4535_; uint8_t v_isSharedCheck_4539_; 
lean_dec(v_constName_4516_);
v_val_4532_ = lean_ctor_get(v___x_4524_, 0);
v_isSharedCheck_4539_ = !lean_is_exclusive(v___x_4524_);
if (v_isSharedCheck_4539_ == 0)
{
v___x_4534_ = v___x_4524_;
v_isShared_4535_ = v_isSharedCheck_4539_;
goto v_resetjp_4533_;
}
else
{
lean_inc(v_val_4532_);
lean_dec(v___x_4524_);
v___x_4534_ = lean_box(0);
v_isShared_4535_ = v_isSharedCheck_4539_;
goto v_resetjp_4533_;
}
v_resetjp_4533_:
{
lean_object* v___x_4537_; 
if (v_isShared_4535_ == 0)
{
lean_ctor_set_tag(v___x_4534_, 0);
v___x_4537_ = v___x_4534_;
goto v_reusejp_4536_;
}
else
{
lean_object* v_reuseFailAlloc_4538_; 
v_reuseFailAlloc_4538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4538_, 0, v_val_4532_);
v___x_4537_ = v_reuseFailAlloc_4538_;
goto v_reusejp_4536_;
}
v_reusejp_4536_:
{
return v___x_4537_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___boxed(lean_object* v_constName_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_){
_start:
{
lean_object* v_res_4546_; 
v_res_4546_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_constName_4540_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_);
lean_dec(v___y_4544_);
lean_dec_ref(v___y_4543_);
lean_dec(v___y_4542_);
lean_dec_ref(v___y_4541_);
return v_res_4546_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__0(void){
_start:
{
lean_object* v___x_4547_; lean_object* v___x_4548_; 
v___x_4547_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0);
v___x_4548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4548_, 0, v___x_4547_);
return v___x_4548_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__1(void){
_start:
{
lean_object* v___x_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; 
v___x_4549_ = lean_unsigned_to_nat(32u);
v___x_4550_ = lean_mk_empty_array_with_capacity(v___x_4549_);
v___x_4551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4551_, 0, v___x_4550_);
return v___x_4551_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__2(void){
_start:
{
size_t v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; 
v___x_4552_ = ((size_t)5ULL);
v___x_4553_ = lean_unsigned_to_nat(0u);
v___x_4554_ = lean_unsigned_to_nat(32u);
v___x_4555_ = lean_mk_empty_array_with_capacity(v___x_4554_);
v___x_4556_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_4557_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4557_, 0, v___x_4556_);
lean_ctor_set(v___x_4557_, 1, v___x_4555_);
lean_ctor_set(v___x_4557_, 2, v___x_4553_);
lean_ctor_set(v___x_4557_, 3, v___x_4553_);
lean_ctor_set_usize(v___x_4557_, 4, v___x_4552_);
return v___x_4557_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__3(void){
_start:
{
lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; 
v___x_4558_ = lean_box(1);
v___x_4559_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__2, &l_Lean_Meta_mkInjectiveTheorems___closed__2_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__2);
v___x_4560_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__0, &l_Lean_Meta_mkInjectiveTheorems___closed__0_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__0);
v___x_4561_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4561_, 0, v___x_4560_);
lean_ctor_set(v___x_4561_, 1, v___x_4559_);
lean_ctor_set(v___x_4561_, 2, v___x_4558_);
return v___x_4561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems(lean_object* v_declName_4564_, lean_object* v_a_4565_, lean_object* v_a_4566_, lean_object* v_a_4567_, lean_object* v_a_4568_){
_start:
{
lean_object* v___f_4570_; lean_object* v___x_4571_; lean_object* v_env_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; 
lean_inc_n(v_declName_4564_, 2);
v___f_4570_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4570_, 0, v_declName_4564_);
v___x_4571_ = lean_st_ref_get(v_a_4568_);
v_env_4572_ = lean_ctor_get(v___x_4571_, 0);
lean_inc_ref(v_env_4572_);
lean_dec(v___x_4571_);
v___x_4573_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_4567_);
v___x_4574_ = l_Lean_Meta_isInductivePredicate(v_declName_4564_, v_a_4565_, v_a_4566_, v_a_4567_, v_a_4568_);
if (lean_obj_tag(v___x_4574_) == 0)
{
lean_object* v_a_4575_; lean_object* v___x_4577_; uint8_t v_isShared_4578_; uint8_t v_isSharedCheck_4769_; 
v_a_4575_ = lean_ctor_get(v___x_4574_, 0);
v_isSharedCheck_4769_ = !lean_is_exclusive(v___x_4574_);
if (v_isSharedCheck_4769_ == 0)
{
v___x_4577_ = v___x_4574_;
v_isShared_4578_ = v_isSharedCheck_4769_;
goto v_resetjp_4576_;
}
else
{
lean_inc(v_a_4575_);
lean_dec(v___x_4574_);
v___x_4577_ = lean_box(0);
v_isShared_4578_ = v_isSharedCheck_4769_;
goto v_resetjp_4576_;
}
v_resetjp_4576_:
{
lean_object* v___x_4584_; uint8_t v___x_4585_; lean_object* v___y_4587_; uint8_t v___y_4588_; lean_object* v___y_4589_; lean_object* v___y_4590_; lean_object* v___y_4591_; lean_object* v___y_4592_; lean_object* v_a_4593_; lean_object* v___y_4603_; lean_object* v___y_4604_; uint8_t v___y_4605_; lean_object* v___y_4606_; lean_object* v___y_4607_; lean_object* v___y_4608_; lean_object* v_a_4609_; lean_object* v___y_4612_; lean_object* v___y_4613_; uint8_t v___y_4614_; lean_object* v___y_4615_; lean_object* v___y_4616_; lean_object* v___y_4617_; lean_object* v_a_4618_; lean_object* v___y_4621_; uint8_t v___y_4622_; lean_object* v___y_4623_; lean_object* v___y_4624_; lean_object* v___y_4625_; lean_object* v___y_4626_; lean_object* v_a_4627_; lean_object* v___y_4640_; uint8_t v___y_4641_; lean_object* v___y_4642_; lean_object* v___y_4643_; lean_object* v___y_4644_; lean_object* v___y_4645_; lean_object* v_a_4646_; lean_object* v___y_4649_; uint8_t v___y_4650_; lean_object* v___y_4651_; lean_object* v___y_4652_; lean_object* v___y_4653_; lean_object* v___y_4654_; lean_object* v_a_4655_; uint8_t v___y_4658_; lean_object* v___y_4659_; uint8_t v___y_4660_; lean_object* v___y_4661_; lean_object* v___y_4662_; uint8_t v___y_4700_; uint8_t v___x_4766_; 
v___x_4584_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__4));
v___x_4585_ = 1;
v___x_4766_ = l_Lean_Environment_contains(v_env_4572_, v___x_4584_, v___x_4585_);
if (v___x_4766_ == 0)
{
lean_dec_ref(v___x_4573_);
v___y_4700_ = v___x_4766_;
goto v___jp_4699_;
}
else
{
lean_object* v___x_4767_; uint8_t v___x_4768_; 
v___x_4767_ = l_Lean_Meta_genInjectivity;
v___x_4768_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v___x_4573_, v___x_4767_);
lean_dec_ref(v___x_4573_);
v___y_4700_ = v___x_4768_;
goto v___jp_4699_;
}
v___jp_4579_:
{
lean_object* v___x_4580_; lean_object* v___x_4582_; 
v___x_4580_ = lean_box(0);
if (v_isShared_4578_ == 0)
{
lean_ctor_set(v___x_4577_, 0, v___x_4580_);
v___x_4582_ = v___x_4577_;
goto v_reusejp_4581_;
}
else
{
lean_object* v_reuseFailAlloc_4583_; 
v_reuseFailAlloc_4583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4583_, 0, v___x_4580_);
v___x_4582_ = v_reuseFailAlloc_4583_;
goto v_reusejp_4581_;
}
v_reusejp_4581_:
{
return v___x_4582_;
}
}
v___jp_4586_:
{
lean_object* v___x_4594_; double v___x_4595_; double v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; 
v___x_4594_ = lean_io_get_num_heartbeats();
v___x_4595_ = lean_float_of_nat(v___y_4589_);
v___x_4596_ = lean_float_of_nat(v___x_4594_);
v___x_4597_ = lean_box_float(v___x_4595_);
v___x_4598_ = lean_box_float(v___x_4596_);
v___x_4599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4599_, 0, v___x_4597_);
lean_ctor_set(v___x_4599_, 1, v___x_4598_);
v___x_4600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4600_, 0, v_a_4593_);
lean_ctor_set(v___x_4600_, 1, v___x_4599_);
lean_inc_ref(v___y_4587_);
lean_inc(v___y_4590_);
v___x_4601_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v___y_4590_, v___x_4585_, v___y_4587_, v___y_4592_, v___y_4588_, v___y_4591_, v___f_4570_, v___x_4600_, v_a_4565_, v_a_4566_, v_a_4567_, v_a_4568_);
return v___x_4601_;
}
v___jp_4602_:
{
lean_object* v___x_4610_; 
v___x_4610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4610_, 0, v_a_4609_);
v___y_4587_ = v___y_4603_;
v___y_4588_ = v___y_4605_;
v___y_4589_ = v___y_4604_;
v___y_4590_ = v___y_4606_;
v___y_4591_ = v___y_4607_;
v___y_4592_ = v___y_4608_;
v_a_4593_ = v___x_4610_;
goto v___jp_4586_;
}
v___jp_4611_:
{
lean_object* v___x_4619_; 
v___x_4619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4619_, 0, v_a_4618_);
v___y_4587_ = v___y_4612_;
v___y_4588_ = v___y_4614_;
v___y_4589_ = v___y_4613_;
v___y_4590_ = v___y_4615_;
v___y_4591_ = v___y_4616_;
v___y_4592_ = v___y_4617_;
v_a_4593_ = v___x_4619_;
goto v___jp_4586_;
}
v___jp_4620_:
{
lean_object* v___x_4628_; double v___x_4629_; double v___x_4630_; double v___x_4631_; double v___x_4632_; double v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; 
v___x_4628_ = lean_io_mono_nanos_now();
v___x_4629_ = lean_float_of_nat(v___y_4626_);
v___x_4630_ = lean_float_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0);
v___x_4631_ = lean_float_div(v___x_4629_, v___x_4630_);
v___x_4632_ = lean_float_of_nat(v___x_4628_);
v___x_4633_ = lean_float_div(v___x_4632_, v___x_4630_);
v___x_4634_ = lean_box_float(v___x_4631_);
v___x_4635_ = lean_box_float(v___x_4633_);
v___x_4636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4636_, 0, v___x_4634_);
lean_ctor_set(v___x_4636_, 1, v___x_4635_);
v___x_4637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4637_, 0, v_a_4627_);
lean_ctor_set(v___x_4637_, 1, v___x_4636_);
lean_inc_ref(v___y_4621_);
lean_inc(v___y_4623_);
v___x_4638_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v___y_4623_, v___x_4585_, v___y_4621_, v___y_4625_, v___y_4622_, v___y_4624_, v___f_4570_, v___x_4637_, v_a_4565_, v_a_4566_, v_a_4567_, v_a_4568_);
return v___x_4638_;
}
v___jp_4639_:
{
lean_object* v___x_4647_; 
v___x_4647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4647_, 0, v_a_4646_);
v___y_4621_ = v___y_4640_;
v___y_4622_ = v___y_4641_;
v___y_4623_ = v___y_4642_;
v___y_4624_ = v___y_4643_;
v___y_4625_ = v___y_4644_;
v___y_4626_ = v___y_4645_;
v_a_4627_ = v___x_4647_;
goto v___jp_4620_;
}
v___jp_4648_:
{
lean_object* v___x_4656_; 
v___x_4656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4656_, 0, v_a_4655_);
v___y_4621_ = v___y_4649_;
v___y_4622_ = v___y_4650_;
v___y_4623_ = v___y_4651_;
v___y_4624_ = v___y_4652_;
v___y_4625_ = v___y_4653_;
v___y_4626_ = v___y_4654_;
v_a_4627_ = v___x_4656_;
goto v___jp_4620_;
}
v___jp_4657_:
{
lean_object* v___x_4663_; lean_object* v_a_4664_; lean_object* v___x_4665_; uint8_t v___x_4666_; 
v___x_4663_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v_a_4568_);
v_a_4664_ = lean_ctor_get(v___x_4663_, 0);
lean_inc(v_a_4664_);
lean_dec_ref(v___x_4663_);
v___x_4665_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4666_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v___y_4662_, v___x_4665_);
if (v___x_4666_ == 0)
{
lean_object* v___x_4667_; lean_object* v___x_4668_; 
v___x_4667_ = lean_io_mono_nanos_now();
v___x_4668_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4564_, v_a_4565_, v_a_4566_, v_a_4567_, v_a_4568_);
if (lean_obj_tag(v___x_4668_) == 0)
{
lean_object* v_a_4669_; uint8_t v_isUnsafe_4670_; 
v_a_4669_ = lean_ctor_get(v___x_4668_, 0);
lean_inc(v_a_4669_);
lean_dec_ref_known(v___x_4668_, 1);
v_isUnsafe_4670_ = lean_ctor_get_uint8(v_a_4669_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4670_ == 0)
{
lean_object* v_ctors_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___f_4677_; lean_object* v___x_4678_; 
v_ctors_4671_ = lean_ctor_get(v_a_4669_, 4);
lean_inc(v_ctors_4671_);
lean_dec(v_a_4669_);
v___x_4672_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_4673_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__4));
v___x_4674_ = lean_box(0);
v___x_4675_ = lean_box(v___y_4658_);
v___x_4676_ = lean_box(v_isUnsafe_4670_);
v___f_4677_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed), 9, 4);
lean_closure_set(v___f_4677_, 0, v___x_4675_);
lean_closure_set(v___f_4677_, 1, v___x_4676_);
lean_closure_set(v___f_4677_, 2, v_ctors_4671_);
lean_closure_set(v___f_4677_, 3, v___x_4674_);
v___x_4678_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4672_, v___x_4673_, v___f_4677_, v_a_4565_, v_a_4566_, v_a_4567_, v_a_4568_);
if (lean_obj_tag(v___x_4678_) == 0)
{
lean_object* v_a_4679_; 
v_a_4679_ = lean_ctor_get(v___x_4678_, 0);
lean_inc(v_a_4679_);
lean_dec_ref_known(v___x_4678_, 1);
v___y_4640_ = v___y_4659_;
v___y_4641_ = v___y_4660_;
v___y_4642_ = v___y_4661_;
v___y_4643_ = v_a_4664_;
v___y_4644_ = v___y_4662_;
v___y_4645_ = v___x_4667_;
v_a_4646_ = v_a_4679_;
goto v___jp_4639_;
}
else
{
lean_object* v_a_4680_; 
v_a_4680_ = lean_ctor_get(v___x_4678_, 0);
lean_inc(v_a_4680_);
lean_dec_ref_known(v___x_4678_, 1);
v___y_4649_ = v___y_4659_;
v___y_4650_ = v___y_4660_;
v___y_4651_ = v___y_4661_;
v___y_4652_ = v_a_4664_;
v___y_4653_ = v___y_4662_;
v___y_4654_ = v___x_4667_;
v_a_4655_ = v_a_4680_;
goto v___jp_4648_;
}
}
else
{
lean_object* v___x_4681_; 
lean_dec(v_a_4669_);
v___x_4681_ = lean_box(0);
v___y_4640_ = v___y_4659_;
v___y_4641_ = v___y_4660_;
v___y_4642_ = v___y_4661_;
v___y_4643_ = v_a_4664_;
v___y_4644_ = v___y_4662_;
v___y_4645_ = v___x_4667_;
v_a_4646_ = v___x_4681_;
goto v___jp_4639_;
}
}
else
{
lean_object* v_a_4682_; 
v_a_4682_ = lean_ctor_get(v___x_4668_, 0);
lean_inc(v_a_4682_);
lean_dec_ref_known(v___x_4668_, 1);
v___y_4649_ = v___y_4659_;
v___y_4650_ = v___y_4660_;
v___y_4651_ = v___y_4661_;
v___y_4652_ = v_a_4664_;
v___y_4653_ = v___y_4662_;
v___y_4654_ = v___x_4667_;
v_a_4655_ = v_a_4682_;
goto v___jp_4648_;
}
}
else
{
lean_object* v___x_4683_; lean_object* v___x_4684_; 
v___x_4683_ = lean_io_get_num_heartbeats();
v___x_4684_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4564_, v_a_4565_, v_a_4566_, v_a_4567_, v_a_4568_);
if (lean_obj_tag(v___x_4684_) == 0)
{
lean_object* v_a_4685_; uint8_t v_isUnsafe_4686_; 
v_a_4685_ = lean_ctor_get(v___x_4684_, 0);
lean_inc(v_a_4685_);
lean_dec_ref_known(v___x_4684_, 1);
v_isUnsafe_4686_ = lean_ctor_get_uint8(v_a_4685_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4686_ == 0)
{
lean_object* v_ctors_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___f_4693_; lean_object* v___x_4694_; 
v_ctors_4687_ = lean_ctor_get(v_a_4685_, 4);
lean_inc(v_ctors_4687_);
lean_dec(v_a_4685_);
v___x_4688_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_4689_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__4));
v___x_4690_ = lean_box(0);
v___x_4691_ = lean_box(v___y_4658_);
v___x_4692_ = lean_box(v_isUnsafe_4686_);
v___f_4693_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed), 9, 4);
lean_closure_set(v___f_4693_, 0, v___x_4691_);
lean_closure_set(v___f_4693_, 1, v___x_4692_);
lean_closure_set(v___f_4693_, 2, v_ctors_4687_);
lean_closure_set(v___f_4693_, 3, v___x_4690_);
v___x_4694_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4688_, v___x_4689_, v___f_4693_, v_a_4565_, v_a_4566_, v_a_4567_, v_a_4568_);
if (lean_obj_tag(v___x_4694_) == 0)
{
lean_object* v_a_4695_; 
v_a_4695_ = lean_ctor_get(v___x_4694_, 0);
lean_inc(v_a_4695_);
lean_dec_ref_known(v___x_4694_, 1);
v___y_4603_ = v___y_4659_;
v___y_4604_ = v___x_4683_;
v___y_4605_ = v___y_4660_;
v___y_4606_ = v___y_4661_;
v___y_4607_ = v_a_4664_;
v___y_4608_ = v___y_4662_;
v_a_4609_ = v_a_4695_;
goto v___jp_4602_;
}
else
{
lean_object* v_a_4696_; 
v_a_4696_ = lean_ctor_get(v___x_4694_, 0);
lean_inc(v_a_4696_);
lean_dec_ref_known(v___x_4694_, 1);
v___y_4612_ = v___y_4659_;
v___y_4613_ = v___x_4683_;
v___y_4614_ = v___y_4660_;
v___y_4615_ = v___y_4661_;
v___y_4616_ = v_a_4664_;
v___y_4617_ = v___y_4662_;
v_a_4618_ = v_a_4696_;
goto v___jp_4611_;
}
}
else
{
lean_object* v___x_4697_; 
lean_dec(v_a_4685_);
v___x_4697_ = lean_box(0);
v___y_4603_ = v___y_4659_;
v___y_4604_ = v___x_4683_;
v___y_4605_ = v___y_4660_;
v___y_4606_ = v___y_4661_;
v___y_4607_ = v_a_4664_;
v___y_4608_ = v___y_4662_;
v_a_4609_ = v___x_4697_;
goto v___jp_4602_;
}
}
else
{
lean_object* v_a_4698_; 
v_a_4698_ = lean_ctor_get(v___x_4684_, 0);
lean_inc(v_a_4698_);
lean_dec_ref_known(v___x_4684_, 1);
v___y_4612_ = v___y_4659_;
v___y_4613_ = v___x_4683_;
v___y_4614_ = v___y_4660_;
v___y_4615_ = v___y_4661_;
v___y_4616_ = v_a_4664_;
v___y_4617_ = v___y_4662_;
v_a_4618_ = v_a_4698_;
goto v___jp_4611_;
}
}
}
v___jp_4699_:
{
if (v___y_4700_ == 0)
{
lean_dec(v_a_4575_);
lean_dec_ref(v___f_4570_);
lean_dec(v_declName_4564_);
goto v___jp_4579_;
}
else
{
uint8_t v___x_4701_; 
v___x_4701_ = lean_unbox(v_a_4575_);
lean_dec(v_a_4575_);
if (v___x_4701_ == 0)
{
lean_object* v_toCold_4702_; lean_object* v_options_4703_; uint8_t v_hasTrace_4704_; 
lean_del_object(v___x_4577_);
v_toCold_4702_ = lean_ctor_get(v_a_4567_, 0);
v_options_4703_ = lean_ctor_get(v_toCold_4702_, 2);
v_hasTrace_4704_ = lean_ctor_get_uint8(v_options_4703_, sizeof(void*)*1);
if (v_hasTrace_4704_ == 0)
{
lean_object* v___x_4705_; 
lean_dec_ref(v___f_4570_);
v___x_4705_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4564_, v_a_4565_, v_a_4566_, v_a_4567_, v_a_4568_);
if (lean_obj_tag(v___x_4705_) == 0)
{
lean_object* v_a_4706_; lean_object* v___x_4708_; uint8_t v_isShared_4709_; uint8_t v_isSharedCheck_4723_; 
v_a_4706_ = lean_ctor_get(v___x_4705_, 0);
v_isSharedCheck_4723_ = !lean_is_exclusive(v___x_4705_);
if (v_isSharedCheck_4723_ == 0)
{
v___x_4708_ = v___x_4705_;
v_isShared_4709_ = v_isSharedCheck_4723_;
goto v_resetjp_4707_;
}
else
{
lean_inc(v_a_4706_);
lean_dec(v___x_4705_);
v___x_4708_ = lean_box(0);
v_isShared_4709_ = v_isSharedCheck_4723_;
goto v_resetjp_4707_;
}
v_resetjp_4707_:
{
uint8_t v_isUnsafe_4710_; 
v_isUnsafe_4710_ = lean_ctor_get_uint8(v_a_4706_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4710_ == 0)
{
lean_object* v_ctors_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___f_4717_; lean_object* v___x_4718_; 
lean_del_object(v___x_4708_);
v_ctors_4711_ = lean_ctor_get(v_a_4706_, 4);
lean_inc(v_ctors_4711_);
lean_dec(v_a_4706_);
v___x_4712_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_4713_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__4));
v___x_4714_ = lean_box(0);
v___x_4715_ = lean_box(v___y_4700_);
v___x_4716_ = lean_box(v_isUnsafe_4710_);
v___f_4717_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed), 9, 4);
lean_closure_set(v___f_4717_, 0, v___x_4715_);
lean_closure_set(v___f_4717_, 1, v___x_4716_);
lean_closure_set(v___f_4717_, 2, v_ctors_4711_);
lean_closure_set(v___f_4717_, 3, v___x_4714_);
v___x_4718_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4712_, v___x_4713_, v___f_4717_, v_a_4565_, v_a_4566_, v_a_4567_, v_a_4568_);
return v___x_4718_;
}
else
{
lean_object* v___x_4719_; lean_object* v___x_4721_; 
lean_dec(v_a_4706_);
v___x_4719_ = lean_box(0);
if (v_isShared_4709_ == 0)
{
lean_ctor_set(v___x_4708_, 0, v___x_4719_);
v___x_4721_ = v___x_4708_;
goto v_reusejp_4720_;
}
else
{
lean_object* v_reuseFailAlloc_4722_; 
v_reuseFailAlloc_4722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4722_, 0, v___x_4719_);
v___x_4721_ = v_reuseFailAlloc_4722_;
goto v_reusejp_4720_;
}
v_reusejp_4720_:
{
return v___x_4721_;
}
}
}
}
else
{
lean_object* v_a_4724_; lean_object* v___x_4726_; uint8_t v_isShared_4727_; uint8_t v_isSharedCheck_4731_; 
v_a_4724_ = lean_ctor_get(v___x_4705_, 0);
v_isSharedCheck_4731_ = !lean_is_exclusive(v___x_4705_);
if (v_isSharedCheck_4731_ == 0)
{
v___x_4726_ = v___x_4705_;
v_isShared_4727_ = v_isSharedCheck_4731_;
goto v_resetjp_4725_;
}
else
{
lean_inc(v_a_4724_);
lean_dec(v___x_4705_);
v___x_4726_ = lean_box(0);
v_isShared_4727_ = v_isSharedCheck_4731_;
goto v_resetjp_4725_;
}
v_resetjp_4725_:
{
lean_object* v___x_4729_; 
if (v_isShared_4727_ == 0)
{
v___x_4729_ = v___x_4726_;
goto v_reusejp_4728_;
}
else
{
lean_object* v_reuseFailAlloc_4730_; 
v_reuseFailAlloc_4730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4730_, 0, v_a_4724_);
v___x_4729_ = v_reuseFailAlloc_4730_;
goto v_reusejp_4728_;
}
v_reusejp_4728_:
{
return v___x_4729_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; uint8_t v___x_4736_; 
v_inheritedTraceOptions_4732_ = lean_ctor_get(v_toCold_4702_, 11);
v___x_4733_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_4734_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_4735_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_4736_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4732_, v_options_4703_, v___x_4735_);
if (v___x_4736_ == 0)
{
lean_object* v___x_4737_; uint8_t v___x_4738_; 
v___x_4737_ = l_Lean_trace_profiler;
v___x_4738_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_4703_, v___x_4737_);
if (v___x_4738_ == 0)
{
lean_object* v___x_4739_; 
lean_dec_ref(v___f_4570_);
v___x_4739_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4564_, v_a_4565_, v_a_4566_, v_a_4567_, v_a_4568_);
if (lean_obj_tag(v___x_4739_) == 0)
{
lean_object* v_a_4740_; lean_object* v___x_4742_; uint8_t v_isShared_4743_; uint8_t v_isSharedCheck_4757_; 
v_a_4740_ = lean_ctor_get(v___x_4739_, 0);
v_isSharedCheck_4757_ = !lean_is_exclusive(v___x_4739_);
if (v_isSharedCheck_4757_ == 0)
{
v___x_4742_ = v___x_4739_;
v_isShared_4743_ = v_isSharedCheck_4757_;
goto v_resetjp_4741_;
}
else
{
lean_inc(v_a_4740_);
lean_dec(v___x_4739_);
v___x_4742_ = lean_box(0);
v_isShared_4743_ = v_isSharedCheck_4757_;
goto v_resetjp_4741_;
}
v_resetjp_4741_:
{
uint8_t v_isUnsafe_4744_; 
v_isUnsafe_4744_ = lean_ctor_get_uint8(v_a_4740_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4744_ == 0)
{
lean_object* v_ctors_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; lean_object* v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___f_4751_; lean_object* v___x_4752_; 
lean_del_object(v___x_4742_);
v_ctors_4745_ = lean_ctor_get(v_a_4740_, 4);
lean_inc(v_ctors_4745_);
lean_dec(v_a_4740_);
v___x_4746_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_4747_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__4));
v___x_4748_ = lean_box(0);
v___x_4749_ = lean_box(v___y_4700_);
v___x_4750_ = lean_box(v_isUnsafe_4744_);
v___f_4751_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed), 9, 4);
lean_closure_set(v___f_4751_, 0, v___x_4749_);
lean_closure_set(v___f_4751_, 1, v___x_4750_);
lean_closure_set(v___f_4751_, 2, v_ctors_4745_);
lean_closure_set(v___f_4751_, 3, v___x_4748_);
v___x_4752_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4746_, v___x_4747_, v___f_4751_, v_a_4565_, v_a_4566_, v_a_4567_, v_a_4568_);
return v___x_4752_;
}
else
{
lean_object* v___x_4753_; lean_object* v___x_4755_; 
lean_dec(v_a_4740_);
v___x_4753_ = lean_box(0);
if (v_isShared_4743_ == 0)
{
lean_ctor_set(v___x_4742_, 0, v___x_4753_);
v___x_4755_ = v___x_4742_;
goto v_reusejp_4754_;
}
else
{
lean_object* v_reuseFailAlloc_4756_; 
v_reuseFailAlloc_4756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4756_, 0, v___x_4753_);
v___x_4755_ = v_reuseFailAlloc_4756_;
goto v_reusejp_4754_;
}
v_reusejp_4754_:
{
return v___x_4755_;
}
}
}
}
else
{
lean_object* v_a_4758_; lean_object* v___x_4760_; uint8_t v_isShared_4761_; uint8_t v_isSharedCheck_4765_; 
v_a_4758_ = lean_ctor_get(v___x_4739_, 0);
v_isSharedCheck_4765_ = !lean_is_exclusive(v___x_4739_);
if (v_isSharedCheck_4765_ == 0)
{
v___x_4760_ = v___x_4739_;
v_isShared_4761_ = v_isSharedCheck_4765_;
goto v_resetjp_4759_;
}
else
{
lean_inc(v_a_4758_);
lean_dec(v___x_4739_);
v___x_4760_ = lean_box(0);
v_isShared_4761_ = v_isSharedCheck_4765_;
goto v_resetjp_4759_;
}
v_resetjp_4759_:
{
lean_object* v___x_4763_; 
if (v_isShared_4761_ == 0)
{
v___x_4763_ = v___x_4760_;
goto v_reusejp_4762_;
}
else
{
lean_object* v_reuseFailAlloc_4764_; 
v_reuseFailAlloc_4764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4764_, 0, v_a_4758_);
v___x_4763_ = v_reuseFailAlloc_4764_;
goto v_reusejp_4762_;
}
v_reusejp_4762_:
{
return v___x_4763_;
}
}
}
}
else
{
v___y_4658_ = v___y_4700_;
v___y_4659_ = v___x_4734_;
v___y_4660_ = v___x_4736_;
v___y_4661_ = v___x_4733_;
v___y_4662_ = v_options_4703_;
goto v___jp_4657_;
}
}
else
{
v___y_4658_ = v___y_4700_;
v___y_4659_ = v___x_4734_;
v___y_4660_ = v___x_4736_;
v___y_4661_ = v___x_4733_;
v___y_4662_ = v_options_4703_;
goto v___jp_4657_;
}
}
}
else
{
lean_dec_ref(v___f_4570_);
lean_dec(v_declName_4564_);
goto v___jp_4579_;
}
}
}
}
}
else
{
lean_object* v_a_4770_; lean_object* v___x_4772_; uint8_t v_isShared_4773_; uint8_t v_isSharedCheck_4777_; 
lean_dec_ref(v___x_4573_);
lean_dec_ref(v_env_4572_);
lean_dec_ref(v___f_4570_);
lean_dec(v_declName_4564_);
v_a_4770_ = lean_ctor_get(v___x_4574_, 0);
v_isSharedCheck_4777_ = !lean_is_exclusive(v___x_4574_);
if (v_isSharedCheck_4777_ == 0)
{
v___x_4772_ = v___x_4574_;
v_isShared_4773_ = v_isSharedCheck_4777_;
goto v_resetjp_4771_;
}
else
{
lean_inc(v_a_4770_);
lean_dec(v___x_4574_);
v___x_4772_ = lean_box(0);
v_isShared_4773_ = v_isSharedCheck_4777_;
goto v_resetjp_4771_;
}
v_resetjp_4771_:
{
lean_object* v___x_4775_; 
if (v_isShared_4773_ == 0)
{
v___x_4775_ = v___x_4772_;
goto v_reusejp_4774_;
}
else
{
lean_object* v_reuseFailAlloc_4776_; 
v_reuseFailAlloc_4776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4776_, 0, v_a_4770_);
v___x_4775_ = v_reuseFailAlloc_4776_;
goto v_reusejp_4774_;
}
v_reusejp_4774_:
{
return v___x_4775_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___boxed(lean_object* v_declName_4778_, lean_object* v_a_4779_, lean_object* v_a_4780_, lean_object* v_a_4781_, lean_object* v_a_4782_, lean_object* v_a_4783_){
_start:
{
lean_object* v_res_4784_; 
v_res_4784_ = l_Lean_Meta_mkInjectiveTheorems(v_declName_4778_, v_a_4779_, v_a_4780_, v_a_4781_, v_a_4782_);
lean_dec(v_a_4782_);
lean_dec_ref(v_a_4781_);
lean_dec(v_a_4780_);
lean_dec_ref(v_a_4779_);
return v_res_4784_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3(uint8_t v___y_4785_, uint8_t v___x_4786_, lean_object* v_as_4787_, lean_object* v_as_x27_4788_, lean_object* v_b_4789_, lean_object* v_a_4790_, lean_object* v___y_4791_, lean_object* v___y_4792_, lean_object* v___y_4793_, lean_object* v___y_4794_){
_start:
{
lean_object* v___x_4796_; 
v___x_4796_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___y_4785_, v___x_4786_, v_as_x27_4788_, v_b_4789_, v___y_4791_, v___y_4792_, v___y_4793_, v___y_4794_);
return v___x_4796_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___boxed(lean_object* v___y_4797_, lean_object* v___x_4798_, lean_object* v_as_4799_, lean_object* v_as_x27_4800_, lean_object* v_b_4801_, lean_object* v_a_4802_, lean_object* v___y_4803_, lean_object* v___y_4804_, lean_object* v___y_4805_, lean_object* v___y_4806_, lean_object* v___y_4807_){
_start:
{
uint8_t v___y_17512__boxed_4808_; uint8_t v___x_17513__boxed_4809_; lean_object* v_res_4810_; 
v___y_17512__boxed_4808_ = lean_unbox(v___y_4797_);
v___x_17513__boxed_4809_ = lean_unbox(v___x_4798_);
v_res_4810_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3(v___y_17512__boxed_4808_, v___x_17513__boxed_4809_, v_as_4799_, v_as_x27_4800_, v_b_4801_, v_a_4802_, v___y_4803_, v___y_4804_, v___y_4805_, v___y_4806_);
lean_dec(v___y_4806_);
lean_dec_ref(v___y_4805_);
lean_dec(v___y_4804_);
lean_dec_ref(v___y_4803_);
lean_dec(v_as_x27_4800_);
lean_dec(v_as_4799_);
return v_res_4810_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; 
v___x_4851_ = lean_unsigned_to_nat(4172903888u);
v___x_4852_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_));
v___x_4853_ = l_Lean_Name_num___override(v___x_4852_, v___x_4851_);
return v___x_4853_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; 
v___x_4855_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_));
v___x_4856_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4857_ = l_Lean_Name_str___override(v___x_4856_, v___x_4855_);
return v___x_4857_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; 
v___x_4859_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_));
v___x_4860_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4861_ = l_Lean_Name_str___override(v___x_4860_, v___x_4859_);
return v___x_4861_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; 
v___x_4862_ = lean_unsigned_to_nat(2u);
v___x_4863_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4864_ = l_Lean_Name_num___override(v___x_4863_, v___x_4862_);
return v___x_4864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4866_; uint8_t v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; 
v___x_4866_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_4867_ = 0;
v___x_4868_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4869_ = l_Lean_registerTraceClass(v___x_4866_, v___x_4867_, v___x_4868_);
return v___x_4869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2____boxed(lean_object* v_a_4870_){
_start:
{
lean_object* v_res_4871_; 
v_res_4871_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_();
return v_res_4871_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(lean_object* v_a_4872_, lean_object* v_b_4873_){
_start:
{
lean_object* v_array_4874_; lean_object* v_start_4875_; lean_object* v_stop_4876_; lean_object* v___x_4878_; uint8_t v_isShared_4879_; uint8_t v_isSharedCheck_4889_; 
v_array_4874_ = lean_ctor_get(v_a_4872_, 0);
v_start_4875_ = lean_ctor_get(v_a_4872_, 1);
v_stop_4876_ = lean_ctor_get(v_a_4872_, 2);
v_isSharedCheck_4889_ = !lean_is_exclusive(v_a_4872_);
if (v_isSharedCheck_4889_ == 0)
{
v___x_4878_ = v_a_4872_;
v_isShared_4879_ = v_isSharedCheck_4889_;
goto v_resetjp_4877_;
}
else
{
lean_inc(v_stop_4876_);
lean_inc(v_start_4875_);
lean_inc(v_array_4874_);
lean_dec(v_a_4872_);
v___x_4878_ = lean_box(0);
v_isShared_4879_ = v_isSharedCheck_4889_;
goto v_resetjp_4877_;
}
v_resetjp_4877_:
{
uint8_t v___x_4880_; 
v___x_4880_ = lean_nat_dec_lt(v_start_4875_, v_stop_4876_);
if (v___x_4880_ == 0)
{
lean_del_object(v___x_4878_);
lean_dec(v_stop_4876_);
lean_dec(v_start_4875_);
lean_dec_ref(v_array_4874_);
return v_b_4873_;
}
else
{
lean_object* v___x_4881_; lean_object* v___x_4882_; lean_object* v___x_4884_; 
v___x_4881_ = lean_unsigned_to_nat(1u);
v___x_4882_ = lean_nat_add(v_start_4875_, v___x_4881_);
lean_inc_ref(v_array_4874_);
if (v_isShared_4879_ == 0)
{
lean_ctor_set(v___x_4878_, 1, v___x_4882_);
v___x_4884_ = v___x_4878_;
goto v_reusejp_4883_;
}
else
{
lean_object* v_reuseFailAlloc_4888_; 
v_reuseFailAlloc_4888_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4888_, 0, v_array_4874_);
lean_ctor_set(v_reuseFailAlloc_4888_, 1, v___x_4882_);
lean_ctor_set(v_reuseFailAlloc_4888_, 2, v_stop_4876_);
v___x_4884_ = v_reuseFailAlloc_4888_;
goto v_reusejp_4883_;
}
v_reusejp_4883_:
{
lean_object* v___x_4885_; lean_object* v___x_4886_; 
v___x_4885_ = lean_array_fget(v_array_4874_, v_start_4875_);
lean_dec(v_start_4875_);
lean_dec_ref(v_array_4874_);
v___x_4886_ = lean_array_push(v_b_4873_, v___x_4885_);
v_a_4872_ = v___x_4884_;
v_b_4873_ = v___x_4886_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_4890_; lean_object* v___x_4891_; 
v___x_4890_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0);
v___x_4891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4891_, 0, v___x_4890_);
return v___x_4891_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_4892_; lean_object* v___x_4893_; lean_object* v___x_4894_; 
v___x_4892_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_4893_ = lean_unsigned_to_nat(0u);
v___x_4894_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_4894_, 0, v___x_4893_);
lean_ctor_set(v___x_4894_, 1, v___x_4893_);
lean_ctor_set(v___x_4894_, 2, v___x_4893_);
lean_ctor_set(v___x_4894_, 3, v___x_4893_);
lean_ctor_set(v___x_4894_, 4, v___x_4892_);
lean_ctor_set(v___x_4894_, 5, v___x_4892_);
lean_ctor_set(v___x_4894_, 6, v___x_4892_);
lean_ctor_set(v___x_4894_, 7, v___x_4892_);
lean_ctor_set(v___x_4894_, 8, v___x_4892_);
lean_ctor_set(v___x_4894_, 9, v___x_4892_);
lean_ctor_set(v___x_4894_, 10, v___x_4892_);
return v___x_4894_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_4895_; lean_object* v___x_4896_; lean_object* v___x_4897_; lean_object* v___x_4898_; 
v___x_4895_ = lean_box(1);
v___x_4896_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__2, &l_Lean_Meta_mkInjectiveTheorems___closed__2_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__2);
v___x_4897_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_4898_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4898_, 0, v___x_4897_);
lean_ctor_set(v___x_4898_, 1, v___x_4896_);
lean_ctor_set(v___x_4898_, 2, v___x_4895_);
return v___x_4898_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_4900_; lean_object* v___x_4901_; 
v___x_4900_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3));
v___x_4901_ = l_Lean_stringToMessageData(v___x_4900_);
return v___x_4901_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6(void){
_start:
{
lean_object* v___x_4903_; lean_object* v___x_4904_; 
v___x_4903_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5));
v___x_4904_ = l_Lean_stringToMessageData(v___x_4903_);
return v___x_4904_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8(void){
_start:
{
lean_object* v___x_4906_; lean_object* v___x_4907_; 
v___x_4906_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7));
v___x_4907_ = l_Lean_stringToMessageData(v___x_4906_);
return v___x_4907_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10(void){
_start:
{
lean_object* v___x_4909_; lean_object* v___x_4910_; 
v___x_4909_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9));
v___x_4910_ = l_Lean_stringToMessageData(v___x_4909_);
return v___x_4910_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12(void){
_start:
{
lean_object* v___x_4912_; lean_object* v___x_4913_; 
v___x_4912_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11));
v___x_4913_ = l_Lean_stringToMessageData(v___x_4912_);
return v___x_4913_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14(void){
_start:
{
lean_object* v___x_4915_; lean_object* v___x_4916_; 
v___x_4915_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13));
v___x_4916_ = l_Lean_stringToMessageData(v___x_4915_);
return v___x_4916_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16(void){
_start:
{
lean_object* v___x_4918_; lean_object* v___x_4919_; 
v___x_4918_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15));
v___x_4919_ = l_Lean_stringToMessageData(v___x_4918_);
return v___x_4919_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_4920_, lean_object* v_declHint_4921_, lean_object* v___y_4922_){
_start:
{
lean_object* v___x_4924_; lean_object* v___x_4925_; lean_object* v_env_4926_; uint8_t v___x_4927_; 
v___x_4924_ = lean_box(0);
v___x_4925_ = lean_st_ref_get(v___y_4922_);
v_env_4926_ = lean_ctor_get(v___x_4925_, 0);
lean_inc_ref(v_env_4926_);
lean_dec(v___x_4925_);
v___x_4927_ = l_Lean_Name_isAnonymous(v_declHint_4921_);
if (v___x_4927_ == 0)
{
uint8_t v_isExporting_4928_; 
v_isExporting_4928_ = lean_ctor_get_uint8(v_env_4926_, sizeof(void*)*8);
if (v_isExporting_4928_ == 0)
{
lean_object* v___x_4929_; 
lean_dec_ref(v_env_4926_);
lean_dec(v_declHint_4921_);
v___x_4929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4929_, 0, v_msg_4920_);
return v___x_4929_;
}
else
{
lean_object* v___x_4930_; uint8_t v___x_4931_; 
lean_inc_ref(v_env_4926_);
v___x_4930_ = l_Lean_Environment_setExporting(v_env_4926_, v___x_4927_);
lean_inc(v_declHint_4921_);
lean_inc_ref(v___x_4930_);
v___x_4931_ = l_Lean_Environment_contains(v___x_4930_, v_declHint_4921_, v_isExporting_4928_);
if (v___x_4931_ == 0)
{
lean_object* v___x_4932_; 
lean_dec_ref(v___x_4930_);
lean_dec_ref(v_env_4926_);
lean_dec(v_declHint_4921_);
v___x_4932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4932_, 0, v_msg_4920_);
return v___x_4932_;
}
else
{
lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v_c_4938_; lean_object* v___x_4939_; 
v___x_4933_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_4934_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_4935_ = l_Lean_Options_empty;
v___x_4936_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4936_, 0, v___x_4930_);
lean_ctor_set(v___x_4936_, 1, v___x_4933_);
lean_ctor_set(v___x_4936_, 2, v___x_4934_);
lean_ctor_set(v___x_4936_, 3, v___x_4935_);
lean_inc(v_declHint_4921_);
v___x_4937_ = l_Lean_MessageData_ofConstName(v_declHint_4921_, v___x_4927_);
v_c_4938_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_4938_, 0, v___x_4936_);
lean_ctor_set(v_c_4938_, 1, v___x_4937_);
v___x_4939_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4926_, v_declHint_4921_);
if (lean_obj_tag(v___x_4939_) == 0)
{
lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; lean_object* v___x_4945_; lean_object* v___x_4946_; 
lean_dec_ref(v_env_4926_);
lean_dec(v_declHint_4921_);
v___x_4940_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_4941_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4941_, 0, v___x_4940_);
lean_ctor_set(v___x_4941_, 1, v_c_4938_);
v___x_4942_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6);
v___x_4943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4943_, 0, v___x_4941_);
lean_ctor_set(v___x_4943_, 1, v___x_4942_);
v___x_4944_ = l_Lean_MessageData_note(v___x_4943_);
v___x_4945_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4945_, 0, v_msg_4920_);
lean_ctor_set(v___x_4945_, 1, v___x_4944_);
v___x_4946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4946_, 0, v___x_4945_);
return v___x_4946_;
}
else
{
lean_object* v_val_4947_; lean_object* v___x_4949_; uint8_t v_isShared_4950_; uint8_t v_isSharedCheck_4981_; 
v_val_4947_ = lean_ctor_get(v___x_4939_, 0);
v_isSharedCheck_4981_ = !lean_is_exclusive(v___x_4939_);
if (v_isSharedCheck_4981_ == 0)
{
v___x_4949_ = v___x_4939_;
v_isShared_4950_ = v_isSharedCheck_4981_;
goto v_resetjp_4948_;
}
else
{
lean_inc(v_val_4947_);
lean_dec(v___x_4939_);
v___x_4949_ = lean_box(0);
v_isShared_4950_ = v_isSharedCheck_4981_;
goto v_resetjp_4948_;
}
v_resetjp_4948_:
{
lean_object* v___x_4951_; lean_object* v___x_4952_; lean_object* v_mod_4953_; uint8_t v___x_4954_; 
v___x_4951_ = l_Lean_Environment_header(v_env_4926_);
lean_dec_ref(v_env_4926_);
v___x_4952_ = l_Lean_EnvironmentHeader_moduleNames(v___x_4951_);
v_mod_4953_ = lean_array_get(v___x_4924_, v___x_4952_, v_val_4947_);
lean_dec(v_val_4947_);
lean_dec_ref(v___x_4952_);
v___x_4954_ = l_Lean_isPrivateName(v_declHint_4921_);
lean_dec(v_declHint_4921_);
if (v___x_4954_ == 0)
{
lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; lean_object* v___x_4963_; lean_object* v___x_4964_; lean_object* v___x_4966_; 
v___x_4955_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8);
v___x_4956_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4956_, 0, v___x_4955_);
lean_ctor_set(v___x_4956_, 1, v_c_4938_);
v___x_4957_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10);
v___x_4958_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4958_, 0, v___x_4956_);
lean_ctor_set(v___x_4958_, 1, v___x_4957_);
v___x_4959_ = l_Lean_MessageData_ofName(v_mod_4953_);
v___x_4960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4960_, 0, v___x_4958_);
lean_ctor_set(v___x_4960_, 1, v___x_4959_);
v___x_4961_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12);
v___x_4962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4962_, 0, v___x_4960_);
lean_ctor_set(v___x_4962_, 1, v___x_4961_);
v___x_4963_ = l_Lean_MessageData_note(v___x_4962_);
v___x_4964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4964_, 0, v_msg_4920_);
lean_ctor_set(v___x_4964_, 1, v___x_4963_);
if (v_isShared_4950_ == 0)
{
lean_ctor_set_tag(v___x_4949_, 0);
lean_ctor_set(v___x_4949_, 0, v___x_4964_);
v___x_4966_ = v___x_4949_;
goto v_reusejp_4965_;
}
else
{
lean_object* v_reuseFailAlloc_4967_; 
v_reuseFailAlloc_4967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4967_, 0, v___x_4964_);
v___x_4966_ = v_reuseFailAlloc_4967_;
goto v_reusejp_4965_;
}
v_reusejp_4965_:
{
return v___x_4966_;
}
}
else
{
lean_object* v___x_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; lean_object* v___x_4976_; lean_object* v___x_4977_; lean_object* v___x_4979_; 
v___x_4968_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_4969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4969_, 0, v___x_4968_);
lean_ctor_set(v___x_4969_, 1, v_c_4938_);
v___x_4970_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14);
v___x_4971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4971_, 0, v___x_4969_);
lean_ctor_set(v___x_4971_, 1, v___x_4970_);
v___x_4972_ = l_Lean_MessageData_ofName(v_mod_4953_);
v___x_4973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4973_, 0, v___x_4971_);
lean_ctor_set(v___x_4973_, 1, v___x_4972_);
v___x_4974_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16);
v___x_4975_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4975_, 0, v___x_4973_);
lean_ctor_set(v___x_4975_, 1, v___x_4974_);
v___x_4976_ = l_Lean_MessageData_note(v___x_4975_);
v___x_4977_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4977_, 0, v_msg_4920_);
lean_ctor_set(v___x_4977_, 1, v___x_4976_);
if (v_isShared_4950_ == 0)
{
lean_ctor_set_tag(v___x_4949_, 0);
lean_ctor_set(v___x_4949_, 0, v___x_4977_);
v___x_4979_ = v___x_4949_;
goto v_reusejp_4978_;
}
else
{
lean_object* v_reuseFailAlloc_4980_; 
v_reuseFailAlloc_4980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4980_, 0, v___x_4977_);
v___x_4979_ = v_reuseFailAlloc_4980_;
goto v_reusejp_4978_;
}
v_reusejp_4978_:
{
return v___x_4979_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4982_; 
lean_dec_ref(v_env_4926_);
lean_dec(v_declHint_4921_);
v___x_4982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4982_, 0, v_msg_4920_);
return v___x_4982_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_4983_, lean_object* v_declHint_4984_, lean_object* v___y_4985_, lean_object* v___y_4986_){
_start:
{
lean_object* v_res_4987_; 
v_res_4987_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_4983_, v_declHint_4984_, v___y_4985_);
lean_dec(v___y_4985_);
return v_res_4987_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_msg_4988_, lean_object* v_declHint_4989_, lean_object* v___y_4990_, lean_object* v___y_4991_, lean_object* v___y_4992_, lean_object* v___y_4993_){
_start:
{
lean_object* v___x_4995_; lean_object* v_a_4996_; lean_object* v___x_4998_; uint8_t v_isShared_4999_; uint8_t v_isSharedCheck_5005_; 
v___x_4995_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_4988_, v_declHint_4989_, v___y_4993_);
v_a_4996_ = lean_ctor_get(v___x_4995_, 0);
v_isSharedCheck_5005_ = !lean_is_exclusive(v___x_4995_);
if (v_isSharedCheck_5005_ == 0)
{
v___x_4998_ = v___x_4995_;
v_isShared_4999_ = v_isSharedCheck_5005_;
goto v_resetjp_4997_;
}
else
{
lean_inc(v_a_4996_);
lean_dec(v___x_4995_);
v___x_4998_ = lean_box(0);
v_isShared_4999_ = v_isSharedCheck_5005_;
goto v_resetjp_4997_;
}
v_resetjp_4997_:
{
lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5003_; 
v___x_5000_ = l_Lean_unknownIdentifierMessageTag;
v___x_5001_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_5001_, 0, v___x_5000_);
lean_ctor_set(v___x_5001_, 1, v_a_4996_);
if (v_isShared_4999_ == 0)
{
lean_ctor_set(v___x_4998_, 0, v___x_5001_);
v___x_5003_ = v___x_4998_;
goto v_reusejp_5002_;
}
else
{
lean_object* v_reuseFailAlloc_5004_; 
v_reuseFailAlloc_5004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5004_, 0, v___x_5001_);
v___x_5003_ = v_reuseFailAlloc_5004_;
goto v_reusejp_5002_;
}
v_reusejp_5002_:
{
return v___x_5003_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v_msg_5006_, lean_object* v_declHint_5007_, lean_object* v___y_5008_, lean_object* v___y_5009_, lean_object* v___y_5010_, lean_object* v___y_5011_, lean_object* v___y_5012_){
_start:
{
lean_object* v_res_5013_; 
v_res_5013_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_5006_, v_declHint_5007_, v___y_5008_, v___y_5009_, v___y_5010_, v___y_5011_);
lean_dec(v___y_5011_);
lean_dec_ref(v___y_5010_);
lean_dec(v___y_5009_);
lean_dec_ref(v___y_5008_);
return v_res_5013_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_5014_, lean_object* v_msg_5015_, lean_object* v___y_5016_, lean_object* v___y_5017_, lean_object* v___y_5018_, lean_object* v___y_5019_){
_start:
{
lean_object* v_toCold_5021_; lean_object* v_currRecDepth_5022_; lean_object* v_ref_5023_; uint16_t v_optionFlags_5024_; uint8_t v_suppressElabErrors_5025_; uint8_t v_isRecordingDeps_5026_; lean_object* v_ref_5027_; lean_object* v___x_5028_; lean_object* v___x_5029_; 
v_toCold_5021_ = lean_ctor_get(v___y_5018_, 0);
v_currRecDepth_5022_ = lean_ctor_get(v___y_5018_, 1);
v_ref_5023_ = lean_ctor_get(v___y_5018_, 2);
v_optionFlags_5024_ = lean_ctor_get_uint16(v___y_5018_, sizeof(void*)*3);
v_suppressElabErrors_5025_ = lean_ctor_get_uint8(v___y_5018_, sizeof(void*)*3 + 2);
v_isRecordingDeps_5026_ = lean_ctor_get_uint8(v___y_5018_, sizeof(void*)*3 + 3);
v_ref_5027_ = l_Lean_replaceRef(v_ref_5014_, v_ref_5023_);
lean_inc(v_currRecDepth_5022_);
lean_inc_ref(v_toCold_5021_);
v___x_5028_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_5028_, 0, v_toCold_5021_);
lean_ctor_set(v___x_5028_, 1, v_currRecDepth_5022_);
lean_ctor_set(v___x_5028_, 2, v_ref_5027_);
lean_ctor_set_uint16(v___x_5028_, sizeof(void*)*3, v_optionFlags_5024_);
lean_ctor_set_uint8(v___x_5028_, sizeof(void*)*3 + 2, v_suppressElabErrors_5025_);
lean_ctor_set_uint8(v___x_5028_, sizeof(void*)*3 + 3, v_isRecordingDeps_5026_);
v___x_5029_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v_msg_5015_, v___y_5016_, v___y_5017_, v___x_5028_, v___y_5019_);
lean_dec_ref_known(v___x_5028_, 3);
return v___x_5029_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_5030_, lean_object* v_msg_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_, lean_object* v___y_5034_, lean_object* v___y_5035_, lean_object* v___y_5036_){
_start:
{
lean_object* v_res_5037_; 
v_res_5037_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5030_, v_msg_5031_, v___y_5032_, v___y_5033_, v___y_5034_, v___y_5035_);
lean_dec(v___y_5035_);
lean_dec_ref(v___y_5034_);
lean_dec(v___y_5033_);
lean_dec_ref(v___y_5032_);
lean_dec(v_ref_5030_);
return v_res_5037_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_5038_, lean_object* v_msg_5039_, lean_object* v_declHint_5040_, lean_object* v___y_5041_, lean_object* v___y_5042_, lean_object* v___y_5043_, lean_object* v___y_5044_){
_start:
{
lean_object* v___x_5046_; lean_object* v_a_5047_; lean_object* v___x_5048_; 
v___x_5046_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_5039_, v_declHint_5040_, v___y_5041_, v___y_5042_, v___y_5043_, v___y_5044_);
v_a_5047_ = lean_ctor_get(v___x_5046_, 0);
lean_inc(v_a_5047_);
lean_dec_ref(v___x_5046_);
v___x_5048_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5038_, v_a_5047_, v___y_5041_, v___y_5042_, v___y_5043_, v___y_5044_);
return v___x_5048_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_5049_, lean_object* v_msg_5050_, lean_object* v_declHint_5051_, lean_object* v___y_5052_, lean_object* v___y_5053_, lean_object* v___y_5054_, lean_object* v___y_5055_, lean_object* v___y_5056_){
_start:
{
lean_object* v_res_5057_; 
v_res_5057_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5049_, v_msg_5050_, v_declHint_5051_, v___y_5052_, v___y_5053_, v___y_5054_, v___y_5055_);
lean_dec(v___y_5055_);
lean_dec_ref(v___y_5054_);
lean_dec(v___y_5053_);
lean_dec_ref(v___y_5052_);
lean_dec(v_ref_5049_);
return v_res_5057_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_5059_; lean_object* v___x_5060_; 
v___x_5059_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_5060_ = l_Lean_stringToMessageData(v___x_5059_);
return v___x_5060_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_5061_, lean_object* v_constName_5062_, lean_object* v___y_5063_, lean_object* v___y_5064_, lean_object* v___y_5065_, lean_object* v___y_5066_){
_start:
{
lean_object* v___x_5068_; uint8_t v___x_5069_; lean_object* v___x_5070_; lean_object* v___x_5071_; lean_object* v___x_5072_; lean_object* v___x_5073_; lean_object* v___x_5074_; 
v___x_5068_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_5069_ = 0;
lean_inc(v_constName_5062_);
v___x_5070_ = l_Lean_MessageData_ofConstName(v_constName_5062_, v___x_5069_);
v___x_5071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5071_, 0, v___x_5068_);
lean_ctor_set(v___x_5071_, 1, v___x_5070_);
v___x_5072_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_5073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5073_, 0, v___x_5071_);
lean_ctor_set(v___x_5073_, 1, v___x_5072_);
v___x_5074_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5061_, v___x_5073_, v_constName_5062_, v___y_5063_, v___y_5064_, v___y_5065_, v___y_5066_);
return v___x_5074_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_5075_, lean_object* v_constName_5076_, lean_object* v___y_5077_, lean_object* v___y_5078_, lean_object* v___y_5079_, lean_object* v___y_5080_, lean_object* v___y_5081_){
_start:
{
lean_object* v_res_5082_; 
v_res_5082_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(v_ref_5075_, v_constName_5076_, v___y_5077_, v___y_5078_, v___y_5079_, v___y_5080_);
lean_dec(v___y_5080_);
lean_dec_ref(v___y_5079_);
lean_dec(v___y_5078_);
lean_dec_ref(v___y_5077_);
lean_dec(v_ref_5075_);
return v_res_5082_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(lean_object* v_constName_5083_, lean_object* v___y_5084_, lean_object* v___y_5085_, lean_object* v___y_5086_, lean_object* v___y_5087_){
_start:
{
lean_object* v_ref_5089_; lean_object* v___x_5090_; 
v_ref_5089_ = lean_ctor_get(v___y_5086_, 2);
v___x_5090_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(v_ref_5089_, v_constName_5083_, v___y_5084_, v___y_5085_, v___y_5086_, v___y_5087_);
return v___x_5090_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_constName_5091_, lean_object* v___y_5092_, lean_object* v___y_5093_, lean_object* v___y_5094_, lean_object* v___y_5095_, lean_object* v___y_5096_){
_start:
{
lean_object* v_res_5097_; 
v_res_5097_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(v_constName_5091_, v___y_5092_, v___y_5093_, v___y_5094_, v___y_5095_);
lean_dec(v___y_5095_);
lean_dec_ref(v___y_5094_);
lean_dec(v___y_5093_);
lean_dec_ref(v___y_5092_);
return v_res_5097_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(lean_object* v_constName_5098_, lean_object* v___y_5099_, lean_object* v___y_5100_, lean_object* v___y_5101_, lean_object* v___y_5102_){
_start:
{
lean_object* v___x_5104_; lean_object* v_env_5105_; uint8_t v___x_5106_; lean_object* v___x_5107_; 
v___x_5104_ = lean_st_ref_get(v___y_5102_);
v_env_5105_ = lean_ctor_get(v___x_5104_, 0);
lean_inc_ref(v_env_5105_);
lean_dec(v___x_5104_);
v___x_5106_ = 0;
lean_inc(v_constName_5098_);
v___x_5107_ = l_Lean_Environment_find_x3f(v_env_5105_, v_constName_5098_, v___x_5106_);
if (lean_obj_tag(v___x_5107_) == 0)
{
lean_object* v___x_5108_; 
v___x_5108_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(v_constName_5098_, v___y_5099_, v___y_5100_, v___y_5101_, v___y_5102_);
return v___x_5108_;
}
else
{
lean_object* v_val_5109_; lean_object* v___x_5111_; uint8_t v_isShared_5112_; uint8_t v_isSharedCheck_5116_; 
lean_dec(v_constName_5098_);
v_val_5109_ = lean_ctor_get(v___x_5107_, 0);
v_isSharedCheck_5116_ = !lean_is_exclusive(v___x_5107_);
if (v_isSharedCheck_5116_ == 0)
{
v___x_5111_ = v___x_5107_;
v_isShared_5112_ = v_isSharedCheck_5116_;
goto v_resetjp_5110_;
}
else
{
lean_inc(v_val_5109_);
lean_dec(v___x_5107_);
v___x_5111_ = lean_box(0);
v_isShared_5112_ = v_isSharedCheck_5116_;
goto v_resetjp_5110_;
}
v_resetjp_5110_:
{
lean_object* v___x_5114_; 
if (v_isShared_5112_ == 0)
{
lean_ctor_set_tag(v___x_5111_, 0);
v___x_5114_ = v___x_5111_;
goto v_reusejp_5113_;
}
else
{
lean_object* v_reuseFailAlloc_5115_; 
v_reuseFailAlloc_5115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5115_, 0, v_val_5109_);
v___x_5114_ = v_reuseFailAlloc_5115_;
goto v_reusejp_5113_;
}
v_reusejp_5113_:
{
return v___x_5114_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0___boxed(lean_object* v_constName_5117_, lean_object* v___y_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_, lean_object* v___y_5122_){
_start:
{
lean_object* v_res_5123_; 
v_res_5123_ = l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(v_constName_5117_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_);
lean_dec(v___y_5121_);
lean_dec_ref(v___y_5120_);
lean_dec(v___y_5119_);
lean_dec_ref(v___y_5118_);
return v_res_5123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(lean_object* v_x_5126_, lean_object* v_x_5127_, lean_object* v_x_5128_, lean_object* v___y_5129_, lean_object* v___y_5130_, lean_object* v___y_5131_, lean_object* v___y_5132_){
_start:
{
if (lean_obj_tag(v_x_5126_) == 5)
{
lean_object* v_fn_5134_; lean_object* v_arg_5135_; lean_object* v___x_5136_; lean_object* v___x_5137_; lean_object* v___x_5138_; 
v_fn_5134_ = lean_ctor_get(v_x_5126_, 0);
lean_inc_ref(v_fn_5134_);
v_arg_5135_ = lean_ctor_get(v_x_5126_, 1);
lean_inc_ref(v_arg_5135_);
lean_dec_ref_known(v_x_5126_, 2);
v___x_5136_ = lean_array_set(v_x_5127_, v_x_5128_, v_arg_5135_);
v___x_5137_ = lean_unsigned_to_nat(1u);
v___x_5138_ = lean_nat_sub(v_x_5128_, v___x_5137_);
lean_dec(v_x_5128_);
v_x_5126_ = v_fn_5134_;
v_x_5127_ = v___x_5136_;
v_x_5128_ = v___x_5138_;
goto _start;
}
else
{
lean_dec(v_x_5128_);
if (lean_obj_tag(v_x_5126_) == 4)
{
lean_object* v_declName_5140_; lean_object* v___x_5141_; 
v_declName_5140_ = lean_ctor_get(v_x_5126_, 0);
lean_inc(v_declName_5140_);
lean_dec_ref_known(v_x_5126_, 2);
v___x_5141_ = l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(v_declName_5140_, v___y_5129_, v___y_5130_, v___y_5131_, v___y_5132_);
if (lean_obj_tag(v___x_5141_) == 0)
{
lean_object* v_a_5142_; lean_object* v___x_5144_; uint8_t v_isShared_5145_; uint8_t v_isSharedCheck_5173_; 
v_a_5142_ = lean_ctor_get(v___x_5141_, 0);
v_isSharedCheck_5173_ = !lean_is_exclusive(v___x_5141_);
if (v_isSharedCheck_5173_ == 0)
{
v___x_5144_ = v___x_5141_;
v_isShared_5145_ = v_isSharedCheck_5173_;
goto v_resetjp_5143_;
}
else
{
lean_inc(v_a_5142_);
lean_dec(v___x_5141_);
v___x_5144_ = lean_box(0);
v_isShared_5145_ = v_isSharedCheck_5173_;
goto v_resetjp_5143_;
}
v_resetjp_5143_:
{
lean_object* v_lower_5147_; lean_object* v_upper_5148_; 
if (lean_obj_tag(v_a_5142_) == 5)
{
lean_object* v_val_5156_; lean_object* v___x_5158_; uint8_t v_isShared_5159_; uint8_t v_isSharedCheck_5170_; 
v_val_5156_ = lean_ctor_get(v_a_5142_, 0);
v_isSharedCheck_5170_ = !lean_is_exclusive(v_a_5142_);
if (v_isSharedCheck_5170_ == 0)
{
v___x_5158_ = v_a_5142_;
v_isShared_5159_ = v_isSharedCheck_5170_;
goto v_resetjp_5157_;
}
else
{
lean_inc(v_val_5156_);
lean_dec(v_a_5142_);
v___x_5158_ = lean_box(0);
v_isShared_5159_ = v_isSharedCheck_5170_;
goto v_resetjp_5157_;
}
v_resetjp_5157_:
{
lean_object* v_numParams_5160_; lean_object* v_numIndices_5161_; lean_object* v___x_5162_; uint8_t v___x_5163_; 
v_numParams_5160_ = lean_ctor_get(v_val_5156_, 1);
lean_inc(v_numParams_5160_);
v_numIndices_5161_ = lean_ctor_get(v_val_5156_, 2);
lean_inc(v_numIndices_5161_);
lean_dec_ref(v_val_5156_);
v___x_5162_ = lean_unsigned_to_nat(0u);
v___x_5163_ = lean_nat_dec_eq(v_numIndices_5161_, v___x_5162_);
lean_dec(v_numIndices_5161_);
if (v___x_5163_ == 0)
{
lean_object* v___x_5164_; uint8_t v___x_5165_; 
lean_del_object(v___x_5158_);
v___x_5164_ = lean_array_get_size(v_x_5127_);
v___x_5165_ = lean_nat_dec_le(v_numParams_5160_, v___x_5162_);
if (v___x_5165_ == 0)
{
v_lower_5147_ = v_numParams_5160_;
v_upper_5148_ = v___x_5164_;
goto v___jp_5146_;
}
else
{
lean_dec(v_numParams_5160_);
v_lower_5147_ = v___x_5162_;
v_upper_5148_ = v___x_5164_;
goto v___jp_5146_;
}
}
else
{
lean_object* v___x_5166_; lean_object* v___x_5168_; 
lean_dec(v_numParams_5160_);
lean_del_object(v___x_5144_);
lean_dec_ref(v_x_5127_);
v___x_5166_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2___closed__0));
if (v_isShared_5159_ == 0)
{
lean_ctor_set_tag(v___x_5158_, 0);
lean_ctor_set(v___x_5158_, 0, v___x_5166_);
v___x_5168_ = v___x_5158_;
goto v_reusejp_5167_;
}
else
{
lean_object* v_reuseFailAlloc_5169_; 
v_reuseFailAlloc_5169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5169_, 0, v___x_5166_);
v___x_5168_ = v_reuseFailAlloc_5169_;
goto v_reusejp_5167_;
}
v_reusejp_5167_:
{
return v___x_5168_;
}
}
}
}
else
{
lean_object* v___x_5171_; lean_object* v___x_5172_; 
lean_del_object(v___x_5144_);
lean_dec(v_a_5142_);
lean_dec_ref(v_x_5127_);
v___x_5171_ = lean_box(0);
v___x_5172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5172_, 0, v___x_5171_);
return v___x_5172_;
}
v___jp_5146_:
{
lean_object* v___x_5149_; lean_object* v___x_5150_; lean_object* v___x_5151_; lean_object* v___x_5152_; lean_object* v___x_5154_; 
v___x_5149_ = l_Array_toSubarray___redArg(v_x_5127_, v_lower_5147_, v_upper_5148_);
v___x_5150_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_5151_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(v___x_5149_, v___x_5150_);
v___x_5152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5152_, 0, v___x_5151_);
if (v_isShared_5145_ == 0)
{
lean_ctor_set(v___x_5144_, 0, v___x_5152_);
v___x_5154_ = v___x_5144_;
goto v_reusejp_5153_;
}
else
{
lean_object* v_reuseFailAlloc_5155_; 
v_reuseFailAlloc_5155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5155_, 0, v___x_5152_);
v___x_5154_ = v_reuseFailAlloc_5155_;
goto v_reusejp_5153_;
}
v_reusejp_5153_:
{
return v___x_5154_;
}
}
}
}
else
{
lean_object* v_a_5174_; lean_object* v___x_5176_; uint8_t v_isShared_5177_; uint8_t v_isSharedCheck_5181_; 
lean_dec_ref(v_x_5127_);
v_a_5174_ = lean_ctor_get(v___x_5141_, 0);
v_isSharedCheck_5181_ = !lean_is_exclusive(v___x_5141_);
if (v_isSharedCheck_5181_ == 0)
{
v___x_5176_ = v___x_5141_;
v_isShared_5177_ = v_isSharedCheck_5181_;
goto v_resetjp_5175_;
}
else
{
lean_inc(v_a_5174_);
lean_dec(v___x_5141_);
v___x_5176_ = lean_box(0);
v_isShared_5177_ = v_isSharedCheck_5181_;
goto v_resetjp_5175_;
}
v_resetjp_5175_:
{
lean_object* v___x_5179_; 
if (v_isShared_5177_ == 0)
{
v___x_5179_ = v___x_5176_;
goto v_reusejp_5178_;
}
else
{
lean_object* v_reuseFailAlloc_5180_; 
v_reuseFailAlloc_5180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5180_, 0, v_a_5174_);
v___x_5179_ = v_reuseFailAlloc_5180_;
goto v_reusejp_5178_;
}
v_reusejp_5178_:
{
return v___x_5179_;
}
}
}
}
else
{
lean_object* v___x_5182_; lean_object* v___x_5183_; 
lean_dec_ref(v_x_5127_);
lean_dec_ref(v_x_5126_);
v___x_5182_ = lean_box(0);
v___x_5183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5183_, 0, v___x_5182_);
return v___x_5183_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2___boxed(lean_object* v_x_5184_, lean_object* v_x_5185_, lean_object* v_x_5186_, lean_object* v___y_5187_, lean_object* v___y_5188_, lean_object* v___y_5189_, lean_object* v___y_5190_, lean_object* v___y_5191_){
_start:
{
lean_object* v_res_5192_; 
v_res_5192_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(v_x_5184_, v_x_5185_, v_x_5186_, v___y_5187_, v___y_5188_, v___y_5189_, v___y_5190_);
lean_dec(v___y_5190_);
lean_dec_ref(v___y_5189_);
lean_dec(v___y_5188_);
lean_dec_ref(v___y_5187_);
return v_res_5192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorAppIndices_x3f(lean_object* v_ctorApp_5193_, lean_object* v_a_5194_, lean_object* v_a_5195_, lean_object* v_a_5196_, lean_object* v_a_5197_){
_start:
{
lean_object* v___x_5199_; 
lean_inc(v_a_5197_);
lean_inc_ref(v_a_5196_);
lean_inc(v_a_5195_);
lean_inc_ref(v_a_5194_);
v___x_5199_ = lean_infer_type(v_ctorApp_5193_, v_a_5194_, v_a_5195_, v_a_5196_, v_a_5197_);
if (lean_obj_tag(v___x_5199_) == 0)
{
lean_object* v_a_5200_; lean_object* v___x_5201_; 
v_a_5200_ = lean_ctor_get(v___x_5199_, 0);
lean_inc(v_a_5200_);
lean_dec_ref_known(v___x_5199_, 1);
v___x_5201_ = l_Lean_Meta_whnfD(v_a_5200_, v_a_5194_, v_a_5195_, v_a_5196_, v_a_5197_);
if (lean_obj_tag(v___x_5201_) == 0)
{
lean_object* v_a_5202_; lean_object* v_dummy_5203_; lean_object* v_nargs_5204_; lean_object* v___x_5205_; lean_object* v___x_5206_; lean_object* v___x_5207_; lean_object* v___x_5208_; 
v_a_5202_ = lean_ctor_get(v___x_5201_, 0);
lean_inc(v_a_5202_);
lean_dec_ref_known(v___x_5201_, 1);
v_dummy_5203_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0);
v_nargs_5204_ = l_Lean_Expr_getAppNumArgs(v_a_5202_);
lean_inc(v_nargs_5204_);
v___x_5205_ = lean_mk_array(v_nargs_5204_, v_dummy_5203_);
v___x_5206_ = lean_unsigned_to_nat(1u);
v___x_5207_ = lean_nat_sub(v_nargs_5204_, v___x_5206_);
lean_dec(v_nargs_5204_);
v___x_5208_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(v_a_5202_, v___x_5205_, v___x_5207_, v_a_5194_, v_a_5195_, v_a_5196_, v_a_5197_);
return v___x_5208_;
}
else
{
lean_object* v_a_5209_; lean_object* v___x_5211_; uint8_t v_isShared_5212_; uint8_t v_isSharedCheck_5216_; 
v_a_5209_ = lean_ctor_get(v___x_5201_, 0);
v_isSharedCheck_5216_ = !lean_is_exclusive(v___x_5201_);
if (v_isSharedCheck_5216_ == 0)
{
v___x_5211_ = v___x_5201_;
v_isShared_5212_ = v_isSharedCheck_5216_;
goto v_resetjp_5210_;
}
else
{
lean_inc(v_a_5209_);
lean_dec(v___x_5201_);
v___x_5211_ = lean_box(0);
v_isShared_5212_ = v_isSharedCheck_5216_;
goto v_resetjp_5210_;
}
v_resetjp_5210_:
{
lean_object* v___x_5214_; 
if (v_isShared_5212_ == 0)
{
v___x_5214_ = v___x_5211_;
goto v_reusejp_5213_;
}
else
{
lean_object* v_reuseFailAlloc_5215_; 
v_reuseFailAlloc_5215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5215_, 0, v_a_5209_);
v___x_5214_ = v_reuseFailAlloc_5215_;
goto v_reusejp_5213_;
}
v_reusejp_5213_:
{
return v___x_5214_;
}
}
}
}
else
{
lean_object* v_a_5217_; lean_object* v___x_5219_; uint8_t v_isShared_5220_; uint8_t v_isSharedCheck_5224_; 
v_a_5217_ = lean_ctor_get(v___x_5199_, 0);
v_isSharedCheck_5224_ = !lean_is_exclusive(v___x_5199_);
if (v_isSharedCheck_5224_ == 0)
{
v___x_5219_ = v___x_5199_;
v_isShared_5220_ = v_isSharedCheck_5224_;
goto v_resetjp_5218_;
}
else
{
lean_inc(v_a_5217_);
lean_dec(v___x_5199_);
v___x_5219_ = lean_box(0);
v_isShared_5220_ = v_isSharedCheck_5224_;
goto v_resetjp_5218_;
}
v_resetjp_5218_:
{
lean_object* v___x_5222_; 
if (v_isShared_5220_ == 0)
{
v___x_5222_ = v___x_5219_;
goto v_reusejp_5221_;
}
else
{
lean_object* v_reuseFailAlloc_5223_; 
v_reuseFailAlloc_5223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5223_, 0, v_a_5217_);
v___x_5222_ = v_reuseFailAlloc_5223_;
goto v_reusejp_5221_;
}
v_reusejp_5221_:
{
return v___x_5222_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorAppIndices_x3f___boxed(lean_object* v_ctorApp_5225_, lean_object* v_a_5226_, lean_object* v_a_5227_, lean_object* v_a_5228_, lean_object* v_a_5229_, lean_object* v_a_5230_){
_start:
{
lean_object* v_res_5231_; 
v_res_5231_ = l_Lean_Meta_getCtorAppIndices_x3f(v_ctorApp_5225_, v_a_5226_, v_a_5227_, v_a_5228_, v_a_5229_);
lean_dec(v_a_5229_);
lean_dec_ref(v_a_5228_);
lean_dec(v_a_5227_);
lean_dec_ref(v_a_5226_);
return v_res_5231_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1(lean_object* v_inst_5232_, lean_object* v_R_5233_, lean_object* v_a_5234_, lean_object* v_b_5235_){
_start:
{
lean_object* v___x_5236_; 
v___x_5236_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(v_a_5234_, v_b_5235_);
return v___x_5236_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0(lean_object* v_00_u03b1_5237_, lean_object* v_constName_5238_, lean_object* v___y_5239_, lean_object* v___y_5240_, lean_object* v___y_5241_, lean_object* v___y_5242_){
_start:
{
lean_object* v___x_5244_; 
v___x_5244_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(v_constName_5238_, v___y_5239_, v___y_5240_, v___y_5241_, v___y_5242_);
return v___x_5244_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b1_5245_, lean_object* v_constName_5246_, lean_object* v___y_5247_, lean_object* v___y_5248_, lean_object* v___y_5249_, lean_object* v___y_5250_, lean_object* v___y_5251_){
_start:
{
lean_object* v_res_5252_; 
v_res_5252_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0(v_00_u03b1_5245_, v_constName_5246_, v___y_5247_, v___y_5248_, v___y_5249_, v___y_5250_);
lean_dec(v___y_5250_);
lean_dec_ref(v___y_5249_);
lean_dec(v___y_5248_);
lean_dec_ref(v___y_5247_);
return v_res_5252_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_5253_, lean_object* v_ref_5254_, lean_object* v_constName_5255_, lean_object* v___y_5256_, lean_object* v___y_5257_, lean_object* v___y_5258_, lean_object* v___y_5259_){
_start:
{
lean_object* v___x_5261_; 
v___x_5261_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(v_ref_5254_, v_constName_5255_, v___y_5256_, v___y_5257_, v___y_5258_, v___y_5259_);
return v___x_5261_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_5262_, lean_object* v_ref_5263_, lean_object* v_constName_5264_, lean_object* v___y_5265_, lean_object* v___y_5266_, lean_object* v___y_5267_, lean_object* v___y_5268_, lean_object* v___y_5269_){
_start:
{
lean_object* v_res_5270_; 
v_res_5270_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1(v_00_u03b1_5262_, v_ref_5263_, v_constName_5264_, v___y_5265_, v___y_5266_, v___y_5267_, v___y_5268_);
lean_dec(v___y_5268_);
lean_dec_ref(v___y_5267_);
lean_dec(v___y_5266_);
lean_dec_ref(v___y_5265_);
lean_dec(v_ref_5263_);
return v_res_5270_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_5271_, lean_object* v_ref_5272_, lean_object* v_msg_5273_, lean_object* v_declHint_5274_, lean_object* v___y_5275_, lean_object* v___y_5276_, lean_object* v___y_5277_, lean_object* v___y_5278_){
_start:
{
lean_object* v___x_5280_; 
v___x_5280_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5272_, v_msg_5273_, v_declHint_5274_, v___y_5275_, v___y_5276_, v___y_5277_, v___y_5278_);
return v___x_5280_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_5281_, lean_object* v_ref_5282_, lean_object* v_msg_5283_, lean_object* v_declHint_5284_, lean_object* v___y_5285_, lean_object* v___y_5286_, lean_object* v___y_5287_, lean_object* v___y_5288_, lean_object* v___y_5289_){
_start:
{
lean_object* v_res_5290_; 
v_res_5290_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_5281_, v_ref_5282_, v_msg_5283_, v_declHint_5284_, v___y_5285_, v___y_5286_, v___y_5287_, v___y_5288_);
lean_dec(v___y_5288_);
lean_dec_ref(v___y_5287_);
lean_dec(v___y_5286_);
lean_dec_ref(v___y_5285_);
lean_dec(v_ref_5282_);
return v_res_5290_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_msg_5291_, lean_object* v_declHint_5292_, lean_object* v___y_5293_, lean_object* v___y_5294_, lean_object* v___y_5295_, lean_object* v___y_5296_){
_start:
{
lean_object* v___x_5298_; 
v___x_5298_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_5291_, v_declHint_5292_, v___y_5296_);
return v___x_5298_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_5299_, lean_object* v_declHint_5300_, lean_object* v___y_5301_, lean_object* v___y_5302_, lean_object* v___y_5303_, lean_object* v___y_5304_, lean_object* v___y_5305_){
_start:
{
lean_object* v_res_5306_; 
v_res_5306_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_5299_, v_declHint_5300_, v___y_5301_, v___y_5302_, v___y_5303_, v___y_5304_);
lean_dec(v___y_5304_);
lean_dec_ref(v___y_5303_);
lean_dec(v___y_5302_);
lean_dec_ref(v___y_5301_);
return v_res_5306_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_5307_, lean_object* v_ref_5308_, lean_object* v_msg_5309_, lean_object* v___y_5310_, lean_object* v___y_5311_, lean_object* v___y_5312_, lean_object* v___y_5313_){
_start:
{
lean_object* v___x_5315_; 
v___x_5315_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5308_, v_msg_5309_, v___y_5310_, v___y_5311_, v___y_5312_, v___y_5313_);
return v___x_5315_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_5316_, lean_object* v_ref_5317_, lean_object* v_msg_5318_, lean_object* v___y_5319_, lean_object* v___y_5320_, lean_object* v___y_5321_, lean_object* v___y_5322_, lean_object* v___y_5323_){
_start:
{
lean_object* v_res_5324_; 
v_res_5324_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_5316_, v_ref_5317_, v_msg_5318_, v___y_5319_, v___y_5320_, v___y_5321_, v___y_5322_);
lean_dec(v___y_5322_);
lean_dec_ref(v___y_5321_);
lean_dec(v___y_5320_);
lean_dec_ref(v___y_5319_);
lean_dec(v_ref_5317_);
return v_res_5324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0___boxed(lean_object* v_i_5325_, lean_object* v_body_5326_, lean_object* v_args2_5327_, lean_object* v_ctorVal_5328_, lean_object* v_args1_5329_, lean_object* v_k_5330_, lean_object* v_arg2_5331_, lean_object* v___y_5332_, lean_object* v___y_5333_, lean_object* v___y_5334_, lean_object* v___y_5335_, lean_object* v___y_5336_){
_start:
{
lean_object* v_res_5337_; 
v_res_5337_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0(v_i_5325_, v_body_5326_, v_args2_5327_, v_ctorVal_5328_, v_args1_5329_, v_k_5330_, v_arg2_5331_, v___y_5332_, v___y_5333_, v___y_5334_, v___y_5335_);
lean_dec(v___y_5335_);
lean_dec_ref(v___y_5334_);
lean_dec(v___y_5333_);
lean_dec_ref(v___y_5332_);
lean_dec_ref(v_body_5326_);
lean_dec(v_i_5325_);
return v_res_5337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(lean_object* v_ctorVal_5338_, lean_object* v_args1_5339_, lean_object* v_k_5340_, lean_object* v_i_5341_, lean_object* v_type_5342_, lean_object* v_args2_5343_, lean_object* v_a_5344_, lean_object* v_a_5345_, lean_object* v_a_5346_, lean_object* v_a_5347_){
_start:
{
lean_object* v___x_5349_; uint8_t v___x_5350_; 
v___x_5349_ = lean_array_get_size(v_args1_5339_);
v___x_5350_ = lean_nat_dec_lt(v_i_5341_, v___x_5349_);
if (v___x_5350_ == 0)
{
lean_object* v___x_5351_; 
lean_dec_ref(v_type_5342_);
lean_dec(v_i_5341_);
lean_dec_ref(v_args1_5339_);
lean_dec_ref(v_ctorVal_5338_);
lean_inc(v_a_5347_);
lean_inc_ref(v_a_5346_);
lean_inc(v_a_5345_);
lean_inc_ref(v_a_5344_);
v___x_5351_ = lean_apply_6(v_k_5340_, v_args2_5343_, v_a_5344_, v_a_5345_, v_a_5346_, v_a_5347_, lean_box(0));
return v___x_5351_;
}
else
{
lean_object* v___x_5352_; 
lean_inc(v_a_5347_);
lean_inc_ref(v_a_5346_);
lean_inc(v_a_5345_);
lean_inc_ref(v_a_5344_);
v___x_5352_ = lean_whnf(v_type_5342_, v_a_5344_, v_a_5345_, v_a_5346_, v_a_5347_);
if (lean_obj_tag(v___x_5352_) == 0)
{
lean_object* v_a_5353_; 
v_a_5353_ = lean_ctor_get(v___x_5352_, 0);
lean_inc(v_a_5353_);
lean_dec_ref_known(v___x_5352_, 1);
if (lean_obj_tag(v_a_5353_) == 7)
{
lean_object* v_binderName_5354_; lean_object* v_binderType_5355_; lean_object* v_body_5356_; lean_object* v___f_5357_; uint8_t v___x_5358_; uint8_t v___x_5359_; lean_object* v___x_5360_; 
v_binderName_5354_ = lean_ctor_get(v_a_5353_, 0);
lean_inc(v_binderName_5354_);
v_binderType_5355_ = lean_ctor_get(v_a_5353_, 1);
lean_inc_ref(v_binderType_5355_);
v_body_5356_ = lean_ctor_get(v_a_5353_, 2);
lean_inc_ref(v_body_5356_);
lean_dec_ref_known(v_a_5353_, 3);
v___f_5357_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0___boxed), 12, 6);
lean_closure_set(v___f_5357_, 0, v_i_5341_);
lean_closure_set(v___f_5357_, 1, v_body_5356_);
lean_closure_set(v___f_5357_, 2, v_args2_5343_);
lean_closure_set(v___f_5357_, 3, v_ctorVal_5338_);
lean_closure_set(v___f_5357_, 4, v_args1_5339_);
lean_closure_set(v___f_5357_, 5, v_k_5340_);
v___x_5358_ = 1;
v___x_5359_ = 0;
v___x_5360_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_binderName_5354_, v___x_5358_, v_binderType_5355_, v___f_5357_, v___x_5359_, v_a_5344_, v_a_5345_, v_a_5346_, v_a_5347_);
return v___x_5360_;
}
else
{
lean_object* v_toConstantVal_5361_; lean_object* v_name_5362_; lean_object* v___x_5363_; lean_object* v___x_5364_; lean_object* v___x_5365_; lean_object* v___x_5366_; lean_object* v___x_5367_; lean_object* v___x_5368_; 
lean_dec(v_a_5353_);
lean_dec_ref(v_args2_5343_);
lean_dec(v_i_5341_);
lean_dec_ref(v_k_5340_);
lean_dec_ref(v_args1_5339_);
v_toConstantVal_5361_ = lean_ctor_get(v_ctorVal_5338_, 0);
lean_inc_ref(v_toConstantVal_5361_);
lean_dec_ref(v_ctorVal_5338_);
v_name_5362_ = lean_ctor_get(v_toConstantVal_5361_, 0);
lean_inc(v_name_5362_);
lean_dec_ref(v_toConstantVal_5361_);
v___x_5363_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1);
v___x_5364_ = l_Lean_MessageData_ofName(v_name_5362_);
v___x_5365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5365_, 0, v___x_5363_);
lean_ctor_set(v___x_5365_, 1, v___x_5364_);
v___x_5366_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_5367_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5367_, 0, v___x_5365_);
lean_ctor_set(v___x_5367_, 1, v___x_5366_);
v___x_5368_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_5367_, v_a_5344_, v_a_5345_, v_a_5346_, v_a_5347_);
return v___x_5368_;
}
}
else
{
lean_object* v_a_5369_; lean_object* v___x_5371_; uint8_t v_isShared_5372_; uint8_t v_isSharedCheck_5376_; 
lean_dec_ref(v_args2_5343_);
lean_dec(v_i_5341_);
lean_dec_ref(v_k_5340_);
lean_dec_ref(v_args1_5339_);
lean_dec_ref(v_ctorVal_5338_);
v_a_5369_ = lean_ctor_get(v___x_5352_, 0);
v_isSharedCheck_5376_ = !lean_is_exclusive(v___x_5352_);
if (v_isSharedCheck_5376_ == 0)
{
v___x_5371_ = v___x_5352_;
v_isShared_5372_ = v_isSharedCheck_5376_;
goto v_resetjp_5370_;
}
else
{
lean_inc(v_a_5369_);
lean_dec(v___x_5352_);
v___x_5371_ = lean_box(0);
v_isShared_5372_ = v_isSharedCheck_5376_;
goto v_resetjp_5370_;
}
v_resetjp_5370_:
{
lean_object* v___x_5374_; 
if (v_isShared_5372_ == 0)
{
v___x_5374_ = v___x_5371_;
goto v_reusejp_5373_;
}
else
{
lean_object* v_reuseFailAlloc_5375_; 
v_reuseFailAlloc_5375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5375_, 0, v_a_5369_);
v___x_5374_ = v_reuseFailAlloc_5375_;
goto v_reusejp_5373_;
}
v_reusejp_5373_:
{
return v___x_5374_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0(lean_object* v_i_5377_, lean_object* v_body_5378_, lean_object* v_args2_5379_, lean_object* v_ctorVal_5380_, lean_object* v_args1_5381_, lean_object* v_k_5382_, lean_object* v_arg2_5383_, lean_object* v___y_5384_, lean_object* v___y_5385_, lean_object* v___y_5386_, lean_object* v___y_5387_){
_start:
{
lean_object* v___x_5389_; lean_object* v___x_5390_; lean_object* v___x_5391_; lean_object* v___x_5392_; lean_object* v___x_5393_; 
v___x_5389_ = lean_unsigned_to_nat(1u);
v___x_5390_ = lean_nat_add(v_i_5377_, v___x_5389_);
v___x_5391_ = lean_expr_instantiate1(v_body_5378_, v_arg2_5383_);
v___x_5392_ = lean_array_push(v_args2_5379_, v_arg2_5383_);
v___x_5393_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(v_ctorVal_5380_, v_args1_5381_, v_k_5382_, v___x_5390_, v___x_5391_, v___x_5392_, v___y_5384_, v___y_5385_, v___y_5386_, v___y_5387_);
return v___x_5393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___boxed(lean_object* v_ctorVal_5394_, lean_object* v_args1_5395_, lean_object* v_k_5396_, lean_object* v_i_5397_, lean_object* v_type_5398_, lean_object* v_args2_5399_, lean_object* v_a_5400_, lean_object* v_a_5401_, lean_object* v_a_5402_, lean_object* v_a_5403_, lean_object* v_a_5404_){
_start:
{
lean_object* v_res_5405_; 
v_res_5405_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(v_ctorVal_5394_, v_args1_5395_, v_k_5396_, v_i_5397_, v_type_5398_, v_args2_5399_, v_a_5400_, v_a_5401_, v_a_5402_, v_a_5403_);
lean_dec(v_a_5403_);
lean_dec_ref(v_a_5402_);
lean_dec(v_a_5401_);
lean_dec_ref(v_a_5400_);
return v_res_5405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0(lean_object* v___x_5406_, lean_object* v_numParams_5407_, lean_object* v_name_5408_, lean_object* v_us_5409_, lean_object* v_args1_5410_, lean_object* v___x_5411_, lean_object* v_args2_5412_, lean_object* v___y_5413_, lean_object* v___y_5414_, lean_object* v___y_5415_, lean_object* v___y_5416_){
_start:
{
lean_object* v___x_5418_; lean_object* v___x_5419_; lean_object* v___x_5420_; lean_object* v___x_5421_; lean_object* v___x_5422_; 
lean_inc_ref(v_args2_5412_);
v___x_5418_ = l_Array_toSubarray___redArg(v_args2_5412_, v___x_5406_, v_numParams_5407_);
lean_inc(v_us_5409_);
v___x_5419_ = l_Lean_mkConst(v_name_5408_, v_us_5409_);
lean_inc_ref(v___x_5419_);
v___x_5420_ = l_Lean_mkAppN(v___x_5419_, v_args1_5410_);
v___x_5421_ = l_Lean_mkAppN(v___x_5419_, v_args2_5412_);
lean_inc_ref(v___x_5421_);
lean_inc_ref(v___x_5420_);
v___x_5422_ = l_Lean_Meta_mkEqHEq(v___x_5420_, v___x_5421_, v___y_5413_, v___y_5414_, v___y_5415_, v___y_5416_);
if (lean_obj_tag(v___x_5422_) == 0)
{
lean_object* v_a_5423_; uint8_t v___x_5424_; lean_object* v___x_5425_; 
v_a_5423_ = lean_ctor_get(v___x_5422_, 0);
lean_inc(v_a_5423_);
lean_dec_ref_known(v___x_5422_, 1);
v___x_5424_ = 1;
lean_inc_ref(v_args2_5412_);
v___x_5425_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v_args1_5410_, v_args2_5412_, v___x_5424_, v___y_5413_, v___y_5414_, v___y_5415_, v___y_5416_);
if (lean_obj_tag(v___x_5425_) == 0)
{
lean_object* v_a_5426_; lean_object* v___x_5428_; uint8_t v_isShared_5429_; uint8_t v_isSharedCheck_5546_; 
v_a_5426_ = lean_ctor_get(v___x_5425_, 0);
v_isSharedCheck_5546_ = !lean_is_exclusive(v___x_5425_);
if (v_isSharedCheck_5546_ == 0)
{
v___x_5428_ = v___x_5425_;
v_isShared_5429_ = v_isSharedCheck_5546_;
goto v_resetjp_5427_;
}
else
{
lean_inc(v_a_5426_);
lean_dec(v___x_5425_);
v___x_5428_ = lean_box(0);
v_isShared_5429_ = v_isSharedCheck_5546_;
goto v_resetjp_5427_;
}
v_resetjp_5427_:
{
lean_object* v___x_5430_; 
v___x_5430_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f(v_a_5426_);
if (lean_obj_tag(v___x_5430_) == 1)
{
lean_object* v_val_5431_; lean_object* v___x_5432_; 
lean_del_object(v___x_5428_);
v_val_5431_ = lean_ctor_get(v___x_5430_, 0);
lean_inc(v_val_5431_);
lean_dec_ref_known(v___x_5430_, 1);
v___x_5432_ = l_Lean_mkArrow(v_a_5423_, v_val_5431_, v___y_5415_, v___y_5416_);
if (lean_obj_tag(v___x_5432_) == 0)
{
lean_object* v_a_5433_; lean_object* v___x_5434_; 
v_a_5433_ = lean_ctor_get(v___x_5432_, 0);
lean_inc(v_a_5433_);
lean_dec_ref_known(v___x_5432_, 1);
v___x_5434_ = l_Lean_Meta_getCtorAppIndices_x3f(v___x_5420_, v___y_5413_, v___y_5414_, v___y_5415_, v___y_5416_);
if (lean_obj_tag(v___x_5434_) == 0)
{
lean_object* v_a_5435_; lean_object* v___x_5437_; uint8_t v_isShared_5438_; uint8_t v_isSharedCheck_5525_; 
v_a_5435_ = lean_ctor_get(v___x_5434_, 0);
v_isSharedCheck_5525_ = !lean_is_exclusive(v___x_5434_);
if (v_isSharedCheck_5525_ == 0)
{
v___x_5437_ = v___x_5434_;
v_isShared_5438_ = v_isSharedCheck_5525_;
goto v_resetjp_5436_;
}
else
{
lean_inc(v_a_5435_);
lean_dec(v___x_5434_);
v___x_5437_ = lean_box(0);
v_isShared_5438_ = v_isSharedCheck_5525_;
goto v_resetjp_5436_;
}
v_resetjp_5436_:
{
if (lean_obj_tag(v_a_5435_) == 1)
{
lean_object* v_val_5439_; lean_object* v___x_5440_; 
lean_del_object(v___x_5437_);
v_val_5439_ = lean_ctor_get(v_a_5435_, 0);
lean_inc(v_val_5439_);
lean_dec_ref_known(v_a_5435_, 1);
v___x_5440_ = l_Lean_Meta_getCtorAppIndices_x3f(v___x_5421_, v___y_5413_, v___y_5414_, v___y_5415_, v___y_5416_);
if (lean_obj_tag(v___x_5440_) == 0)
{
lean_object* v_a_5441_; lean_object* v___x_5443_; uint8_t v_isShared_5444_; uint8_t v_isSharedCheck_5512_; 
v_a_5441_ = lean_ctor_get(v___x_5440_, 0);
v_isSharedCheck_5512_ = !lean_is_exclusive(v___x_5440_);
if (v_isSharedCheck_5512_ == 0)
{
v___x_5443_ = v___x_5440_;
v_isShared_5444_ = v_isSharedCheck_5512_;
goto v_resetjp_5442_;
}
else
{
lean_inc(v_a_5441_);
lean_dec(v___x_5440_);
v___x_5443_ = lean_box(0);
v_isShared_5444_ = v_isSharedCheck_5512_;
goto v_resetjp_5442_;
}
v_resetjp_5442_:
{
if (lean_obj_tag(v_a_5441_) == 1)
{
lean_object* v_val_5445_; lean_object* v___x_5447_; uint8_t v_isShared_5448_; uint8_t v_isSharedCheck_5507_; 
lean_del_object(v___x_5443_);
v_val_5445_ = lean_ctor_get(v_a_5441_, 0);
v_isSharedCheck_5507_ = !lean_is_exclusive(v_a_5441_);
if (v_isSharedCheck_5507_ == 0)
{
v___x_5447_ = v_a_5441_;
v_isShared_5448_ = v_isSharedCheck_5507_;
goto v_resetjp_5446_;
}
else
{
lean_inc(v_val_5445_);
lean_dec(v_a_5441_);
v___x_5447_ = lean_box(0);
v_isShared_5448_ = v_isSharedCheck_5507_;
goto v_resetjp_5446_;
}
v_resetjp_5446_:
{
lean_object* v___x_5449_; lean_object* v___x_5450_; lean_object* v___x_5451_; lean_object* v___x_5452_; uint8_t v___x_5453_; lean_object* v___x_5454_; 
v___x_5449_ = l_Subarray_copy___redArg(v___x_5411_);
v___x_5450_ = l_Array_append___redArg(v___x_5449_, v_val_5439_);
v___x_5451_ = l_Subarray_copy___redArg(v___x_5418_);
v___x_5452_ = l_Array_append___redArg(v___x_5451_, v_val_5445_);
lean_dec(v_val_5445_);
v___x_5453_ = 0;
v___x_5454_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v___x_5450_, v___x_5452_, v___x_5453_, v___y_5413_, v___y_5414_, v___y_5415_, v___y_5416_);
lean_dec_ref(v___x_5450_);
if (lean_obj_tag(v___x_5454_) == 0)
{
lean_object* v_a_5455_; lean_object* v___x_5456_; 
v_a_5455_ = lean_ctor_get(v___x_5454_, 0);
lean_inc(v_a_5455_);
lean_dec_ref_known(v___x_5454_, 1);
v___x_5456_ = l_Lean_mkArrowN(v_a_5455_, v_a_5433_, v___y_5415_, v___y_5416_);
lean_dec(v_a_5455_);
if (lean_obj_tag(v___x_5456_) == 0)
{
lean_object* v_a_5457_; uint8_t v___x_5458_; lean_object* v___x_5459_; 
v_a_5457_ = lean_ctor_get(v___x_5456_, 0);
lean_inc(v_a_5457_);
lean_dec_ref_known(v___x_5456_, 1);
v___x_5458_ = 1;
v___x_5459_ = l_Lean_Meta_mkForallFVars(v_args2_5412_, v_a_5457_, v___x_5453_, v___x_5424_, v___x_5424_, v___x_5458_, v___y_5413_, v___y_5414_, v___y_5415_, v___y_5416_);
lean_dec_ref(v_args2_5412_);
if (lean_obj_tag(v___x_5459_) == 0)
{
lean_object* v_a_5460_; lean_object* v___x_5461_; 
v_a_5460_ = lean_ctor_get(v___x_5459_, 0);
lean_inc(v_a_5460_);
lean_dec_ref_known(v___x_5459_, 1);
v___x_5461_ = l_Lean_Meta_mkForallFVars(v_args1_5410_, v_a_5460_, v___x_5453_, v___x_5424_, v___x_5424_, v___x_5458_, v___y_5413_, v___y_5414_, v___y_5415_, v___y_5416_);
if (lean_obj_tag(v___x_5461_) == 0)
{
lean_object* v_a_5462_; lean_object* v___x_5464_; uint8_t v_isShared_5465_; uint8_t v_isSharedCheck_5474_; 
v_a_5462_ = lean_ctor_get(v___x_5461_, 0);
v_isSharedCheck_5474_ = !lean_is_exclusive(v___x_5461_);
if (v_isSharedCheck_5474_ == 0)
{
v___x_5464_ = v___x_5461_;
v_isShared_5465_ = v_isSharedCheck_5474_;
goto v_resetjp_5463_;
}
else
{
lean_inc(v_a_5462_);
lean_dec(v___x_5461_);
v___x_5464_ = lean_box(0);
v_isShared_5465_ = v_isSharedCheck_5474_;
goto v_resetjp_5463_;
}
v_resetjp_5463_:
{
lean_object* v___x_5466_; lean_object* v___x_5467_; lean_object* v___x_5469_; 
v___x_5466_ = lean_array_get_size(v_val_5439_);
lean_dec(v_val_5439_);
v___x_5467_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5467_, 0, v_a_5462_);
lean_ctor_set(v___x_5467_, 1, v_us_5409_);
lean_ctor_set(v___x_5467_, 2, v___x_5466_);
if (v_isShared_5448_ == 0)
{
lean_ctor_set(v___x_5447_, 0, v___x_5467_);
v___x_5469_ = v___x_5447_;
goto v_reusejp_5468_;
}
else
{
lean_object* v_reuseFailAlloc_5473_; 
v_reuseFailAlloc_5473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5473_, 0, v___x_5467_);
v___x_5469_ = v_reuseFailAlloc_5473_;
goto v_reusejp_5468_;
}
v_reusejp_5468_:
{
lean_object* v___x_5471_; 
if (v_isShared_5465_ == 0)
{
lean_ctor_set(v___x_5464_, 0, v___x_5469_);
v___x_5471_ = v___x_5464_;
goto v_reusejp_5470_;
}
else
{
lean_object* v_reuseFailAlloc_5472_; 
v_reuseFailAlloc_5472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5472_, 0, v___x_5469_);
v___x_5471_ = v_reuseFailAlloc_5472_;
goto v_reusejp_5470_;
}
v_reusejp_5470_:
{
return v___x_5471_;
}
}
}
}
else
{
lean_object* v_a_5475_; lean_object* v___x_5477_; uint8_t v_isShared_5478_; uint8_t v_isSharedCheck_5482_; 
lean_del_object(v___x_5447_);
lean_dec(v_val_5439_);
lean_dec(v_us_5409_);
v_a_5475_ = lean_ctor_get(v___x_5461_, 0);
v_isSharedCheck_5482_ = !lean_is_exclusive(v___x_5461_);
if (v_isSharedCheck_5482_ == 0)
{
v___x_5477_ = v___x_5461_;
v_isShared_5478_ = v_isSharedCheck_5482_;
goto v_resetjp_5476_;
}
else
{
lean_inc(v_a_5475_);
lean_dec(v___x_5461_);
v___x_5477_ = lean_box(0);
v_isShared_5478_ = v_isSharedCheck_5482_;
goto v_resetjp_5476_;
}
v_resetjp_5476_:
{
lean_object* v___x_5480_; 
if (v_isShared_5478_ == 0)
{
v___x_5480_ = v___x_5477_;
goto v_reusejp_5479_;
}
else
{
lean_object* v_reuseFailAlloc_5481_; 
v_reuseFailAlloc_5481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5481_, 0, v_a_5475_);
v___x_5480_ = v_reuseFailAlloc_5481_;
goto v_reusejp_5479_;
}
v_reusejp_5479_:
{
return v___x_5480_;
}
}
}
}
else
{
lean_object* v_a_5483_; lean_object* v___x_5485_; uint8_t v_isShared_5486_; uint8_t v_isSharedCheck_5490_; 
lean_del_object(v___x_5447_);
lean_dec(v_val_5439_);
lean_dec(v_us_5409_);
v_a_5483_ = lean_ctor_get(v___x_5459_, 0);
v_isSharedCheck_5490_ = !lean_is_exclusive(v___x_5459_);
if (v_isSharedCheck_5490_ == 0)
{
v___x_5485_ = v___x_5459_;
v_isShared_5486_ = v_isSharedCheck_5490_;
goto v_resetjp_5484_;
}
else
{
lean_inc(v_a_5483_);
lean_dec(v___x_5459_);
v___x_5485_ = lean_box(0);
v_isShared_5486_ = v_isSharedCheck_5490_;
goto v_resetjp_5484_;
}
v_resetjp_5484_:
{
lean_object* v___x_5488_; 
if (v_isShared_5486_ == 0)
{
v___x_5488_ = v___x_5485_;
goto v_reusejp_5487_;
}
else
{
lean_object* v_reuseFailAlloc_5489_; 
v_reuseFailAlloc_5489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5489_, 0, v_a_5483_);
v___x_5488_ = v_reuseFailAlloc_5489_;
goto v_reusejp_5487_;
}
v_reusejp_5487_:
{
return v___x_5488_;
}
}
}
}
else
{
lean_object* v_a_5491_; lean_object* v___x_5493_; uint8_t v_isShared_5494_; uint8_t v_isSharedCheck_5498_; 
lean_del_object(v___x_5447_);
lean_dec(v_val_5439_);
lean_dec_ref(v_args2_5412_);
lean_dec(v_us_5409_);
v_a_5491_ = lean_ctor_get(v___x_5456_, 0);
v_isSharedCheck_5498_ = !lean_is_exclusive(v___x_5456_);
if (v_isSharedCheck_5498_ == 0)
{
v___x_5493_ = v___x_5456_;
v_isShared_5494_ = v_isSharedCheck_5498_;
goto v_resetjp_5492_;
}
else
{
lean_inc(v_a_5491_);
lean_dec(v___x_5456_);
v___x_5493_ = lean_box(0);
v_isShared_5494_ = v_isSharedCheck_5498_;
goto v_resetjp_5492_;
}
v_resetjp_5492_:
{
lean_object* v___x_5496_; 
if (v_isShared_5494_ == 0)
{
v___x_5496_ = v___x_5493_;
goto v_reusejp_5495_;
}
else
{
lean_object* v_reuseFailAlloc_5497_; 
v_reuseFailAlloc_5497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5497_, 0, v_a_5491_);
v___x_5496_ = v_reuseFailAlloc_5497_;
goto v_reusejp_5495_;
}
v_reusejp_5495_:
{
return v___x_5496_;
}
}
}
}
else
{
lean_object* v_a_5499_; lean_object* v___x_5501_; uint8_t v_isShared_5502_; uint8_t v_isSharedCheck_5506_; 
lean_del_object(v___x_5447_);
lean_dec(v_val_5439_);
lean_dec(v_a_5433_);
lean_dec_ref(v_args2_5412_);
lean_dec(v_us_5409_);
v_a_5499_ = lean_ctor_get(v___x_5454_, 0);
v_isSharedCheck_5506_ = !lean_is_exclusive(v___x_5454_);
if (v_isSharedCheck_5506_ == 0)
{
v___x_5501_ = v___x_5454_;
v_isShared_5502_ = v_isSharedCheck_5506_;
goto v_resetjp_5500_;
}
else
{
lean_inc(v_a_5499_);
lean_dec(v___x_5454_);
v___x_5501_ = lean_box(0);
v_isShared_5502_ = v_isSharedCheck_5506_;
goto v_resetjp_5500_;
}
v_resetjp_5500_:
{
lean_object* v___x_5504_; 
if (v_isShared_5502_ == 0)
{
v___x_5504_ = v___x_5501_;
goto v_reusejp_5503_;
}
else
{
lean_object* v_reuseFailAlloc_5505_; 
v_reuseFailAlloc_5505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5505_, 0, v_a_5499_);
v___x_5504_ = v_reuseFailAlloc_5505_;
goto v_reusejp_5503_;
}
v_reusejp_5503_:
{
return v___x_5504_;
}
}
}
}
}
else
{
lean_object* v___x_5508_; lean_object* v___x_5510_; 
lean_dec(v_a_5441_);
lean_dec(v_val_5439_);
lean_dec(v_a_5433_);
lean_dec_ref(v___x_5418_);
lean_dec_ref(v_args2_5412_);
lean_dec_ref(v___x_5411_);
lean_dec(v_us_5409_);
v___x_5508_ = lean_box(0);
if (v_isShared_5444_ == 0)
{
lean_ctor_set(v___x_5443_, 0, v___x_5508_);
v___x_5510_ = v___x_5443_;
goto v_reusejp_5509_;
}
else
{
lean_object* v_reuseFailAlloc_5511_; 
v_reuseFailAlloc_5511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5511_, 0, v___x_5508_);
v___x_5510_ = v_reuseFailAlloc_5511_;
goto v_reusejp_5509_;
}
v_reusejp_5509_:
{
return v___x_5510_;
}
}
}
}
else
{
lean_object* v_a_5513_; lean_object* v___x_5515_; uint8_t v_isShared_5516_; uint8_t v_isSharedCheck_5520_; 
lean_dec(v_val_5439_);
lean_dec(v_a_5433_);
lean_dec_ref(v___x_5418_);
lean_dec_ref(v_args2_5412_);
lean_dec_ref(v___x_5411_);
lean_dec(v_us_5409_);
v_a_5513_ = lean_ctor_get(v___x_5440_, 0);
v_isSharedCheck_5520_ = !lean_is_exclusive(v___x_5440_);
if (v_isSharedCheck_5520_ == 0)
{
v___x_5515_ = v___x_5440_;
v_isShared_5516_ = v_isSharedCheck_5520_;
goto v_resetjp_5514_;
}
else
{
lean_inc(v_a_5513_);
lean_dec(v___x_5440_);
v___x_5515_ = lean_box(0);
v_isShared_5516_ = v_isSharedCheck_5520_;
goto v_resetjp_5514_;
}
v_resetjp_5514_:
{
lean_object* v___x_5518_; 
if (v_isShared_5516_ == 0)
{
v___x_5518_ = v___x_5515_;
goto v_reusejp_5517_;
}
else
{
lean_object* v_reuseFailAlloc_5519_; 
v_reuseFailAlloc_5519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5519_, 0, v_a_5513_);
v___x_5518_ = v_reuseFailAlloc_5519_;
goto v_reusejp_5517_;
}
v_reusejp_5517_:
{
return v___x_5518_;
}
}
}
}
else
{
lean_object* v___x_5521_; lean_object* v___x_5523_; 
lean_dec(v_a_5435_);
lean_dec(v_a_5433_);
lean_dec_ref(v___x_5421_);
lean_dec_ref(v___x_5418_);
lean_dec_ref(v_args2_5412_);
lean_dec_ref(v___x_5411_);
lean_dec(v_us_5409_);
v___x_5521_ = lean_box(0);
if (v_isShared_5438_ == 0)
{
lean_ctor_set(v___x_5437_, 0, v___x_5521_);
v___x_5523_ = v___x_5437_;
goto v_reusejp_5522_;
}
else
{
lean_object* v_reuseFailAlloc_5524_; 
v_reuseFailAlloc_5524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5524_, 0, v___x_5521_);
v___x_5523_ = v_reuseFailAlloc_5524_;
goto v_reusejp_5522_;
}
v_reusejp_5522_:
{
return v___x_5523_;
}
}
}
}
else
{
lean_object* v_a_5526_; lean_object* v___x_5528_; uint8_t v_isShared_5529_; uint8_t v_isSharedCheck_5533_; 
lean_dec(v_a_5433_);
lean_dec_ref(v___x_5421_);
lean_dec_ref(v___x_5418_);
lean_dec_ref(v_args2_5412_);
lean_dec_ref(v___x_5411_);
lean_dec(v_us_5409_);
v_a_5526_ = lean_ctor_get(v___x_5434_, 0);
v_isSharedCheck_5533_ = !lean_is_exclusive(v___x_5434_);
if (v_isSharedCheck_5533_ == 0)
{
v___x_5528_ = v___x_5434_;
v_isShared_5529_ = v_isSharedCheck_5533_;
goto v_resetjp_5527_;
}
else
{
lean_inc(v_a_5526_);
lean_dec(v___x_5434_);
v___x_5528_ = lean_box(0);
v_isShared_5529_ = v_isSharedCheck_5533_;
goto v_resetjp_5527_;
}
v_resetjp_5527_:
{
lean_object* v___x_5531_; 
if (v_isShared_5529_ == 0)
{
v___x_5531_ = v___x_5528_;
goto v_reusejp_5530_;
}
else
{
lean_object* v_reuseFailAlloc_5532_; 
v_reuseFailAlloc_5532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5532_, 0, v_a_5526_);
v___x_5531_ = v_reuseFailAlloc_5532_;
goto v_reusejp_5530_;
}
v_reusejp_5530_:
{
return v___x_5531_;
}
}
}
}
else
{
lean_object* v_a_5534_; lean_object* v___x_5536_; uint8_t v_isShared_5537_; uint8_t v_isSharedCheck_5541_; 
lean_dec_ref(v___x_5421_);
lean_dec_ref(v___x_5420_);
lean_dec_ref(v___x_5418_);
lean_dec_ref(v_args2_5412_);
lean_dec_ref(v___x_5411_);
lean_dec(v_us_5409_);
v_a_5534_ = lean_ctor_get(v___x_5432_, 0);
v_isSharedCheck_5541_ = !lean_is_exclusive(v___x_5432_);
if (v_isSharedCheck_5541_ == 0)
{
v___x_5536_ = v___x_5432_;
v_isShared_5537_ = v_isSharedCheck_5541_;
goto v_resetjp_5535_;
}
else
{
lean_inc(v_a_5534_);
lean_dec(v___x_5432_);
v___x_5536_ = lean_box(0);
v_isShared_5537_ = v_isSharedCheck_5541_;
goto v_resetjp_5535_;
}
v_resetjp_5535_:
{
lean_object* v___x_5539_; 
if (v_isShared_5537_ == 0)
{
v___x_5539_ = v___x_5536_;
goto v_reusejp_5538_;
}
else
{
lean_object* v_reuseFailAlloc_5540_; 
v_reuseFailAlloc_5540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5540_, 0, v_a_5534_);
v___x_5539_ = v_reuseFailAlloc_5540_;
goto v_reusejp_5538_;
}
v_reusejp_5538_:
{
return v___x_5539_;
}
}
}
}
else
{
lean_object* v___x_5542_; lean_object* v___x_5544_; 
lean_dec(v___x_5430_);
lean_dec(v_a_5423_);
lean_dec_ref(v___x_5421_);
lean_dec_ref(v___x_5420_);
lean_dec_ref(v___x_5418_);
lean_dec_ref(v_args2_5412_);
lean_dec_ref(v___x_5411_);
lean_dec(v_us_5409_);
v___x_5542_ = lean_box(0);
if (v_isShared_5429_ == 0)
{
lean_ctor_set(v___x_5428_, 0, v___x_5542_);
v___x_5544_ = v___x_5428_;
goto v_reusejp_5543_;
}
else
{
lean_object* v_reuseFailAlloc_5545_; 
v_reuseFailAlloc_5545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5545_, 0, v___x_5542_);
v___x_5544_ = v_reuseFailAlloc_5545_;
goto v_reusejp_5543_;
}
v_reusejp_5543_:
{
return v___x_5544_;
}
}
}
}
else
{
lean_object* v_a_5547_; lean_object* v___x_5549_; uint8_t v_isShared_5550_; uint8_t v_isSharedCheck_5554_; 
lean_dec(v_a_5423_);
lean_dec_ref(v___x_5421_);
lean_dec_ref(v___x_5420_);
lean_dec_ref(v___x_5418_);
lean_dec_ref(v_args2_5412_);
lean_dec_ref(v___x_5411_);
lean_dec(v_us_5409_);
v_a_5547_ = lean_ctor_get(v___x_5425_, 0);
v_isSharedCheck_5554_ = !lean_is_exclusive(v___x_5425_);
if (v_isSharedCheck_5554_ == 0)
{
v___x_5549_ = v___x_5425_;
v_isShared_5550_ = v_isSharedCheck_5554_;
goto v_resetjp_5548_;
}
else
{
lean_inc(v_a_5547_);
lean_dec(v___x_5425_);
v___x_5549_ = lean_box(0);
v_isShared_5550_ = v_isSharedCheck_5554_;
goto v_resetjp_5548_;
}
v_resetjp_5548_:
{
lean_object* v___x_5552_; 
if (v_isShared_5550_ == 0)
{
v___x_5552_ = v___x_5549_;
goto v_reusejp_5551_;
}
else
{
lean_object* v_reuseFailAlloc_5553_; 
v_reuseFailAlloc_5553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5553_, 0, v_a_5547_);
v___x_5552_ = v_reuseFailAlloc_5553_;
goto v_reusejp_5551_;
}
v_reusejp_5551_:
{
return v___x_5552_;
}
}
}
}
else
{
lean_object* v_a_5555_; lean_object* v___x_5557_; uint8_t v_isShared_5558_; uint8_t v_isSharedCheck_5562_; 
lean_dec_ref(v___x_5421_);
lean_dec_ref(v___x_5420_);
lean_dec_ref(v___x_5418_);
lean_dec_ref(v_args2_5412_);
lean_dec_ref(v___x_5411_);
lean_dec(v_us_5409_);
v_a_5555_ = lean_ctor_get(v___x_5422_, 0);
v_isSharedCheck_5562_ = !lean_is_exclusive(v___x_5422_);
if (v_isSharedCheck_5562_ == 0)
{
v___x_5557_ = v___x_5422_;
v_isShared_5558_ = v_isSharedCheck_5562_;
goto v_resetjp_5556_;
}
else
{
lean_inc(v_a_5555_);
lean_dec(v___x_5422_);
v___x_5557_ = lean_box(0);
v_isShared_5558_ = v_isSharedCheck_5562_;
goto v_resetjp_5556_;
}
v_resetjp_5556_:
{
lean_object* v___x_5560_; 
if (v_isShared_5558_ == 0)
{
v___x_5560_ = v___x_5557_;
goto v_reusejp_5559_;
}
else
{
lean_object* v_reuseFailAlloc_5561_; 
v_reuseFailAlloc_5561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5561_, 0, v_a_5555_);
v___x_5560_ = v_reuseFailAlloc_5561_;
goto v_reusejp_5559_;
}
v_reusejp_5559_:
{
return v___x_5560_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0___boxed(lean_object* v___x_5563_, lean_object* v_numParams_5564_, lean_object* v_name_5565_, lean_object* v_us_5566_, lean_object* v_args1_5567_, lean_object* v___x_5568_, lean_object* v_args2_5569_, lean_object* v___y_5570_, lean_object* v___y_5571_, lean_object* v___y_5572_, lean_object* v___y_5573_, lean_object* v___y_5574_){
_start:
{
lean_object* v_res_5575_; 
v_res_5575_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0(v___x_5563_, v_numParams_5564_, v_name_5565_, v_us_5566_, v_args1_5567_, v___x_5568_, v_args2_5569_, v___y_5570_, v___y_5571_, v___y_5572_, v___y_5573_);
lean_dec(v___y_5573_);
lean_dec_ref(v___y_5572_);
lean_dec(v___y_5571_);
lean_dec_ref(v___y_5570_);
lean_dec_ref(v_args1_5567_);
return v_res_5575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1(lean_object* v_numParams_5576_, lean_object* v_name_5577_, lean_object* v_us_5578_, lean_object* v_ctorVal_5579_, lean_object* v_a_5580_, lean_object* v_args1_5581_, lean_object* v_x_5582_, lean_object* v___y_5583_, lean_object* v___y_5584_, lean_object* v___y_5585_, lean_object* v___y_5586_){
_start:
{
lean_object* v___x_5588_; lean_object* v___x_5589_; lean_object* v___f_5590_; lean_object* v___x_5591_; lean_object* v___x_5592_; lean_object* v___x_5593_; 
v___x_5588_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_5576_);
lean_inc_ref_n(v_args1_5581_, 3);
v___x_5589_ = l_Array_toSubarray___redArg(v_args1_5581_, v___x_5588_, v_numParams_5576_);
v___f_5590_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0___boxed), 12, 6);
lean_closure_set(v___f_5590_, 0, v___x_5588_);
lean_closure_set(v___f_5590_, 1, v_numParams_5576_);
lean_closure_set(v___f_5590_, 2, v_name_5577_);
lean_closure_set(v___f_5590_, 3, v_us_5578_);
lean_closure_set(v___f_5590_, 4, v_args1_5581_);
lean_closure_set(v___f_5590_, 5, v___x_5589_);
v___x_5591_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_5592_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___boxed), 11, 6);
lean_closure_set(v___x_5592_, 0, v_ctorVal_5579_);
lean_closure_set(v___x_5592_, 1, v_args1_5581_);
lean_closure_set(v___x_5592_, 2, v___f_5590_);
lean_closure_set(v___x_5592_, 3, v___x_5588_);
lean_closure_set(v___x_5592_, 4, v_a_5580_);
lean_closure_set(v___x_5592_, 5, v___x_5591_);
v___x_5593_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v_args1_5581_, v___x_5592_, v___y_5583_, v___y_5584_, v___y_5585_, v___y_5586_);
return v___x_5593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1___boxed(lean_object* v_numParams_5594_, lean_object* v_name_5595_, lean_object* v_us_5596_, lean_object* v_ctorVal_5597_, lean_object* v_a_5598_, lean_object* v_args1_5599_, lean_object* v_x_5600_, lean_object* v___y_5601_, lean_object* v___y_5602_, lean_object* v___y_5603_, lean_object* v___y_5604_, lean_object* v___y_5605_){
_start:
{
lean_object* v_res_5606_; 
v_res_5606_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1(v_numParams_5594_, v_name_5595_, v_us_5596_, v_ctorVal_5597_, v_a_5598_, v_args1_5599_, v_x_5600_, v___y_5601_, v___y_5602_, v___y_5603_, v___y_5604_);
lean_dec(v___y_5604_);
lean_dec_ref(v___y_5603_);
lean_dec(v___y_5602_);
lean_dec_ref(v___y_5601_);
lean_dec_ref(v_x_5600_);
return v_res_5606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(lean_object* v_ctorVal_5607_, lean_object* v_a_5608_, lean_object* v_a_5609_, lean_object* v_a_5610_, lean_object* v_a_5611_){
_start:
{
lean_object* v_toConstantVal_5613_; lean_object* v_numParams_5614_; lean_object* v_name_5615_; lean_object* v_levelParams_5616_; lean_object* v_type_5617_; lean_object* v___x_5618_; lean_object* v_us_5619_; lean_object* v___x_5620_; 
v_toConstantVal_5613_ = lean_ctor_get(v_ctorVal_5607_, 0);
v_numParams_5614_ = lean_ctor_get(v_ctorVal_5607_, 3);
lean_inc(v_numParams_5614_);
v_name_5615_ = lean_ctor_get(v_toConstantVal_5613_, 0);
lean_inc(v_name_5615_);
v_levelParams_5616_ = lean_ctor_get(v_toConstantVal_5613_, 1);
v_type_5617_ = lean_ctor_get(v_toConstantVal_5613_, 2);
v___x_5618_ = lean_box(0);
lean_inc(v_levelParams_5616_);
v_us_5619_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(v_levelParams_5616_, v___x_5618_);
lean_inc_ref(v_type_5617_);
v___x_5620_ = l_Lean_Meta_elimOptParam(v_type_5617_, v_a_5610_, v_a_5611_);
if (lean_obj_tag(v___x_5620_) == 0)
{
lean_object* v_a_5621_; lean_object* v___f_5622_; uint8_t v___x_5623_; lean_object* v___x_5624_; 
v_a_5621_ = lean_ctor_get(v___x_5620_, 0);
lean_inc_n(v_a_5621_, 2);
lean_dec_ref_known(v___x_5620_, 1);
v___f_5622_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1___boxed), 12, 5);
lean_closure_set(v___f_5622_, 0, v_numParams_5614_);
lean_closure_set(v___f_5622_, 1, v_name_5615_);
lean_closure_set(v___f_5622_, 2, v_us_5619_);
lean_closure_set(v___f_5622_, 3, v_ctorVal_5607_);
lean_closure_set(v___f_5622_, 4, v_a_5621_);
v___x_5623_ = 0;
v___x_5624_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_a_5621_, v___f_5622_, v___x_5623_, v_a_5608_, v_a_5609_, v_a_5610_, v_a_5611_);
return v___x_5624_;
}
else
{
lean_object* v_a_5625_; lean_object* v___x_5627_; uint8_t v_isShared_5628_; uint8_t v_isSharedCheck_5632_; 
lean_dec(v_us_5619_);
lean_dec(v_name_5615_);
lean_dec(v_numParams_5614_);
lean_dec_ref(v_ctorVal_5607_);
v_a_5625_ = lean_ctor_get(v___x_5620_, 0);
v_isSharedCheck_5632_ = !lean_is_exclusive(v___x_5620_);
if (v_isSharedCheck_5632_ == 0)
{
v___x_5627_ = v___x_5620_;
v_isShared_5628_ = v_isSharedCheck_5632_;
goto v_resetjp_5626_;
}
else
{
lean_inc(v_a_5625_);
lean_dec(v___x_5620_);
v___x_5627_ = lean_box(0);
v_isShared_5628_ = v_isSharedCheck_5632_;
goto v_resetjp_5626_;
}
v_resetjp_5626_:
{
lean_object* v___x_5630_; 
if (v_isShared_5628_ == 0)
{
v___x_5630_ = v___x_5627_;
goto v_reusejp_5629_;
}
else
{
lean_object* v_reuseFailAlloc_5631_; 
v_reuseFailAlloc_5631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5631_, 0, v_a_5625_);
v___x_5630_ = v_reuseFailAlloc_5631_;
goto v_reusejp_5629_;
}
v_reusejp_5629_:
{
return v___x_5630_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___boxed(lean_object* v_ctorVal_5633_, lean_object* v_a_5634_, lean_object* v_a_5635_, lean_object* v_a_5636_, lean_object* v_a_5637_, lean_object* v_a_5638_){
_start:
{
lean_object* v_res_5639_; 
v_res_5639_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(v_ctorVal_5633_, v_a_5634_, v_a_5635_, v_a_5636_, v_a_5637_);
lean_dec(v_a_5637_);
lean_dec_ref(v_a_5636_);
lean_dec(v_a_5635_);
lean_dec_ref(v_a_5634_);
return v_res_5639_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1(void){
_start:
{
lean_object* v___x_5641_; lean_object* v___x_5642_; 
v___x_5641_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__0));
v___x_5642_ = l_Lean_stringToMessageData(v___x_5641_);
return v___x_5642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(lean_object* v_ctorVal_5643_, lean_object* v_a_5644_, lean_object* v_a_5645_, lean_object* v_a_5646_, lean_object* v_a_5647_){
_start:
{
lean_object* v_toConstantVal_5649_; lean_object* v_name_5650_; lean_object* v___x_5651_; lean_object* v___x_5652_; lean_object* v___x_5653_; lean_object* v___x_5654_; lean_object* v___x_5655_; lean_object* v___x_5656_; 
v_toConstantVal_5649_ = lean_ctor_get(v_ctorVal_5643_, 0);
lean_inc_ref(v_toConstantVal_5649_);
lean_dec_ref(v_ctorVal_5643_);
v_name_5650_ = lean_ctor_get(v_toConstantVal_5649_, 0);
lean_inc(v_name_5650_);
lean_dec_ref(v_toConstantVal_5649_);
v___x_5651_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1);
v___x_5652_ = l_Lean_MessageData_ofName(v_name_5650_);
v___x_5653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5653_, 0, v___x_5651_);
lean_ctor_set(v___x_5653_, 1, v___x_5652_);
v___x_5654_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_5655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5655_, 0, v___x_5653_);
lean_ctor_set(v___x_5655_, 1, v___x_5654_);
v___x_5656_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_5655_, v_a_5644_, v_a_5645_, v_a_5646_, v_a_5647_);
return v___x_5656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___boxed(lean_object* v_ctorVal_5657_, lean_object* v_a_5658_, lean_object* v_a_5659_, lean_object* v_a_5660_, lean_object* v_a_5661_, lean_object* v_a_5662_){
_start:
{
lean_object* v_res_5663_; 
v_res_5663_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5657_, v_a_5658_, v_a_5659_, v_a_5660_, v_a_5661_);
lean_dec(v_a_5661_);
lean_dec_ref(v_a_5660_);
lean_dec(v_a_5659_);
lean_dec_ref(v_a_5658_);
return v_res_5663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj(lean_object* v_00_u03b1_5664_, lean_object* v_ctorVal_5665_, lean_object* v_a_5666_, lean_object* v_a_5667_, lean_object* v_a_5668_, lean_object* v_a_5669_){
_start:
{
lean_object* v___x_5671_; 
v___x_5671_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5665_, v_a_5666_, v_a_5667_, v_a_5668_, v_a_5669_);
return v___x_5671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___boxed(lean_object* v_00_u03b1_5672_, lean_object* v_ctorVal_5673_, lean_object* v_a_5674_, lean_object* v_a_5675_, lean_object* v_a_5676_, lean_object* v_a_5677_, lean_object* v_a_5678_){
_start:
{
lean_object* v_res_5679_; 
v_res_5679_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj(v_00_u03b1_5672_, v_ctorVal_5673_, v_a_5674_, v_a_5675_, v_a_5676_, v_a_5677_);
lean_dec(v_a_5677_);
lean_dec_ref(v_a_5676_);
lean_dec(v_a_5675_);
lean_dec_ref(v_a_5674_);
return v_res_5679_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(lean_object* v_ctorVal_5685_, size_t v_sz_5686_, size_t v_i_5687_, lean_object* v_bs_5688_, lean_object* v___y_5689_, lean_object* v___y_5690_, lean_object* v___y_5691_, lean_object* v___y_5692_){
_start:
{
uint8_t v___x_5694_; 
v___x_5694_ = lean_usize_dec_lt(v_i_5687_, v_sz_5686_);
if (v___x_5694_ == 0)
{
lean_object* v___x_5695_; 
lean_dec_ref(v_ctorVal_5685_);
v___x_5695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5695_, 0, v_bs_5688_);
return v___x_5695_;
}
else
{
lean_object* v_v_5696_; lean_object* v___x_5697_; lean_object* v_bs_x27_5698_; lean_object* v_a_5700_; lean_object* v___y_5706_; lean_object* v_lhs_5717_; lean_object* v_rhs_5718_; lean_object* v___x_5720_; 
v_v_5696_ = lean_array_uget(v_bs_5688_, v_i_5687_);
v___x_5697_ = lean_unsigned_to_nat(0u);
v_bs_x27_5698_ = lean_array_uset(v_bs_5688_, v_i_5687_, v___x_5697_);
lean_inc(v___y_5692_);
lean_inc_ref(v___y_5691_);
lean_inc(v___y_5690_);
lean_inc_ref(v___y_5689_);
v___x_5720_ = lean_infer_type(v_v_5696_, v___y_5689_, v___y_5690_, v___y_5691_, v___y_5692_);
if (lean_obj_tag(v___x_5720_) == 0)
{
lean_object* v_a_5721_; lean_object* v___x_5722_; 
v_a_5721_ = lean_ctor_get(v___x_5720_, 0);
lean_inc(v_a_5721_);
lean_dec_ref_known(v___x_5720_, 1);
v___x_5722_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_5721_, v___y_5690_);
if (lean_obj_tag(v___x_5722_) == 0)
{
lean_object* v_a_5723_; lean_object* v___x_5724_; uint8_t v___x_5725_; 
v_a_5723_ = lean_ctor_get(v___x_5722_, 0);
lean_inc(v_a_5723_);
lean_dec_ref_known(v___x_5722_, 1);
v___x_5724_ = l_Lean_Expr_cleanupAnnotations(v_a_5723_);
v___x_5725_ = l_Lean_Expr_isApp(v___x_5724_);
if (v___x_5725_ == 0)
{
lean_object* v___x_5726_; 
lean_dec_ref(v___x_5724_);
lean_inc_ref(v_ctorVal_5685_);
v___x_5726_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5685_, v___y_5689_, v___y_5690_, v___y_5691_, v___y_5692_);
v___y_5706_ = v___x_5726_;
goto v___jp_5705_;
}
else
{
lean_object* v_arg_5727_; lean_object* v___x_5728_; uint8_t v___x_5729_; 
v_arg_5727_ = lean_ctor_get(v___x_5724_, 1);
lean_inc_ref(v_arg_5727_);
v___x_5728_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5724_);
v___x_5729_ = l_Lean_Expr_isApp(v___x_5728_);
if (v___x_5729_ == 0)
{
lean_object* v___x_5730_; 
lean_dec_ref(v___x_5728_);
lean_dec_ref(v_arg_5727_);
lean_inc_ref(v_ctorVal_5685_);
v___x_5730_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5685_, v___y_5689_, v___y_5690_, v___y_5691_, v___y_5692_);
v___y_5706_ = v___x_5730_;
goto v___jp_5705_;
}
else
{
lean_object* v_arg_5731_; lean_object* v___x_5732_; uint8_t v___x_5733_; 
v_arg_5731_ = lean_ctor_get(v___x_5728_, 1);
lean_inc_ref(v_arg_5731_);
v___x_5732_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5728_);
v___x_5733_ = l_Lean_Expr_isApp(v___x_5732_);
if (v___x_5733_ == 0)
{
lean_object* v___x_5734_; 
lean_dec_ref(v___x_5732_);
lean_dec_ref(v_arg_5731_);
lean_dec_ref(v_arg_5727_);
lean_inc_ref(v_ctorVal_5685_);
v___x_5734_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5685_, v___y_5689_, v___y_5690_, v___y_5691_, v___y_5692_);
v___y_5706_ = v___x_5734_;
goto v___jp_5705_;
}
else
{
lean_object* v_arg_5735_; lean_object* v___x_5736_; lean_object* v___x_5737_; uint8_t v___x_5738_; 
v_arg_5735_ = lean_ctor_get(v___x_5732_, 1);
lean_inc_ref(v_arg_5735_);
v___x_5736_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5732_);
v___x_5737_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__0));
v___x_5738_ = l_Lean_Expr_isConstOf(v___x_5736_, v___x_5737_);
if (v___x_5738_ == 0)
{
uint8_t v___x_5739_; 
lean_dec_ref(v_arg_5731_);
v___x_5739_ = l_Lean_Expr_isApp(v___x_5736_);
if (v___x_5739_ == 0)
{
lean_object* v___x_5740_; 
lean_dec_ref(v___x_5736_);
lean_dec_ref(v_arg_5735_);
lean_dec_ref(v_arg_5727_);
lean_inc_ref(v_ctorVal_5685_);
v___x_5740_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5685_, v___y_5689_, v___y_5690_, v___y_5691_, v___y_5692_);
v___y_5706_ = v___x_5740_;
goto v___jp_5705_;
}
else
{
lean_object* v___x_5741_; lean_object* v___x_5742_; uint8_t v___x_5743_; 
v___x_5741_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5736_);
v___x_5742_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__2));
v___x_5743_ = l_Lean_Expr_isConstOf(v___x_5741_, v___x_5742_);
lean_dec_ref(v___x_5741_);
if (v___x_5743_ == 0)
{
lean_object* v___x_5744_; 
lean_dec_ref(v_arg_5735_);
lean_dec_ref(v_arg_5727_);
lean_inc_ref(v_ctorVal_5685_);
v___x_5744_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5685_, v___y_5689_, v___y_5690_, v___y_5691_, v___y_5692_);
v___y_5706_ = v___x_5744_;
goto v___jp_5705_;
}
else
{
v_lhs_5717_ = v_arg_5735_;
v_rhs_5718_ = v_arg_5727_;
goto v___jp_5716_;
}
}
}
else
{
lean_dec_ref(v___x_5736_);
lean_dec_ref(v_arg_5735_);
v_lhs_5717_ = v_arg_5731_;
v_rhs_5718_ = v_arg_5727_;
goto v___jp_5716_;
}
}
}
}
}
else
{
lean_object* v_a_5745_; lean_object* v___x_5747_; uint8_t v_isShared_5748_; uint8_t v_isSharedCheck_5752_; 
lean_dec_ref(v_bs_x27_5698_);
lean_dec_ref(v_ctorVal_5685_);
v_a_5745_ = lean_ctor_get(v___x_5722_, 0);
v_isSharedCheck_5752_ = !lean_is_exclusive(v___x_5722_);
if (v_isSharedCheck_5752_ == 0)
{
v___x_5747_ = v___x_5722_;
v_isShared_5748_ = v_isSharedCheck_5752_;
goto v_resetjp_5746_;
}
else
{
lean_inc(v_a_5745_);
lean_dec(v___x_5722_);
v___x_5747_ = lean_box(0);
v_isShared_5748_ = v_isSharedCheck_5752_;
goto v_resetjp_5746_;
}
v_resetjp_5746_:
{
lean_object* v___x_5750_; 
if (v_isShared_5748_ == 0)
{
v___x_5750_ = v___x_5747_;
goto v_reusejp_5749_;
}
else
{
lean_object* v_reuseFailAlloc_5751_; 
v_reuseFailAlloc_5751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5751_, 0, v_a_5745_);
v___x_5750_ = v_reuseFailAlloc_5751_;
goto v_reusejp_5749_;
}
v_reusejp_5749_:
{
return v___x_5750_;
}
}
}
}
else
{
lean_object* v_a_5753_; lean_object* v___x_5755_; uint8_t v_isShared_5756_; uint8_t v_isSharedCheck_5760_; 
lean_dec_ref(v_bs_x27_5698_);
lean_dec_ref(v_ctorVal_5685_);
v_a_5753_ = lean_ctor_get(v___x_5720_, 0);
v_isSharedCheck_5760_ = !lean_is_exclusive(v___x_5720_);
if (v_isSharedCheck_5760_ == 0)
{
v___x_5755_ = v___x_5720_;
v_isShared_5756_ = v_isSharedCheck_5760_;
goto v_resetjp_5754_;
}
else
{
lean_inc(v_a_5753_);
lean_dec(v___x_5720_);
v___x_5755_ = lean_box(0);
v_isShared_5756_ = v_isSharedCheck_5760_;
goto v_resetjp_5754_;
}
v_resetjp_5754_:
{
lean_object* v___x_5758_; 
if (v_isShared_5756_ == 0)
{
v___x_5758_ = v___x_5755_;
goto v_reusejp_5757_;
}
else
{
lean_object* v_reuseFailAlloc_5759_; 
v_reuseFailAlloc_5759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5759_, 0, v_a_5753_);
v___x_5758_ = v_reuseFailAlloc_5759_;
goto v_reusejp_5757_;
}
v_reusejp_5757_:
{
return v___x_5758_;
}
}
}
v___jp_5699_:
{
size_t v___x_5701_; size_t v___x_5702_; lean_object* v___x_5703_; 
v___x_5701_ = ((size_t)1ULL);
v___x_5702_ = lean_usize_add(v_i_5687_, v___x_5701_);
v___x_5703_ = lean_array_uset(v_bs_x27_5698_, v_i_5687_, v_a_5700_);
v_i_5687_ = v___x_5702_;
v_bs_5688_ = v___x_5703_;
goto _start;
}
v___jp_5705_:
{
if (lean_obj_tag(v___y_5706_) == 0)
{
lean_object* v_a_5707_; 
v_a_5707_ = lean_ctor_get(v___y_5706_, 0);
lean_inc(v_a_5707_);
lean_dec_ref_known(v___y_5706_, 1);
v_a_5700_ = v_a_5707_;
goto v___jp_5699_;
}
else
{
lean_object* v_a_5708_; lean_object* v___x_5710_; uint8_t v_isShared_5711_; uint8_t v_isSharedCheck_5715_; 
lean_dec_ref(v_bs_x27_5698_);
lean_dec_ref(v_ctorVal_5685_);
v_a_5708_ = lean_ctor_get(v___y_5706_, 0);
v_isSharedCheck_5715_ = !lean_is_exclusive(v___y_5706_);
if (v_isSharedCheck_5715_ == 0)
{
v___x_5710_ = v___y_5706_;
v_isShared_5711_ = v_isSharedCheck_5715_;
goto v_resetjp_5709_;
}
else
{
lean_inc(v_a_5708_);
lean_dec(v___y_5706_);
v___x_5710_ = lean_box(0);
v_isShared_5711_ = v_isSharedCheck_5715_;
goto v_resetjp_5709_;
}
v_resetjp_5709_:
{
lean_object* v___x_5713_; 
if (v_isShared_5711_ == 0)
{
v___x_5713_ = v___x_5710_;
goto v_reusejp_5712_;
}
else
{
lean_object* v_reuseFailAlloc_5714_; 
v_reuseFailAlloc_5714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5714_, 0, v_a_5708_);
v___x_5713_ = v_reuseFailAlloc_5714_;
goto v_reusejp_5712_;
}
v_reusejp_5712_:
{
return v___x_5713_;
}
}
}
}
v___jp_5716_:
{
lean_object* v___x_5719_; 
v___x_5719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5719_, 0, v_lhs_5717_);
lean_ctor_set(v___x_5719_, 1, v_rhs_5718_);
v_a_5700_ = v___x_5719_;
goto v___jp_5699_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___boxed(lean_object* v_ctorVal_5761_, lean_object* v_sz_5762_, lean_object* v_i_5763_, lean_object* v_bs_5764_, lean_object* v___y_5765_, lean_object* v___y_5766_, lean_object* v___y_5767_, lean_object* v___y_5768_, lean_object* v___y_5769_){
_start:
{
size_t v_sz_boxed_5770_; size_t v_i_boxed_5771_; lean_object* v_res_5772_; 
v_sz_boxed_5770_ = lean_unbox_usize(v_sz_5762_);
lean_dec(v_sz_5762_);
v_i_boxed_5771_ = lean_unbox_usize(v_i_5763_);
lean_dec(v_i_5763_);
v_res_5772_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(v_ctorVal_5761_, v_sz_boxed_5770_, v_i_boxed_5771_, v_bs_5764_, v___y_5765_, v___y_5766_, v___y_5767_, v___y_5768_);
lean_dec(v___y_5768_);
lean_dec_ref(v___y_5767_);
lean_dec(v___y_5766_);
lean_dec_ref(v___y_5765_);
return v_res_5772_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5774_; lean_object* v___x_5775_; 
v___x_5774_ = lean_unsigned_to_nat(0u);
v___x_5775_ = l_Lean_Level_ofNat(v___x_5774_);
return v___x_5775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0(lean_object* v_ctorVal_5776_, lean_object* v_us_5777_, lean_object* v_numIndices_5778_, lean_object* v_xs_5779_, lean_object* v_type_5780_, lean_object* v___y_5781_, lean_object* v___y_5782_, lean_object* v___y_5783_, lean_object* v___y_5784_){
_start:
{
lean_object* v_toConstantVal_5786_; lean_object* v_induct_5787_; lean_object* v_numParams_5788_; lean_object* v___x_5789_; lean_object* v_noConfusionName_5790_; lean_object* v___x_5791_; lean_object* v___x_5792_; lean_object* v___x_5793_; lean_object* v_noConfusion_5794_; lean_object* v_noConfusion_5795_; lean_object* v_lower_5797_; lean_object* v_upper_5798_; lean_object* v___x_5905_; lean_object* v___x_5906_; lean_object* v___x_5907_; lean_object* v___x_5908_; lean_object* v_n_5909_; uint8_t v___x_5910_; 
v_toConstantVal_5786_ = lean_ctor_get(v_ctorVal_5776_, 0);
v_induct_5787_ = lean_ctor_get(v_ctorVal_5776_, 1);
v_numParams_5788_ = lean_ctor_get(v_ctorVal_5776_, 3);
v___x_5789_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__0));
lean_inc(v_induct_5787_);
v_noConfusionName_5790_ = l_Lean_Name_str___override(v_induct_5787_, v___x_5789_);
v___x_5791_ = lean_unsigned_to_nat(0u);
v___x_5792_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1);
v___x_5793_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5793_, 0, v___x_5792_);
lean_ctor_set(v___x_5793_, 1, v_us_5777_);
v_noConfusion_5794_ = l_Lean_mkConst(v_noConfusionName_5790_, v___x_5793_);
v_noConfusion_5795_ = l_Lean_Expr_app___override(v_noConfusion_5794_, v_type_5780_);
v___x_5905_ = lean_array_get_size(v_xs_5779_);
v___x_5906_ = lean_nat_sub(v___x_5905_, v_numParams_5788_);
v___x_5907_ = lean_nat_sub(v___x_5906_, v_numIndices_5778_);
lean_dec(v___x_5906_);
v___x_5908_ = lean_unsigned_to_nat(1u);
v_n_5909_ = lean_nat_sub(v___x_5907_, v___x_5908_);
lean_dec(v___x_5907_);
v___x_5910_ = lean_nat_dec_le(v_n_5909_, v___x_5791_);
if (v___x_5910_ == 0)
{
v_lower_5797_ = v_n_5909_;
v_upper_5798_ = v___x_5905_;
goto v___jp_5796_;
}
else
{
lean_dec(v_n_5909_);
v_lower_5797_ = v___x_5791_;
v_upper_5798_ = v___x_5905_;
goto v___jp_5796_;
}
v___jp_5796_:
{
lean_object* v___x_5799_; lean_object* v___x_5800_; lean_object* v_eqs_5801_; size_t v_sz_5802_; size_t v___x_5803_; lean_object* v___x_5804_; 
lean_inc_ref(v_xs_5779_);
v___x_5799_ = l_Array_toSubarray___redArg(v_xs_5779_, v_lower_5797_, v_upper_5798_);
v___x_5800_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v_eqs_5801_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(v___x_5799_, v___x_5800_);
v_sz_5802_ = lean_array_size(v_eqs_5801_);
v___x_5803_ = ((size_t)0ULL);
lean_inc_ref(v_eqs_5801_);
lean_inc_ref(v_ctorVal_5776_);
v___x_5804_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(v_ctorVal_5776_, v_sz_5802_, v___x_5803_, v_eqs_5801_, v___y_5781_, v___y_5782_, v___y_5783_, v___y_5784_);
if (lean_obj_tag(v___x_5804_) == 0)
{
lean_object* v_a_5805_; lean_object* v___x_5806_; lean_object* v_fst_5807_; lean_object* v_snd_5808_; lean_object* v___x_5809_; lean_object* v___x_5810_; lean_object* v___x_5811_; lean_object* v___x_5812_; 
v_a_5805_ = lean_ctor_get(v___x_5804_, 0);
lean_inc(v_a_5805_);
lean_dec_ref_known(v___x_5804_, 1);
v___x_5806_ = l_Array_unzip___redArg(v_a_5805_);
lean_dec(v_a_5805_);
v_fst_5807_ = lean_ctor_get(v___x_5806_, 0);
lean_inc(v_fst_5807_);
v_snd_5808_ = lean_ctor_get(v___x_5806_, 1);
lean_inc(v_snd_5808_);
lean_dec_ref(v___x_5806_);
v___x_5809_ = l_Lean_mkAppN(v_noConfusion_5795_, v_fst_5807_);
lean_dec(v_fst_5807_);
v___x_5810_ = l_Lean_mkAppN(v___x_5809_, v_snd_5808_);
lean_dec(v_snd_5808_);
v___x_5811_ = l_Lean_mkAppN(v___x_5810_, v_eqs_5801_);
lean_dec_ref(v_eqs_5801_);
lean_inc(v___y_5784_);
lean_inc_ref(v___y_5783_);
lean_inc(v___y_5782_);
lean_inc_ref(v___y_5781_);
lean_inc_ref(v___x_5811_);
v___x_5812_ = lean_infer_type(v___x_5811_, v___y_5781_, v___y_5782_, v___y_5783_, v___y_5784_);
if (lean_obj_tag(v___x_5812_) == 0)
{
lean_object* v_a_5813_; lean_object* v___x_5814_; 
v_a_5813_ = lean_ctor_get(v___x_5812_, 0);
lean_inc(v_a_5813_);
lean_dec_ref_known(v___x_5812_, 1);
lean_inc(v___y_5784_);
lean_inc_ref(v___y_5783_);
lean_inc(v___y_5782_);
lean_inc_ref(v___y_5781_);
v___x_5814_ = lean_whnf(v_a_5813_, v___y_5781_, v___y_5782_, v___y_5783_, v___y_5784_);
if (lean_obj_tag(v___x_5814_) == 0)
{
lean_object* v_a_5815_; 
v_a_5815_ = lean_ctor_get(v___x_5814_, 0);
lean_inc(v_a_5815_);
lean_dec_ref_known(v___x_5814_, 1);
if (lean_obj_tag(v_a_5815_) == 7)
{
lean_object* v_binderType_5816_; lean_object* v___x_5817_; lean_object* v___x_5818_; 
lean_inc_ref(v_toConstantVal_5786_);
lean_dec_ref(v_ctorVal_5776_);
v_binderType_5816_ = lean_ctor_get(v_a_5815_, 1);
lean_inc_ref(v_binderType_5816_);
lean_dec_ref_known(v_a_5815_, 3);
v___x_5817_ = lean_box(0);
v___x_5818_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_binderType_5816_, v___x_5817_, v___y_5781_, v___y_5782_, v___y_5783_, v___y_5784_);
if (lean_obj_tag(v___x_5818_) == 0)
{
lean_object* v_a_5819_; lean_object* v___x_5820_; lean_object* v___x_5821_; lean_object* v___x_5822_; 
v_a_5819_ = lean_ctor_get(v___x_5818_, 0);
lean_inc_n(v_a_5819_, 2);
lean_dec_ref_known(v___x_5818_, 1);
v___x_5820_ = l_Lean_Expr_app___override(v___x_5811_, v_a_5819_);
v___x_5821_ = l_Lean_Expr_mvarId_x21(v_a_5819_);
lean_dec(v_a_5819_);
v___x_5822_ = l_Lean_MVarId_intros(v___x_5821_, v___y_5781_, v___y_5782_, v___y_5783_, v___y_5784_);
if (lean_obj_tag(v___x_5822_) == 0)
{
lean_object* v_a_5823_; lean_object* v_snd_5824_; lean_object* v_name_5825_; lean_object* v___x_5826_; 
v_a_5823_ = lean_ctor_get(v___x_5822_, 0);
lean_inc(v_a_5823_);
lean_dec_ref_known(v___x_5822_, 1);
v_snd_5824_ = lean_ctor_get(v_a_5823_, 1);
lean_inc(v_snd_5824_);
lean_dec(v_a_5823_);
v_name_5825_ = lean_ctor_get(v_toConstantVal_5786_, 0);
lean_inc(v_name_5825_);
lean_dec_ref(v_toConstantVal_5786_);
v___x_5826_ = l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(v_snd_5824_, v_name_5825_, v___y_5781_, v___y_5782_, v___y_5783_, v___y_5784_);
if (lean_obj_tag(v___x_5826_) == 0)
{
lean_object* v___x_5827_; lean_object* v_a_5828_; lean_object* v___x_5830_; uint8_t v_isShared_5831_; uint8_t v_isSharedCheck_5855_; 
lean_dec_ref_known(v___x_5826_, 1);
v___x_5827_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v___x_5820_, v___y_5782_);
v_a_5828_ = lean_ctor_get(v___x_5827_, 0);
v_isSharedCheck_5855_ = !lean_is_exclusive(v___x_5827_);
if (v_isSharedCheck_5855_ == 0)
{
v___x_5830_ = v___x_5827_;
v_isShared_5831_ = v_isSharedCheck_5855_;
goto v_resetjp_5829_;
}
else
{
lean_inc(v_a_5828_);
lean_dec(v___x_5827_);
v___x_5830_ = lean_box(0);
v_isShared_5831_ = v_isSharedCheck_5855_;
goto v_resetjp_5829_;
}
v_resetjp_5829_:
{
uint8_t v___x_5832_; uint8_t v___x_5833_; uint8_t v___x_5834_; lean_object* v___x_5835_; 
v___x_5832_ = 0;
v___x_5833_ = 1;
v___x_5834_ = 1;
v___x_5835_ = l_Lean_Meta_mkLambdaFVars(v_xs_5779_, v_a_5828_, v___x_5832_, v___x_5833_, v___x_5832_, v___x_5833_, v___x_5834_, v___y_5781_, v___y_5782_, v___y_5783_, v___y_5784_);
lean_dec_ref(v_xs_5779_);
if (lean_obj_tag(v___x_5835_) == 0)
{
lean_object* v_a_5836_; lean_object* v___x_5838_; uint8_t v_isShared_5839_; uint8_t v_isSharedCheck_5846_; 
v_a_5836_ = lean_ctor_get(v___x_5835_, 0);
v_isSharedCheck_5846_ = !lean_is_exclusive(v___x_5835_);
if (v_isSharedCheck_5846_ == 0)
{
v___x_5838_ = v___x_5835_;
v_isShared_5839_ = v_isSharedCheck_5846_;
goto v_resetjp_5837_;
}
else
{
lean_inc(v_a_5836_);
lean_dec(v___x_5835_);
v___x_5838_ = lean_box(0);
v_isShared_5839_ = v_isSharedCheck_5846_;
goto v_resetjp_5837_;
}
v_resetjp_5837_:
{
lean_object* v___x_5841_; 
if (v_isShared_5831_ == 0)
{
lean_ctor_set_tag(v___x_5830_, 1);
lean_ctor_set(v___x_5830_, 0, v_a_5836_);
v___x_5841_ = v___x_5830_;
goto v_reusejp_5840_;
}
else
{
lean_object* v_reuseFailAlloc_5845_; 
v_reuseFailAlloc_5845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5845_, 0, v_a_5836_);
v___x_5841_ = v_reuseFailAlloc_5845_;
goto v_reusejp_5840_;
}
v_reusejp_5840_:
{
lean_object* v___x_5843_; 
if (v_isShared_5839_ == 0)
{
lean_ctor_set(v___x_5838_, 0, v___x_5841_);
v___x_5843_ = v___x_5838_;
goto v_reusejp_5842_;
}
else
{
lean_object* v_reuseFailAlloc_5844_; 
v_reuseFailAlloc_5844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5844_, 0, v___x_5841_);
v___x_5843_ = v_reuseFailAlloc_5844_;
goto v_reusejp_5842_;
}
v_reusejp_5842_:
{
return v___x_5843_;
}
}
}
}
else
{
lean_object* v_a_5847_; lean_object* v___x_5849_; uint8_t v_isShared_5850_; uint8_t v_isSharedCheck_5854_; 
lean_del_object(v___x_5830_);
v_a_5847_ = lean_ctor_get(v___x_5835_, 0);
v_isSharedCheck_5854_ = !lean_is_exclusive(v___x_5835_);
if (v_isSharedCheck_5854_ == 0)
{
v___x_5849_ = v___x_5835_;
v_isShared_5850_ = v_isSharedCheck_5854_;
goto v_resetjp_5848_;
}
else
{
lean_inc(v_a_5847_);
lean_dec(v___x_5835_);
v___x_5849_ = lean_box(0);
v_isShared_5850_ = v_isSharedCheck_5854_;
goto v_resetjp_5848_;
}
v_resetjp_5848_:
{
lean_object* v___x_5852_; 
if (v_isShared_5850_ == 0)
{
v___x_5852_ = v___x_5849_;
goto v_reusejp_5851_;
}
else
{
lean_object* v_reuseFailAlloc_5853_; 
v_reuseFailAlloc_5853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5853_, 0, v_a_5847_);
v___x_5852_ = v_reuseFailAlloc_5853_;
goto v_reusejp_5851_;
}
v_reusejp_5851_:
{
return v___x_5852_;
}
}
}
}
}
else
{
lean_object* v_a_5856_; lean_object* v___x_5858_; uint8_t v_isShared_5859_; uint8_t v_isSharedCheck_5863_; 
lean_dec_ref(v___x_5820_);
lean_dec_ref(v_xs_5779_);
v_a_5856_ = lean_ctor_get(v___x_5826_, 0);
v_isSharedCheck_5863_ = !lean_is_exclusive(v___x_5826_);
if (v_isSharedCheck_5863_ == 0)
{
v___x_5858_ = v___x_5826_;
v_isShared_5859_ = v_isSharedCheck_5863_;
goto v_resetjp_5857_;
}
else
{
lean_inc(v_a_5856_);
lean_dec(v___x_5826_);
v___x_5858_ = lean_box(0);
v_isShared_5859_ = v_isSharedCheck_5863_;
goto v_resetjp_5857_;
}
v_resetjp_5857_:
{
lean_object* v___x_5861_; 
if (v_isShared_5859_ == 0)
{
v___x_5861_ = v___x_5858_;
goto v_reusejp_5860_;
}
else
{
lean_object* v_reuseFailAlloc_5862_; 
v_reuseFailAlloc_5862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5862_, 0, v_a_5856_);
v___x_5861_ = v_reuseFailAlloc_5862_;
goto v_reusejp_5860_;
}
v_reusejp_5860_:
{
return v___x_5861_;
}
}
}
}
else
{
lean_object* v_a_5864_; lean_object* v___x_5866_; uint8_t v_isShared_5867_; uint8_t v_isSharedCheck_5871_; 
lean_dec_ref(v___x_5820_);
lean_dec_ref(v_toConstantVal_5786_);
lean_dec_ref(v_xs_5779_);
v_a_5864_ = lean_ctor_get(v___x_5822_, 0);
v_isSharedCheck_5871_ = !lean_is_exclusive(v___x_5822_);
if (v_isSharedCheck_5871_ == 0)
{
v___x_5866_ = v___x_5822_;
v_isShared_5867_ = v_isSharedCheck_5871_;
goto v_resetjp_5865_;
}
else
{
lean_inc(v_a_5864_);
lean_dec(v___x_5822_);
v___x_5866_ = lean_box(0);
v_isShared_5867_ = v_isSharedCheck_5871_;
goto v_resetjp_5865_;
}
v_resetjp_5865_:
{
lean_object* v___x_5869_; 
if (v_isShared_5867_ == 0)
{
v___x_5869_ = v___x_5866_;
goto v_reusejp_5868_;
}
else
{
lean_object* v_reuseFailAlloc_5870_; 
v_reuseFailAlloc_5870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5870_, 0, v_a_5864_);
v___x_5869_ = v_reuseFailAlloc_5870_;
goto v_reusejp_5868_;
}
v_reusejp_5868_:
{
return v___x_5869_;
}
}
}
}
else
{
lean_object* v_a_5872_; lean_object* v___x_5874_; uint8_t v_isShared_5875_; uint8_t v_isSharedCheck_5879_; 
lean_dec_ref(v___x_5811_);
lean_dec_ref(v_toConstantVal_5786_);
lean_dec_ref(v_xs_5779_);
v_a_5872_ = lean_ctor_get(v___x_5818_, 0);
v_isSharedCheck_5879_ = !lean_is_exclusive(v___x_5818_);
if (v_isSharedCheck_5879_ == 0)
{
v___x_5874_ = v___x_5818_;
v_isShared_5875_ = v_isSharedCheck_5879_;
goto v_resetjp_5873_;
}
else
{
lean_inc(v_a_5872_);
lean_dec(v___x_5818_);
v___x_5874_ = lean_box(0);
v_isShared_5875_ = v_isSharedCheck_5879_;
goto v_resetjp_5873_;
}
v_resetjp_5873_:
{
lean_object* v___x_5877_; 
if (v_isShared_5875_ == 0)
{
v___x_5877_ = v___x_5874_;
goto v_reusejp_5876_;
}
else
{
lean_object* v_reuseFailAlloc_5878_; 
v_reuseFailAlloc_5878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5878_, 0, v_a_5872_);
v___x_5877_ = v_reuseFailAlloc_5878_;
goto v_reusejp_5876_;
}
v_reusejp_5876_:
{
return v___x_5877_;
}
}
}
}
else
{
lean_object* v___x_5880_; 
lean_dec(v_a_5815_);
lean_dec_ref(v___x_5811_);
lean_dec_ref(v_xs_5779_);
v___x_5880_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5776_, v___y_5781_, v___y_5782_, v___y_5783_, v___y_5784_);
return v___x_5880_;
}
}
else
{
lean_object* v_a_5881_; lean_object* v___x_5883_; uint8_t v_isShared_5884_; uint8_t v_isSharedCheck_5888_; 
lean_dec_ref(v___x_5811_);
lean_dec_ref(v_xs_5779_);
lean_dec_ref(v_ctorVal_5776_);
v_a_5881_ = lean_ctor_get(v___x_5814_, 0);
v_isSharedCheck_5888_ = !lean_is_exclusive(v___x_5814_);
if (v_isSharedCheck_5888_ == 0)
{
v___x_5883_ = v___x_5814_;
v_isShared_5884_ = v_isSharedCheck_5888_;
goto v_resetjp_5882_;
}
else
{
lean_inc(v_a_5881_);
lean_dec(v___x_5814_);
v___x_5883_ = lean_box(0);
v_isShared_5884_ = v_isSharedCheck_5888_;
goto v_resetjp_5882_;
}
v_resetjp_5882_:
{
lean_object* v___x_5886_; 
if (v_isShared_5884_ == 0)
{
v___x_5886_ = v___x_5883_;
goto v_reusejp_5885_;
}
else
{
lean_object* v_reuseFailAlloc_5887_; 
v_reuseFailAlloc_5887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5887_, 0, v_a_5881_);
v___x_5886_ = v_reuseFailAlloc_5887_;
goto v_reusejp_5885_;
}
v_reusejp_5885_:
{
return v___x_5886_;
}
}
}
}
else
{
lean_object* v_a_5889_; lean_object* v___x_5891_; uint8_t v_isShared_5892_; uint8_t v_isSharedCheck_5896_; 
lean_dec_ref(v___x_5811_);
lean_dec_ref(v_xs_5779_);
lean_dec_ref(v_ctorVal_5776_);
v_a_5889_ = lean_ctor_get(v___x_5812_, 0);
v_isSharedCheck_5896_ = !lean_is_exclusive(v___x_5812_);
if (v_isSharedCheck_5896_ == 0)
{
v___x_5891_ = v___x_5812_;
v_isShared_5892_ = v_isSharedCheck_5896_;
goto v_resetjp_5890_;
}
else
{
lean_inc(v_a_5889_);
lean_dec(v___x_5812_);
v___x_5891_ = lean_box(0);
v_isShared_5892_ = v_isSharedCheck_5896_;
goto v_resetjp_5890_;
}
v_resetjp_5890_:
{
lean_object* v___x_5894_; 
if (v_isShared_5892_ == 0)
{
v___x_5894_ = v___x_5891_;
goto v_reusejp_5893_;
}
else
{
lean_object* v_reuseFailAlloc_5895_; 
v_reuseFailAlloc_5895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5895_, 0, v_a_5889_);
v___x_5894_ = v_reuseFailAlloc_5895_;
goto v_reusejp_5893_;
}
v_reusejp_5893_:
{
return v___x_5894_;
}
}
}
}
else
{
lean_object* v_a_5897_; lean_object* v___x_5899_; uint8_t v_isShared_5900_; uint8_t v_isSharedCheck_5904_; 
lean_dec_ref(v_eqs_5801_);
lean_dec_ref(v_noConfusion_5795_);
lean_dec_ref(v_xs_5779_);
lean_dec_ref(v_ctorVal_5776_);
v_a_5897_ = lean_ctor_get(v___x_5804_, 0);
v_isSharedCheck_5904_ = !lean_is_exclusive(v___x_5804_);
if (v_isSharedCheck_5904_ == 0)
{
v___x_5899_ = v___x_5804_;
v_isShared_5900_ = v_isSharedCheck_5904_;
goto v_resetjp_5898_;
}
else
{
lean_inc(v_a_5897_);
lean_dec(v___x_5804_);
v___x_5899_ = lean_box(0);
v_isShared_5900_ = v_isSharedCheck_5904_;
goto v_resetjp_5898_;
}
v_resetjp_5898_:
{
lean_object* v___x_5902_; 
if (v_isShared_5900_ == 0)
{
v___x_5902_ = v___x_5899_;
goto v_reusejp_5901_;
}
else
{
lean_object* v_reuseFailAlloc_5903_; 
v_reuseFailAlloc_5903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5903_, 0, v_a_5897_);
v___x_5902_ = v_reuseFailAlloc_5903_;
goto v_reusejp_5901_;
}
v_reusejp_5901_:
{
return v___x_5902_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___boxed(lean_object* v_ctorVal_5911_, lean_object* v_us_5912_, lean_object* v_numIndices_5913_, lean_object* v_xs_5914_, lean_object* v_type_5915_, lean_object* v___y_5916_, lean_object* v___y_5917_, lean_object* v___y_5918_, lean_object* v___y_5919_, lean_object* v___y_5920_){
_start:
{
lean_object* v_res_5921_; 
v_res_5921_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0(v_ctorVal_5911_, v_us_5912_, v_numIndices_5913_, v_xs_5914_, v_type_5915_, v___y_5916_, v___y_5917_, v___y_5918_, v___y_5919_);
lean_dec(v___y_5919_);
lean_dec_ref(v___y_5918_);
lean_dec(v___y_5917_);
lean_dec_ref(v___y_5916_);
lean_dec(v_numIndices_5913_);
return v_res_5921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(lean_object* v_ctorVal_5922_, lean_object* v_typeInfo_5923_, lean_object* v_a_5924_, lean_object* v_a_5925_, lean_object* v_a_5926_, lean_object* v_a_5927_){
_start:
{
lean_object* v_thmType_5929_; lean_object* v_us_5930_; lean_object* v_numIndices_5931_; lean_object* v___f_5932_; uint8_t v___x_5933_; lean_object* v___x_5934_; 
v_thmType_5929_ = lean_ctor_get(v_typeInfo_5923_, 0);
lean_inc_ref(v_thmType_5929_);
v_us_5930_ = lean_ctor_get(v_typeInfo_5923_, 1);
lean_inc(v_us_5930_);
v_numIndices_5931_ = lean_ctor_get(v_typeInfo_5923_, 2);
lean_inc(v_numIndices_5931_);
lean_dec_ref(v_typeInfo_5923_);
v___f_5932_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___boxed), 10, 3);
lean_closure_set(v___f_5932_, 0, v_ctorVal_5922_);
lean_closure_set(v___f_5932_, 1, v_us_5930_);
lean_closure_set(v___f_5932_, 2, v_numIndices_5931_);
v___x_5933_ = 0;
v___x_5934_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_thmType_5929_, v___f_5932_, v___x_5933_, v___x_5933_, v_a_5924_, v_a_5925_, v_a_5926_, v_a_5927_);
return v___x_5934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___boxed(lean_object* v_ctorVal_5935_, lean_object* v_typeInfo_5936_, lean_object* v_a_5937_, lean_object* v_a_5938_, lean_object* v_a_5939_, lean_object* v_a_5940_, lean_object* v_a_5941_){
_start:
{
lean_object* v_res_5942_; 
v_res_5942_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(v_ctorVal_5935_, v_typeInfo_5936_, v_a_5937_, v_a_5938_, v_a_5939_, v_a_5940_);
lean_dec(v_a_5940_);
lean_dec_ref(v_a_5939_);
lean_dec(v_a_5938_);
lean_dec_ref(v_a_5937_);
return v_res_5942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHInjectiveTheoremNameFor(lean_object* v_ctorName_5945_){
_start:
{
lean_object* v___x_5946_; lean_object* v___x_5947_; 
v___x_5946_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0));
v___x_5947_ = l_Lean_Name_str___override(v_ctorName_5945_, v___x_5946_);
return v___x_5947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(lean_object* v_thmName_5948_, lean_object* v_ctorVal_5949_, lean_object* v_a_5950_, lean_object* v_a_5951_, lean_object* v_a_5952_, lean_object* v_a_5953_){
_start:
{
lean_object* v___x_5955_; 
lean_inc_ref(v_ctorVal_5949_);
v___x_5955_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(v_ctorVal_5949_, v_a_5950_, v_a_5951_, v_a_5952_, v_a_5953_);
if (lean_obj_tag(v___x_5955_) == 0)
{
lean_object* v_a_5956_; lean_object* v___x_5958_; uint8_t v_isShared_5959_; uint8_t v_isSharedCheck_6017_; 
v_a_5956_ = lean_ctor_get(v___x_5955_, 0);
v_isSharedCheck_6017_ = !lean_is_exclusive(v___x_5955_);
if (v_isSharedCheck_6017_ == 0)
{
v___x_5958_ = v___x_5955_;
v_isShared_5959_ = v_isSharedCheck_6017_;
goto v_resetjp_5957_;
}
else
{
lean_inc(v_a_5956_);
lean_dec(v___x_5955_);
v___x_5958_ = lean_box(0);
v_isShared_5959_ = v_isSharedCheck_6017_;
goto v_resetjp_5957_;
}
v_resetjp_5957_:
{
if (lean_obj_tag(v_a_5956_) == 1)
{
lean_object* v_val_5960_; lean_object* v___x_5961_; 
lean_del_object(v___x_5958_);
v_val_5960_ = lean_ctor_get(v_a_5956_, 0);
lean_inc_n(v_val_5960_, 2);
lean_dec_ref_known(v_a_5956_, 1);
lean_inc_ref(v_ctorVal_5949_);
v___x_5961_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(v_ctorVal_5949_, v_val_5960_, v_a_5950_, v_a_5951_, v_a_5952_, v_a_5953_);
if (lean_obj_tag(v___x_5961_) == 0)
{
lean_object* v_a_5962_; lean_object* v___x_5964_; uint8_t v_isShared_5965_; uint8_t v_isSharedCheck_6004_; 
v_a_5962_ = lean_ctor_get(v___x_5961_, 0);
v_isSharedCheck_6004_ = !lean_is_exclusive(v___x_5961_);
if (v_isSharedCheck_6004_ == 0)
{
v___x_5964_ = v___x_5961_;
v_isShared_5965_ = v_isSharedCheck_6004_;
goto v_resetjp_5963_;
}
else
{
lean_inc(v_a_5962_);
lean_dec(v___x_5961_);
v___x_5964_ = lean_box(0);
v_isShared_5965_ = v_isSharedCheck_6004_;
goto v_resetjp_5963_;
}
v_resetjp_5963_:
{
if (lean_obj_tag(v_a_5962_) == 1)
{
lean_object* v_toConstantVal_5966_; lean_object* v_val_5967_; lean_object* v___x_5969_; uint8_t v_isShared_5970_; uint8_t v_isSharedCheck_5999_; 
v_toConstantVal_5966_ = lean_ctor_get(v_ctorVal_5949_, 0);
lean_inc_ref(v_toConstantVal_5966_);
lean_dec_ref(v_ctorVal_5949_);
v_val_5967_ = lean_ctor_get(v_a_5962_, 0);
v_isSharedCheck_5999_ = !lean_is_exclusive(v_a_5962_);
if (v_isSharedCheck_5999_ == 0)
{
v___x_5969_ = v_a_5962_;
v_isShared_5970_ = v_isSharedCheck_5999_;
goto v_resetjp_5968_;
}
else
{
lean_inc(v_val_5967_);
lean_dec(v_a_5962_);
v___x_5969_ = lean_box(0);
v_isShared_5970_ = v_isSharedCheck_5999_;
goto v_resetjp_5968_;
}
v_resetjp_5968_:
{
lean_object* v_levelParams_5971_; lean_object* v___x_5973_; uint8_t v_isShared_5974_; uint8_t v_isSharedCheck_5996_; 
v_levelParams_5971_ = lean_ctor_get(v_toConstantVal_5966_, 1);
v_isSharedCheck_5996_ = !lean_is_exclusive(v_toConstantVal_5966_);
if (v_isSharedCheck_5996_ == 0)
{
lean_object* v_unused_5997_; lean_object* v_unused_5998_; 
v_unused_5997_ = lean_ctor_get(v_toConstantVal_5966_, 2);
lean_dec(v_unused_5997_);
v_unused_5998_ = lean_ctor_get(v_toConstantVal_5966_, 0);
lean_dec(v_unused_5998_);
v___x_5973_ = v_toConstantVal_5966_;
v_isShared_5974_ = v_isSharedCheck_5996_;
goto v_resetjp_5972_;
}
else
{
lean_inc(v_levelParams_5971_);
lean_dec(v_toConstantVal_5966_);
v___x_5973_ = lean_box(0);
v_isShared_5974_ = v_isSharedCheck_5996_;
goto v_resetjp_5972_;
}
v_resetjp_5972_:
{
lean_object* v_thmType_5975_; lean_object* v___x_5977_; uint8_t v_isShared_5978_; uint8_t v_isSharedCheck_5993_; 
v_thmType_5975_ = lean_ctor_get(v_val_5960_, 0);
v_isSharedCheck_5993_ = !lean_is_exclusive(v_val_5960_);
if (v_isSharedCheck_5993_ == 0)
{
lean_object* v_unused_5994_; lean_object* v_unused_5995_; 
v_unused_5994_ = lean_ctor_get(v_val_5960_, 2);
lean_dec(v_unused_5994_);
v_unused_5995_ = lean_ctor_get(v_val_5960_, 1);
lean_dec(v_unused_5995_);
v___x_5977_ = v_val_5960_;
v_isShared_5978_ = v_isSharedCheck_5993_;
goto v_resetjp_5976_;
}
else
{
lean_inc(v_thmType_5975_);
lean_dec(v_val_5960_);
v___x_5977_ = lean_box(0);
v_isShared_5978_ = v_isSharedCheck_5993_;
goto v_resetjp_5976_;
}
v_resetjp_5976_:
{
lean_object* v___x_5980_; 
lean_inc(v_thmName_5948_);
if (v_isShared_5974_ == 0)
{
lean_ctor_set(v___x_5973_, 2, v_thmType_5975_);
lean_ctor_set(v___x_5973_, 0, v_thmName_5948_);
v___x_5980_ = v___x_5973_;
goto v_reusejp_5979_;
}
else
{
lean_object* v_reuseFailAlloc_5992_; 
v_reuseFailAlloc_5992_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5992_, 0, v_thmName_5948_);
lean_ctor_set(v_reuseFailAlloc_5992_, 1, v_levelParams_5971_);
lean_ctor_set(v_reuseFailAlloc_5992_, 2, v_thmType_5975_);
v___x_5980_ = v_reuseFailAlloc_5992_;
goto v_reusejp_5979_;
}
v_reusejp_5979_:
{
lean_object* v___x_5981_; lean_object* v___x_5982_; lean_object* v___x_5984_; 
v___x_5981_ = lean_box(0);
v___x_5982_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5982_, 0, v_thmName_5948_);
lean_ctor_set(v___x_5982_, 1, v___x_5981_);
if (v_isShared_5978_ == 0)
{
lean_ctor_set(v___x_5977_, 2, v___x_5982_);
lean_ctor_set(v___x_5977_, 1, v_val_5967_);
lean_ctor_set(v___x_5977_, 0, v___x_5980_);
v___x_5984_ = v___x_5977_;
goto v_reusejp_5983_;
}
else
{
lean_object* v_reuseFailAlloc_5991_; 
v_reuseFailAlloc_5991_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5991_, 0, v___x_5980_);
lean_ctor_set(v_reuseFailAlloc_5991_, 1, v_val_5967_);
lean_ctor_set(v_reuseFailAlloc_5991_, 2, v___x_5982_);
v___x_5984_ = v_reuseFailAlloc_5991_;
goto v_reusejp_5983_;
}
v_reusejp_5983_:
{
lean_object* v___x_5986_; 
if (v_isShared_5970_ == 0)
{
lean_ctor_set(v___x_5969_, 0, v___x_5984_);
v___x_5986_ = v___x_5969_;
goto v_reusejp_5985_;
}
else
{
lean_object* v_reuseFailAlloc_5990_; 
v_reuseFailAlloc_5990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5990_, 0, v___x_5984_);
v___x_5986_ = v_reuseFailAlloc_5990_;
goto v_reusejp_5985_;
}
v_reusejp_5985_:
{
lean_object* v___x_5988_; 
if (v_isShared_5965_ == 0)
{
lean_ctor_set(v___x_5964_, 0, v___x_5986_);
v___x_5988_ = v___x_5964_;
goto v_reusejp_5987_;
}
else
{
lean_object* v_reuseFailAlloc_5989_; 
v_reuseFailAlloc_5989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5989_, 0, v___x_5986_);
v___x_5988_ = v_reuseFailAlloc_5989_;
goto v_reusejp_5987_;
}
v_reusejp_5987_:
{
return v___x_5988_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_6000_; lean_object* v___x_6002_; 
lean_dec(v_a_5962_);
lean_dec(v_val_5960_);
lean_dec_ref(v_ctorVal_5949_);
lean_dec(v_thmName_5948_);
v___x_6000_ = lean_box(0);
if (v_isShared_5965_ == 0)
{
lean_ctor_set(v___x_5964_, 0, v___x_6000_);
v___x_6002_ = v___x_5964_;
goto v_reusejp_6001_;
}
else
{
lean_object* v_reuseFailAlloc_6003_; 
v_reuseFailAlloc_6003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6003_, 0, v___x_6000_);
v___x_6002_ = v_reuseFailAlloc_6003_;
goto v_reusejp_6001_;
}
v_reusejp_6001_:
{
return v___x_6002_;
}
}
}
}
else
{
lean_object* v_a_6005_; lean_object* v___x_6007_; uint8_t v_isShared_6008_; uint8_t v_isSharedCheck_6012_; 
lean_dec(v_val_5960_);
lean_dec_ref(v_ctorVal_5949_);
lean_dec(v_thmName_5948_);
v_a_6005_ = lean_ctor_get(v___x_5961_, 0);
v_isSharedCheck_6012_ = !lean_is_exclusive(v___x_5961_);
if (v_isSharedCheck_6012_ == 0)
{
v___x_6007_ = v___x_5961_;
v_isShared_6008_ = v_isSharedCheck_6012_;
goto v_resetjp_6006_;
}
else
{
lean_inc(v_a_6005_);
lean_dec(v___x_5961_);
v___x_6007_ = lean_box(0);
v_isShared_6008_ = v_isSharedCheck_6012_;
goto v_resetjp_6006_;
}
v_resetjp_6006_:
{
lean_object* v___x_6010_; 
if (v_isShared_6008_ == 0)
{
v___x_6010_ = v___x_6007_;
goto v_reusejp_6009_;
}
else
{
lean_object* v_reuseFailAlloc_6011_; 
v_reuseFailAlloc_6011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6011_, 0, v_a_6005_);
v___x_6010_ = v_reuseFailAlloc_6011_;
goto v_reusejp_6009_;
}
v_reusejp_6009_:
{
return v___x_6010_;
}
}
}
}
else
{
lean_object* v___x_6013_; lean_object* v___x_6015_; 
lean_dec(v_a_5956_);
lean_dec_ref(v_ctorVal_5949_);
lean_dec(v_thmName_5948_);
v___x_6013_ = lean_box(0);
if (v_isShared_5959_ == 0)
{
lean_ctor_set(v___x_5958_, 0, v___x_6013_);
v___x_6015_ = v___x_5958_;
goto v_reusejp_6014_;
}
else
{
lean_object* v_reuseFailAlloc_6016_; 
v_reuseFailAlloc_6016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6016_, 0, v___x_6013_);
v___x_6015_ = v_reuseFailAlloc_6016_;
goto v_reusejp_6014_;
}
v_reusejp_6014_:
{
return v___x_6015_;
}
}
}
}
else
{
lean_object* v_a_6018_; lean_object* v___x_6020_; uint8_t v_isShared_6021_; uint8_t v_isSharedCheck_6025_; 
lean_dec_ref(v_ctorVal_5949_);
lean_dec(v_thmName_5948_);
v_a_6018_ = lean_ctor_get(v___x_5955_, 0);
v_isSharedCheck_6025_ = !lean_is_exclusive(v___x_5955_);
if (v_isSharedCheck_6025_ == 0)
{
v___x_6020_ = v___x_5955_;
v_isShared_6021_ = v_isSharedCheck_6025_;
goto v_resetjp_6019_;
}
else
{
lean_inc(v_a_6018_);
lean_dec(v___x_5955_);
v___x_6020_ = lean_box(0);
v_isShared_6021_ = v_isSharedCheck_6025_;
goto v_resetjp_6019_;
}
v_resetjp_6019_:
{
lean_object* v___x_6023_; 
if (v_isShared_6021_ == 0)
{
v___x_6023_ = v___x_6020_;
goto v_reusejp_6022_;
}
else
{
lean_object* v_reuseFailAlloc_6024_; 
v_reuseFailAlloc_6024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6024_, 0, v_a_6018_);
v___x_6023_ = v_reuseFailAlloc_6024_;
goto v_reusejp_6022_;
}
v_reusejp_6022_:
{
return v___x_6023_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f___boxed(lean_object* v_thmName_6026_, lean_object* v_ctorVal_6027_, lean_object* v_a_6028_, lean_object* v_a_6029_, lean_object* v_a_6030_, lean_object* v_a_6031_, lean_object* v_a_6032_){
_start:
{
lean_object* v_res_6033_; 
v_res_6033_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(v_thmName_6026_, v_ctorVal_6027_, v_a_6028_, v_a_6029_, v_a_6030_, v_a_6031_);
lean_dec(v_a_6031_);
lean_dec_ref(v_a_6030_);
lean_dec(v_a_6029_);
lean_dec_ref(v_a_6028_);
return v_res_6033_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(lean_object* v_env_6034_, lean_object* v_n_6035_){
_start:
{
if (lean_obj_tag(v_n_6035_) == 1)
{
lean_object* v_pre_6036_; lean_object* v_str_6037_; lean_object* v___x_6038_; uint8_t v___x_6039_; 
v_pre_6036_ = lean_ctor_get(v_n_6035_, 0);
lean_inc(v_pre_6036_);
v_str_6037_ = lean_ctor_get(v_n_6035_, 1);
lean_inc_ref(v_str_6037_);
lean_dec_ref_known(v_n_6035_, 2);
v___x_6038_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0));
v___x_6039_ = lean_string_dec_eq(v_str_6037_, v___x_6038_);
lean_dec_ref(v_str_6037_);
if (v___x_6039_ == 0)
{
lean_dec(v_pre_6036_);
lean_dec_ref(v_env_6034_);
return v___x_6039_;
}
else
{
uint8_t v___x_6040_; lean_object* v___x_6041_; 
v___x_6040_ = 0;
v___x_6041_ = l_Lean_Environment_find_x3f(v_env_6034_, v_pre_6036_, v___x_6040_);
if (lean_obj_tag(v___x_6041_) == 1)
{
lean_object* v_val_6042_; 
v_val_6042_ = lean_ctor_get(v___x_6041_, 0);
lean_inc(v_val_6042_);
lean_dec_ref_known(v___x_6041_, 1);
if (lean_obj_tag(v_val_6042_) == 6)
{
lean_dec_ref_known(v_val_6042_, 1);
return v___x_6039_;
}
else
{
lean_dec(v_val_6042_);
return v___x_6040_;
}
}
else
{
lean_dec(v___x_6041_);
return v___x_6040_;
}
}
}
else
{
uint8_t v___x_6043_; 
lean_dec(v_n_6035_);
lean_dec_ref(v_env_6034_);
v___x_6043_ = 0;
return v___x_6043_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2____boxed(lean_object* v_env_6044_, lean_object* v_n_6045_){
_start:
{
uint8_t v_res_6046_; lean_object* v_r_6047_; 
v_res_6046_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(v_env_6044_, v_n_6045_);
v_r_6047_ = lean_box(v_res_6046_);
return v_r_6047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_6050_; lean_object* v___x_6051_; 
v___f_6050_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_));
v___x_6051_ = l_Lean_registerReservedNamePredicate(v___f_6050_);
return v___x_6051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2____boxed(lean_object* v_a_6052_){
_start:
{
lean_object* v_res_6053_; 
v_res_6053_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_();
return v_res_6053_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(lean_object* v_thm_6054_, lean_object* v___y_6055_){
_start:
{
lean_object* v___x_6057_; lean_object* v_env_6058_; lean_object* v_toConstantVal_6059_; lean_object* v_value_6060_; lean_object* v_all_6061_; uint8_t v___y_6063_; lean_object* v_type_6071_; uint8_t v___x_6072_; 
v___x_6057_ = lean_st_ref_get(v___y_6055_);
v_env_6058_ = lean_ctor_get(v___x_6057_, 0);
lean_inc_ref_n(v_env_6058_, 2);
lean_dec(v___x_6057_);
v_toConstantVal_6059_ = lean_ctor_get(v_thm_6054_, 0);
v_value_6060_ = lean_ctor_get(v_thm_6054_, 1);
v_all_6061_ = lean_ctor_get(v_thm_6054_, 2);
v_type_6071_ = lean_ctor_get(v_toConstantVal_6059_, 2);
v___x_6072_ = l_Lean_Environment_hasUnsafe(v_env_6058_, v_type_6071_);
if (v___x_6072_ == 0)
{
uint8_t v___x_6073_; 
v___x_6073_ = l_Lean_Environment_hasUnsafe(v_env_6058_, v_value_6060_);
v___y_6063_ = v___x_6073_;
goto v___jp_6062_;
}
else
{
lean_dec_ref(v_env_6058_);
v___y_6063_ = v___x_6072_;
goto v___jp_6062_;
}
v___jp_6062_:
{
if (v___y_6063_ == 0)
{
lean_object* v___x_6064_; lean_object* v___x_6065_; 
v___x_6064_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_6064_, 0, v_thm_6054_);
v___x_6065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6065_, 0, v___x_6064_);
return v___x_6065_;
}
else
{
lean_object* v___x_6066_; uint8_t v___x_6067_; lean_object* v___x_6068_; lean_object* v___x_6069_; lean_object* v___x_6070_; 
lean_inc(v_all_6061_);
lean_inc_ref(v_value_6060_);
lean_inc_ref(v_toConstantVal_6059_);
lean_dec_ref(v_thm_6054_);
v___x_6066_ = lean_box(0);
v___x_6067_ = 0;
v___x_6068_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_6068_, 0, v_toConstantVal_6059_);
lean_ctor_set(v___x_6068_, 1, v_value_6060_);
lean_ctor_set(v___x_6068_, 2, v___x_6066_);
lean_ctor_set(v___x_6068_, 3, v_all_6061_);
lean_ctor_set_uint8(v___x_6068_, sizeof(void*)*4, v___x_6067_);
v___x_6069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6069_, 0, v___x_6068_);
v___x_6070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6070_, 0, v___x_6069_);
return v___x_6070_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_thm_6074_, lean_object* v___y_6075_, lean_object* v___y_6076_){
_start:
{
lean_object* v_res_6077_; 
v_res_6077_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(v_thm_6074_, v___y_6075_);
lean_dec(v___y_6075_);
return v_res_6077_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0(lean_object* v_thm_6078_, lean_object* v___y_6079_, lean_object* v___y_6080_, lean_object* v___y_6081_, lean_object* v___y_6082_){
_start:
{
lean_object* v___x_6084_; 
v___x_6084_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(v_thm_6078_, v___y_6082_);
return v___x_6084_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___boxed(lean_object* v_thm_6085_, lean_object* v___y_6086_, lean_object* v___y_6087_, lean_object* v___y_6088_, lean_object* v___y_6089_, lean_object* v___y_6090_){
_start:
{
lean_object* v_res_6091_; 
v_res_6091_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0(v_thm_6085_, v___y_6086_, v___y_6087_, v___y_6088_, v___y_6089_);
lean_dec(v___y_6089_);
lean_dec_ref(v___y_6088_);
lean_dec(v___y_6087_);
lean_dec_ref(v___y_6086_);
return v_res_6091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(lean_object* v_val_6092_, uint8_t v___x_6093_, lean_object* v___y_6094_, lean_object* v___y_6095_, lean_object* v___y_6096_, lean_object* v___y_6097_){
_start:
{
lean_object* v___x_6099_; lean_object* v_a_6100_; lean_object* v___x_6101_; 
v___x_6099_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(v_val_6092_, v___y_6097_);
v_a_6100_ = lean_ctor_get(v___x_6099_, 0);
lean_inc(v_a_6100_);
lean_dec_ref(v___x_6099_);
v___x_6101_ = l_Lean_addDecl(v_a_6100_, v___x_6093_, v___y_6096_, v___y_6097_);
return v___x_6101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object* v_val_6102_, lean_object* v___x_6103_, lean_object* v___y_6104_, lean_object* v___y_6105_, lean_object* v___y_6106_, lean_object* v___y_6107_, lean_object* v___y_6108_){
_start:
{
uint8_t v___x_2143__boxed_6109_; lean_object* v_res_6110_; 
v___x_2143__boxed_6109_ = lean_unbox(v___x_6103_);
v_res_6110_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(v_val_6102_, v___x_2143__boxed_6109_, v___y_6104_, v___y_6105_, v___y_6106_, v___y_6107_);
lean_dec(v___y_6107_);
lean_dec_ref(v___y_6106_);
lean_dec(v___y_6105_);
lean_dec_ref(v___y_6104_);
return v_res_6110_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6113_; lean_object* v___x_6114_; lean_object* v___x_6115_; 
v___x_6113_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__0, &l_Lean_Meta_mkInjectiveTheorems___closed__0_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__0);
v___x_6114_ = lean_unsigned_to_nat(0u);
v___x_6115_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_6115_, 0, v___x_6114_);
lean_ctor_set(v___x_6115_, 1, v___x_6114_);
lean_ctor_set(v___x_6115_, 2, v___x_6114_);
lean_ctor_set(v___x_6115_, 3, v___x_6114_);
lean_ctor_set(v___x_6115_, 4, v___x_6113_);
lean_ctor_set(v___x_6115_, 5, v___x_6113_);
lean_ctor_set(v___x_6115_, 6, v___x_6113_);
lean_ctor_set(v___x_6115_, 7, v___x_6113_);
lean_ctor_set(v___x_6115_, 8, v___x_6113_);
lean_ctor_set(v___x_6115_, 9, v___x_6113_);
lean_ctor_set(v___x_6115_, 10, v___x_6113_);
return v___x_6115_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6116_; lean_object* v___x_6117_; 
v___x_6116_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__0, &l_Lean_Meta_mkInjectiveTheorems___closed__0_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__0);
v___x_6117_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6117_, 0, v___x_6116_);
lean_ctor_set(v___x_6117_, 1, v___x_6116_);
lean_ctor_set(v___x_6117_, 2, v___x_6116_);
lean_ctor_set(v___x_6117_, 3, v___x_6116_);
lean_ctor_set(v___x_6117_, 4, v___x_6116_);
lean_ctor_set(v___x_6117_, 5, v___x_6116_);
return v___x_6117_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6118_; lean_object* v___x_6119_; 
v___x_6118_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__0, &l_Lean_Meta_mkInjectiveTheorems___closed__0_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__0);
v___x_6119_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6119_, 0, v___x_6118_);
lean_ctor_set(v___x_6119_, 1, v___x_6118_);
lean_ctor_set(v___x_6119_, 2, v___x_6118_);
lean_ctor_set(v___x_6119_, 3, v___x_6118_);
lean_ctor_set(v___x_6119_, 4, v___x_6118_);
return v___x_6119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(lean_object* v___x_6120_, lean_object* v_name_6121_, lean_object* v___y_6122_, lean_object* v___y_6123_){
_start:
{
if (lean_obj_tag(v_name_6121_) == 1)
{
lean_object* v_pre_6133_; lean_object* v_str_6134_; lean_object* v___x_6135_; uint8_t v___x_6136_; 
v_pre_6133_ = lean_ctor_get(v_name_6121_, 0);
lean_inc(v_pre_6133_);
v_str_6134_ = lean_ctor_get(v_name_6121_, 1);
v___x_6135_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0));
v___x_6136_ = lean_string_dec_eq(v_str_6134_, v___x_6135_);
if (v___x_6136_ == 0)
{
lean_dec_ref_known(v_name_6121_, 2);
lean_dec(v_pre_6133_);
lean_dec(v___x_6120_);
goto v___jp_6129_;
}
else
{
lean_object* v___x_6137_; lean_object* v_env_6138_; uint8_t v___x_6139_; lean_object* v___x_6140_; 
v___x_6137_ = lean_st_ref_get(v___y_6123_);
v_env_6138_ = lean_ctor_get(v___x_6137_, 0);
lean_inc_ref(v_env_6138_);
lean_dec(v___x_6137_);
v___x_6139_ = 0;
lean_inc(v_pre_6133_);
v___x_6140_ = l_Lean_Environment_find_x3f(v_env_6138_, v_pre_6133_, v___x_6139_);
if (lean_obj_tag(v___x_6140_) == 1)
{
lean_object* v_val_6141_; 
v_val_6141_ = lean_ctor_get(v___x_6140_, 0);
lean_inc(v_val_6141_);
lean_dec_ref_known(v___x_6140_, 1);
if (lean_obj_tag(v_val_6141_) == 6)
{
lean_object* v_val_6142_; lean_object* v___x_6144_; uint8_t v_isShared_6145_; uint8_t v_isSharedCheck_6192_; 
v_val_6142_ = lean_ctor_get(v_val_6141_, 0);
v_isSharedCheck_6192_ = !lean_is_exclusive(v_val_6141_);
if (v_isSharedCheck_6192_ == 0)
{
v___x_6144_ = v_val_6141_;
v_isShared_6145_ = v_isSharedCheck_6192_;
goto v_resetjp_6143_;
}
else
{
lean_inc(v_val_6142_);
lean_dec(v_val_6141_);
v___x_6144_ = lean_box(0);
v_isShared_6145_ = v_isSharedCheck_6192_;
goto v_resetjp_6143_;
}
v_resetjp_6143_:
{
uint8_t v___x_6146_; uint8_t v___x_6147_; uint8_t v___x_6148_; lean_object* v___x_6149_; uint64_t v___x_6150_; lean_object* v___x_6151_; lean_object* v___x_6152_; lean_object* v___x_6153_; lean_object* v___x_6154_; lean_object* v___x_6155_; lean_object* v___x_6156_; lean_object* v___x_6157_; lean_object* v___x_6158_; lean_object* v___x_6159_; lean_object* v___x_6160_; lean_object* v___x_6161_; lean_object* v___x_6162_; uint8_t v_a_6164_; lean_object* v___x_6170_; 
v___x_6146_ = 1;
v___x_6147_ = 0;
v___x_6148_ = 2;
v___x_6149_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_6149_, 0, v___x_6139_);
lean_ctor_set_uint8(v___x_6149_, 1, v___x_6139_);
lean_ctor_set_uint8(v___x_6149_, 2, v___x_6139_);
lean_ctor_set_uint8(v___x_6149_, 3, v___x_6139_);
lean_ctor_set_uint8(v___x_6149_, 4, v___x_6139_);
lean_ctor_set_uint8(v___x_6149_, 5, v___x_6136_);
lean_ctor_set_uint8(v___x_6149_, 6, v___x_6136_);
lean_ctor_set_uint8(v___x_6149_, 7, v___x_6139_);
lean_ctor_set_uint8(v___x_6149_, 8, v___x_6136_);
lean_ctor_set_uint8(v___x_6149_, 9, v___x_6146_);
lean_ctor_set_uint8(v___x_6149_, 10, v___x_6147_);
lean_ctor_set_uint8(v___x_6149_, 11, v___x_6136_);
lean_ctor_set_uint8(v___x_6149_, 12, v___x_6136_);
lean_ctor_set_uint8(v___x_6149_, 13, v___x_6136_);
lean_ctor_set_uint8(v___x_6149_, 14, v___x_6148_);
lean_ctor_set_uint8(v___x_6149_, 15, v___x_6136_);
lean_ctor_set_uint8(v___x_6149_, 16, v___x_6136_);
lean_ctor_set_uint8(v___x_6149_, 17, v___x_6136_);
lean_ctor_set_uint8(v___x_6149_, 18, v___x_6136_);
lean_ctor_set_uint8(v___x_6149_, 19, v___x_6139_);
v___x_6150_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_6149_);
v___x_6151_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_6151_, 0, v___x_6149_);
lean_ctor_set_uint64(v___x_6151_, sizeof(void*)*1, v___x_6150_);
v___x_6152_ = lean_unsigned_to_nat(0u);
v___x_6153_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__2, &l_Lean_Meta_mkInjectiveTheorems___closed__2_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__2);
v___x_6154_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_6155_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_));
v___x_6156_ = lean_box(0);
lean_inc(v___x_6120_);
v___x_6157_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_6157_, 0, v___x_6151_);
lean_ctor_set(v___x_6157_, 1, v___x_6120_);
lean_ctor_set(v___x_6157_, 2, v___x_6154_);
lean_ctor_set(v___x_6157_, 3, v___x_6155_);
lean_ctor_set(v___x_6157_, 4, v___x_6156_);
lean_ctor_set(v___x_6157_, 5, v___x_6152_);
lean_ctor_set(v___x_6157_, 6, v___x_6156_);
lean_ctor_set_uint8(v___x_6157_, sizeof(void*)*7, v___x_6139_);
lean_ctor_set_uint8(v___x_6157_, sizeof(void*)*7 + 1, v___x_6139_);
lean_ctor_set_uint8(v___x_6157_, sizeof(void*)*7 + 2, v___x_6139_);
lean_ctor_set_uint8(v___x_6157_, sizeof(void*)*7 + 3, v___x_6136_);
v___x_6158_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6159_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6160_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6161_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6161_, 0, v___x_6158_);
lean_ctor_set(v___x_6161_, 1, v___x_6159_);
lean_ctor_set(v___x_6161_, 2, v___x_6120_);
lean_ctor_set(v___x_6161_, 3, v___x_6153_);
lean_ctor_set(v___x_6161_, 4, v___x_6160_);
v___x_6162_ = lean_st_mk_ref(v___x_6161_);
lean_inc_ref(v_name_6121_);
v___x_6170_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(v_name_6121_, v_val_6142_, v___x_6157_, v___x_6162_, v___y_6122_, v___y_6123_);
if (lean_obj_tag(v___x_6170_) == 0)
{
lean_object* v_a_6171_; 
v_a_6171_ = lean_ctor_get(v___x_6170_, 0);
lean_inc(v_a_6171_);
lean_dec_ref_known(v___x_6170_, 1);
if (lean_obj_tag(v_a_6171_) == 1)
{
lean_object* v_val_6172_; lean_object* v___x_6173_; lean_object* v___f_6174_; lean_object* v___x_6175_; 
v_val_6172_ = lean_ctor_get(v_a_6171_, 0);
lean_inc(v_val_6172_);
lean_dec_ref_known(v_a_6171_, 1);
v___x_6173_ = lean_box(v___x_6139_);
v___f_6174_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed), 7, 2);
lean_closure_set(v___f_6174_, 0, v_val_6172_);
lean_closure_set(v___f_6174_, 1, v___x_6173_);
v___x_6175_ = l_Lean_Meta_realizeConst(v_pre_6133_, v_name_6121_, v___f_6174_, v___x_6157_, v___x_6162_, v___y_6122_, v___y_6123_);
lean_dec_ref_known(v___x_6157_, 7);
if (lean_obj_tag(v___x_6175_) == 0)
{
lean_dec_ref_known(v___x_6175_, 1);
v_a_6164_ = v___x_6136_;
goto v___jp_6163_;
}
else
{
lean_object* v_a_6176_; lean_object* v___x_6178_; uint8_t v_isShared_6179_; uint8_t v_isSharedCheck_6183_; 
lean_dec(v___x_6162_);
lean_del_object(v___x_6144_);
v_a_6176_ = lean_ctor_get(v___x_6175_, 0);
v_isSharedCheck_6183_ = !lean_is_exclusive(v___x_6175_);
if (v_isSharedCheck_6183_ == 0)
{
v___x_6178_ = v___x_6175_;
v_isShared_6179_ = v_isSharedCheck_6183_;
goto v_resetjp_6177_;
}
else
{
lean_inc(v_a_6176_);
lean_dec(v___x_6175_);
v___x_6178_ = lean_box(0);
v_isShared_6179_ = v_isSharedCheck_6183_;
goto v_resetjp_6177_;
}
v_resetjp_6177_:
{
lean_object* v___x_6181_; 
if (v_isShared_6179_ == 0)
{
v___x_6181_ = v___x_6178_;
goto v_reusejp_6180_;
}
else
{
lean_object* v_reuseFailAlloc_6182_; 
v_reuseFailAlloc_6182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6182_, 0, v_a_6176_);
v___x_6181_ = v_reuseFailAlloc_6182_;
goto v_reusejp_6180_;
}
v_reusejp_6180_:
{
return v___x_6181_;
}
}
}
}
else
{
lean_dec(v_a_6171_);
lean_dec_ref_known(v___x_6157_, 7);
lean_dec(v_pre_6133_);
lean_dec_ref_known(v_name_6121_, 2);
v_a_6164_ = v___x_6139_;
goto v___jp_6163_;
}
}
else
{
lean_object* v_a_6184_; lean_object* v___x_6186_; uint8_t v_isShared_6187_; uint8_t v_isSharedCheck_6191_; 
lean_dec(v___x_6162_);
lean_dec_ref_known(v___x_6157_, 7);
lean_del_object(v___x_6144_);
lean_dec(v_pre_6133_);
lean_dec_ref_known(v_name_6121_, 2);
v_a_6184_ = lean_ctor_get(v___x_6170_, 0);
v_isSharedCheck_6191_ = !lean_is_exclusive(v___x_6170_);
if (v_isSharedCheck_6191_ == 0)
{
v___x_6186_ = v___x_6170_;
v_isShared_6187_ = v_isSharedCheck_6191_;
goto v_resetjp_6185_;
}
else
{
lean_inc(v_a_6184_);
lean_dec(v___x_6170_);
v___x_6186_ = lean_box(0);
v_isShared_6187_ = v_isSharedCheck_6191_;
goto v_resetjp_6185_;
}
v_resetjp_6185_:
{
lean_object* v___x_6189_; 
if (v_isShared_6187_ == 0)
{
v___x_6189_ = v___x_6186_;
goto v_reusejp_6188_;
}
else
{
lean_object* v_reuseFailAlloc_6190_; 
v_reuseFailAlloc_6190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6190_, 0, v_a_6184_);
v___x_6189_ = v_reuseFailAlloc_6190_;
goto v_reusejp_6188_;
}
v_reusejp_6188_:
{
return v___x_6189_;
}
}
}
v___jp_6163_:
{
lean_object* v___x_6165_; lean_object* v___x_6166_; lean_object* v___x_6168_; 
v___x_6165_ = lean_st_ref_get(v___x_6162_);
lean_dec(v___x_6162_);
lean_dec(v___x_6165_);
v___x_6166_ = lean_box(v_a_6164_);
if (v_isShared_6145_ == 0)
{
lean_ctor_set_tag(v___x_6144_, 0);
lean_ctor_set(v___x_6144_, 0, v___x_6166_);
v___x_6168_ = v___x_6144_;
goto v_reusejp_6167_;
}
else
{
lean_object* v_reuseFailAlloc_6169_; 
v_reuseFailAlloc_6169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6169_, 0, v___x_6166_);
v___x_6168_ = v_reuseFailAlloc_6169_;
goto v_reusejp_6167_;
}
v_reusejp_6167_:
{
return v___x_6168_;
}
}
}
}
else
{
lean_dec(v_val_6141_);
lean_dec_ref_known(v_name_6121_, 2);
lean_dec(v_pre_6133_);
lean_dec(v___x_6120_);
goto v___jp_6125_;
}
}
else
{
lean_dec(v___x_6140_);
lean_dec_ref_known(v_name_6121_, 2);
lean_dec(v_pre_6133_);
lean_dec(v___x_6120_);
goto v___jp_6125_;
}
}
}
else
{
lean_dec(v_name_6121_);
lean_dec(v___x_6120_);
goto v___jp_6129_;
}
v___jp_6125_:
{
uint8_t v___x_6126_; lean_object* v___x_6127_; lean_object* v___x_6128_; 
v___x_6126_ = 0;
v___x_6127_ = lean_box(v___x_6126_);
v___x_6128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6128_, 0, v___x_6127_);
return v___x_6128_;
}
v___jp_6129_:
{
uint8_t v___x_6130_; lean_object* v___x_6131_; lean_object* v___x_6132_; 
v___x_6130_ = 0;
v___x_6131_ = lean_box(v___x_6130_);
v___x_6132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6132_, 0, v___x_6131_);
return v___x_6132_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object* v___x_6193_, lean_object* v_name_6194_, lean_object* v___y_6195_, lean_object* v___y_6196_, lean_object* v___y_6197_){
_start:
{
lean_object* v_res_6198_; 
v_res_6198_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(v___x_6193_, v_name_6194_, v___y_6195_, v___y_6196_);
lean_dec(v___y_6196_);
lean_dec_ref(v___y_6195_);
return v_res_6198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_6202_; lean_object* v___x_6203_; 
v___f_6202_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_));
v___x_6203_ = l_Lean_registerReservedNameAction(v___f_6202_);
return v___x_6203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object* v_a_6204_){
_start:
{
lean_object* v_res_6205_; 
v_res_6205_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_();
return v_res_6205_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Refl(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Assumption(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_SameCtorUtils(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Injection(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Attr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Injective(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Refl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Assumption(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_SameCtorUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Injection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_genInjectivity = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_genInjectivity);
lean_dec_ref(res);
res = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Injective(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Refl(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Assumption(uint8_t builtin);
lean_object* initialize_Lean_Meta_SameCtorUtils(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Injection(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Attr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Injective(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Refl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Assumption(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_SameCtorUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Injection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Injective(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Injective(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Injective(builtin);
}
#ifdef __cplusplus
}
#endif
