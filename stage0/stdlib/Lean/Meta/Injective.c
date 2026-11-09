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
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_array_size(lean_object*);
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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_nat_sub(lean_object*, lean_object*);
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
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateAppN(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_IO_CancelToken_isSet(lean_object*);
extern lean_object* l_Lean_interruptExceptionId;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "transform"};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2_spec__3_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2_spec__3_spec__5___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2_spec__3_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2_spec__3_spec__5___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2_spec__3_spec__5___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2_spec__3_spec__5___redArg___boxed(lean_object*);
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
static lean_once_cell_t l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__4;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2_spec__3_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2_spec__3___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2_spec__3___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2_spec__3(lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_;
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
lean_object* v___y_255_; lean_object* v___y_265_; lean_object* v___y_266_; uint8_t v___y_267_; uint8_t v___y_268_; uint8_t v___y_269_; lean_object* v___y_270_; uint16_t v___y_271_; lean_object* v_toCold_276_; lean_object* v_currRecDepth_277_; lean_object* v_ref_278_; uint16_t v_optionFlags_279_; uint8_t v_suppressElabErrors_280_; uint8_t v_checkDeprecated_281_; uint8_t v_isRecordingDeps_282_; lean_object* v_maxRecDepth_283_; lean_object* v_cancelTk_x3f_284_; 
v_toCold_276_ = lean_ctor_get(v___y_251_, 0);
v_currRecDepth_277_ = lean_ctor_get(v___y_251_, 1);
v_ref_278_ = lean_ctor_get(v___y_251_, 2);
v_optionFlags_279_ = lean_ctor_get_uint16(v___y_251_, sizeof(void*)*3);
v_suppressElabErrors_280_ = lean_ctor_get_uint8(v___y_251_, sizeof(void*)*3 + 2);
v_checkDeprecated_281_ = lean_ctor_get_uint8(v___y_251_, sizeof(void*)*3 + 3);
v_isRecordingDeps_282_ = lean_ctor_get_uint8(v___y_251_, sizeof(void*)*3 + 4);
v_maxRecDepth_283_ = lean_ctor_get(v_toCold_276_, 3);
v_cancelTk_x3f_284_ = lean_ctor_get(v_toCold_276_, 10);
if (lean_obj_tag(v_cancelTk_x3f_284_) == 1)
{
lean_object* v_val_290_; uint8_t v___x_291_; 
v_val_290_ = lean_ctor_get(v_cancelTk_x3f_284_, 0);
v___x_291_ = l_IO_CancelToken_isSet(v_val_290_);
if (v___x_291_ == 0)
{
goto v___jp_285_;
}
else
{
lean_object* v___x_292_; lean_object* v_a_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_300_; 
lean_dec_ref(v_x_249_);
v___x_292_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg();
v_a_293_ = lean_ctor_get(v___x_292_, 0);
v_isSharedCheck_300_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_300_ == 0)
{
v___x_295_ = v___x_292_;
v_isShared_296_ = v_isSharedCheck_300_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_a_293_);
lean_dec(v___x_292_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_300_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_298_; 
if (v_isShared_296_ == 0)
{
v___x_298_ = v___x_295_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v_a_293_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
}
}
else
{
goto v___jp_285_;
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
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_272_ = lean_unsigned_to_nat(1u);
v___x_273_ = lean_nat_add(v___y_270_, v___x_272_);
lean_inc_ref(v___y_265_);
v___x_274_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_274_, 0, v___y_265_);
lean_ctor_set(v___x_274_, 1, v___x_273_);
lean_ctor_set(v___x_274_, 2, v___y_266_);
lean_ctor_set_uint16(v___x_274_, sizeof(void*)*3, v___y_271_);
lean_ctor_set_uint8(v___x_274_, sizeof(void*)*3 + 2, v___y_268_);
lean_ctor_set_uint8(v___x_274_, sizeof(void*)*3 + 3, v___y_267_);
lean_ctor_set_uint8(v___x_274_, sizeof(void*)*3 + 4, v___y_269_);
lean_inc(v___y_252_);
lean_inc(v___y_250_);
v___x_275_ = lean_apply_4(v_x_249_, v___y_250_, v___x_274_, v___y_252_, lean_box(0));
v___y_255_ = v___x_275_;
goto v___jp_254_;
}
v___jp_285_:
{
lean_object* v___x_286_; uint8_t v___x_287_; 
v___x_286_ = lean_unsigned_to_nat(0u);
v___x_287_ = lean_nat_dec_eq(v_maxRecDepth_283_, v___x_286_);
if (v___x_287_ == 0)
{
uint8_t v___x_288_; 
v___x_288_ = lean_nat_dec_eq(v_currRecDepth_277_, v_maxRecDepth_283_);
if (v___x_288_ == 0)
{
lean_inc(v_ref_278_);
v___y_265_ = v_toCold_276_;
v___y_266_ = v_ref_278_;
v___y_267_ = v_checkDeprecated_281_;
v___y_268_ = v_suppressElabErrors_280_;
v___y_269_ = v_isRecordingDeps_282_;
v___y_270_ = v_currRecDepth_277_;
v___y_271_ = v_optionFlags_279_;
goto v___jp_264_;
}
else
{
lean_object* v___x_289_; 
lean_dec_ref(v_x_249_);
lean_inc(v_ref_278_);
v___x_289_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_278_);
v___y_255_ = v___x_289_;
goto v___jp_254_;
}
}
else
{
lean_inc(v_ref_278_);
v___y_265_ = v_toCold_276_;
v___y_266_ = v_ref_278_;
v___y_267_ = v_checkDeprecated_281_;
v___y_268_ = v_suppressElabErrors_280_;
v___y_269_ = v_isRecordingDeps_282_;
v___y_270_ = v_currRecDepth_277_;
v___y_271_ = v_optionFlags_279_;
goto v___jp_264_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(v_x_301_, v___y_302_, v___y_303_, v___y_304_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
lean_dec(v___y_302_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_307_, lean_object* v_x_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = lean_apply_1(v_x_308_, lean_box(0));
v___x_313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_314_, lean_object* v_x_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(v_00_u03b1_314_, v_x_315_, v___y_316_, v___y_317_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_a_320_, lean_object* v_x_321_){
_start:
{
if (lean_obj_tag(v_x_321_) == 0)
{
lean_object* v___x_322_; 
v___x_322_ = lean_box(0);
return v___x_322_;
}
else
{
lean_object* v_key_323_; lean_object* v_value_324_; lean_object* v_tail_325_; uint8_t v___x_326_; 
v_key_323_ = lean_ctor_get(v_x_321_, 0);
v_value_324_ = lean_ctor_get(v_x_321_, 1);
v_tail_325_ = lean_ctor_get(v_x_321_, 2);
v___x_326_ = l_Lean_ExprStructEq_beq(v_key_323_, v_a_320_);
if (v___x_326_ == 0)
{
v_x_321_ = v_tail_325_;
goto _start;
}
else
{
lean_object* v___x_328_; 
lean_inc(v_value_324_);
v___x_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_328_, 0, v_value_324_);
return v___x_328_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_a_329_, lean_object* v_x_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1_spec__2___redArg(v_a_329_, v_x_330_);
lean_dec(v_x_330_);
lean_dec_ref(v_a_329_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1___redArg(lean_object* v_m_332_, lean_object* v_a_333_){
_start:
{
lean_object* v_buckets_334_; lean_object* v___x_335_; uint64_t v___x_336_; uint64_t v___x_337_; uint64_t v___x_338_; uint64_t v_fold_339_; uint64_t v___x_340_; uint64_t v___x_341_; uint64_t v___x_342_; size_t v___x_343_; size_t v___x_344_; size_t v___x_345_; size_t v___x_346_; size_t v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v_buckets_334_ = lean_ctor_get(v_m_332_, 1);
v___x_335_ = lean_array_get_size(v_buckets_334_);
v___x_336_ = l_Lean_ExprStructEq_hash(v_a_333_);
v___x_337_ = 32ULL;
v___x_338_ = lean_uint64_shift_right(v___x_336_, v___x_337_);
v_fold_339_ = lean_uint64_xor(v___x_336_, v___x_338_);
v___x_340_ = 16ULL;
v___x_341_ = lean_uint64_shift_right(v_fold_339_, v___x_340_);
v___x_342_ = lean_uint64_xor(v_fold_339_, v___x_341_);
v___x_343_ = lean_uint64_to_usize(v___x_342_);
v___x_344_ = lean_usize_of_nat(v___x_335_);
v___x_345_ = ((size_t)1ULL);
v___x_346_ = lean_usize_sub(v___x_344_, v___x_345_);
v___x_347_ = lean_usize_land(v___x_343_, v___x_346_);
v___x_348_ = lean_array_uget_borrowed(v_buckets_334_, v___x_347_);
v___x_349_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1_spec__2___redArg(v_a_333_, v___x_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_m_350_, lean_object* v_a_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1___redArg(v_m_350_, v_a_351_);
lean_dec_ref(v_a_351_);
lean_dec_ref(v_m_350_);
return v_res_352_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0(void){
_start:
{
lean_object* v___x_354_; lean_object* v_dummy_355_; 
v___x_354_ = lean_box(0);
v_dummy_355_ = l_Lean_Expr_sort___override(v___x_354_);
return v_dummy_355_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(lean_object* v_pre_356_, lean_object* v_post_357_, size_t v_sz_358_, size_t v_i_359_, lean_object* v_bs_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
uint8_t v___x_365_; 
v___x_365_ = lean_usize_dec_lt(v_i_359_, v_sz_358_);
if (v___x_365_ == 0)
{
lean_object* v___x_366_; 
lean_dec_ref(v_post_357_);
lean_dec_ref(v_pre_356_);
v___x_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_366_, 0, v_bs_360_);
return v___x_366_;
}
else
{
lean_object* v_v_367_; lean_object* v___x_368_; lean_object* v_bs_x27_369_; lean_object* v___x_370_; 
v_v_367_ = lean_array_uget(v_bs_360_, v_i_359_);
v___x_368_ = lean_unsigned_to_nat(0u);
v_bs_x27_369_ = lean_array_uset(v_bs_360_, v_i_359_, v___x_368_);
lean_inc_ref(v_post_357_);
lean_inc_ref(v_pre_356_);
v___x_370_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_356_, v_post_357_, v_v_367_, v___y_361_, v___y_362_, v___y_363_);
if (lean_obj_tag(v___x_370_) == 0)
{
lean_object* v_a_371_; size_t v___x_372_; size_t v___x_373_; lean_object* v___x_374_; 
v_a_371_ = lean_ctor_get(v___x_370_, 0);
lean_inc(v_a_371_);
lean_dec_ref_known(v___x_370_, 1);
v___x_372_ = ((size_t)1ULL);
v___x_373_ = lean_usize_add(v_i_359_, v___x_372_);
v___x_374_ = lean_array_uset(v_bs_x27_369_, v_i_359_, v_a_371_);
v_i_359_ = v___x_373_;
v_bs_360_ = v___x_374_;
goto _start;
}
else
{
lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_383_; 
lean_dec_ref(v_bs_x27_369_);
lean_dec_ref(v_post_357_);
lean_dec_ref(v_pre_356_);
v_a_376_ = lean_ctor_get(v___x_370_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_383_ == 0)
{
v___x_378_ = v___x_370_;
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_dec(v___x_370_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_381_; 
if (v_isShared_379_ == 0)
{
v___x_381_ = v___x_378_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_a_376_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4(lean_object* v_pre_384_, lean_object* v_post_385_, lean_object* v___y_386_, lean_object* v_x_387_, lean_object* v_x_388_, lean_object* v_x_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
if (lean_obj_tag(v_x_387_) == 5)
{
lean_object* v_fn_394_; lean_object* v_arg_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v_fn_394_ = lean_ctor_get(v_x_387_, 0);
lean_inc_ref(v_fn_394_);
v_arg_395_ = lean_ctor_get(v_x_387_, 1);
lean_inc_ref(v_arg_395_);
lean_dec_ref_known(v_x_387_, 2);
v___x_396_ = lean_array_set(v_x_388_, v_x_389_, v_arg_395_);
v___x_397_ = lean_unsigned_to_nat(1u);
v___x_398_ = lean_nat_sub(v_x_389_, v___x_397_);
lean_dec(v_x_389_);
v_x_387_ = v_fn_394_;
v_x_388_ = v___x_396_;
v_x_389_ = v___x_398_;
goto _start;
}
else
{
lean_object* v___x_400_; 
lean_dec(v_x_389_);
lean_inc_ref(v_post_385_);
lean_inc_ref(v_pre_384_);
v___x_400_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_384_, v_post_385_, v_x_387_, v___y_390_, v___y_391_, v___y_392_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v_a_401_; size_t v_sz_402_; size_t v___x_403_; lean_object* v___x_404_; 
v_a_401_ = lean_ctor_get(v___x_400_, 0);
lean_inc(v_a_401_);
lean_dec_ref_known(v___x_400_, 1);
v_sz_402_ = lean_array_size(v_x_388_);
v___x_403_ = ((size_t)0ULL);
v___x_404_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_384_, v_post_385_, v_sz_402_, v___x_403_, v_x_388_, v___y_390_, v___y_391_, v___y_392_);
if (lean_obj_tag(v___x_404_) == 0)
{
lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_413_; 
v_a_405_ = lean_ctor_get(v___x_404_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_413_ == 0)
{
v___x_407_ = v___x_404_;
v_isShared_408_ = v_isSharedCheck_413_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_404_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_413_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_409_; lean_object* v___x_411_; 
v___x_409_ = l_Lean_Expr_updateAppN(v___y_386_, v_a_401_, v_a_405_);
lean_dec(v_a_405_);
if (v_isShared_408_ == 0)
{
lean_ctor_set(v___x_407_, 0, v___x_409_);
v___x_411_ = v___x_407_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_409_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
else
{
lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_421_; 
lean_dec(v_a_401_);
v_a_414_ = lean_ctor_get(v___x_404_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_421_ == 0)
{
v___x_416_ = v___x_404_;
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_a_414_);
lean_dec(v___x_404_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_419_; 
if (v_isShared_417_ == 0)
{
v___x_419_ = v___x_416_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_a_414_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
else
{
lean_dec_ref(v_x_388_);
lean_dec_ref(v_post_385_);
lean_dec_ref(v_pre_384_);
return v___x_400_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1(lean_object* v___x_422_, lean_object* v_pre_423_, lean_object* v_e_424_, lean_object* v_post_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l_Lean_Core_checkSystem(v___x_422_, v___y_427_, v___y_428_);
if (lean_obj_tag(v___x_430_) == 0)
{
lean_object* v___x_431_; 
lean_dec_ref_known(v___x_430_, 1);
lean_inc_ref(v_pre_423_);
lean_inc(v___y_428_);
lean_inc_ref(v___y_427_);
lean_inc_ref(v_e_424_);
v___x_431_ = lean_apply_4(v_pre_423_, v_e_424_, v___y_427_, v___y_428_, lean_box(0));
if (lean_obj_tag(v___x_431_) == 0)
{
lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_549_; 
v_a_432_ = lean_ctor_get(v___x_431_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_549_ == 0)
{
v___x_434_ = v___x_431_;
v_isShared_435_ = v_isSharedCheck_549_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_dec(v___x_431_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_549_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___y_437_; 
switch(lean_obj_tag(v_a_432_))
{
case 0:
{
lean_object* v_e_539_; lean_object* v___x_541_; 
lean_dec_ref(v_post_425_);
lean_dec_ref(v_e_424_);
lean_dec_ref(v_pre_423_);
v_e_539_ = lean_ctor_get(v_a_432_, 0);
lean_inc_ref(v_e_539_);
lean_dec_ref_known(v_a_432_, 1);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 0, v_e_539_);
v___x_541_ = v___x_434_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_e_539_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
case 1:
{
lean_object* v_e_543_; lean_object* v___x_544_; 
lean_del_object(v___x_434_);
lean_dec_ref(v_e_424_);
v_e_543_ = lean_ctor_get(v_a_432_, 0);
lean_inc_ref(v_e_543_);
lean_dec_ref_known(v_a_432_, 1);
lean_inc_ref(v_post_425_);
lean_inc_ref(v_pre_423_);
v___x_544_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_423_, v_post_425_, v_e_543_, v___y_426_, v___y_427_, v___y_428_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v_a_545_; lean_object* v___x_546_; 
v_a_545_ = lean_ctor_get(v___x_544_, 0);
lean_inc(v_a_545_);
lean_dec_ref_known(v___x_544_, 1);
v___x_546_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(v_pre_423_, v_post_425_, v_a_545_, v___y_426_, v___y_427_, v___y_428_);
return v___x_546_;
}
else
{
lean_dec_ref(v_post_425_);
lean_dec_ref(v_pre_423_);
return v___x_544_;
}
}
default: 
{
lean_object* v_e_x3f_547_; 
lean_del_object(v___x_434_);
v_e_x3f_547_ = lean_ctor_get(v_a_432_, 0);
lean_inc(v_e_x3f_547_);
lean_dec_ref_known(v_a_432_, 1);
if (lean_obj_tag(v_e_x3f_547_) == 0)
{
v___y_437_ = v_e_424_;
goto v___jp_436_;
}
else
{
lean_object* v_val_548_; 
lean_dec_ref(v_e_424_);
v_val_548_ = lean_ctor_get(v_e_x3f_547_, 0);
lean_inc(v_val_548_);
lean_dec_ref_known(v_e_x3f_547_, 1);
v___y_437_ = v_val_548_;
goto v___jp_436_;
}
}
}
v___jp_436_:
{
switch(lean_obj_tag(v___y_437_))
{
case 7:
{
lean_object* v_binderName_438_; lean_object* v_binderType_439_; lean_object* v_body_440_; uint8_t v_binderInfo_441_; lean_object* v___x_442_; 
v_binderName_438_ = lean_ctor_get(v___y_437_, 0);
v_binderType_439_ = lean_ctor_get(v___y_437_, 1);
v_body_440_ = lean_ctor_get(v___y_437_, 2);
v_binderInfo_441_ = lean_ctor_get_uint8(v___y_437_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_439_);
lean_inc_ref(v_post_425_);
lean_inc_ref(v_pre_423_);
v___x_442_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_423_, v_post_425_, v_binderType_439_, v___y_426_, v___y_427_, v___y_428_);
if (lean_obj_tag(v___x_442_) == 0)
{
lean_object* v_a_443_; lean_object* v___x_444_; 
v_a_443_ = lean_ctor_get(v___x_442_, 0);
lean_inc(v_a_443_);
lean_dec_ref_known(v___x_442_, 1);
lean_inc_ref(v_body_440_);
lean_inc_ref(v_post_425_);
lean_inc_ref(v_pre_423_);
v___x_444_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_423_, v_post_425_, v_body_440_, v___y_426_, v___y_427_, v___y_428_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_object* v_a_445_; size_t v___x_446_; size_t v___x_447_; uint8_t v___x_448_; 
v_a_445_ = lean_ctor_get(v___x_444_, 0);
lean_inc(v_a_445_);
lean_dec_ref_known(v___x_444_, 1);
v___x_446_ = lean_ptr_addr(v_binderType_439_);
v___x_447_ = lean_ptr_addr(v_a_443_);
v___x_448_ = lean_usize_dec_eq(v___x_446_, v___x_447_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; lean_object* v___x_450_; 
lean_inc(v_binderName_438_);
lean_dec_ref_known(v___y_437_, 3);
v___x_449_ = l_Lean_Expr_forallE___override(v_binderName_438_, v_a_443_, v_a_445_, v_binderInfo_441_);
v___x_450_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(v_pre_423_, v_post_425_, v___x_449_, v___y_426_, v___y_427_, v___y_428_);
return v___x_450_;
}
else
{
size_t v___x_451_; size_t v___x_452_; uint8_t v___x_453_; 
v___x_451_ = lean_ptr_addr(v_body_440_);
v___x_452_ = lean_ptr_addr(v_a_445_);
v___x_453_ = lean_usize_dec_eq(v___x_451_, v___x_452_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; lean_object* v___x_455_; 
lean_inc(v_binderName_438_);
lean_dec_ref_known(v___y_437_, 3);
v___x_454_ = l_Lean_Expr_forallE___override(v_binderName_438_, v_a_443_, v_a_445_, v_binderInfo_441_);
v___x_455_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(v_pre_423_, v_post_425_, v___x_454_, v___y_426_, v___y_427_, v___y_428_);
return v___x_455_;
}
else
{
uint8_t v___x_456_; 
v___x_456_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_441_, v_binderInfo_441_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; lean_object* v___x_458_; 
lean_inc(v_binderName_438_);
lean_dec_ref_known(v___y_437_, 3);
v___x_457_ = l_Lean_Expr_forallE___override(v_binderName_438_, v_a_443_, v_a_445_, v_binderInfo_441_);
v___x_458_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(v_pre_423_, v_post_425_, v___x_457_, v___y_426_, v___y_427_, v___y_428_);
return v___x_458_;
}
else
{
lean_object* v___x_459_; 
lean_dec(v_a_445_);
lean_dec(v_a_443_);
v___x_459_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(v_pre_423_, v_post_425_, v___y_437_, v___y_426_, v___y_427_, v___y_428_);
return v___x_459_;
}
}
}
}
else
{
lean_dec(v_a_443_);
lean_dec_ref_known(v___y_437_, 3);
lean_dec_ref(v_post_425_);
lean_dec_ref(v_pre_423_);
return v___x_444_;
}
}
else
{
lean_dec_ref_known(v___y_437_, 3);
lean_dec_ref(v_post_425_);
lean_dec_ref(v_pre_423_);
return v___x_442_;
}
}
case 6:
{
lean_object* v_binderName_460_; lean_object* v_binderType_461_; lean_object* v_body_462_; uint8_t v_binderInfo_463_; lean_object* v___x_464_; 
v_binderName_460_ = lean_ctor_get(v___y_437_, 0);
v_binderType_461_ = lean_ctor_get(v___y_437_, 1);
v_body_462_ = lean_ctor_get(v___y_437_, 2);
v_binderInfo_463_ = lean_ctor_get_uint8(v___y_437_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_461_);
lean_inc_ref(v_post_425_);
lean_inc_ref(v_pre_423_);
v___x_464_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_423_, v_post_425_, v_binderType_461_, v___y_426_, v___y_427_, v___y_428_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_object* v_a_465_; lean_object* v___x_466_; 
v_a_465_ = lean_ctor_get(v___x_464_, 0);
lean_inc(v_a_465_);
lean_dec_ref_known(v___x_464_, 1);
lean_inc_ref(v_body_462_);
lean_inc_ref(v_post_425_);
lean_inc_ref(v_pre_423_);
v___x_466_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_423_, v_post_425_, v_body_462_, v___y_426_, v___y_427_, v___y_428_);
if (lean_obj_tag(v___x_466_) == 0)
{
lean_object* v_a_467_; size_t v___x_468_; size_t v___x_469_; uint8_t v___x_470_; 
v_a_467_ = lean_ctor_get(v___x_466_, 0);
lean_inc(v_a_467_);
lean_dec_ref_known(v___x_466_, 1);
v___x_468_ = lean_ptr_addr(v_binderType_461_);
v___x_469_ = lean_ptr_addr(v_a_465_);
v___x_470_ = lean_usize_dec_eq(v___x_468_, v___x_469_);
if (v___x_470_ == 0)
{
lean_object* v___x_471_; lean_object* v___x_472_; 
lean_inc(v_binderName_460_);
lean_dec_ref_known(v___y_437_, 3);
v___x_471_ = l_Lean_Expr_lam___override(v_binderName_460_, v_a_465_, v_a_467_, v_binderInfo_463_);
v___x_472_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(v_pre_423_, v_post_425_, v___x_471_, v___y_426_, v___y_427_, v___y_428_);
return v___x_472_;
}
else
{
size_t v___x_473_; size_t v___x_474_; uint8_t v___x_475_; 
v___x_473_ = lean_ptr_addr(v_body_462_);
v___x_474_ = lean_ptr_addr(v_a_467_);
v___x_475_ = lean_usize_dec_eq(v___x_473_, v___x_474_);
if (v___x_475_ == 0)
{
lean_object* v___x_476_; lean_object* v___x_477_; 
lean_inc(v_binderName_460_);
lean_dec_ref_known(v___y_437_, 3);
v___x_476_ = l_Lean_Expr_lam___override(v_binderName_460_, v_a_465_, v_a_467_, v_binderInfo_463_);
v___x_477_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(v_pre_423_, v_post_425_, v___x_476_, v___y_426_, v___y_427_, v___y_428_);
return v___x_477_;
}
else
{
uint8_t v___x_478_; 
v___x_478_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_463_, v_binderInfo_463_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; lean_object* v___x_480_; 
lean_inc(v_binderName_460_);
lean_dec_ref_known(v___y_437_, 3);
v___x_479_ = l_Lean_Expr_lam___override(v_binderName_460_, v_a_465_, v_a_467_, v_binderInfo_463_);
v___x_480_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(v_pre_423_, v_post_425_, v___x_479_, v___y_426_, v___y_427_, v___y_428_);
return v___x_480_;
}
else
{
lean_object* v___x_481_; 
lean_dec(v_a_467_);
lean_dec(v_a_465_);
v___x_481_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(v_pre_423_, v_post_425_, v___y_437_, v___y_426_, v___y_427_, v___y_428_);
return v___x_481_;
}
}
}
}
else
{
lean_dec(v_a_465_);
lean_dec_ref_known(v___y_437_, 3);
lean_dec_ref(v_post_425_);
lean_dec_ref(v_pre_423_);
return v___x_466_;
}
}
else
{
lean_dec_ref_known(v___y_437_, 3);
lean_dec_ref(v_post_425_);
lean_dec_ref(v_pre_423_);
return v___x_464_;
}
}
case 8:
{
lean_object* v_declName_482_; lean_object* v_type_483_; lean_object* v_value_484_; lean_object* v_body_485_; uint8_t v_nondep_486_; lean_object* v___x_487_; 
v_declName_482_ = lean_ctor_get(v___y_437_, 0);
v_type_483_ = lean_ctor_get(v___y_437_, 1);
v_value_484_ = lean_ctor_get(v___y_437_, 2);
v_body_485_ = lean_ctor_get(v___y_437_, 3);
v_nondep_486_ = lean_ctor_get_uint8(v___y_437_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_483_);
lean_inc_ref(v_post_425_);
lean_inc_ref(v_pre_423_);
v___x_487_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_423_, v_post_425_, v_type_483_, v___y_426_, v___y_427_, v___y_428_);
if (lean_obj_tag(v___x_487_) == 0)
{
lean_object* v_a_488_; lean_object* v___x_489_; 
v_a_488_ = lean_ctor_get(v___x_487_, 0);
lean_inc(v_a_488_);
lean_dec_ref_known(v___x_487_, 1);
lean_inc_ref(v_value_484_);
lean_inc_ref(v_post_425_);
lean_inc_ref(v_pre_423_);
v___x_489_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_423_, v_post_425_, v_value_484_, v___y_426_, v___y_427_, v___y_428_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_object* v_a_490_; lean_object* v___x_491_; 
v_a_490_ = lean_ctor_get(v___x_489_, 0);
lean_inc(v_a_490_);
lean_dec_ref_known(v___x_489_, 1);
lean_inc_ref(v_body_485_);
lean_inc_ref(v_post_425_);
lean_inc_ref(v_pre_423_);
v___x_491_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_423_, v_post_425_, v_body_485_, v___y_426_, v___y_427_, v___y_428_);
if (lean_obj_tag(v___x_491_) == 0)
{
lean_object* v_a_492_; size_t v___x_493_; size_t v___x_494_; uint8_t v___x_495_; 
v_a_492_ = lean_ctor_get(v___x_491_, 0);
lean_inc(v_a_492_);
lean_dec_ref_known(v___x_491_, 1);
v___x_493_ = lean_ptr_addr(v_type_483_);
v___x_494_ = lean_ptr_addr(v_a_488_);
v___x_495_ = lean_usize_dec_eq(v___x_493_, v___x_494_);
if (v___x_495_ == 0)
{
lean_object* v___x_496_; lean_object* v___x_497_; 
lean_inc(v_declName_482_);
lean_dec_ref_known(v___y_437_, 4);
v___x_496_ = l_Lean_Expr_letE___override(v_declName_482_, v_a_488_, v_a_490_, v_a_492_, v_nondep_486_);
v___x_497_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(v_pre_423_, v_post_425_, v___x_496_, v___y_426_, v___y_427_, v___y_428_);
return v___x_497_;
}
else
{
size_t v___x_498_; size_t v___x_499_; uint8_t v___x_500_; 
v___x_498_ = lean_ptr_addr(v_value_484_);
v___x_499_ = lean_ptr_addr(v_a_490_);
v___x_500_ = lean_usize_dec_eq(v___x_498_, v___x_499_);
if (v___x_500_ == 0)
{
lean_object* v___x_501_; lean_object* v___x_502_; 
lean_inc(v_declName_482_);
lean_dec_ref_known(v___y_437_, 4);
v___x_501_ = l_Lean_Expr_letE___override(v_declName_482_, v_a_488_, v_a_490_, v_a_492_, v_nondep_486_);
v___x_502_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(v_pre_423_, v_post_425_, v___x_501_, v___y_426_, v___y_427_, v___y_428_);
return v___x_502_;
}
else
{
size_t v___x_503_; size_t v___x_504_; uint8_t v___x_505_; 
v___x_503_ = lean_ptr_addr(v_body_485_);
v___x_504_ = lean_ptr_addr(v_a_492_);
v___x_505_ = lean_usize_dec_eq(v___x_503_, v___x_504_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; lean_object* v___x_507_; 
lean_inc(v_declName_482_);
lean_dec_ref_known(v___y_437_, 4);
v___x_506_ = l_Lean_Expr_letE___override(v_declName_482_, v_a_488_, v_a_490_, v_a_492_, v_nondep_486_);
v___x_507_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(v_pre_423_, v_post_425_, v___x_506_, v___y_426_, v___y_427_, v___y_428_);
return v___x_507_;
}
else
{
lean_object* v___x_508_; 
lean_dec(v_a_492_);
lean_dec(v_a_490_);
lean_dec(v_a_488_);
v___x_508_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(v_pre_423_, v_post_425_, v___y_437_, v___y_426_, v___y_427_, v___y_428_);
return v___x_508_;
}
}
}
}
else
{
lean_dec(v_a_490_);
lean_dec(v_a_488_);
lean_dec_ref_known(v___y_437_, 4);
lean_dec_ref(v_post_425_);
lean_dec_ref(v_pre_423_);
return v___x_491_;
}
}
else
{
lean_dec(v_a_488_);
lean_dec_ref_known(v___y_437_, 4);
lean_dec_ref(v_post_425_);
lean_dec_ref(v_pre_423_);
return v___x_489_;
}
}
else
{
lean_dec_ref_known(v___y_437_, 4);
lean_dec_ref(v_post_425_);
lean_dec_ref(v_pre_423_);
return v___x_487_;
}
}
case 5:
{
lean_object* v_dummy_509_; lean_object* v_nargs_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v_dummy_509_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0);
v_nargs_510_ = l_Lean_Expr_getAppNumArgs(v___y_437_);
lean_inc(v_nargs_510_);
v___x_511_ = lean_mk_array(v_nargs_510_, v_dummy_509_);
v___x_512_ = lean_unsigned_to_nat(1u);
v___x_513_ = lean_nat_sub(v_nargs_510_, v___x_512_);
lean_dec(v_nargs_510_);
lean_inc_ref(v___y_437_);
lean_inc_ref(v_post_425_);
lean_inc_ref(v_pre_423_);
v___x_514_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4(v_pre_423_, v_post_425_, v___y_437_, v___y_437_, v___x_511_, v___x_513_, v___y_426_, v___y_427_, v___y_428_);
lean_dec_ref_known(v___y_437_, 2);
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v_a_515_; lean_object* v___x_516_; 
v_a_515_ = lean_ctor_get(v___x_514_, 0);
lean_inc(v_a_515_);
lean_dec_ref_known(v___x_514_, 1);
v___x_516_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(v_pre_423_, v_post_425_, v_a_515_, v___y_426_, v___y_427_, v___y_428_);
return v___x_516_;
}
else
{
lean_dec_ref(v_post_425_);
lean_dec_ref(v_pre_423_);
return v___x_514_;
}
}
case 10:
{
lean_object* v_data_517_; lean_object* v_expr_518_; lean_object* v___x_519_; 
v_data_517_ = lean_ctor_get(v___y_437_, 0);
v_expr_518_ = lean_ctor_get(v___y_437_, 1);
lean_inc_ref(v_expr_518_);
lean_inc_ref(v_post_425_);
lean_inc_ref(v_pre_423_);
v___x_519_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_423_, v_post_425_, v_expr_518_, v___y_426_, v___y_427_, v___y_428_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v_a_520_; size_t v___x_521_; size_t v___x_522_; uint8_t v___x_523_; 
v_a_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_a_520_);
lean_dec_ref_known(v___x_519_, 1);
v___x_521_ = lean_ptr_addr(v_expr_518_);
v___x_522_ = lean_ptr_addr(v_a_520_);
v___x_523_ = lean_usize_dec_eq(v___x_521_, v___x_522_);
if (v___x_523_ == 0)
{
lean_object* v___x_524_; lean_object* v___x_525_; 
lean_inc(v_data_517_);
lean_dec_ref_known(v___y_437_, 2);
v___x_524_ = l_Lean_Expr_mdata___override(v_data_517_, v_a_520_);
v___x_525_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(v_pre_423_, v_post_425_, v___x_524_, v___y_426_, v___y_427_, v___y_428_);
return v___x_525_;
}
else
{
lean_object* v___x_526_; 
lean_dec(v_a_520_);
v___x_526_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(v_pre_423_, v_post_425_, v___y_437_, v___y_426_, v___y_427_, v___y_428_);
return v___x_526_;
}
}
else
{
lean_dec_ref_known(v___y_437_, 2);
lean_dec_ref(v_post_425_);
lean_dec_ref(v_pre_423_);
return v___x_519_;
}
}
case 11:
{
lean_object* v_typeName_527_; lean_object* v_idx_528_; lean_object* v_struct_529_; lean_object* v___x_530_; 
v_typeName_527_ = lean_ctor_get(v___y_437_, 0);
v_idx_528_ = lean_ctor_get(v___y_437_, 1);
v_struct_529_ = lean_ctor_get(v___y_437_, 2);
lean_inc_ref(v_struct_529_);
lean_inc_ref(v_post_425_);
lean_inc_ref(v_pre_423_);
v___x_530_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_423_, v_post_425_, v_struct_529_, v___y_426_, v___y_427_, v___y_428_);
if (lean_obj_tag(v___x_530_) == 0)
{
lean_object* v_a_531_; size_t v___x_532_; size_t v___x_533_; uint8_t v___x_534_; 
v_a_531_ = lean_ctor_get(v___x_530_, 0);
lean_inc(v_a_531_);
lean_dec_ref_known(v___x_530_, 1);
v___x_532_ = lean_ptr_addr(v_struct_529_);
v___x_533_ = lean_ptr_addr(v_a_531_);
v___x_534_ = lean_usize_dec_eq(v___x_532_, v___x_533_);
if (v___x_534_ == 0)
{
lean_object* v___x_535_; lean_object* v___x_536_; 
lean_inc(v_idx_528_);
lean_inc(v_typeName_527_);
lean_dec_ref_known(v___y_437_, 3);
v___x_535_ = l_Lean_Expr_proj___override(v_typeName_527_, v_idx_528_, v_a_531_);
v___x_536_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(v_pre_423_, v_post_425_, v___x_535_, v___y_426_, v___y_427_, v___y_428_);
return v___x_536_;
}
else
{
lean_object* v___x_537_; 
lean_dec(v_a_531_);
v___x_537_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(v_pre_423_, v_post_425_, v___y_437_, v___y_426_, v___y_427_, v___y_428_);
return v___x_537_;
}
}
else
{
lean_dec_ref_known(v___y_437_, 3);
lean_dec_ref(v_post_425_);
lean_dec_ref(v_pre_423_);
return v___x_530_;
}
}
default: 
{
lean_object* v___x_538_; 
v___x_538_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(v_pre_423_, v_post_425_, v___y_437_, v___y_426_, v___y_427_, v___y_428_);
return v___x_538_;
}
}
}
}
}
else
{
lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_557_; 
lean_dec_ref(v_post_425_);
lean_dec_ref(v_e_424_);
lean_dec_ref(v_pre_423_);
v_a_550_ = lean_ctor_get(v___x_431_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_557_ == 0)
{
v___x_552_ = v___x_431_;
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_431_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_555_; 
if (v_isShared_553_ == 0)
{
v___x_555_ = v___x_552_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_a_550_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
else
{
lean_object* v_a_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_565_; 
lean_dec_ref(v_post_425_);
lean_dec_ref(v_e_424_);
lean_dec_ref(v_pre_423_);
v_a_558_ = lean_ctor_get(v___x_430_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_565_ == 0)
{
v___x_560_ = v___x_430_;
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_a_558_);
lean_dec(v___x_430_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_563_; 
if (v_isShared_561_ == 0)
{
v___x_563_ = v___x_560_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_a_558_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___boxed(lean_object* v___x_566_, lean_object* v_pre_567_, lean_object* v_e_568_, lean_object* v_post_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1(v___x_566_, v_pre_567_, v_e_568_, v_post_569_, v___y_570_, v___y_571_, v___y_572_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v___y_570_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(lean_object* v_pre_575_, lean_object* v_post_576_, lean_object* v_e_577_, lean_object* v_a_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; 
lean_inc(v_a_578_);
v___x_582_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_582_, 0, lean_box(0));
lean_closure_set(v___x_582_, 1, lean_box(0));
lean_closure_set(v___x_582_, 2, v_a_578_);
v___x_583_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(lean_box(0), v___x_582_, v___y_579_, v___y_580_);
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v_a_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_615_; 
v_a_584_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_615_ == 0)
{
v___x_586_ = v___x_583_;
v_isShared_587_ = v_isSharedCheck_615_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_a_584_);
lean_dec(v___x_583_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_615_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_588_; 
v___x_588_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1___redArg(v_a_584_, v_e_577_);
lean_dec(v_a_584_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v___x_589_; lean_object* v___f_590_; lean_object* v___x_591_; 
lean_del_object(v___x_586_);
v___x_589_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___closed__0));
lean_inc_ref(v_e_577_);
v___f_590_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___boxed), 8, 4);
lean_closure_set(v___f_590_, 0, v___x_589_);
lean_closure_set(v___f_590_, 1, v_pre_575_);
lean_closure_set(v___f_590_, 2, v_e_577_);
lean_closure_set(v___f_590_, 3, v_post_576_);
v___x_591_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(v___f_590_, v_a_578_, v___y_579_, v___y_580_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v_a_592_; lean_object* v___f_593_; lean_object* v___x_594_; 
v_a_592_ = lean_ctor_get(v___x_591_, 0);
lean_inc_n(v_a_592_, 2);
lean_dec_ref_known(v___x_591_, 1);
lean_inc(v_a_578_);
v___f_593_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_593_, 0, v_a_578_);
lean_closure_set(v___f_593_, 1, v_e_577_);
lean_closure_set(v___f_593_, 2, v_a_592_);
v___x_594_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(lean_box(0), v___f_593_, v___y_579_, v___y_580_);
if (lean_obj_tag(v___x_594_) == 0)
{
lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_601_; 
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_601_ == 0)
{
lean_object* v_unused_602_; 
v_unused_602_ = lean_ctor_get(v___x_594_, 0);
lean_dec(v_unused_602_);
v___x_596_ = v___x_594_;
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
else
{
lean_dec(v___x_594_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_599_; 
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 0, v_a_592_);
v___x_599_ = v___x_596_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_a_592_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
else
{
lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_610_; 
lean_dec(v_a_592_);
v_a_603_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_610_ == 0)
{
v___x_605_ = v___x_594_;
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v___x_594_);
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
}
else
{
lean_dec_ref(v_e_577_);
return v___x_591_;
}
}
else
{
lean_object* v_val_611_; lean_object* v___x_613_; 
lean_dec_ref(v_e_577_);
lean_dec_ref(v_post_576_);
lean_dec_ref(v_pre_575_);
v_val_611_ = lean_ctor_get(v___x_588_, 0);
lean_inc(v_val_611_);
lean_dec_ref_known(v___x_588_, 1);
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 0, v_val_611_);
v___x_613_ = v___x_586_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_val_611_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
else
{
lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_623_; 
lean_dec_ref(v_e_577_);
lean_dec_ref(v_post_576_);
lean_dec_ref(v_pre_575_);
v_a_616_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_623_ == 0)
{
v___x_618_ = v___x_583_;
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_dec(v___x_583_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_621_; 
if (v_isShared_619_ == 0)
{
v___x_621_ = v___x_618_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_a_616_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(lean_object* v_pre_624_, lean_object* v_post_625_, lean_object* v_e_626_, lean_object* v_a_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
lean_object* v___x_631_; 
lean_inc_ref(v_post_625_);
lean_inc(v___y_629_);
lean_inc_ref(v___y_628_);
lean_inc_ref(v_e_626_);
v___x_631_ = lean_apply_4(v_post_625_, v_e_626_, v___y_628_, v___y_629_, lean_box(0));
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v_a_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_650_; 
v_a_632_ = lean_ctor_get(v___x_631_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_650_ == 0)
{
v___x_634_ = v___x_631_;
v_isShared_635_ = v_isSharedCheck_650_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_a_632_);
lean_dec(v___x_631_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_650_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
switch(lean_obj_tag(v_a_632_))
{
case 0:
{
lean_object* v_e_636_; lean_object* v___x_638_; 
lean_dec_ref(v_e_626_);
lean_dec_ref(v_post_625_);
lean_dec_ref(v_pre_624_);
v_e_636_ = lean_ctor_get(v_a_632_, 0);
lean_inc_ref(v_e_636_);
lean_dec_ref_known(v_a_632_, 1);
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 0, v_e_636_);
v___x_638_ = v___x_634_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_e_636_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
case 1:
{
lean_object* v_e_640_; lean_object* v___x_641_; 
lean_del_object(v___x_634_);
lean_dec_ref(v_e_626_);
v_e_640_ = lean_ctor_get(v_a_632_, 0);
lean_inc_ref(v_e_640_);
lean_dec_ref_known(v_a_632_, 1);
v___x_641_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_624_, v_post_625_, v_e_640_, v_a_627_, v___y_628_, v___y_629_);
return v___x_641_;
}
default: 
{
lean_object* v_e_x3f_642_; 
lean_dec_ref(v_post_625_);
lean_dec_ref(v_pre_624_);
v_e_x3f_642_ = lean_ctor_get(v_a_632_, 0);
lean_inc(v_e_x3f_642_);
lean_dec_ref_known(v_a_632_, 1);
if (lean_obj_tag(v_e_x3f_642_) == 0)
{
lean_object* v___x_644_; 
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 0, v_e_626_);
v___x_644_ = v___x_634_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_e_626_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
else
{
lean_object* v_val_646_; lean_object* v___x_648_; 
lean_dec_ref(v_e_626_);
v_val_646_ = lean_ctor_get(v_e_x3f_642_, 0);
lean_inc(v_val_646_);
lean_dec_ref_known(v_e_x3f_642_, 1);
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 0, v_val_646_);
v___x_648_ = v___x_634_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_val_646_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
}
}
else
{
lean_object* v_a_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_658_; 
lean_dec_ref(v_e_626_);
lean_dec_ref(v_post_625_);
lean_dec_ref(v_pre_624_);
v_a_651_ = lean_ctor_get(v___x_631_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_658_ == 0)
{
v___x_653_ = v___x_631_;
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_a_651_);
lean_dec(v___x_631_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_656_; 
if (v_isShared_654_ == 0)
{
v___x_656_ = v___x_653_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_a_651_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___boxed(lean_object* v_pre_659_, lean_object* v_post_660_, lean_object* v_e_661_, lean_object* v_a_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(v_pre_659_, v_post_660_, v_e_661_, v_a_662_, v___y_663_, v___y_664_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
lean_dec(v_a_662_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_667_, lean_object* v_post_668_, lean_object* v_sz_669_, lean_object* v_i_670_, lean_object* v_bs_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
size_t v_sz_boxed_676_; size_t v_i_boxed_677_; lean_object* v_res_678_; 
v_sz_boxed_676_ = lean_unbox_usize(v_sz_669_);
lean_dec(v_sz_669_);
v_i_boxed_677_ = lean_unbox_usize(v_i_670_);
lean_dec(v_i_670_);
v_res_678_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_667_, v_post_668_, v_sz_boxed_676_, v_i_boxed_677_, v_bs_671_, v___y_672_, v___y_673_, v___y_674_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
lean_dec(v___y_672_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_679_, lean_object* v_post_680_, lean_object* v___y_681_, lean_object* v_x_682_, lean_object* v_x_683_, lean_object* v_x_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4(v_pre_679_, v_post_680_, v___y_681_, v_x_682_, v_x_683_, v_x_684_, v___y_685_, v___y_686_, v___y_687_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_681_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___boxed(lean_object* v_pre_690_, lean_object* v_post_691_, lean_object* v_e_692_, lean_object* v_a_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_690_, v_post_691_, v_e_692_, v_a_693_, v___y_694_, v___y_695_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_694_);
lean_dec(v_a_693_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(lean_object* v_00_u03b1_698_, lean_object* v_x_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_703_ = lean_apply_1(v_x_699_, lean_box(0));
v___x_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0___boxed(lean_object* v_00_u03b1_705_, lean_object* v_x_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(v_00_u03b1_705_, v_x_706_, v___y_707_, v___y_708_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
return v_res_710_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0(void){
_start:
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_711_ = lean_box(0);
v___x_712_ = lean_unsigned_to_nat(16u);
v___x_713_ = lean_mk_array(v___x_712_, v___x_711_);
return v___x_713_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1(void){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_714_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0);
v___x_715_ = lean_unsigned_to_nat(0u);
v___x_716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_716_, 0, v___x_715_);
lean_ctor_set(v___x_716_, 1, v___x_714_);
return v___x_716_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2(void){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_717_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1, &l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1);
v___x_718_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_718_, 0, lean_box(0));
lean_closure_set(v___x_718_, 1, lean_box(0));
lean_closure_set(v___x_718_, 2, v___x_717_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0(lean_object* v_input_719_, lean_object* v_pre_720_, lean_object* v_post_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v_a_727_; lean_object* v___x_728_; 
v___x_725_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2);
v___x_726_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(lean_box(0), v___x_725_, v___y_722_, v___y_723_);
v_a_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc(v_a_727_);
lean_dec_ref(v___x_726_);
v___x_728_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_720_, v_post_721_, v_input_719_, v_a_727_, v___y_722_, v___y_723_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v_a_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
v_a_729_ = lean_ctor_get(v___x_728_, 0);
lean_inc(v_a_729_);
lean_dec_ref_known(v___x_728_, 1);
v___x_730_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_730_, 0, lean_box(0));
lean_closure_set(v___x_730_, 1, lean_box(0));
lean_closure_set(v___x_730_, 2, v_a_727_);
v___x_731_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(lean_box(0), v___x_730_, v___y_722_, v___y_723_);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_738_ == 0)
{
lean_object* v_unused_739_; 
v_unused_739_ = lean_ctor_get(v___x_731_, 0);
lean_dec(v_unused_739_);
v___x_733_ = v___x_731_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_dec(v___x_731_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 0, v_a_729_);
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_a_729_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
else
{
lean_dec(v_a_727_);
return v___x_728_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___boxed(lean_object* v_input_740_, lean_object* v_pre_741_, lean_object* v_post_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0(v_input_740_, v_pre_741_, v_post_742_, v___y_743_, v___y_744_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam(lean_object* v_type_749_, lean_object* v_a_750_, lean_object* v_a_751_){
_start:
{
lean_object* v___f_753_; lean_object* v___f_754_; lean_object* v___x_755_; 
v___f_753_ = ((lean_object*)(l_Lean_Meta_elimOptParam___closed__0));
v___f_754_ = ((lean_object*)(l_Lean_Meta_elimOptParam___closed__1));
v___x_755_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0(v_type_749_, v___f_753_, v___f_754_, v_a_750_, v_a_751_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam___boxed(lean_object* v_type_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Lean_Meta_elimOptParam(v_type_756_, v_a_757_, v_a_758_);
lean_dec(v_a_758_);
lean_dec_ref(v_a_757_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_761_, lean_object* v_m_762_, lean_object* v_a_763_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1___redArg(v_m_762_, v_a_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_765_, lean_object* v_m_766_, lean_object* v_a_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1(v_00_u03b2_765_, v_m_766_, v_a_767_);
lean_dec_ref(v_a_767_);
lean_dec_ref(v_m_766_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_769_, lean_object* v_ref_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
lean_object* v___x_774_; 
v___x_774_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_770_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_775_, lean_object* v_ref_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_775_, v_ref_776_, v___y_777_, v___y_778_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8(lean_object* v_00_u03b1_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg();
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___boxed(lean_object* v_00_u03b1_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_786_, v___y_787_, v___y_788_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_791_, lean_object* v_x_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(v_x_792_, v___y_793_, v___y_794_, v___y_795_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_798_, lean_object* v_x_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5(v_00_u03b1_798_, v_x_799_, v___y_800_, v___y_801_, v___y_802_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
lean_dec(v___y_800_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_805_, lean_object* v_m_806_, lean_object* v_a_807_, lean_object* v_b_808_){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6___redArg(v_m_806_, v_a_807_, v_b_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_810_, lean_object* v_a_811_, lean_object* v_x_812_){
_start:
{
lean_object* v___x_813_; 
v___x_813_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1_spec__2___redArg(v_a_811_, v_x_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_814_, lean_object* v_a_815_, lean_object* v_x_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_814_, v_a_815_, v_x_816_);
lean_dec(v_x_816_);
lean_dec_ref(v_a_815_);
return v_res_817_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_818_, lean_object* v_a_819_, lean_object* v_x_820_){
_start:
{
uint8_t v___x_821_; 
v___x_821_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___redArg(v_a_819_, v_x_820_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___boxed(lean_object* v_00_u03b2_822_, lean_object* v_a_823_, lean_object* v_x_824_){
_start:
{
uint8_t v_res_825_; lean_object* v_r_826_; 
v_res_825_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_822_, v_a_823_, v_x_824_);
lean_dec(v_x_824_);
lean_dec_ref(v_a_823_);
v_r_826_ = lean_box(v_res_825_);
return v_r_826_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_827_, lean_object* v_data_828_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11___redArg(v_data_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__12(lean_object* v_00_u03b2_830_, lean_object* v_a_831_, lean_object* v_b_832_, lean_object* v_x_833_){
_start:
{
lean_object* v___x_834_; 
v___x_834_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__12___redArg(v_a_831_, v_b_832_, v_x_833_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12(lean_object* v_00_u03b2_835_, lean_object* v_i_836_, lean_object* v_source_837_, lean_object* v_target_838_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v_i_836_, v_source_837_, v_target_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_840_, lean_object* v_x_841_, lean_object* v_x_842_){
_start:
{
lean_object* v___x_843_; 
v___x_843_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_x_841_, v_x_842_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0(uint8_t v_skipIfPropOrEq_844_, lean_object* v_as_845_, size_t v_sz_846_, size_t v_i_847_, lean_object* v_b_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v_a_855_; uint8_t v___x_859_; 
v___x_859_ = lean_usize_dec_lt(v_i_847_, v_sz_846_);
if (v___x_859_ == 0)
{
lean_object* v___x_860_; 
v___x_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_860_, 0, v_b_848_);
return v___x_860_;
}
else
{
lean_object* v_snd_861_; lean_object* v_fst_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_940_; 
v_snd_861_ = lean_ctor_get(v_b_848_, 1);
v_fst_862_ = lean_ctor_get(v_b_848_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v_b_848_);
if (v_isSharedCheck_940_ == 0)
{
v___x_864_ = v_b_848_;
v_isShared_865_ = v_isSharedCheck_940_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_snd_861_);
lean_inc(v_fst_862_);
lean_dec(v_b_848_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_940_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v_array_866_; lean_object* v_start_867_; lean_object* v_stop_868_; uint8_t v___x_869_; 
v_array_866_ = lean_ctor_get(v_snd_861_, 0);
v_start_867_ = lean_ctor_get(v_snd_861_, 1);
v_stop_868_ = lean_ctor_get(v_snd_861_, 2);
v___x_869_ = lean_nat_dec_lt(v_start_867_, v_stop_868_);
if (v___x_869_ == 0)
{
lean_object* v___x_871_; 
if (v_isShared_865_ == 0)
{
v___x_871_ = v___x_864_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_fst_862_);
lean_ctor_set(v_reuseFailAlloc_873_, 1, v_snd_861_);
v___x_871_ = v_reuseFailAlloc_873_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
lean_object* v___x_872_; 
v___x_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_872_, 0, v___x_871_);
return v___x_872_;
}
}
else
{
lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_936_; 
lean_inc(v_stop_868_);
lean_inc(v_start_867_);
lean_inc_ref(v_array_866_);
v_isSharedCheck_936_ = !lean_is_exclusive(v_snd_861_);
if (v_isSharedCheck_936_ == 0)
{
lean_object* v_unused_937_; lean_object* v_unused_938_; lean_object* v_unused_939_; 
v_unused_937_ = lean_ctor_get(v_snd_861_, 2);
lean_dec(v_unused_937_);
v_unused_938_ = lean_ctor_get(v_snd_861_, 1);
lean_dec(v_unused_938_);
v_unused_939_ = lean_ctor_get(v_snd_861_, 0);
lean_dec(v_unused_939_);
v___x_875_ = v_snd_861_;
v_isShared_876_ = v_isSharedCheck_936_;
goto v_resetjp_874_;
}
else
{
lean_dec(v_snd_861_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_936_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v_a_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_882_; 
v_a_877_ = lean_array_uget_borrowed(v_as_845_, v_i_847_);
v___x_878_ = lean_array_fget(v_array_866_, v_start_867_);
v___x_879_ = lean_unsigned_to_nat(1u);
v___x_880_ = lean_nat_add(v_start_867_, v___x_879_);
lean_dec(v_start_867_);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 1, v___x_880_);
v___x_882_ = v___x_875_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_array_866_);
lean_ctor_set(v_reuseFailAlloc_935_, 1, v___x_880_);
lean_ctor_set(v_reuseFailAlloc_935_, 2, v_stop_868_);
v___x_882_ = v_reuseFailAlloc_935_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
lean_object* v___x_883_; 
lean_inc(v___y_852_);
lean_inc_ref(v___y_851_);
lean_inc(v___y_850_);
lean_inc_ref(v___y_849_);
lean_inc(v_a_877_);
v___x_883_ = lean_infer_type(v_a_877_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
if (lean_obj_tag(v___x_883_) == 0)
{
if (v_skipIfPropOrEq_844_ == 0)
{
lean_object* v___x_884_; 
lean_dec_ref_known(v___x_883_, 1);
lean_inc(v_a_877_);
v___x_884_ = l_Lean_Meta_mkEqHEq(v_a_877_, v___x_878_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
if (lean_obj_tag(v___x_884_) == 0)
{
lean_object* v_a_885_; lean_object* v___x_886_; lean_object* v___x_888_; 
v_a_885_ = lean_ctor_get(v___x_884_, 0);
lean_inc(v_a_885_);
lean_dec_ref_known(v___x_884_, 1);
v___x_886_ = lean_array_push(v_fst_862_, v_a_885_);
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 1, v___x_882_);
lean_ctor_set(v___x_864_, 0, v___x_886_);
v___x_888_ = v___x_864_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_886_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v___x_882_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
v_a_855_ = v___x_888_;
goto v___jp_854_;
}
}
else
{
lean_object* v_a_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_897_; 
lean_dec_ref(v___x_882_);
lean_del_object(v___x_864_);
lean_dec(v_fst_862_);
v_a_890_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_897_ == 0)
{
v___x_892_ = v___x_884_;
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_a_890_);
lean_dec(v___x_884_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_895_; 
if (v_isShared_893_ == 0)
{
v___x_895_ = v___x_892_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_a_890_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
}
else
{
lean_object* v_a_898_; lean_object* v___x_899_; 
v_a_898_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_a_898_);
lean_dec_ref_known(v___x_883_, 1);
v___x_899_ = l_Lean_Meta_isProp(v_a_898_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v_a_900_; uint8_t v___x_905_; 
v_a_900_ = lean_ctor_get(v___x_899_, 0);
lean_inc(v_a_900_);
lean_dec_ref_known(v___x_899_, 1);
v___x_905_ = lean_unbox(v_a_900_);
lean_dec(v_a_900_);
if (v___x_905_ == 0)
{
uint8_t v___x_906_; 
v___x_906_ = lean_expr_eqv(v_a_877_, v___x_878_);
if (v___x_906_ == 0)
{
lean_object* v___x_907_; 
lean_del_object(v___x_864_);
lean_inc(v_a_877_);
v___x_907_ = l_Lean_Meta_mkEqHEq(v_a_877_, v___x_878_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
if (lean_obj_tag(v___x_907_) == 0)
{
lean_object* v_a_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v_a_908_ = lean_ctor_get(v___x_907_, 0);
lean_inc(v_a_908_);
lean_dec_ref_known(v___x_907_, 1);
v___x_909_ = lean_array_push(v_fst_862_, v_a_908_);
v___x_910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_910_, 0, v___x_909_);
lean_ctor_set(v___x_910_, 1, v___x_882_);
v_a_855_ = v___x_910_;
goto v___jp_854_;
}
else
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_918_; 
lean_dec_ref(v___x_882_);
lean_dec(v_fst_862_);
v_a_911_ = lean_ctor_get(v___x_907_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_918_ == 0)
{
v___x_913_ = v___x_907_;
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_907_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_916_; 
if (v_isShared_914_ == 0)
{
v___x_916_ = v___x_913_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_a_911_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
else
{
lean_dec(v___x_878_);
goto v___jp_901_;
}
}
else
{
lean_dec(v___x_878_);
goto v___jp_901_;
}
v___jp_901_:
{
lean_object* v___x_903_; 
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 1, v___x_882_);
v___x_903_ = v___x_864_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_fst_862_);
lean_ctor_set(v_reuseFailAlloc_904_, 1, v___x_882_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
v_a_855_ = v___x_903_;
goto v___jp_854_;
}
}
}
else
{
lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_926_; 
lean_dec_ref(v___x_882_);
lean_dec(v___x_878_);
lean_del_object(v___x_864_);
lean_dec(v_fst_862_);
v_a_919_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_926_ == 0)
{
v___x_921_ = v___x_899_;
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v___x_899_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_924_; 
if (v_isShared_922_ == 0)
{
v___x_924_ = v___x_921_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_a_919_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
}
}
else
{
lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_934_; 
lean_dec_ref(v___x_882_);
lean_dec(v___x_878_);
lean_del_object(v___x_864_);
lean_dec(v_fst_862_);
v_a_927_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_934_ == 0)
{
v___x_929_ = v___x_883_;
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_883_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_932_; 
if (v_isShared_930_ == 0)
{
v___x_932_ = v___x_929_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_a_927_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
}
}
}
}
}
v___jp_854_:
{
size_t v___x_856_; size_t v___x_857_; 
v___x_856_ = ((size_t)1ULL);
v___x_857_ = lean_usize_add(v_i_847_, v___x_856_);
v_i_847_ = v___x_857_;
v_b_848_ = v_a_855_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0___boxed(lean_object* v_skipIfPropOrEq_941_, lean_object* v_as_942_, lean_object* v_sz_943_, lean_object* v_i_944_, lean_object* v_b_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
uint8_t v_skipIfPropOrEq_boxed_951_; size_t v_sz_boxed_952_; size_t v_i_boxed_953_; lean_object* v_res_954_; 
v_skipIfPropOrEq_boxed_951_ = lean_unbox(v_skipIfPropOrEq_941_);
v_sz_boxed_952_ = lean_unbox_usize(v_sz_943_);
lean_dec(v_sz_943_);
v_i_boxed_953_ = lean_unbox_usize(v_i_944_);
lean_dec(v_i_944_);
v_res_954_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0(v_skipIfPropOrEq_boxed_951_, v_as_942_, v_sz_boxed_952_, v_i_boxed_953_, v_b_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec_ref(v_as_942_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(lean_object* v_args1_957_, lean_object* v_args2_958_, uint8_t v_skipIfPropOrEq_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_){
_start:
{
lean_object* v___x_965_; lean_object* v_eqs_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; size_t v_sz_970_; size_t v___x_971_; lean_object* v___x_972_; 
v___x_965_ = lean_unsigned_to_nat(0u);
v_eqs_966_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_967_ = lean_array_get_size(v_args2_958_);
v___x_968_ = l_Array_toSubarray___redArg(v_args2_958_, v___x_965_, v___x_967_);
v___x_969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_969_, 0, v_eqs_966_);
lean_ctor_set(v___x_969_, 1, v___x_968_);
v_sz_970_ = lean_array_size(v_args1_957_);
v___x_971_ = ((size_t)0ULL);
v___x_972_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0(v_skipIfPropOrEq_959_, v_args1_957_, v_sz_970_, v___x_971_, v___x_969_, v_a_960_, v_a_961_, v_a_962_, v_a_963_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_981_; 
v_a_973_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_981_ == 0)
{
v___x_975_ = v___x_972_;
v_isShared_976_ = v_isSharedCheck_981_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_972_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_981_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v_fst_977_; lean_object* v___x_979_; 
v_fst_977_ = lean_ctor_get(v_a_973_, 0);
lean_inc(v_fst_977_);
lean_dec(v_a_973_);
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 0, v_fst_977_);
v___x_979_ = v___x_975_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_fst_977_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
else
{
lean_object* v_a_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_989_; 
v_a_982_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_989_ == 0)
{
v___x_984_ = v___x_972_;
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_a_982_);
lean_dec(v___x_972_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_987_; 
if (v_isShared_985_ == 0)
{
v___x_987_ = v___x_984_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_a_982_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___boxed(lean_object* v_args1_990_, lean_object* v_args2_991_, lean_object* v_skipIfPropOrEq_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_){
_start:
{
uint8_t v_skipIfPropOrEq_boxed_998_; lean_object* v_res_999_; 
v_skipIfPropOrEq_boxed_998_ = lean_unbox(v_skipIfPropOrEq_992_);
v_res_999_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v_args1_990_, v_args2_991_, v_skipIfPropOrEq_boxed_998_, v_a_993_, v_a_994_, v_a_995_, v_a_996_);
lean_dec(v_a_996_);
lean_dec_ref(v_a_995_);
lean_dec(v_a_994_);
lean_dec_ref(v_a_993_);
lean_dec_ref(v_args1_990_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0(lean_object* v_k_1000_, lean_object* v_b_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v___x_1007_; 
lean_inc(v___y_1005_);
lean_inc_ref(v___y_1004_);
lean_inc(v___y_1003_);
lean_inc_ref(v___y_1002_);
v___x_1007_ = lean_apply_6(v_k_1000_, v_b_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, lean_box(0));
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0___boxed(lean_object* v_k_1008_, lean_object* v_b_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0(v_k_1008_, v_b_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(lean_object* v_name_1016_, uint8_t v_bi_1017_, lean_object* v_type_1018_, lean_object* v_k_1019_, uint8_t v_kind_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v___f_1026_; lean_object* v___x_1027_; 
v___f_1026_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1026_, 0, v_k_1019_);
v___x_1027_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1016_, v_bi_1017_, v_type_1018_, v___f_1026_, v_kind_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1035_; 
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1030_ = v___x_1027_;
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_1027_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1033_; 
if (v_isShared_1031_ == 0)
{
v___x_1033_ = v___x_1030_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_a_1028_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
else
{
lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1043_; 
v_a_1036_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1038_ = v___x_1027_;
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___x_1027_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1041_; 
if (v_isShared_1039_ == 0)
{
v___x_1041_ = v___x_1038_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_a_1036_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___boxed(lean_object* v_name_1044_, lean_object* v_bi_1045_, lean_object* v_type_1046_, lean_object* v_k_1047_, lean_object* v_kind_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
uint8_t v_bi_boxed_1054_; uint8_t v_kind_boxed_1055_; lean_object* v_res_1056_; 
v_bi_boxed_1054_ = lean_unbox(v_bi_1045_);
v_kind_boxed_1055_ = lean_unbox(v_kind_1048_);
v_res_1056_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_name_1044_, v_bi_boxed_1054_, v_type_1046_, v_k_1047_, v_kind_boxed_1055_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0(lean_object* v_00_u03b1_1057_, lean_object* v_name_1058_, uint8_t v_bi_1059_, lean_object* v_type_1060_, lean_object* v_k_1061_, uint8_t v_kind_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_){
_start:
{
lean_object* v___x_1068_; 
v___x_1068_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_name_1058_, v_bi_1059_, v_type_1060_, v_k_1061_, v_kind_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___boxed(lean_object* v_00_u03b1_1069_, lean_object* v_name_1070_, lean_object* v_bi_1071_, lean_object* v_type_1072_, lean_object* v_k_1073_, lean_object* v_kind_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
uint8_t v_bi_boxed_1080_; uint8_t v_kind_boxed_1081_; lean_object* v_res_1082_; 
v_bi_boxed_1080_ = lean_unbox(v_bi_1071_);
v_kind_boxed_1081_ = lean_unbox(v_kind_1074_);
v_res_1082_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0(v_00_u03b1_1069_, v_name_1070_, v_bi_boxed_1080_, v_type_1072_, v_k_1073_, v_kind_boxed_1081_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(lean_object* v_msgData_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
lean_object* v___x_1089_; lean_object* v_env_1090_; uint8_t v___x_1091_; lean_object* v_env_1092_; lean_object* v___x_1093_; lean_object* v_toCold_1094_; lean_object* v_mctx_1095_; lean_object* v_lctx_1096_; lean_object* v_options_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1089_ = lean_st_ref_get(v___y_1087_);
v_env_1090_ = lean_ctor_get(v___x_1089_, 0);
lean_inc_ref(v_env_1090_);
lean_dec(v___x_1089_);
v___x_1091_ = 0;
v_env_1092_ = l_Lean_Environment_setRecordingDeps(v_env_1090_, v___x_1091_);
v___x_1093_ = lean_st_ref_get(v___y_1085_);
v_toCold_1094_ = lean_ctor_get(v___y_1086_, 0);
v_mctx_1095_ = lean_ctor_get(v___x_1093_, 0);
lean_inc_ref(v_mctx_1095_);
lean_dec(v___x_1093_);
v_lctx_1096_ = lean_ctor_get(v___y_1084_, 2);
v_options_1097_ = lean_ctor_get(v_toCold_1094_, 2);
lean_inc_ref(v_options_1097_);
lean_inc_ref(v_lctx_1096_);
v___x_1098_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1098_, 0, v_env_1092_);
lean_ctor_set(v___x_1098_, 1, v_mctx_1095_);
lean_ctor_set(v___x_1098_, 2, v_lctx_1096_);
lean_ctor_set(v___x_1098_, 3, v_options_1097_);
v___x_1099_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1098_);
lean_ctor_set(v___x_1099_, 1, v_msgData_1083_);
v___x_1100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1099_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1___boxed(lean_object* v_msgData_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msgData_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(lean_object* v_msg_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
lean_object* v_ref_1114_; lean_object* v___x_1115_; lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1124_; 
v_ref_1114_ = lean_ctor_get(v___y_1111_, 2);
v___x_1115_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msg_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1118_ = v___x_1115_;
v_isShared_1119_ = v_isSharedCheck_1124_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1115_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1124_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1120_; lean_object* v___x_1122_; 
lean_inc(v_ref_1114_);
v___x_1120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1120_, 0, v_ref_1114_);
lean_ctor_set(v___x_1120_, 1, v_a_1116_);
if (v_isShared_1119_ == 0)
{
lean_ctor_set_tag(v___x_1118_, 1);
lean_ctor_set(v___x_1118_, 0, v___x_1120_);
v___x_1122_ = v___x_1118_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v___x_1120_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg___boxed(lean_object* v_msg_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v_msg_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0___boxed(lean_object* v_i_1132_, lean_object* v_body_1133_, lean_object* v_args2_1134_, lean_object* v_args2New_1135_, lean_object* v_ctorVal_1136_, lean_object* v_useEq_1137_, lean_object* v_args1_1138_, lean_object* v_resultType_1139_, lean_object* v_k_1140_, lean_object* v_arg2_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_){
_start:
{
uint8_t v_useEq_boxed_1147_; lean_object* v_res_1148_; 
v_useEq_boxed_1147_ = lean_unbox(v_useEq_1137_);
v_res_1148_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0(v_i_1132_, v_body_1133_, v_args2_1134_, v_args2New_1135_, v_ctorVal_1136_, v_useEq_boxed_1147_, v_args1_1138_, v_resultType_1139_, v_k_1140_, v_arg2_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
lean_dec_ref(v_body_1133_);
lean_dec(v_i_1132_);
return v_res_1148_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1(void){
_start:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1150_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__0));
v___x_1151_ = l_Lean_stringToMessageData(v___x_1150_);
return v___x_1151_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3(void){
_start:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1153_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__2));
v___x_1154_ = l_Lean_stringToMessageData(v___x_1153_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(lean_object* v_ctorVal_1155_, uint8_t v_useEq_1156_, lean_object* v_args1_1157_, lean_object* v_resultType_1158_, lean_object* v_k_1159_, lean_object* v_i_1160_, lean_object* v_type_1161_, lean_object* v_args2_1162_, lean_object* v_args2New_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_){
_start:
{
lean_object* v___x_1169_; uint8_t v___x_1170_; 
v___x_1169_ = lean_array_get_size(v_args1_1157_);
v___x_1170_ = lean_nat_dec_lt(v_i_1160_, v___x_1169_);
if (v___x_1170_ == 0)
{
lean_object* v___x_1171_; 
lean_dec_ref(v_type_1161_);
lean_dec(v_i_1160_);
lean_dec_ref(v_resultType_1158_);
lean_dec_ref(v_args1_1157_);
lean_dec_ref(v_ctorVal_1155_);
lean_inc(v_a_1167_);
lean_inc_ref(v_a_1166_);
lean_inc(v_a_1165_);
lean_inc_ref(v_a_1164_);
v___x_1171_ = lean_apply_7(v_k_1159_, v_args2_1162_, v_args2New_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, lean_box(0));
return v___x_1171_;
}
else
{
lean_object* v___x_1172_; 
lean_inc(v_a_1167_);
lean_inc_ref(v_a_1166_);
lean_inc(v_a_1165_);
lean_inc_ref(v_a_1164_);
v___x_1172_ = lean_whnf(v_type_1161_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_);
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_object* v_a_1173_; 
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
lean_inc(v_a_1173_);
lean_dec_ref_known(v___x_1172_, 1);
if (lean_obj_tag(v_a_1173_) == 7)
{
lean_object* v_binderName_1174_; lean_object* v_binderType_1175_; lean_object* v_body_1176_; lean_object* v_lctx_1177_; lean_object* v___x_1178_; uint8_t v___x_1179_; 
v_binderName_1174_ = lean_ctor_get(v_a_1173_, 0);
lean_inc(v_binderName_1174_);
v_binderType_1175_ = lean_ctor_get(v_a_1173_, 1);
lean_inc_ref(v_binderType_1175_);
v_body_1176_ = lean_ctor_get(v_a_1173_, 2);
lean_inc_ref(v_body_1176_);
lean_dec_ref_known(v_a_1173_, 3);
v_lctx_1177_ = lean_ctor_get(v_a_1164_, 2);
v___x_1178_ = lean_array_fget_borrowed(v_args1_1157_, v_i_1160_);
lean_inc(v___x_1178_);
lean_inc_ref(v_lctx_1177_);
v___x_1179_ = l_Lean_Meta_occursOrInType(v_lctx_1177_, v___x_1178_, v_resultType_1158_);
if (v___x_1179_ == 0)
{
lean_object* v___x_1180_; lean_object* v___f_1181_; uint8_t v___y_1183_; 
v___x_1180_ = lean_box(v_useEq_1156_);
v___f_1181_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0___boxed), 15, 9);
lean_closure_set(v___f_1181_, 0, v_i_1160_);
lean_closure_set(v___f_1181_, 1, v_body_1176_);
lean_closure_set(v___f_1181_, 2, v_args2_1162_);
lean_closure_set(v___f_1181_, 3, v_args2New_1163_);
lean_closure_set(v___f_1181_, 4, v_ctorVal_1155_);
lean_closure_set(v___f_1181_, 5, v___x_1180_);
lean_closure_set(v___f_1181_, 6, v_args1_1157_);
lean_closure_set(v___f_1181_, 7, v_resultType_1158_);
lean_closure_set(v___f_1181_, 8, v_k_1159_);
if (v_useEq_1156_ == 0)
{
uint8_t v___x_1186_; 
v___x_1186_ = 1;
v___y_1183_ = v___x_1186_;
goto v___jp_1182_;
}
else
{
uint8_t v___x_1187_; 
v___x_1187_ = 0;
v___y_1183_ = v___x_1187_;
goto v___jp_1182_;
}
v___jp_1182_:
{
uint8_t v___x_1184_; lean_object* v___x_1185_; 
v___x_1184_ = 0;
v___x_1185_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_binderName_1174_, v___y_1183_, v_binderType_1175_, v___f_1181_, v___x_1184_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_);
return v___x_1185_;
}
}
else
{
lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
lean_dec_ref(v_binderType_1175_);
lean_dec(v_binderName_1174_);
v___x_1188_ = lean_unsigned_to_nat(1u);
v___x_1189_ = lean_nat_add(v_i_1160_, v___x_1188_);
lean_dec(v_i_1160_);
v___x_1190_ = lean_expr_instantiate1(v_body_1176_, v___x_1178_);
lean_dec_ref(v_body_1176_);
lean_inc(v___x_1178_);
v___x_1191_ = lean_array_push(v_args2_1162_, v___x_1178_);
v_i_1160_ = v___x_1189_;
v_type_1161_ = v___x_1190_;
v_args2_1162_ = v___x_1191_;
goto _start;
}
}
else
{
lean_object* v_toConstantVal_1193_; lean_object* v_name_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
lean_dec(v_a_1173_);
lean_dec_ref(v_args2New_1163_);
lean_dec_ref(v_args2_1162_);
lean_dec(v_i_1160_);
lean_dec_ref(v_k_1159_);
lean_dec_ref(v_resultType_1158_);
lean_dec_ref(v_args1_1157_);
v_toConstantVal_1193_ = lean_ctor_get(v_ctorVal_1155_, 0);
lean_inc_ref(v_toConstantVal_1193_);
lean_dec_ref(v_ctorVal_1155_);
v_name_1194_ = lean_ctor_get(v_toConstantVal_1193_, 0);
lean_inc(v_name_1194_);
lean_dec_ref(v_toConstantVal_1193_);
v___x_1195_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1);
v___x_1196_ = l_Lean_MessageData_ofName(v_name_1194_);
v___x_1197_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1195_);
lean_ctor_set(v___x_1197_, 1, v___x_1196_);
v___x_1198_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_1199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1197_);
lean_ctor_set(v___x_1199_, 1, v___x_1198_);
v___x_1200_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_1199_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_);
return v___x_1200_;
}
}
else
{
lean_object* v_a_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1208_; 
lean_dec_ref(v_args2New_1163_);
lean_dec_ref(v_args2_1162_);
lean_dec(v_i_1160_);
lean_dec_ref(v_k_1159_);
lean_dec_ref(v_resultType_1158_);
lean_dec_ref(v_args1_1157_);
lean_dec_ref(v_ctorVal_1155_);
v_a_1201_ = lean_ctor_get(v___x_1172_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1203_ = v___x_1172_;
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_a_1201_);
lean_dec(v___x_1172_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1206_; 
if (v_isShared_1204_ == 0)
{
v___x_1206_ = v___x_1203_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_a_1201_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0(lean_object* v_i_1209_, lean_object* v_body_1210_, lean_object* v_args2_1211_, lean_object* v_args2New_1212_, lean_object* v_ctorVal_1213_, uint8_t v_useEq_1214_, lean_object* v_args1_1215_, lean_object* v_resultType_1216_, lean_object* v_k_1217_, lean_object* v_arg2_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1224_ = lean_unsigned_to_nat(1u);
v___x_1225_ = lean_nat_add(v_i_1209_, v___x_1224_);
v___x_1226_ = lean_expr_instantiate1(v_body_1210_, v_arg2_1218_);
lean_inc_ref(v_arg2_1218_);
v___x_1227_ = lean_array_push(v_args2_1211_, v_arg2_1218_);
v___x_1228_ = lean_array_push(v_args2New_1212_, v_arg2_1218_);
v___x_1229_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(v_ctorVal_1213_, v_useEq_1214_, v_args1_1215_, v_resultType_1216_, v_k_1217_, v___x_1225_, v___x_1226_, v___x_1227_, v___x_1228_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___boxed(lean_object* v_ctorVal_1230_, lean_object* v_useEq_1231_, lean_object* v_args1_1232_, lean_object* v_resultType_1233_, lean_object* v_k_1234_, lean_object* v_i_1235_, lean_object* v_type_1236_, lean_object* v_args2_1237_, lean_object* v_args2New_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_){
_start:
{
uint8_t v_useEq_boxed_1244_; lean_object* v_res_1245_; 
v_useEq_boxed_1244_ = lean_unbox(v_useEq_1231_);
v_res_1245_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(v_ctorVal_1230_, v_useEq_boxed_1244_, v_args1_1232_, v_resultType_1233_, v_k_1234_, v_i_1235_, v_type_1236_, v_args2_1237_, v_args2New_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_);
lean_dec(v_a_1242_);
lean_dec_ref(v_a_1241_);
lean_dec(v_a_1240_);
lean_dec_ref(v_a_1239_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1(lean_object* v_00_u03b1_1246_, lean_object* v_msg_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
lean_object* v___x_1253_; 
v___x_1253_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v_msg_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___boxed(lean_object* v_00_u03b1_1254_, lean_object* v_msg_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1(v_00_u03b1_1254_, v_msg_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_);
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_match__1_splitter___redArg(lean_object* v_____x_1262_, lean_object* v_h__1_1263_, lean_object* v_h__2_1264_){
_start:
{
if (lean_obj_tag(v_____x_1262_) == 7)
{
lean_object* v_binderName_1265_; lean_object* v_binderType_1266_; lean_object* v_body_1267_; uint8_t v_binderInfo_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
lean_dec(v_h__2_1264_);
v_binderName_1265_ = lean_ctor_get(v_____x_1262_, 0);
lean_inc(v_binderName_1265_);
v_binderType_1266_ = lean_ctor_get(v_____x_1262_, 1);
lean_inc_ref(v_binderType_1266_);
v_body_1267_ = lean_ctor_get(v_____x_1262_, 2);
lean_inc_ref(v_body_1267_);
v_binderInfo_1268_ = lean_ctor_get_uint8(v_____x_1262_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_____x_1262_, 3);
v___x_1269_ = lean_box(v_binderInfo_1268_);
v___x_1270_ = lean_apply_4(v_h__1_1263_, v_binderName_1265_, v_binderType_1266_, v_body_1267_, v___x_1269_);
return v___x_1270_;
}
else
{
lean_object* v___x_1271_; 
lean_dec(v_h__1_1263_);
v___x_1271_ = lean_apply_2(v_h__2_1264_, v_____x_1262_, lean_box(0));
return v___x_1271_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_match__1_splitter(lean_object* v_motive_1272_, lean_object* v_____x_1273_, lean_object* v_h__1_1274_, lean_object* v_h__2_1275_){
_start:
{
if (lean_obj_tag(v_____x_1273_) == 7)
{
lean_object* v_binderName_1276_; lean_object* v_binderType_1277_; lean_object* v_body_1278_; uint8_t v_binderInfo_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
lean_dec(v_h__2_1275_);
v_binderName_1276_ = lean_ctor_get(v_____x_1273_, 0);
lean_inc(v_binderName_1276_);
v_binderType_1277_ = lean_ctor_get(v_____x_1273_, 1);
lean_inc_ref(v_binderType_1277_);
v_body_1278_ = lean_ctor_get(v_____x_1273_, 2);
lean_inc_ref(v_body_1278_);
v_binderInfo_1279_ = lean_ctor_get_uint8(v_____x_1273_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_____x_1273_, 3);
v___x_1280_ = lean_box(v_binderInfo_1279_);
v___x_1281_ = lean_apply_4(v_h__1_1274_, v_binderName_1276_, v_binderType_1277_, v_body_1278_, v___x_1280_);
return v___x_1281_;
}
else
{
lean_object* v___x_1282_; 
lean_dec(v_h__1_1274_);
v___x_1282_ = lean_apply_2(v_h__2_1275_, v_____x_1273_, lean_box(0));
return v___x_1282_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0(lean_object* v_k_1283_, lean_object* v_b_1284_, lean_object* v_c_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v___x_1291_; 
lean_inc(v___y_1289_);
lean_inc_ref(v___y_1288_);
lean_inc(v___y_1287_);
lean_inc_ref(v___y_1286_);
v___x_1291_ = lean_apply_7(v_k_1283_, v_b_1284_, v_c_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, lean_box(0));
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed(lean_object* v_k_1292_, lean_object* v_b_1293_, lean_object* v_c_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0(v_k_1292_, v_b_1293_, v_c_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
lean_dec(v___y_1296_);
lean_dec_ref(v___y_1295_);
return v_res_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(lean_object* v_type_1301_, lean_object* v_k_1302_, uint8_t v_cleanupAnnotations_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
lean_object* v___f_1309_; uint8_t v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___f_1309_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1309_, 0, v_k_1302_);
v___x_1310_ = 0;
v___x_1311_ = lean_box(0);
v___x_1312_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_1310_, v___x_1311_, v_type_1301_, v___f_1309_, v_cleanupAnnotations_1303_, v___x_1310_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
if (lean_obj_tag(v___x_1312_) == 0)
{
lean_object* v_a_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1320_; 
v_a_1313_ = lean_ctor_get(v___x_1312_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1315_ = v___x_1312_;
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_a_1313_);
lean_dec(v___x_1312_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1318_; 
if (v_isShared_1316_ == 0)
{
v___x_1318_ = v___x_1315_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_a_1313_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
else
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1328_; 
v_a_1321_ = lean_ctor_get(v___x_1312_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1323_ = v___x_1312_;
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1312_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1326_; 
if (v_isShared_1324_ == 0)
{
v___x_1326_ = v___x_1323_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_a_1321_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___boxed(lean_object* v_type_1329_, lean_object* v_k_1330_, lean_object* v_cleanupAnnotations_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1337_; lean_object* v_res_1338_; 
v_cleanupAnnotations_boxed_1337_ = lean_unbox(v_cleanupAnnotations_1331_);
v_res_1338_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_type_1329_, v_k_1330_, v_cleanupAnnotations_boxed_1337_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
return v_res_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2(lean_object* v_00_u03b1_1339_, lean_object* v_type_1340_, lean_object* v_k_1341_, uint8_t v_cleanupAnnotations_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_){
_start:
{
lean_object* v___x_1348_; 
v___x_1348_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_type_1340_, v_k_1341_, v_cleanupAnnotations_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___boxed(lean_object* v_00_u03b1_1349_, lean_object* v_type_1350_, lean_object* v_k_1351_, lean_object* v_cleanupAnnotations_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1358_; lean_object* v_res_1359_; 
v_cleanupAnnotations_boxed_1358_ = lean_unbox(v_cleanupAnnotations_1352_);
v_res_1359_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2(v_00_u03b1_1349_, v_type_1350_, v_k_1351_, v_cleanupAnnotations_boxed_1358_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(lean_object* v_type_1360_, lean_object* v_maxFVars_x3f_1361_, lean_object* v_k_1362_, uint8_t v_cleanupAnnotations_1363_, uint8_t v_whnfType_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v___f_1370_; lean_object* v___x_1371_; 
v___f_1370_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1370_, 0, v_k_1362_);
v___x_1371_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_1360_, v_maxFVars_x3f_1361_, v___f_1370_, v_cleanupAnnotations_1363_, v_whnfType_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_object* v_a_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1379_; 
v_a_1372_ = lean_ctor_get(v___x_1371_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1374_ = v___x_1371_;
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_a_1372_);
lean_dec(v___x_1371_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1377_; 
if (v_isShared_1375_ == 0)
{
v___x_1377_ = v___x_1374_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_a_1372_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
else
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1387_; 
v_a_1380_ = lean_ctor_get(v___x_1371_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1382_ = v___x_1371_;
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1371_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1385_; 
if (v_isShared_1383_ == 0)
{
v___x_1385_ = v___x_1382_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_a_1380_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg___boxed(lean_object* v_type_1388_, lean_object* v_maxFVars_x3f_1389_, lean_object* v_k_1390_, lean_object* v_cleanupAnnotations_1391_, lean_object* v_whnfType_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1398_; uint8_t v_whnfType_boxed_1399_; lean_object* v_res_1400_; 
v_cleanupAnnotations_boxed_1398_ = lean_unbox(v_cleanupAnnotations_1391_);
v_whnfType_boxed_1399_ = lean_unbox(v_whnfType_1392_);
v_res_1400_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(v_type_1388_, v_maxFVars_x3f_1389_, v_k_1390_, v_cleanupAnnotations_boxed_1398_, v_whnfType_boxed_1399_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1395_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3(lean_object* v_00_u03b1_1401_, lean_object* v_type_1402_, lean_object* v_maxFVars_x3f_1403_, lean_object* v_k_1404_, uint8_t v_cleanupAnnotations_1405_, uint8_t v_whnfType_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_){
_start:
{
lean_object* v___x_1412_; 
v___x_1412_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(v_type_1402_, v_maxFVars_x3f_1403_, v_k_1404_, v_cleanupAnnotations_1405_, v_whnfType_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___boxed(lean_object* v_00_u03b1_1413_, lean_object* v_type_1414_, lean_object* v_maxFVars_x3f_1415_, lean_object* v_k_1416_, lean_object* v_cleanupAnnotations_1417_, lean_object* v_whnfType_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1424_; uint8_t v_whnfType_boxed_1425_; lean_object* v_res_1426_; 
v_cleanupAnnotations_boxed_1424_ = lean_unbox(v_cleanupAnnotations_1417_);
v_whnfType_boxed_1425_ = lean_unbox(v_whnfType_1418_);
v_res_1426_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3(v_00_u03b1_1413_, v_type_1414_, v_maxFVars_x3f_1415_, v_k_1416_, v_cleanupAnnotations_boxed_1424_, v_whnfType_boxed_1425_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0(lean_object* v_name_1427_, lean_object* v_us_1428_, lean_object* v_params_1429_, lean_object* v_args1_1430_, uint8_t v_useEq_1431_, lean_object* v_args2_1432_, lean_object* v_args2New_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_){
_start:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; 
v___x_1439_ = l_Lean_mkConst(v_name_1427_, v_us_1428_);
v___x_1440_ = l_Lean_mkAppN(v___x_1439_, v_params_1429_);
lean_inc_ref(v___x_1440_);
v___x_1441_ = l_Lean_mkAppN(v___x_1440_, v_args1_1430_);
v___x_1442_ = l_Lean_mkAppN(v___x_1440_, v_args2_1432_);
v___x_1443_ = l_Lean_Meta_mkEq(v___x_1441_, v___x_1442_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_);
if (lean_obj_tag(v___x_1443_) == 0)
{
lean_object* v_a_1444_; uint8_t v___x_1445_; lean_object* v_result_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___x_1492_; 
v_a_1444_ = lean_ctor_get(v___x_1443_, 0);
lean_inc(v_a_1444_);
lean_dec_ref_known(v___x_1443_, 1);
v___x_1445_ = 1;
v___x_1492_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v_args1_1430_, v_args2_1432_, v___x_1445_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_);
if (lean_obj_tag(v___x_1492_) == 0)
{
lean_object* v_a_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1524_; 
v_a_1493_ = lean_ctor_get(v___x_1492_, 0);
v_isSharedCheck_1524_ = !lean_is_exclusive(v___x_1492_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1495_ = v___x_1492_;
v_isShared_1496_ = v_isSharedCheck_1524_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_a_1493_);
lean_dec(v___x_1492_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1524_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1497_; 
v___x_1497_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f(v_a_1493_);
if (lean_obj_tag(v___x_1497_) == 1)
{
lean_del_object(v___x_1495_);
if (v_useEq_1431_ == 0)
{
lean_object* v_val_1498_; lean_object* v___x_1499_; 
v_val_1498_ = lean_ctor_get(v___x_1497_, 0);
lean_inc(v_val_1498_);
lean_dec_ref_known(v___x_1497_, 1);
v___x_1499_ = l_Lean_mkArrow(v_a_1444_, v_val_1498_, v___y_1436_, v___y_1437_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_object* v_a_1500_; 
v_a_1500_ = lean_ctor_get(v___x_1499_, 0);
lean_inc(v_a_1500_);
lean_dec_ref_known(v___x_1499_, 1);
v_result_1447_ = v_a_1500_;
v___y_1448_ = v___y_1434_;
v___y_1449_ = v___y_1435_;
v___y_1450_ = v___y_1436_;
v___y_1451_ = v___y_1437_;
goto v___jp_1446_;
}
else
{
lean_object* v_a_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1508_; 
v_a_1501_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1503_ = v___x_1499_;
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_a_1501_);
lean_dec(v___x_1499_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1506_; 
if (v_isShared_1504_ == 0)
{
v___x_1506_ = v___x_1503_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_a_1501_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
}
else
{
lean_object* v_val_1509_; lean_object* v___x_1510_; 
v_val_1509_ = lean_ctor_get(v___x_1497_, 0);
lean_inc(v_val_1509_);
lean_dec_ref_known(v___x_1497_, 1);
v___x_1510_ = l_Lean_Meta_mkEq(v_a_1444_, v_val_1509_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_);
if (lean_obj_tag(v___x_1510_) == 0)
{
lean_object* v_a_1511_; 
v_a_1511_ = lean_ctor_get(v___x_1510_, 0);
lean_inc(v_a_1511_);
lean_dec_ref_known(v___x_1510_, 1);
v_result_1447_ = v_a_1511_;
v___y_1448_ = v___y_1434_;
v___y_1449_ = v___y_1435_;
v___y_1450_ = v___y_1436_;
v___y_1451_ = v___y_1437_;
goto v___jp_1446_;
}
else
{
lean_object* v_a_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1519_; 
v_a_1512_ = lean_ctor_get(v___x_1510_, 0);
v_isSharedCheck_1519_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1514_ = v___x_1510_;
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_a_1512_);
lean_dec(v___x_1510_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1517_; 
if (v_isShared_1515_ == 0)
{
v___x_1517_ = v___x_1514_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_a_1512_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
return v___x_1517_;
}
}
}
}
}
else
{
lean_object* v___x_1520_; lean_object* v___x_1522_; 
lean_dec(v___x_1497_);
lean_dec(v_a_1444_);
v___x_1520_ = lean_box(0);
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 0, v___x_1520_);
v___x_1522_ = v___x_1495_;
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
else
{
lean_object* v_a_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1532_; 
lean_dec(v_a_1444_);
v_a_1525_ = lean_ctor_get(v___x_1492_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1492_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1527_ = v___x_1492_;
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_a_1525_);
lean_dec(v___x_1492_);
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
v___jp_1446_:
{
uint8_t v___x_1452_; uint8_t v___x_1453_; lean_object* v___x_1454_; 
v___x_1452_ = 0;
v___x_1453_ = 1;
v___x_1454_ = l_Lean_Meta_mkForallFVars(v_args2New_1433_, v_result_1447_, v___x_1452_, v___x_1445_, v___x_1445_, v___x_1453_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v_a_1455_; lean_object* v___x_1456_; 
v_a_1455_ = lean_ctor_get(v___x_1454_, 0);
lean_inc(v_a_1455_);
lean_dec_ref_known(v___x_1454_, 1);
v___x_1456_ = l_Lean_Meta_mkForallFVars(v_args1_1430_, v_a_1455_, v___x_1452_, v___x_1445_, v___x_1445_, v___x_1453_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_object* v_a_1457_; lean_object* v___x_1458_; 
v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
lean_inc(v_a_1457_);
lean_dec_ref_known(v___x_1456_, 1);
v___x_1458_ = l_Lean_Meta_mkForallFVars(v_params_1429_, v_a_1457_, v___x_1452_, v___x_1445_, v___x_1445_, v___x_1453_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_);
if (lean_obj_tag(v___x_1458_) == 0)
{
lean_object* v_a_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1467_; 
v_a_1459_ = lean_ctor_get(v___x_1458_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1461_ = v___x_1458_;
v_isShared_1462_ = v_isSharedCheck_1467_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_a_1459_);
lean_dec(v___x_1458_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1467_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1463_; lean_object* v___x_1465_; 
v___x_1463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1463_, 0, v_a_1459_);
if (v_isShared_1462_ == 0)
{
lean_ctor_set(v___x_1461_, 0, v___x_1463_);
v___x_1465_ = v___x_1461_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v___x_1463_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
else
{
lean_object* v_a_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1475_; 
v_a_1468_ = lean_ctor_get(v___x_1458_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1470_ = v___x_1458_;
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_a_1468_);
lean_dec(v___x_1458_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1473_; 
if (v_isShared_1471_ == 0)
{
v___x_1473_ = v___x_1470_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_a_1468_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
}
else
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1483_; 
v_a_1476_ = lean_ctor_get(v___x_1456_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1478_ = v___x_1456_;
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1456_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1481_; 
if (v_isShared_1479_ == 0)
{
v___x_1481_ = v___x_1478_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_a_1476_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
}
}
else
{
lean_object* v_a_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1491_; 
v_a_1484_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1486_ = v___x_1454_;
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_a_1484_);
lean_dec(v___x_1454_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1489_; 
if (v_isShared_1487_ == 0)
{
v___x_1489_ = v___x_1486_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_a_1484_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
}
}
else
{
lean_object* v_a_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1540_; 
lean_dec_ref(v_args2_1432_);
v_a_1533_ = lean_ctor_get(v___x_1443_, 0);
v_isSharedCheck_1540_ = !lean_is_exclusive(v___x_1443_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1535_ = v___x_1443_;
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_a_1533_);
lean_dec(v___x_1443_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1538_; 
if (v_isShared_1536_ == 0)
{
v___x_1538_ = v___x_1535_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_a_1533_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0___boxed(lean_object* v_name_1541_, lean_object* v_us_1542_, lean_object* v_params_1543_, lean_object* v_args1_1544_, lean_object* v_useEq_1545_, lean_object* v_args2_1546_, lean_object* v_args2New_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_){
_start:
{
uint8_t v_useEq_boxed_1553_; lean_object* v_res_1554_; 
v_useEq_boxed_1553_ = lean_unbox(v_useEq_1545_);
v_res_1554_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0(v_name_1541_, v_us_1542_, v_params_1543_, v_args1_1544_, v_useEq_boxed_1553_, v_args2_1546_, v_args2New_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
lean_dec(v___y_1551_);
lean_dec_ref(v___y_1550_);
lean_dec(v___y_1549_);
lean_dec_ref(v___y_1548_);
lean_dec_ref(v_args2New_1547_);
lean_dec_ref(v_args1_1544_);
lean_dec_ref(v_params_1543_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1(size_t v_sz_1555_, size_t v_i_1556_, lean_object* v_bs_1557_){
_start:
{
uint8_t v___x_1558_; 
v___x_1558_ = lean_usize_dec_lt(v_i_1556_, v_sz_1555_);
if (v___x_1558_ == 0)
{
return v_bs_1557_;
}
else
{
lean_object* v_v_1559_; lean_object* v___x_1560_; lean_object* v_bs_x27_1561_; lean_object* v___x_1562_; uint8_t v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; size_t v___x_1566_; size_t v___x_1567_; lean_object* v___x_1568_; 
v_v_1559_ = lean_array_uget(v_bs_1557_, v_i_1556_);
v___x_1560_ = lean_unsigned_to_nat(0u);
v_bs_x27_1561_ = lean_array_uset(v_bs_1557_, v_i_1556_, v___x_1560_);
v___x_1562_ = l_Lean_Expr_fvarId_x21(v_v_1559_);
lean_dec(v_v_1559_);
v___x_1563_ = 1;
v___x_1564_ = lean_box(v___x_1563_);
v___x_1565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1562_);
lean_ctor_set(v___x_1565_, 1, v___x_1564_);
v___x_1566_ = ((size_t)1ULL);
v___x_1567_ = lean_usize_add(v_i_1556_, v___x_1566_);
v___x_1568_ = lean_array_uset(v_bs_x27_1561_, v_i_1556_, v___x_1565_);
v_i_1556_ = v___x_1567_;
v_bs_1557_ = v___x_1568_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1___boxed(lean_object* v_sz_1570_, lean_object* v_i_1571_, lean_object* v_bs_1572_){
_start:
{
size_t v_sz_boxed_1573_; size_t v_i_boxed_1574_; lean_object* v_res_1575_; 
v_sz_boxed_1573_ = lean_unbox_usize(v_sz_1570_);
lean_dec(v_sz_1570_);
v_i_boxed_1574_ = lean_unbox_usize(v_i_1571_);
lean_dec(v_i_1571_);
v_res_1575_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1(v_sz_boxed_1573_, v_i_boxed_1574_, v_bs_1572_);
return v_res_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(lean_object* v_bs_1576_, lean_object* v_k_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_){
_start:
{
lean_object* v___x_1583_; 
v___x_1583_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_box(0), v_bs_1576_, v_k_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1591_; 
v_a_1584_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1586_ = v___x_1583_;
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v___x_1583_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1589_; 
if (v_isShared_1587_ == 0)
{
v___x_1589_ = v___x_1586_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_a_1584_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
else
{
lean_object* v_a_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1599_; 
v_a_1592_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1594_ = v___x_1583_;
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_a_1592_);
lean_dec(v___x_1583_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1597_; 
if (v_isShared_1595_ == 0)
{
v___x_1597_ = v___x_1594_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_a_1592_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_bs_1600_, lean_object* v_k_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
lean_object* v_res_1607_; 
v_res_1607_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(v_bs_1600_, v_k_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
lean_dec_ref(v_bs_1600_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(lean_object* v_bs_1608_, lean_object* v_k_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_){
_start:
{
size_t v_sz_1615_; size_t v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; 
v_sz_1615_ = lean_array_size(v_bs_1608_);
v___x_1616_ = ((size_t)0ULL);
v___x_1617_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1(v_sz_1615_, v___x_1616_, v_bs_1608_);
v___x_1618_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(v___x_1617_, v_k_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_);
lean_dec_ref(v___x_1617_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg___boxed(lean_object* v_bs_1619_, lean_object* v_k_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v_bs_1619_, v_k_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1(lean_object* v_name_1627_, lean_object* v_us_1628_, lean_object* v_params_1629_, uint8_t v_useEq_1630_, lean_object* v_ctorVal_1631_, lean_object* v_type_1632_, lean_object* v_args1_1633_, lean_object* v_resultType_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_){
_start:
{
lean_object* v___x_1640_; lean_object* v___f_1641_; 
v___x_1640_ = lean_box(v_useEq_1630_);
lean_inc_ref(v_args1_1633_);
lean_inc_ref(v_params_1629_);
v___f_1641_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1641_, 0, v_name_1627_);
lean_closure_set(v___f_1641_, 1, v_us_1628_);
lean_closure_set(v___f_1641_, 2, v_params_1629_);
lean_closure_set(v___f_1641_, 3, v_args1_1633_);
lean_closure_set(v___f_1641_, 4, v___x_1640_);
if (v_useEq_1630_ == 0)
{
lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1642_ = l_Array_append___redArg(v_params_1629_, v_args1_1633_);
v___x_1643_ = lean_unsigned_to_nat(0u);
v___x_1644_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_1645_ = lean_box(v_useEq_1630_);
v___x_1646_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___boxed), 14, 9);
lean_closure_set(v___x_1646_, 0, v_ctorVal_1631_);
lean_closure_set(v___x_1646_, 1, v___x_1645_);
lean_closure_set(v___x_1646_, 2, v_args1_1633_);
lean_closure_set(v___x_1646_, 3, v_resultType_1634_);
lean_closure_set(v___x_1646_, 4, v___f_1641_);
lean_closure_set(v___x_1646_, 5, v___x_1643_);
lean_closure_set(v___x_1646_, 6, v_type_1632_);
lean_closure_set(v___x_1646_, 7, v___x_1644_);
lean_closure_set(v___x_1646_, 8, v___x_1644_);
v___x_1647_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v___x_1642_, v___x_1646_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_);
return v___x_1647_;
}
else
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
lean_dec_ref(v_params_1629_);
v___x_1648_ = lean_unsigned_to_nat(0u);
v___x_1649_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_1650_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(v_ctorVal_1631_, v_useEq_1630_, v_args1_1633_, v_resultType_1634_, v___f_1641_, v___x_1648_, v_type_1632_, v___x_1649_, v___x_1649_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_);
return v___x_1650_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1___boxed(lean_object* v_name_1651_, lean_object* v_us_1652_, lean_object* v_params_1653_, lean_object* v_useEq_1654_, lean_object* v_ctorVal_1655_, lean_object* v_type_1656_, lean_object* v_args1_1657_, lean_object* v_resultType_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_){
_start:
{
uint8_t v_useEq_boxed_1664_; lean_object* v_res_1665_; 
v_useEq_boxed_1664_ = lean_unbox(v_useEq_1654_);
v_res_1665_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1(v_name_1651_, v_us_1652_, v_params_1653_, v_useEq_boxed_1664_, v_ctorVal_1655_, v_type_1656_, v_args1_1657_, v_resultType_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2(lean_object* v_name_1666_, lean_object* v_us_1667_, uint8_t v_useEq_1668_, lean_object* v_ctorVal_1669_, lean_object* v_params_1670_, lean_object* v_type_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_){
_start:
{
lean_object* v___x_1677_; lean_object* v___f_1678_; uint8_t v___x_1679_; lean_object* v___x_1680_; 
v___x_1677_ = lean_box(v_useEq_1668_);
lean_inc_ref(v_type_1671_);
v___f_1678_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1___boxed), 13, 6);
lean_closure_set(v___f_1678_, 0, v_name_1666_);
lean_closure_set(v___f_1678_, 1, v_us_1667_);
lean_closure_set(v___f_1678_, 2, v_params_1670_);
lean_closure_set(v___f_1678_, 3, v___x_1677_);
lean_closure_set(v___f_1678_, 4, v_ctorVal_1669_);
lean_closure_set(v___f_1678_, 5, v_type_1671_);
v___x_1679_ = 0;
v___x_1680_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_type_1671_, v___f_1678_, v___x_1679_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2___boxed(lean_object* v_name_1681_, lean_object* v_us_1682_, lean_object* v_useEq_1683_, lean_object* v_ctorVal_1684_, lean_object* v_params_1685_, lean_object* v_type_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_){
_start:
{
uint8_t v_useEq_boxed_1692_; lean_object* v_res_1693_; 
v_useEq_boxed_1692_ = lean_unbox(v_useEq_1683_);
v_res_1693_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2(v_name_1681_, v_us_1682_, v_useEq_boxed_1692_, v_ctorVal_1684_, v_params_1685_, v_type_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(lean_object* v_a_1694_, lean_object* v_a_1695_){
_start:
{
if (lean_obj_tag(v_a_1694_) == 0)
{
lean_object* v___x_1696_; 
v___x_1696_ = l_List_reverse___redArg(v_a_1695_);
return v___x_1696_;
}
else
{
lean_object* v_head_1697_; lean_object* v_tail_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1707_; 
v_head_1697_ = lean_ctor_get(v_a_1694_, 0);
v_tail_1698_ = lean_ctor_get(v_a_1694_, 1);
v_isSharedCheck_1707_ = !lean_is_exclusive(v_a_1694_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1700_ = v_a_1694_;
v_isShared_1701_ = v_isSharedCheck_1707_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_tail_1698_);
lean_inc(v_head_1697_);
lean_dec(v_a_1694_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1707_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1702_; lean_object* v___x_1704_; 
v___x_1702_ = l_Lean_mkLevelParam(v_head_1697_);
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 1, v_a_1695_);
lean_ctor_set(v___x_1700_, 0, v___x_1702_);
v___x_1704_ = v___x_1700_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v___x_1702_);
lean_ctor_set(v_reuseFailAlloc_1706_, 1, v_a_1695_);
v___x_1704_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
v_a_1694_ = v_tail_1698_;
v_a_1695_ = v___x_1704_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(lean_object* v_ctorVal_1708_, uint8_t v_useEq_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_){
_start:
{
lean_object* v_toConstantVal_1715_; lean_object* v_numParams_1716_; lean_object* v_name_1717_; lean_object* v_levelParams_1718_; lean_object* v_type_1719_; lean_object* v___x_1720_; lean_object* v_us_1721_; lean_object* v___x_1722_; lean_object* v___f_1723_; lean_object* v___x_1724_; 
v_toConstantVal_1715_ = lean_ctor_get(v_ctorVal_1708_, 0);
v_numParams_1716_ = lean_ctor_get(v_ctorVal_1708_, 3);
lean_inc(v_numParams_1716_);
v_name_1717_ = lean_ctor_get(v_toConstantVal_1715_, 0);
lean_inc(v_name_1717_);
v_levelParams_1718_ = lean_ctor_get(v_toConstantVal_1715_, 1);
v_type_1719_ = lean_ctor_get(v_toConstantVal_1715_, 2);
lean_inc_ref(v_type_1719_);
v___x_1720_ = lean_box(0);
lean_inc(v_levelParams_1718_);
v_us_1721_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(v_levelParams_1718_, v___x_1720_);
v___x_1722_ = lean_box(v_useEq_1709_);
v___f_1723_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2___boxed), 11, 4);
lean_closure_set(v___f_1723_, 0, v_name_1717_);
lean_closure_set(v___f_1723_, 1, v_us_1721_);
lean_closure_set(v___f_1723_, 2, v___x_1722_);
lean_closure_set(v___f_1723_, 3, v_ctorVal_1708_);
v___x_1724_ = l_Lean_Meta_elimOptParam(v_type_1719_, v_a_1712_, v_a_1713_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v_a_1725_; lean_object* v___x_1726_; uint8_t v___x_1727_; lean_object* v___x_1728_; 
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
lean_inc(v_a_1725_);
lean_dec_ref_known(v___x_1724_, 1);
v___x_1726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1726_, 0, v_numParams_1716_);
v___x_1727_ = 0;
v___x_1728_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(v_a_1725_, v___x_1726_, v___f_1723_, v___x_1727_, v___x_1727_, v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_);
return v___x_1728_;
}
else
{
lean_object* v_a_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1736_; 
lean_dec_ref(v___f_1723_);
lean_dec(v_numParams_1716_);
v_a_1729_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1736_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1731_ = v___x_1724_;
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_a_1729_);
lean_dec(v___x_1724_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1734_; 
if (v_isShared_1732_ == 0)
{
v___x_1734_ = v___x_1731_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_a_1729_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___boxed(lean_object* v_ctorVal_1737_, lean_object* v_useEq_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_){
_start:
{
uint8_t v_useEq_boxed_1744_; lean_object* v_res_1745_; 
v_useEq_boxed_1744_ = lean_unbox(v_useEq_1738_);
v_res_1745_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(v_ctorVal_1737_, v_useEq_boxed_1744_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_);
lean_dec(v_a_1742_);
lean_dec_ref(v_a_1741_);
lean_dec(v_a_1740_);
lean_dec_ref(v_a_1739_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2(lean_object* v_00_u03b1_1746_, lean_object* v_bs_1747_, lean_object* v_k_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_){
_start:
{
lean_object* v___x_1754_; 
v___x_1754_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(v_bs_1747_, v_k_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1755_, lean_object* v_bs_1756_, lean_object* v_k_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_){
_start:
{
lean_object* v_res_1763_; 
v_res_1763_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2(v_00_u03b1_1755_, v_bs_1756_, v_k_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_);
lean_dec(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec(v___y_1759_);
lean_dec_ref(v___y_1758_);
lean_dec_ref(v_bs_1756_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1(lean_object* v_00_u03b1_1764_, lean_object* v_bs_1765_, lean_object* v_k_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_){
_start:
{
lean_object* v___x_1772_; 
v___x_1772_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v_bs_1765_, v_k_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___boxed(lean_object* v_00_u03b1_1773_, lean_object* v_bs_1774_, lean_object* v_k_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1(v_00_u03b1_1773_, v_bs_1774_, v_k_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec(v___y_1777_);
lean_dec_ref(v___y_1776_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(lean_object* v_ctorVal_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_){
_start:
{
uint8_t v___x_1788_; lean_object* v___x_1789_; 
v___x_1788_ = 0;
v___x_1789_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(v_ctorVal_1782_, v___x_1788_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f___boxed(lean_object* v_ctorVal_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_1790_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_);
lean_dec(v_a_1794_);
lean_dec_ref(v_a_1793_);
lean_dec(v_a_1792_);
lean_dec_ref(v_a_1791_);
return v_res_1796_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1(void){
_start:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1798_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__0));
v___x_1799_ = l_Lean_stringToMessageData(v___x_1798_);
return v___x_1799_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3(void){
_start:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1801_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__2));
v___x_1802_ = l_Lean_stringToMessageData(v___x_1801_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(lean_object* v_ctorName_1803_){
_start:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1804_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1);
v___x_1805_ = l_Lean_MessageData_ofName(v_ctorName_1803_);
v___x_1806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1804_);
lean_ctor_set(v___x_1806_, 1, v___x_1805_);
v___x_1807_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3);
v___x_1808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1806_);
lean_ctor_set(v___x_1808_, 1, v___x_1807_);
return v___x_1808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(lean_object* v_ctorName_1809_, lean_object* v_mvarId_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_){
_start:
{
lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; 
v___x_1816_ = l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(v_ctorName_1809_);
v___x_1817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1817_, 0, v_mvarId_1810_);
v___x_1818_ = l_Lean_indentD(v___x_1817_);
v___x_1819_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1816_);
lean_ctor_set(v___x_1819_, 1, v___x_1818_);
v___x_1820_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_1819_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_);
return v___x_1820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg___boxed(lean_object* v_ctorName_1821_, lean_object* v_mvarId_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(v_ctorName_1821_, v_mvarId_1822_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_);
lean_dec(v_a_1826_);
lean_dec_ref(v_a_1825_);
lean_dec(v_a_1824_);
lean_dec_ref(v_a_1823_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure(lean_object* v_00_u03b1_1829_, lean_object* v_ctorName_1830_, lean_object* v_mvarId_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_){
_start:
{
lean_object* v___x_1837_; 
v___x_1837_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(v_ctorName_1830_, v_mvarId_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_);
return v___x_1837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___boxed(lean_object* v_00_u03b1_1838_, lean_object* v_ctorName_1839_, lean_object* v_mvarId_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_){
_start:
{
lean_object* v_res_1846_; 
v_res_1846_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure(v_00_u03b1_1838_, v_ctorName_1839_, v_mvarId_1840_, v_a_1841_, v_a_1842_, v_a_1843_, v_a_1844_);
lean_dec(v_a_1844_);
lean_dec_ref(v_a_1843_);
lean_dec(v_a_1842_);
lean_dec_ref(v_a_1841_);
return v_res_1846_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0(lean_object* v_ctorName_1847_, lean_object* v_as_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_){
_start:
{
if (lean_obj_tag(v_as_1848_) == 0)
{
lean_object* v___x_1854_; lean_object* v___x_1855_; 
lean_dec(v_ctorName_1847_);
v___x_1854_ = lean_box(0);
v___x_1855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1854_);
return v___x_1855_;
}
else
{
lean_object* v_head_1856_; lean_object* v_tail_1857_; lean_object* v___x_1858_; 
v_head_1856_ = lean_ctor_get(v_as_1848_, 0);
lean_inc_n(v_head_1856_, 2);
v_tail_1857_ = lean_ctor_get(v_as_1848_, 1);
lean_inc(v_tail_1857_);
lean_dec_ref_known(v_as_1848_, 2);
v___x_1858_ = l_Lean_MVarId_assumptionCore(v_head_1856_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_);
if (lean_obj_tag(v___x_1858_) == 0)
{
lean_object* v_a_1859_; uint8_t v___x_1860_; 
v_a_1859_ = lean_ctor_get(v___x_1858_, 0);
lean_inc(v_a_1859_);
lean_dec_ref_known(v___x_1858_, 1);
v___x_1860_ = lean_unbox(v_a_1859_);
lean_dec(v_a_1859_);
if (v___x_1860_ == 0)
{
lean_object* v___x_1861_; 
lean_dec(v_tail_1857_);
v___x_1861_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(v_ctorName_1847_, v_head_1856_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_);
return v___x_1861_;
}
else
{
lean_dec(v_head_1856_);
v_as_1848_ = v_tail_1857_;
goto _start;
}
}
else
{
lean_object* v_a_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1870_; 
lean_dec(v_tail_1857_);
lean_dec(v_head_1856_);
lean_dec(v_ctorName_1847_);
v_a_1863_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1870_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1865_ = v___x_1858_;
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_a_1863_);
lean_dec(v___x_1858_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1868_; 
if (v_isShared_1866_ == 0)
{
v___x_1868_ = v___x_1865_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_a_1863_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0___boxed(lean_object* v_ctorName_1871_, lean_object* v_as_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v_res_1878_; 
v_res_1878_ = l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0(v_ctorName_1871_, v_as_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(lean_object* v_mvarId_1879_, lean_object* v_ctorName_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_){
_start:
{
lean_object* v___x_1886_; 
v___x_1886_ = l_Lean_MVarId_splitAndCore(v_mvarId_1879_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v_a_1887_; lean_object* v___x_1888_; 
v_a_1887_ = lean_ctor_get(v___x_1886_, 0);
lean_inc(v_a_1887_);
lean_dec_ref_known(v___x_1886_, 1);
v___x_1888_ = l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0(v_ctorName_1880_, v_a_1887_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_);
return v___x_1888_;
}
else
{
lean_object* v_a_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1896_; 
lean_dec(v_ctorName_1880_);
v_a_1889_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1891_ = v___x_1886_;
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_a_1889_);
lean_dec(v___x_1886_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1894_; 
if (v_isShared_1892_ == 0)
{
v___x_1894_ = v___x_1891_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_a_1889_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
return v___x_1894_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption___boxed(lean_object* v_mvarId_1897_, lean_object* v_ctorName_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_){
_start:
{
lean_object* v_res_1904_; 
v_res_1904_ = l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(v_mvarId_1897_, v_ctorName_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_);
lean_dec(v_a_1902_);
lean_dec_ref(v_a_1901_);
lean_dec(v_a_1900_);
lean_dec_ref(v_a_1899_);
return v_res_1904_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0(lean_object* v_msg_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_){
_start:
{
lean_object* v___f_1912_; lean_object* v___x_922__overap_1913_; lean_object* v___x_1914_; 
v___f_1912_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0___closed__0));
v___x_922__overap_1913_ = lean_panic_fn_borrowed(v___f_1912_, v_msg_1906_);
lean_inc(v___y_1910_);
lean_inc_ref(v___y_1909_);
lean_inc(v___y_1908_);
lean_inc_ref(v___y_1907_);
v___x_1914_ = lean_apply_5(v___x_922__overap_1913_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, lean_box(0));
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0___boxed(lean_object* v_msg_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_){
_start:
{
lean_object* v_res_1921_; 
v_res_1921_ = l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0(v_msg_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_);
lean_dec(v___y_1919_);
lean_dec_ref(v___y_1918_);
lean_dec(v___y_1917_);
lean_dec_ref(v___y_1916_);
return v_res_1921_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1922_; double v___x_1923_; 
v___x_1922_ = lean_unsigned_to_nat(0u);
v___x_1923_ = lean_float_of_nat(v___x_1922_);
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(lean_object* v_cls_1927_, lean_object* v_msg_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_){
_start:
{
lean_object* v_ref_1934_; lean_object* v___x_1935_; lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1981_; 
v_ref_1934_ = lean_ctor_get(v___y_1931_, 2);
v___x_1935_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msg_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_);
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1938_ = v___x_1935_;
v_isShared_1939_ = v_isSharedCheck_1981_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_dec(v___x_1935_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1981_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1940_; lean_object* v_traceState_1941_; lean_object* v_env_1942_; lean_object* v_nextMacroScope_1943_; lean_object* v_ngen_1944_; lean_object* v_auxDeclNGen_1945_; lean_object* v_cache_1946_; lean_object* v_recordedDeps_1947_; lean_object* v_messages_1948_; lean_object* v_infoState_1949_; lean_object* v_snapshotTasks_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1980_; 
v___x_1940_ = lean_st_ref_take(v___y_1932_);
v_traceState_1941_ = lean_ctor_get(v___x_1940_, 4);
v_env_1942_ = lean_ctor_get(v___x_1940_, 0);
v_nextMacroScope_1943_ = lean_ctor_get(v___x_1940_, 1);
v_ngen_1944_ = lean_ctor_get(v___x_1940_, 2);
v_auxDeclNGen_1945_ = lean_ctor_get(v___x_1940_, 3);
v_cache_1946_ = lean_ctor_get(v___x_1940_, 5);
v_recordedDeps_1947_ = lean_ctor_get(v___x_1940_, 6);
v_messages_1948_ = lean_ctor_get(v___x_1940_, 7);
v_infoState_1949_ = lean_ctor_get(v___x_1940_, 8);
v_snapshotTasks_1950_ = lean_ctor_get(v___x_1940_, 9);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1940_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1952_ = v___x_1940_;
v_isShared_1953_ = v_isSharedCheck_1980_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_snapshotTasks_1950_);
lean_inc(v_infoState_1949_);
lean_inc(v_messages_1948_);
lean_inc(v_recordedDeps_1947_);
lean_inc(v_cache_1946_);
lean_inc(v_traceState_1941_);
lean_inc(v_auxDeclNGen_1945_);
lean_inc(v_ngen_1944_);
lean_inc(v_nextMacroScope_1943_);
lean_inc(v_env_1942_);
lean_dec(v___x_1940_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1980_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
uint64_t v_tid_1954_; lean_object* v_traces_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1979_; 
v_tid_1954_ = lean_ctor_get_uint64(v_traceState_1941_, sizeof(void*)*1);
v_traces_1955_ = lean_ctor_get(v_traceState_1941_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v_traceState_1941_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1957_ = v_traceState_1941_;
v_isShared_1958_ = v_isSharedCheck_1979_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_traces_1955_);
lean_dec(v_traceState_1941_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1979_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; double v___x_1961_; uint8_t v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1970_; 
v___x_1959_ = lean_box(0);
v___x_1960_ = lean_box(0);
v___x_1961_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0);
v___x_1962_ = 0;
v___x_1963_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_1964_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1964_, 0, v_cls_1927_);
lean_ctor_set(v___x_1964_, 1, v___x_1960_);
lean_ctor_set(v___x_1964_, 2, v___x_1963_);
lean_ctor_set_float(v___x_1964_, sizeof(void*)*3, v___x_1961_);
lean_ctor_set_float(v___x_1964_, sizeof(void*)*3 + 8, v___x_1961_);
lean_ctor_set_uint8(v___x_1964_, sizeof(void*)*3 + 16, v___x_1962_);
v___x_1965_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__2));
v___x_1966_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1966_, 0, v___x_1964_);
lean_ctor_set(v___x_1966_, 1, v_a_1936_);
lean_ctor_set(v___x_1966_, 2, v___x_1965_);
lean_inc(v_ref_1934_);
v___x_1967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1967_, 0, v_ref_1934_);
lean_ctor_set(v___x_1967_, 1, v___x_1966_);
v___x_1968_ = l_Lean_PersistentArray_push___redArg(v_traces_1955_, v___x_1967_);
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 0, v___x_1968_);
v___x_1970_ = v___x_1957_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v___x_1968_);
lean_ctor_set_uint64(v_reuseFailAlloc_1978_, sizeof(void*)*1, v_tid_1954_);
v___x_1970_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
lean_object* v___x_1972_; 
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 4, v___x_1970_);
v___x_1972_ = v___x_1952_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_env_1942_);
lean_ctor_set(v_reuseFailAlloc_1977_, 1, v_nextMacroScope_1943_);
lean_ctor_set(v_reuseFailAlloc_1977_, 2, v_ngen_1944_);
lean_ctor_set(v_reuseFailAlloc_1977_, 3, v_auxDeclNGen_1945_);
lean_ctor_set(v_reuseFailAlloc_1977_, 4, v___x_1970_);
lean_ctor_set(v_reuseFailAlloc_1977_, 5, v_cache_1946_);
lean_ctor_set(v_reuseFailAlloc_1977_, 6, v_recordedDeps_1947_);
lean_ctor_set(v_reuseFailAlloc_1977_, 7, v_messages_1948_);
lean_ctor_set(v_reuseFailAlloc_1977_, 8, v_infoState_1949_);
lean_ctor_set(v_reuseFailAlloc_1977_, 9, v_snapshotTasks_1950_);
v___x_1972_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
lean_object* v___x_1973_; lean_object* v___x_1975_; 
v___x_1973_ = lean_st_ref_put(v___y_1932_, v___x_1972_);
if (v_isShared_1939_ == 0)
{
lean_ctor_set(v___x_1938_, 0, v___x_1959_);
v___x_1975_ = v___x_1938_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v___x_1959_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
return v___x_1975_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___boxed(lean_object* v_cls_1982_, lean_object* v_msg_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_){
_start:
{
lean_object* v_res_1989_; 
v_res_1989_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_1982_, v_msg_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_);
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1984_);
return v_res_1989_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3(void){
_start:
{
lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1993_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__2));
v___x_1994_ = lean_unsigned_to_nat(30u);
v___x_1995_ = lean_unsigned_to_nat(96u);
v___x_1996_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__1));
v___x_1997_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__0));
v___x_1998_ = l_mkPanicMessageWithDecl(v___x_1997_, v___x_1996_, v___x_1995_, v___x_1994_, v___x_1993_);
return v___x_1998_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9(void){
_start:
{
lean_object* v_cls_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; 
v_cls_2007_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_2008_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__8));
v___x_2009_ = l_Lean_Name_append(v___x_2008_, v_cls_2007_);
return v___x_2009_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11(void){
_start:
{
lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2011_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__10));
v___x_2012_ = l_Lean_stringToMessageData(v___x_2011_);
return v___x_2012_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13(void){
_start:
{
lean_object* v___x_2014_; lean_object* v___x_2015_; 
v___x_2014_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__12));
v___x_2015_ = l_Lean_stringToMessageData(v___x_2014_);
return v___x_2015_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15(void){
_start:
{
lean_object* v___x_2017_; lean_object* v___x_2018_; 
v___x_2017_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__14));
v___x_2018_ = l_Lean_stringToMessageData(v___x_2017_);
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(lean_object* v_ctorName_2019_, lean_object* v_mvarId_2020_, lean_object* v_h_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_){
_start:
{
lean_object* v___y_2028_; lean_object* v___y_2029_; lean_object* v___y_2030_; lean_object* v___y_2031_; lean_object* v_toCold_2047_; lean_object* v_options_2048_; uint8_t v_hasTrace_2049_; 
v_toCold_2047_ = lean_ctor_get(v_a_2024_, 0);
v_options_2048_ = lean_ctor_get(v_toCold_2047_, 2);
v_hasTrace_2049_ = lean_ctor_get_uint8(v_options_2048_, sizeof(void*)*1);
if (v_hasTrace_2049_ == 0)
{
v___y_2028_ = v_a_2022_;
v___y_2029_ = v_a_2023_;
v___y_2030_ = v_a_2024_;
v___y_2031_ = v_a_2025_;
goto v___jp_2027_;
}
else
{
lean_object* v_inheritedTraceOptions_2050_; lean_object* v_cls_2051_; lean_object* v___x_2052_; uint8_t v___x_2053_; 
v_inheritedTraceOptions_2050_ = lean_ctor_get(v_toCold_2047_, 11);
v_cls_2051_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_2052_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_2053_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2050_, v_options_2048_, v___x_2052_);
if (v___x_2053_ == 0)
{
v___y_2028_ = v_a_2022_;
v___y_2029_ = v_a_2023_;
v___y_2030_ = v_a_2024_;
v___y_2031_ = v_a_2025_;
goto v___jp_2027_;
}
else
{
lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2054_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11);
lean_inc(v_ctorName_2019_);
v___x_2055_ = l_Lean_MessageData_ofName(v_ctorName_2019_);
v___x_2056_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2054_);
lean_ctor_set(v___x_2056_, 1, v___x_2055_);
v___x_2057_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13);
v___x_2058_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2058_, 0, v___x_2056_);
lean_ctor_set(v___x_2058_, 1, v___x_2057_);
lean_inc(v_h_2021_);
v___x_2059_ = l_Lean_mkFVar(v_h_2021_);
v___x_2060_ = l_Lean_MessageData_ofExpr(v___x_2059_);
v___x_2061_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2061_, 0, v___x_2058_);
lean_ctor_set(v___x_2061_, 1, v___x_2060_);
v___x_2062_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15);
v___x_2063_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2063_, 0, v___x_2061_);
lean_ctor_set(v___x_2063_, 1, v___x_2062_);
lean_inc(v_mvarId_2020_);
v___x_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2064_, 0, v_mvarId_2020_);
v___x_2065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2063_);
lean_ctor_set(v___x_2065_, 1, v___x_2064_);
v___x_2066_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2051_, v___x_2065_, v_a_2022_, v_a_2023_, v_a_2024_, v_a_2025_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_dec_ref_known(v___x_2066_, 1);
v___y_2028_ = v_a_2022_;
v___y_2029_ = v_a_2023_;
v___y_2030_ = v_a_2024_;
v___y_2031_ = v_a_2025_;
goto v___jp_2027_;
}
else
{
lean_dec(v_h_2021_);
lean_dec(v_mvarId_2020_);
lean_dec(v_ctorName_2019_);
return v___x_2066_;
}
}
}
v___jp_2027_:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2032_ = lean_box(0);
v___x_2033_ = l_Lean_Meta_injection(v_mvarId_2020_, v_h_2021_, v___x_2032_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_);
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_object* v_a_2034_; 
v_a_2034_ = lean_ctor_get(v___x_2033_, 0);
lean_inc(v_a_2034_);
lean_dec_ref_known(v___x_2033_, 1);
if (lean_obj_tag(v_a_2034_) == 0)
{
lean_object* v___x_2035_; lean_object* v___x_2036_; 
lean_dec(v_ctorName_2019_);
v___x_2035_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3);
v___x_2036_ = l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0(v___x_2035_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_);
return v___x_2036_;
}
else
{
lean_object* v_mvarId_2037_; lean_object* v___x_2038_; 
v_mvarId_2037_ = lean_ctor_get(v_a_2034_, 0);
lean_inc(v_mvarId_2037_);
lean_dec_ref_known(v_a_2034_, 3);
v___x_2038_ = l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(v_mvarId_2037_, v_ctorName_2019_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_);
return v___x_2038_;
}
}
else
{
lean_object* v_a_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2046_; 
lean_dec(v_ctorName_2019_);
v_a_2039_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2041_ = v___x_2033_;
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_a_2039_);
lean_dec(v___x_2033_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___boxed(lean_object* v_ctorName_2067_, lean_object* v_mvarId_2068_, lean_object* v_h_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_){
_start:
{
lean_object* v_res_2075_; 
v_res_2075_ = l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(v_ctorName_2067_, v_mvarId_2068_, v_h_2069_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_);
lean_dec(v_a_2073_);
lean_dec_ref(v_a_2072_);
lean_dec(v_a_2071_);
lean_dec_ref(v_a_2070_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(lean_object* v_type_2076_, lean_object* v_k_2077_, uint8_t v_cleanupAnnotations_2078_, uint8_t v_whnfType_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_){
_start:
{
lean_object* v___f_2085_; lean_object* v___x_2086_; 
v___f_2085_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2085_, 0, v_k_2077_);
v___x_2086_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_2076_, v___f_2085_, v_cleanupAnnotations_2078_, v_whnfType_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_);
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2094_; 
v_a_2087_ = lean_ctor_get(v___x_2086_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2089_ = v___x_2086_;
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_dec(v___x_2086_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2092_; 
if (v_isShared_2090_ == 0)
{
v___x_2092_ = v___x_2089_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_a_2087_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
else
{
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2102_; 
v_a_2095_ = lean_ctor_get(v___x_2086_, 0);
v_isSharedCheck_2102_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2097_ = v___x_2086_;
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v___x_2086_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2100_; 
if (v_isShared_2098_ == 0)
{
v___x_2100_ = v___x_2097_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_a_2095_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg___boxed(lean_object* v_type_2103_, lean_object* v_k_2104_, lean_object* v_cleanupAnnotations_2105_, lean_object* v_whnfType_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2112_; uint8_t v_whnfType_boxed_2113_; lean_object* v_res_2114_; 
v_cleanupAnnotations_boxed_2112_ = lean_unbox(v_cleanupAnnotations_2105_);
v_whnfType_boxed_2113_ = lean_unbox(v_whnfType_2106_);
v_res_2114_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_type_2103_, v_k_2104_, v_cleanupAnnotations_boxed_2112_, v_whnfType_boxed_2113_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
lean_dec(v___y_2110_);
lean_dec_ref(v___y_2109_);
lean_dec(v___y_2108_);
lean_dec_ref(v___y_2107_);
return v_res_2114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0(lean_object* v_00_u03b1_2115_, lean_object* v_type_2116_, lean_object* v_k_2117_, uint8_t v_cleanupAnnotations_2118_, uint8_t v_whnfType_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_){
_start:
{
lean_object* v___x_2125_; 
v___x_2125_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_type_2116_, v_k_2117_, v_cleanupAnnotations_2118_, v_whnfType_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
return v___x_2125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___boxed(lean_object* v_00_u03b1_2126_, lean_object* v_type_2127_, lean_object* v_k_2128_, lean_object* v_cleanupAnnotations_2129_, lean_object* v_whnfType_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2136_; uint8_t v_whnfType_boxed_2137_; lean_object* v_res_2138_; 
v_cleanupAnnotations_boxed_2136_ = lean_unbox(v_cleanupAnnotations_2129_);
v_whnfType_boxed_2137_ = lean_unbox(v_whnfType_2130_);
v_res_2138_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0(v_00_u03b1_2126_, v_type_2127_, v_k_2128_, v_cleanupAnnotations_boxed_2136_, v_whnfType_boxed_2137_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
return v_res_2138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0(lean_object* v___x_2139_, lean_object* v_ctorName_2140_, lean_object* v_xs_2141_, lean_object* v_type_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_){
_start:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; 
v___x_2148_ = lean_box(0);
v___x_2149_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_2142_, v___x_2148_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_object* v_a_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
v_a_2150_ = lean_ctor_get(v___x_2149_, 0);
lean_inc(v_a_2150_);
lean_dec_ref_known(v___x_2149_, 1);
v___x_2151_ = l_Lean_Expr_mvarId_x21(v_a_2150_);
v___x_2152_ = lean_array_get_size(v_xs_2141_);
v___x_2153_ = lean_unsigned_to_nat(1u);
v___x_2154_ = lean_nat_sub(v___x_2152_, v___x_2153_);
v___x_2155_ = lean_array_get_borrowed(v___x_2139_, v_xs_2141_, v___x_2154_);
lean_dec(v___x_2154_);
v___x_2156_ = l_Lean_Expr_fvarId_x21(v___x_2155_);
v___x_2157_ = l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(v_ctorName_2140_, v___x_2151_, v___x_2156_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_);
if (lean_obj_tag(v___x_2157_) == 0)
{
uint8_t v___x_2158_; uint8_t v___x_2159_; uint8_t v___x_2160_; lean_object* v___x_2161_; 
lean_dec_ref_known(v___x_2157_, 1);
v___x_2158_ = 0;
v___x_2159_ = 1;
v___x_2160_ = 1;
v___x_2161_ = l_Lean_Meta_mkLambdaFVars(v_xs_2141_, v_a_2150_, v___x_2158_, v___x_2159_, v___x_2158_, v___x_2159_, v___x_2160_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_);
return v___x_2161_;
}
else
{
lean_object* v_a_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2169_; 
lean_dec(v_a_2150_);
v_a_2162_ = lean_ctor_get(v___x_2157_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2157_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2164_ = v___x_2157_;
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_a_2162_);
lean_dec(v___x_2157_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2167_; 
if (v_isShared_2165_ == 0)
{
v___x_2167_ = v___x_2164_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_a_2162_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
}
}
else
{
lean_dec(v_ctorName_2140_);
return v___x_2149_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0___boxed(lean_object* v___x_2170_, lean_object* v_ctorName_2171_, lean_object* v_xs_2172_, lean_object* v_type_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_){
_start:
{
lean_object* v_res_2179_; 
v_res_2179_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0(v___x_2170_, v_ctorName_2171_, v_xs_2172_, v_type_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_);
lean_dec(v___y_2177_);
lean_dec_ref(v___y_2176_);
lean_dec(v___y_2175_);
lean_dec_ref(v___y_2174_);
lean_dec_ref(v_xs_2172_);
lean_dec_ref(v___x_2170_);
return v_res_2179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(lean_object* v_ctorName_2180_, lean_object* v_targetType_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_){
_start:
{
lean_object* v___x_2187_; lean_object* v___f_2188_; uint8_t v___x_2189_; lean_object* v___x_2190_; 
v___x_2187_ = l_Lean_instInhabitedExpr;
v___f_2188_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2188_, 0, v___x_2187_);
lean_closure_set(v___f_2188_, 1, v_ctorName_2180_);
v___x_2189_ = 0;
v___x_2190_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_targetType_2181_, v___f_2188_, v___x_2189_, v___x_2189_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_);
return v___x_2190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___boxed(lean_object* v_ctorName_2191_, lean_object* v_targetType_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_){
_start:
{
lean_object* v_res_2198_; 
v_res_2198_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_ctorName_2191_, v_targetType_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_);
lean_dec(v_a_2196_);
lean_dec_ref(v_a_2195_);
lean_dec(v_a_2194_);
lean_dec_ref(v_a_2193_);
return v_res_2198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheoremNameFor(lean_object* v_ctorName_2202_){
_start:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2203_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheoremNameFor___closed__1));
v___x_2204_ = l_Lean_Name_append(v_ctorName_2202_, v___x_2203_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(lean_object* v_e_2205_, lean_object* v___y_2206_){
_start:
{
uint8_t v___x_2208_; 
v___x_2208_ = l_Lean_Expr_hasMVar(v_e_2205_);
if (v___x_2208_ == 0)
{
lean_object* v___x_2209_; 
v___x_2209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2209_, 0, v_e_2205_);
return v___x_2209_;
}
else
{
lean_object* v___x_2210_; lean_object* v_mctx_2211_; lean_object* v___x_2212_; lean_object* v_fst_2213_; lean_object* v_snd_2214_; lean_object* v___x_2215_; lean_object* v_cache_2216_; lean_object* v_zetaDeltaFVarIds_2217_; lean_object* v_postponed_2218_; lean_object* v_diag_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2228_; 
v___x_2210_ = lean_st_ref_get(v___y_2206_);
v_mctx_2211_ = lean_ctor_get(v___x_2210_, 0);
lean_inc_ref(v_mctx_2211_);
lean_dec(v___x_2210_);
v___x_2212_ = l_Lean_instantiateMVarsCore(v_mctx_2211_, v_e_2205_);
v_fst_2213_ = lean_ctor_get(v___x_2212_, 0);
lean_inc(v_fst_2213_);
v_snd_2214_ = lean_ctor_get(v___x_2212_, 1);
lean_inc(v_snd_2214_);
lean_dec_ref(v___x_2212_);
v___x_2215_ = lean_st_ref_take(v___y_2206_);
v_cache_2216_ = lean_ctor_get(v___x_2215_, 1);
v_zetaDeltaFVarIds_2217_ = lean_ctor_get(v___x_2215_, 2);
v_postponed_2218_ = lean_ctor_get(v___x_2215_, 3);
v_diag_2219_ = lean_ctor_get(v___x_2215_, 4);
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2215_);
if (v_isSharedCheck_2228_ == 0)
{
lean_object* v_unused_2229_; 
v_unused_2229_ = lean_ctor_get(v___x_2215_, 0);
lean_dec(v_unused_2229_);
v___x_2221_ = v___x_2215_;
v_isShared_2222_ = v_isSharedCheck_2228_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_diag_2219_);
lean_inc(v_postponed_2218_);
lean_inc(v_zetaDeltaFVarIds_2217_);
lean_inc(v_cache_2216_);
lean_dec(v___x_2215_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2228_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v___x_2224_; 
if (v_isShared_2222_ == 0)
{
lean_ctor_set(v___x_2221_, 0, v_snd_2214_);
v___x_2224_ = v___x_2221_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_snd_2214_);
lean_ctor_set(v_reuseFailAlloc_2227_, 1, v_cache_2216_);
lean_ctor_set(v_reuseFailAlloc_2227_, 2, v_zetaDeltaFVarIds_2217_);
lean_ctor_set(v_reuseFailAlloc_2227_, 3, v_postponed_2218_);
lean_ctor_set(v_reuseFailAlloc_2227_, 4, v_diag_2219_);
v___x_2224_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2225_ = lean_st_ref_put(v___y_2206_, v___x_2224_);
v___x_2226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2226_, 0, v_fst_2213_);
return v___x_2226_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg___boxed(lean_object* v_e_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
lean_object* v_res_2233_; 
v_res_2233_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_e_2230_, v___y_2231_);
lean_dec(v___y_2231_);
return v_res_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0(lean_object* v_e_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_){
_start:
{
lean_object* v___x_2240_; 
v___x_2240_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_e_2234_, v___y_2236_);
return v___x_2240_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___boxed(lean_object* v_e_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0(v_e_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
return v_res_2247_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2248_ = lean_unsigned_to_nat(32u);
v___x_2249_ = lean_mk_empty_array_with_capacity(v___x_2248_);
v___x_2250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2249_);
return v___x_2250_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2251_ = ((size_t)5ULL);
v___x_2252_ = lean_unsigned_to_nat(0u);
v___x_2253_ = lean_unsigned_to_nat(32u);
v___x_2254_ = lean_mk_empty_array_with_capacity(v___x_2253_);
v___x_2255_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0);
v___x_2256_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2256_, 0, v___x_2255_);
lean_ctor_set(v___x_2256_, 1, v___x_2254_);
lean_ctor_set(v___x_2256_, 2, v___x_2252_);
lean_ctor_set(v___x_2256_, 3, v___x_2252_);
lean_ctor_set_usize(v___x_2256_, 4, v___x_2251_);
return v___x_2256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(lean_object* v___y_2257_){
_start:
{
lean_object* v___x_2259_; lean_object* v_traceState_2260_; lean_object* v_traces_2261_; lean_object* v___x_2262_; lean_object* v_traceState_2263_; lean_object* v_env_2264_; lean_object* v_nextMacroScope_2265_; lean_object* v_ngen_2266_; lean_object* v_auxDeclNGen_2267_; lean_object* v_cache_2268_; lean_object* v_recordedDeps_2269_; lean_object* v_messages_2270_; lean_object* v_infoState_2271_; lean_object* v_snapshotTasks_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2291_; 
v___x_2259_ = lean_st_ref_get(v___y_2257_);
v_traceState_2260_ = lean_ctor_get(v___x_2259_, 4);
lean_inc_ref(v_traceState_2260_);
lean_dec(v___x_2259_);
v_traces_2261_ = lean_ctor_get(v_traceState_2260_, 0);
lean_inc_ref(v_traces_2261_);
lean_dec_ref(v_traceState_2260_);
v___x_2262_ = lean_st_ref_take(v___y_2257_);
v_traceState_2263_ = lean_ctor_get(v___x_2262_, 4);
v_env_2264_ = lean_ctor_get(v___x_2262_, 0);
v_nextMacroScope_2265_ = lean_ctor_get(v___x_2262_, 1);
v_ngen_2266_ = lean_ctor_get(v___x_2262_, 2);
v_auxDeclNGen_2267_ = lean_ctor_get(v___x_2262_, 3);
v_cache_2268_ = lean_ctor_get(v___x_2262_, 5);
v_recordedDeps_2269_ = lean_ctor_get(v___x_2262_, 6);
v_messages_2270_ = lean_ctor_get(v___x_2262_, 7);
v_infoState_2271_ = lean_ctor_get(v___x_2262_, 8);
v_snapshotTasks_2272_ = lean_ctor_get(v___x_2262_, 9);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2262_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2274_ = v___x_2262_;
v_isShared_2275_ = v_isSharedCheck_2291_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_snapshotTasks_2272_);
lean_inc(v_infoState_2271_);
lean_inc(v_messages_2270_);
lean_inc(v_recordedDeps_2269_);
lean_inc(v_cache_2268_);
lean_inc(v_traceState_2263_);
lean_inc(v_auxDeclNGen_2267_);
lean_inc(v_ngen_2266_);
lean_inc(v_nextMacroScope_2265_);
lean_inc(v_env_2264_);
lean_dec(v___x_2262_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2291_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
uint64_t v_tid_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2289_; 
v_tid_2276_ = lean_ctor_get_uint64(v_traceState_2263_, sizeof(void*)*1);
v_isSharedCheck_2289_ = !lean_is_exclusive(v_traceState_2263_);
if (v_isSharedCheck_2289_ == 0)
{
lean_object* v_unused_2290_; 
v_unused_2290_ = lean_ctor_get(v_traceState_2263_, 0);
lean_dec(v_unused_2290_);
v___x_2278_ = v_traceState_2263_;
v_isShared_2279_ = v_isSharedCheck_2289_;
goto v_resetjp_2277_;
}
else
{
lean_dec(v_traceState_2263_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2289_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2280_; lean_object* v___x_2282_; 
v___x_2280_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1);
if (v_isShared_2279_ == 0)
{
lean_ctor_set(v___x_2278_, 0, v___x_2280_);
v___x_2282_ = v___x_2278_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v___x_2280_);
lean_ctor_set_uint64(v_reuseFailAlloc_2288_, sizeof(void*)*1, v_tid_2276_);
v___x_2282_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
lean_object* v___x_2284_; 
if (v_isShared_2275_ == 0)
{
lean_ctor_set(v___x_2274_, 4, v___x_2282_);
v___x_2284_ = v___x_2274_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_env_2264_);
lean_ctor_set(v_reuseFailAlloc_2287_, 1, v_nextMacroScope_2265_);
lean_ctor_set(v_reuseFailAlloc_2287_, 2, v_ngen_2266_);
lean_ctor_set(v_reuseFailAlloc_2287_, 3, v_auxDeclNGen_2267_);
lean_ctor_set(v_reuseFailAlloc_2287_, 4, v___x_2282_);
lean_ctor_set(v_reuseFailAlloc_2287_, 5, v_cache_2268_);
lean_ctor_set(v_reuseFailAlloc_2287_, 6, v_recordedDeps_2269_);
lean_ctor_set(v_reuseFailAlloc_2287_, 7, v_messages_2270_);
lean_ctor_set(v_reuseFailAlloc_2287_, 8, v_infoState_2271_);
lean_ctor_set(v_reuseFailAlloc_2287_, 9, v_snapshotTasks_2272_);
v___x_2284_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2285_ = lean_st_ref_put(v___y_2257_, v___x_2284_);
v___x_2286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2286_, 0, v_traces_2261_);
return v___x_2286_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___boxed(lean_object* v___y_2292_, lean_object* v___y_2293_){
_start:
{
lean_object* v_res_2294_; 
v_res_2294_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v___y_2292_);
lean_dec(v___y_2292_);
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1(lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_){
_start:
{
lean_object* v___x_2300_; 
v___x_2300_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v___y_2298_);
return v___x_2300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___boxed(lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_){
_start:
{
lean_object* v_res_2306_; 
v_res_2306_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1(v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_);
lean_dec(v___y_2304_);
lean_dec_ref(v___y_2303_);
lean_dec(v___y_2302_);
lean_dec_ref(v___y_2301_);
return v_res_2306_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(lean_object* v_opts_2307_, lean_object* v_opt_2308_){
_start:
{
lean_object* v_name_2309_; lean_object* v_defValue_2310_; lean_object* v_map_2311_; lean_object* v___x_2312_; 
v_name_2309_ = lean_ctor_get(v_opt_2308_, 0);
v_defValue_2310_ = lean_ctor_get(v_opt_2308_, 1);
v_map_2311_ = lean_ctor_get(v_opts_2307_, 0);
v___x_2312_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2311_, v_name_2309_);
if (lean_obj_tag(v___x_2312_) == 0)
{
uint8_t v___x_2313_; 
v___x_2313_ = lean_unbox(v_defValue_2310_);
return v___x_2313_;
}
else
{
lean_object* v_val_2314_; 
v_val_2314_ = lean_ctor_get(v___x_2312_, 0);
lean_inc(v_val_2314_);
lean_dec_ref_known(v___x_2312_, 1);
if (lean_obj_tag(v_val_2314_) == 1)
{
uint8_t v_v_2315_; 
v_v_2315_ = lean_ctor_get_uint8(v_val_2314_, 0);
lean_dec_ref_known(v_val_2314_, 0);
return v_v_2315_;
}
else
{
uint8_t v___x_2316_; 
lean_dec(v_val_2314_);
v___x_2316_ = lean_unbox(v_defValue_2310_);
return v___x_2316_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2___boxed(lean_object* v_opts_2317_, lean_object* v_opt_2318_){
_start:
{
uint8_t v_res_2319_; lean_object* v_r_2320_; 
v_res_2319_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_opts_2317_, v_opt_2318_);
lean_dec_ref(v_opt_2318_);
lean_dec_ref(v_opts_2317_);
v_r_2320_ = lean_box(v_res_2319_);
return v_r_2320_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___x_2322_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__0));
v___x_2323_ = l_Lean_stringToMessageData(v___x_2322_);
return v___x_2323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0(lean_object* v_name_2324_, lean_object* v_x_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_){
_start:
{
lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2331_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1);
v___x_2332_ = l_Lean_MessageData_ofName(v_name_2324_);
v___x_2333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2333_, 0, v___x_2331_);
lean_ctor_set(v___x_2333_, 1, v___x_2332_);
v___x_2334_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_2335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2333_);
lean_ctor_set(v___x_2335_, 1, v___x_2334_);
v___x_2336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2335_);
return v___x_2336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed(lean_object* v_name_2337_, lean_object* v_x_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_){
_start:
{
lean_object* v_res_2344_; 
v_res_2344_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0(v_name_2337_, v_x_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_);
lean_dec(v___y_2342_);
lean_dec_ref(v___y_2341_);
lean_dec(v___y_2340_);
lean_dec_ref(v___y_2339_);
lean_dec_ref(v_x_2338_);
return v_res_2344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(lean_object* v_name_2345_, lean_object* v_val_2346_, lean_object* v_name_2347_, lean_object* v_levelParams_2348_, uint8_t v___x_2349_, lean_object* v_____r_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_){
_start:
{
lean_object* v___x_2356_; 
lean_inc_ref(v_val_2346_);
v___x_2356_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2345_, v_val_2346_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_);
if (lean_obj_tag(v___x_2356_) == 0)
{
lean_object* v_a_2357_; lean_object* v___x_2358_; lean_object* v_a_2359_; lean_object* v___x_2360_; lean_object* v_a_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2373_; 
v_a_2357_ = lean_ctor_get(v___x_2356_, 0);
lean_inc(v_a_2357_);
lean_dec_ref_known(v___x_2356_, 1);
v___x_2358_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2346_, v___y_2352_);
v_a_2359_ = lean_ctor_get(v___x_2358_, 0);
lean_inc(v_a_2359_);
lean_dec_ref(v___x_2358_);
v___x_2360_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2357_, v___y_2352_);
v_a_2361_ = lean_ctor_get(v___x_2360_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2363_ = v___x_2360_;
v_isShared_2364_ = v_isSharedCheck_2373_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_a_2361_);
lean_dec(v___x_2360_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2373_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2370_; 
lean_inc(v_name_2347_);
v___x_2365_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2365_, 0, v_name_2347_);
lean_ctor_set(v___x_2365_, 1, v_levelParams_2348_);
lean_ctor_set(v___x_2365_, 2, v_a_2359_);
v___x_2366_ = lean_box(0);
v___x_2367_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2367_, 0, v_name_2347_);
lean_ctor_set(v___x_2367_, 1, v___x_2366_);
v___x_2368_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2365_);
lean_ctor_set(v___x_2368_, 1, v_a_2361_);
lean_ctor_set(v___x_2368_, 2, v___x_2367_);
if (v_isShared_2364_ == 0)
{
lean_ctor_set_tag(v___x_2363_, 2);
lean_ctor_set(v___x_2363_, 0, v___x_2368_);
v___x_2370_ = v___x_2363_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v___x_2368_);
v___x_2370_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
lean_object* v___x_2371_; 
v___x_2371_ = l_Lean_addDecl(v___x_2370_, v___x_2349_, v___y_2353_, v___y_2354_);
return v___x_2371_;
}
}
}
else
{
lean_object* v_a_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2381_; 
lean_dec(v_levelParams_2348_);
lean_dec(v_name_2347_);
lean_dec_ref(v_val_2346_);
v_a_2374_ = lean_ctor_get(v___x_2356_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2376_ = v___x_2356_;
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_a_2374_);
lean_dec(v___x_2356_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v___x_2379_; 
if (v_isShared_2377_ == 0)
{
v___x_2379_ = v___x_2376_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v_a_2374_);
v___x_2379_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
return v___x_2379_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1___boxed(lean_object* v_name_2382_, lean_object* v_val_2383_, lean_object* v_name_2384_, lean_object* v_levelParams_2385_, lean_object* v___x_2386_, lean_object* v_____r_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_){
_start:
{
uint8_t v___x_12492__boxed_2393_; lean_object* v_res_2394_; 
v___x_12492__boxed_2393_ = lean_unbox(v___x_2386_);
v_res_2394_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(v_name_2382_, v_val_2383_, v_name_2384_, v_levelParams_2385_, v___x_12492__boxed_2393_, v_____r_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_);
lean_dec(v___y_2391_);
lean_dec_ref(v___y_2390_);
lean_dec(v___y_2389_);
lean_dec_ref(v___y_2388_);
return v_res_2394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(lean_object* v_name_2395_, lean_object* v_val_2396_, lean_object* v_name_2397_, lean_object* v_levelParams_2398_, lean_object* v_____r_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_){
_start:
{
lean_object* v___x_2405_; 
lean_inc_ref(v_val_2396_);
v___x_2405_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2395_, v_val_2396_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
if (lean_obj_tag(v___x_2405_) == 0)
{
lean_object* v_a_2406_; lean_object* v___x_2407_; lean_object* v_a_2408_; lean_object* v___x_2409_; lean_object* v_a_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2423_; 
v_a_2406_ = lean_ctor_get(v___x_2405_, 0);
lean_inc(v_a_2406_);
lean_dec_ref_known(v___x_2405_, 1);
v___x_2407_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2396_, v___y_2401_);
v_a_2408_ = lean_ctor_get(v___x_2407_, 0);
lean_inc(v_a_2408_);
lean_dec_ref(v___x_2407_);
v___x_2409_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2406_, v___y_2401_);
v_a_2410_ = lean_ctor_get(v___x_2409_, 0);
v_isSharedCheck_2423_ = !lean_is_exclusive(v___x_2409_);
if (v_isSharedCheck_2423_ == 0)
{
v___x_2412_ = v___x_2409_;
v_isShared_2413_ = v_isSharedCheck_2423_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_a_2410_);
lean_dec(v___x_2409_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2423_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2419_; 
lean_inc(v_name_2397_);
v___x_2414_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2414_, 0, v_name_2397_);
lean_ctor_set(v___x_2414_, 1, v_levelParams_2398_);
lean_ctor_set(v___x_2414_, 2, v_a_2408_);
v___x_2415_ = lean_box(0);
v___x_2416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2416_, 0, v_name_2397_);
lean_ctor_set(v___x_2416_, 1, v___x_2415_);
v___x_2417_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2417_, 0, v___x_2414_);
lean_ctor_set(v___x_2417_, 1, v_a_2410_);
lean_ctor_set(v___x_2417_, 2, v___x_2416_);
if (v_isShared_2413_ == 0)
{
lean_ctor_set_tag(v___x_2412_, 2);
lean_ctor_set(v___x_2412_, 0, v___x_2417_);
v___x_2419_ = v___x_2412_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v___x_2417_);
v___x_2419_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
uint8_t v___x_2420_; lean_object* v___x_2421_; 
v___x_2420_ = 0;
v___x_2421_ = l_Lean_addDecl(v___x_2419_, v___x_2420_, v___y_2402_, v___y_2403_);
return v___x_2421_;
}
}
}
else
{
lean_object* v_a_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2431_; 
lean_dec(v_levelParams_2398_);
lean_dec(v_name_2397_);
lean_dec_ref(v_val_2396_);
v_a_2424_ = lean_ctor_get(v___x_2405_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2426_ = v___x_2405_;
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_a_2424_);
lean_dec(v___x_2405_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v___x_2429_; 
if (v_isShared_2427_ == 0)
{
v___x_2429_ = v___x_2426_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_a_2424_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2___boxed(lean_object* v_name_2432_, lean_object* v_val_2433_, lean_object* v_name_2434_, lean_object* v_levelParams_2435_, lean_object* v_____r_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_){
_start:
{
lean_object* v_res_2442_; 
v_res_2442_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(v_name_2432_, v_val_2433_, v_name_2434_, v_levelParams_2435_, v_____r_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
return v_res_2442_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3_spec__4(size_t v_sz_2443_, size_t v_i_2444_, lean_object* v_bs_2445_){
_start:
{
uint8_t v___x_2446_; 
v___x_2446_ = lean_usize_dec_lt(v_i_2444_, v_sz_2443_);
if (v___x_2446_ == 0)
{
return v_bs_2445_;
}
else
{
lean_object* v_v_2447_; lean_object* v_msg_2448_; lean_object* v___x_2449_; lean_object* v_bs_x27_2450_; size_t v___x_2451_; size_t v___x_2452_; lean_object* v___x_2453_; 
v_v_2447_ = lean_array_uget_borrowed(v_bs_2445_, v_i_2444_);
v_msg_2448_ = lean_ctor_get(v_v_2447_, 1);
lean_inc_ref(v_msg_2448_);
v___x_2449_ = lean_unsigned_to_nat(0u);
v_bs_x27_2450_ = lean_array_uset(v_bs_2445_, v_i_2444_, v___x_2449_);
v___x_2451_ = ((size_t)1ULL);
v___x_2452_ = lean_usize_add(v_i_2444_, v___x_2451_);
v___x_2453_ = lean_array_uset(v_bs_x27_2450_, v_i_2444_, v_msg_2448_);
v_i_2444_ = v___x_2452_;
v_bs_2445_ = v___x_2453_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_2455_, lean_object* v_i_2456_, lean_object* v_bs_2457_){
_start:
{
size_t v_sz_boxed_2458_; size_t v_i_boxed_2459_; lean_object* v_res_2460_; 
v_sz_boxed_2458_ = lean_unbox_usize(v_sz_2455_);
lean_dec(v_sz_2455_);
v_i_boxed_2459_ = lean_unbox_usize(v_i_2456_);
lean_dec(v_i_2456_);
v_res_2460_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3_spec__4(v_sz_boxed_2458_, v_i_boxed_2459_, v_bs_2457_);
return v_res_2460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(lean_object* v_oldTraces_2461_, lean_object* v_data_2462_, lean_object* v_ref_2463_, lean_object* v_msg_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_){
_start:
{
lean_object* v_toCold_2470_; lean_object* v_currRecDepth_2471_; lean_object* v_ref_2472_; uint16_t v_optionFlags_2473_; uint8_t v_suppressElabErrors_2474_; uint8_t v_checkDeprecated_2475_; uint8_t v_isRecordingDeps_2476_; lean_object* v_ref_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v_traceState_2480_; lean_object* v_traces_2481_; lean_object* v___x_2482_; size_t v_sz_2483_; size_t v___x_2484_; lean_object* v___x_2485_; lean_object* v_msg_2486_; lean_object* v___x_2487_; lean_object* v_a_2488_; lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2526_; 
v_toCold_2470_ = lean_ctor_get(v___y_2467_, 0);
v_currRecDepth_2471_ = lean_ctor_get(v___y_2467_, 1);
v_ref_2472_ = lean_ctor_get(v___y_2467_, 2);
v_optionFlags_2473_ = lean_ctor_get_uint16(v___y_2467_, sizeof(void*)*3);
v_suppressElabErrors_2474_ = lean_ctor_get_uint8(v___y_2467_, sizeof(void*)*3 + 2);
v_checkDeprecated_2475_ = lean_ctor_get_uint8(v___y_2467_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2476_ = lean_ctor_get_uint8(v___y_2467_, sizeof(void*)*3 + 4);
v_ref_2477_ = l_Lean_replaceRef(v_ref_2463_, v_ref_2472_);
lean_inc(v_currRecDepth_2471_);
lean_inc_ref(v_toCold_2470_);
v___x_2478_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2478_, 0, v_toCold_2470_);
lean_ctor_set(v___x_2478_, 1, v_currRecDepth_2471_);
lean_ctor_set(v___x_2478_, 2, v_ref_2477_);
lean_ctor_set_uint16(v___x_2478_, sizeof(void*)*3, v_optionFlags_2473_);
lean_ctor_set_uint8(v___x_2478_, sizeof(void*)*3 + 2, v_suppressElabErrors_2474_);
lean_ctor_set_uint8(v___x_2478_, sizeof(void*)*3 + 3, v_checkDeprecated_2475_);
lean_ctor_set_uint8(v___x_2478_, sizeof(void*)*3 + 4, v_isRecordingDeps_2476_);
v___x_2479_ = lean_st_ref_get(v___y_2468_);
v_traceState_2480_ = lean_ctor_get(v___x_2479_, 4);
lean_inc_ref(v_traceState_2480_);
lean_dec(v___x_2479_);
v_traces_2481_ = lean_ctor_get(v_traceState_2480_, 0);
lean_inc_ref(v_traces_2481_);
lean_dec_ref(v_traceState_2480_);
v___x_2482_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2481_);
lean_dec_ref(v_traces_2481_);
v_sz_2483_ = lean_array_size(v___x_2482_);
v___x_2484_ = ((size_t)0ULL);
v___x_2485_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3_spec__4(v_sz_2483_, v___x_2484_, v___x_2482_);
v_msg_2486_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2486_, 0, v_data_2462_);
lean_ctor_set(v_msg_2486_, 1, v_msg_2464_);
lean_ctor_set(v_msg_2486_, 2, v___x_2485_);
v___x_2487_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msg_2486_, v___y_2465_, v___y_2466_, v___x_2478_, v___y_2468_);
lean_dec_ref_known(v___x_2478_, 3);
v_a_2488_ = lean_ctor_get(v___x_2487_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2487_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2490_ = v___x_2487_;
v_isShared_2491_ = v_isSharedCheck_2526_;
goto v_resetjp_2489_;
}
else
{
lean_inc(v_a_2488_);
lean_dec(v___x_2487_);
v___x_2490_ = lean_box(0);
v_isShared_2491_ = v_isSharedCheck_2526_;
goto v_resetjp_2489_;
}
v_resetjp_2489_:
{
lean_object* v___x_2492_; lean_object* v_traceState_2493_; lean_object* v_env_2494_; lean_object* v_nextMacroScope_2495_; lean_object* v_ngen_2496_; lean_object* v_auxDeclNGen_2497_; lean_object* v_cache_2498_; lean_object* v_recordedDeps_2499_; lean_object* v_messages_2500_; lean_object* v_infoState_2501_; lean_object* v_snapshotTasks_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2525_; 
v___x_2492_ = lean_st_ref_take(v___y_2468_);
v_traceState_2493_ = lean_ctor_get(v___x_2492_, 4);
v_env_2494_ = lean_ctor_get(v___x_2492_, 0);
v_nextMacroScope_2495_ = lean_ctor_get(v___x_2492_, 1);
v_ngen_2496_ = lean_ctor_get(v___x_2492_, 2);
v_auxDeclNGen_2497_ = lean_ctor_get(v___x_2492_, 3);
v_cache_2498_ = lean_ctor_get(v___x_2492_, 5);
v_recordedDeps_2499_ = lean_ctor_get(v___x_2492_, 6);
v_messages_2500_ = lean_ctor_get(v___x_2492_, 7);
v_infoState_2501_ = lean_ctor_get(v___x_2492_, 8);
v_snapshotTasks_2502_ = lean_ctor_get(v___x_2492_, 9);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2492_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2504_ = v___x_2492_;
v_isShared_2505_ = v_isSharedCheck_2525_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_snapshotTasks_2502_);
lean_inc(v_infoState_2501_);
lean_inc(v_messages_2500_);
lean_inc(v_recordedDeps_2499_);
lean_inc(v_cache_2498_);
lean_inc(v_traceState_2493_);
lean_inc(v_auxDeclNGen_2497_);
lean_inc(v_ngen_2496_);
lean_inc(v_nextMacroScope_2495_);
lean_inc(v_env_2494_);
lean_dec(v___x_2492_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2525_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
uint64_t v_tid_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2523_; 
v_tid_2506_ = lean_ctor_get_uint64(v_traceState_2493_, sizeof(void*)*1);
v_isSharedCheck_2523_ = !lean_is_exclusive(v_traceState_2493_);
if (v_isSharedCheck_2523_ == 0)
{
lean_object* v_unused_2524_; 
v_unused_2524_ = lean_ctor_get(v_traceState_2493_, 0);
lean_dec(v_unused_2524_);
v___x_2508_ = v_traceState_2493_;
v_isShared_2509_ = v_isSharedCheck_2523_;
goto v_resetjp_2507_;
}
else
{
lean_dec(v_traceState_2493_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2523_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2514_; 
v___x_2510_ = lean_box(0);
v___x_2511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2511_, 0, v_ref_2463_);
lean_ctor_set(v___x_2511_, 1, v_a_2488_);
v___x_2512_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2461_, v___x_2511_);
if (v_isShared_2509_ == 0)
{
lean_ctor_set(v___x_2508_, 0, v___x_2512_);
v___x_2514_ = v___x_2508_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v___x_2512_);
lean_ctor_set_uint64(v_reuseFailAlloc_2522_, sizeof(void*)*1, v_tid_2506_);
v___x_2514_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
lean_object* v___x_2516_; 
if (v_isShared_2505_ == 0)
{
lean_ctor_set(v___x_2504_, 4, v___x_2514_);
v___x_2516_ = v___x_2504_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v_env_2494_);
lean_ctor_set(v_reuseFailAlloc_2521_, 1, v_nextMacroScope_2495_);
lean_ctor_set(v_reuseFailAlloc_2521_, 2, v_ngen_2496_);
lean_ctor_set(v_reuseFailAlloc_2521_, 3, v_auxDeclNGen_2497_);
lean_ctor_set(v_reuseFailAlloc_2521_, 4, v___x_2514_);
lean_ctor_set(v_reuseFailAlloc_2521_, 5, v_cache_2498_);
lean_ctor_set(v_reuseFailAlloc_2521_, 6, v_recordedDeps_2499_);
lean_ctor_set(v_reuseFailAlloc_2521_, 7, v_messages_2500_);
lean_ctor_set(v_reuseFailAlloc_2521_, 8, v_infoState_2501_);
lean_ctor_set(v_reuseFailAlloc_2521_, 9, v_snapshotTasks_2502_);
v___x_2516_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
lean_object* v___x_2517_; lean_object* v___x_2519_; 
v___x_2517_ = lean_st_ref_put(v___y_2468_, v___x_2516_);
if (v_isShared_2491_ == 0)
{
lean_ctor_set(v___x_2490_, 0, v___x_2510_);
v___x_2519_ = v___x_2490_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v___x_2510_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3___boxed(lean_object* v_oldTraces_2527_, lean_object* v_data_2528_, lean_object* v_ref_2529_, lean_object* v_msg_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_){
_start:
{
lean_object* v_res_2536_; 
v_res_2536_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(v_oldTraces_2527_, v_data_2528_, v_ref_2529_, v_msg_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
lean_dec(v___y_2534_);
lean_dec_ref(v___y_2533_);
lean_dec(v___y_2532_);
lean_dec_ref(v___y_2531_);
return v_res_2536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(lean_object* v_opts_2537_, lean_object* v_opt_2538_){
_start:
{
lean_object* v_name_2539_; lean_object* v_defValue_2540_; lean_object* v_map_2541_; lean_object* v___x_2542_; 
v_name_2539_ = lean_ctor_get(v_opt_2538_, 0);
v_defValue_2540_ = lean_ctor_get(v_opt_2538_, 1);
v_map_2541_ = lean_ctor_get(v_opts_2537_, 0);
v___x_2542_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2541_, v_name_2539_);
if (lean_obj_tag(v___x_2542_) == 0)
{
lean_inc(v_defValue_2540_);
return v_defValue_2540_;
}
else
{
lean_object* v_val_2543_; 
v_val_2543_ = lean_ctor_get(v___x_2542_, 0);
lean_inc(v_val_2543_);
lean_dec_ref_known(v___x_2542_, 1);
if (lean_obj_tag(v_val_2543_) == 3)
{
lean_object* v_v_2544_; 
v_v_2544_ = lean_ctor_get(v_val_2543_, 0);
lean_inc(v_v_2544_);
lean_dec_ref_known(v_val_2543_, 1);
return v_v_2544_;
}
else
{
lean_dec(v_val_2543_);
lean_inc(v_defValue_2540_);
return v_defValue_2540_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6___boxed(lean_object* v_opts_2545_, lean_object* v_opt_2546_){
_start:
{
lean_object* v_res_2547_; 
v_res_2547_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(v_opts_2545_, v_opt_2546_);
lean_dec_ref(v_opt_2546_);
lean_dec_ref(v_opts_2545_);
return v_res_2547_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5(lean_object* v_e_2548_){
_start:
{
if (lean_obj_tag(v_e_2548_) == 0)
{
uint8_t v___x_2549_; 
v___x_2549_ = 2;
return v___x_2549_;
}
else
{
uint8_t v___x_2550_; 
v___x_2550_ = 0;
return v___x_2550_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___boxed(lean_object* v_e_2551_){
_start:
{
uint8_t v_res_2552_; lean_object* v_r_2553_; 
v_res_2552_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5(v_e_2551_);
lean_dec_ref(v_e_2551_);
v_r_2553_ = lean_box(v_res_2552_);
return v_r_2553_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg(lean_object* v_x_2554_){
_start:
{
if (lean_obj_tag(v_x_2554_) == 0)
{
lean_object* v_a_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2563_; 
v_a_2556_ = lean_ctor_get(v_x_2554_, 0);
v_isSharedCheck_2563_ = !lean_is_exclusive(v_x_2554_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2558_ = v_x_2554_;
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_a_2556_);
lean_dec(v_x_2554_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2561_; 
if (v_isShared_2559_ == 0)
{
lean_ctor_set_tag(v___x_2558_, 1);
v___x_2561_ = v___x_2558_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_a_2556_);
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
lean_object* v_a_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2571_; 
v_a_2564_ = lean_ctor_get(v_x_2554_, 0);
v_isSharedCheck_2571_ = !lean_is_exclusive(v_x_2554_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2566_ = v_x_2554_;
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_a_2564_);
lean_dec(v_x_2554_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v___x_2569_; 
if (v_isShared_2567_ == 0)
{
lean_ctor_set_tag(v___x_2566_, 0);
v___x_2569_ = v___x_2566_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v_a_2564_);
v___x_2569_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
return v___x_2569_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg___boxed(lean_object* v_x_2572_, lean_object* v___y_2573_){
_start:
{
lean_object* v_res_2574_; 
v_res_2574_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg(v_x_2572_);
return v_res_2574_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___x_2576_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__0));
v___x_2577_ = l_Lean_stringToMessageData(v___x_2576_);
return v___x_2577_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2578_; double v___x_2579_; 
v___x_2578_ = lean_unsigned_to_nat(1000u);
v___x_2579_ = lean_float_of_nat(v___x_2578_);
return v___x_2579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(lean_object* v_cls_2580_, uint8_t v_collapsed_2581_, lean_object* v_tag_2582_, lean_object* v_opts_2583_, uint8_t v_clsEnabled_2584_, lean_object* v_oldTraces_2585_, lean_object* v_msg_2586_, lean_object* v_resStartStop_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_){
_start:
{
lean_object* v_fst_2593_; lean_object* v_snd_2594_; lean_object* v___y_2596_; lean_object* v___y_2597_; lean_object* v_data_2598_; lean_object* v_fst_2601_; lean_object* v_snd_2602_; lean_object* v___x_2603_; uint8_t v___x_2604_; lean_object* v___y_2606_; lean_object* v_a_2607_; uint8_t v___y_2622_; double v___y_2654_; 
v_fst_2593_ = lean_ctor_get(v_resStartStop_2587_, 0);
lean_inc(v_fst_2593_);
v_snd_2594_ = lean_ctor_get(v_resStartStop_2587_, 1);
lean_inc(v_snd_2594_);
lean_dec_ref(v_resStartStop_2587_);
v_fst_2601_ = lean_ctor_get(v_snd_2594_, 0);
lean_inc(v_fst_2601_);
v_snd_2602_ = lean_ctor_get(v_snd_2594_, 1);
lean_inc(v_snd_2602_);
lean_dec(v_snd_2594_);
v___x_2603_ = l_Lean_trace_profiler;
v___x_2604_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_opts_2583_, v___x_2603_);
if (v___x_2604_ == 0)
{
v___y_2622_ = v___x_2604_;
goto v___jp_2621_;
}
else
{
lean_object* v___x_2659_; uint8_t v___x_2660_; 
v___x_2659_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2660_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_opts_2583_, v___x_2659_);
if (v___x_2660_ == 0)
{
lean_object* v___x_2661_; lean_object* v___x_2662_; double v___x_2663_; double v___x_2664_; double v___x_2665_; 
v___x_2661_ = l_Lean_trace_profiler_threshold;
v___x_2662_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(v_opts_2583_, v___x_2661_);
v___x_2663_ = lean_float_of_nat(v___x_2662_);
v___x_2664_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2);
v___x_2665_ = lean_float_div(v___x_2663_, v___x_2664_);
v___y_2654_ = v___x_2665_;
goto v___jp_2653_;
}
else
{
lean_object* v___x_2666_; lean_object* v___x_2667_; double v___x_2668_; 
v___x_2666_ = l_Lean_trace_profiler_threshold;
v___x_2667_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(v_opts_2583_, v___x_2666_);
v___x_2668_ = lean_float_of_nat(v___x_2667_);
v___y_2654_ = v___x_2668_;
goto v___jp_2653_;
}
}
v___jp_2595_:
{
lean_object* v___x_2599_; 
lean_inc(v___y_2596_);
v___x_2599_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(v_oldTraces_2585_, v_data_2598_, v___y_2596_, v___y_2597_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_);
if (lean_obj_tag(v___x_2599_) == 0)
{
lean_object* v___x_2600_; 
lean_dec_ref_known(v___x_2599_, 1);
v___x_2600_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg(v_fst_2593_);
return v___x_2600_;
}
else
{
lean_dec(v_fst_2593_);
return v___x_2599_;
}
}
v___jp_2605_:
{
uint8_t v_result_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; double v___x_2611_; lean_object* v_data_2612_; 
v_result_2608_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5(v_fst_2593_);
v___x_2609_ = lean_box(v_result_2608_);
v___x_2610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2609_);
v___x_2611_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0);
lean_inc_ref(v_tag_2582_);
lean_inc_ref(v___x_2610_);
lean_inc(v_cls_2580_);
v_data_2612_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2612_, 0, v_cls_2580_);
lean_ctor_set(v_data_2612_, 1, v___x_2610_);
lean_ctor_set(v_data_2612_, 2, v_tag_2582_);
lean_ctor_set_float(v_data_2612_, sizeof(void*)*3, v___x_2611_);
lean_ctor_set_float(v_data_2612_, sizeof(void*)*3 + 8, v___x_2611_);
lean_ctor_set_uint8(v_data_2612_, sizeof(void*)*3 + 16, v_collapsed_2581_);
if (v___x_2604_ == 0)
{
lean_dec_ref_known(v___x_2610_, 1);
lean_dec(v_snd_2602_);
lean_dec(v_fst_2601_);
lean_dec_ref(v_tag_2582_);
lean_dec(v_cls_2580_);
v___y_2596_ = v___y_2606_;
v___y_2597_ = v_a_2607_;
v_data_2598_ = v_data_2612_;
goto v___jp_2595_;
}
else
{
lean_object* v_data_2613_; double v___x_2614_; double v___x_2615_; 
lean_dec_ref_known(v_data_2612_, 3);
v_data_2613_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2613_, 0, v_cls_2580_);
lean_ctor_set(v_data_2613_, 1, v___x_2610_);
lean_ctor_set(v_data_2613_, 2, v_tag_2582_);
v___x_2614_ = lean_unbox_float(v_fst_2601_);
lean_dec(v_fst_2601_);
lean_ctor_set_float(v_data_2613_, sizeof(void*)*3, v___x_2614_);
v___x_2615_ = lean_unbox_float(v_snd_2602_);
lean_dec(v_snd_2602_);
lean_ctor_set_float(v_data_2613_, sizeof(void*)*3 + 8, v___x_2615_);
lean_ctor_set_uint8(v_data_2613_, sizeof(void*)*3 + 16, v_collapsed_2581_);
v___y_2596_ = v___y_2606_;
v___y_2597_ = v_a_2607_;
v_data_2598_ = v_data_2613_;
goto v___jp_2595_;
}
}
v___jp_2616_:
{
lean_object* v_ref_2617_; lean_object* v___x_2618_; 
v_ref_2617_ = lean_ctor_get(v___y_2590_, 2);
lean_inc(v___y_2591_);
lean_inc_ref(v___y_2590_);
lean_inc(v___y_2589_);
lean_inc_ref(v___y_2588_);
lean_inc(v_fst_2593_);
v___x_2618_ = lean_apply_6(v_msg_2586_, v_fst_2593_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, lean_box(0));
if (lean_obj_tag(v___x_2618_) == 0)
{
lean_object* v_a_2619_; 
v_a_2619_ = lean_ctor_get(v___x_2618_, 0);
lean_inc(v_a_2619_);
lean_dec_ref_known(v___x_2618_, 1);
v___y_2606_ = v_ref_2617_;
v_a_2607_ = v_a_2619_;
goto v___jp_2605_;
}
else
{
lean_object* v___x_2620_; 
lean_dec_ref_known(v___x_2618_, 1);
v___x_2620_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1);
v___y_2606_ = v_ref_2617_;
v_a_2607_ = v___x_2620_;
goto v___jp_2605_;
}
}
v___jp_2621_:
{
if (v_clsEnabled_2584_ == 0)
{
if (v___y_2622_ == 0)
{
lean_object* v___x_2623_; lean_object* v_traceState_2624_; lean_object* v_env_2625_; lean_object* v_nextMacroScope_2626_; lean_object* v_ngen_2627_; lean_object* v_auxDeclNGen_2628_; lean_object* v_cache_2629_; lean_object* v_recordedDeps_2630_; lean_object* v_messages_2631_; lean_object* v_infoState_2632_; lean_object* v_snapshotTasks_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2652_; 
lean_dec(v_snd_2602_);
lean_dec(v_fst_2601_);
lean_dec_ref(v_msg_2586_);
lean_dec_ref(v_tag_2582_);
lean_dec(v_cls_2580_);
v___x_2623_ = lean_st_ref_take(v___y_2591_);
v_traceState_2624_ = lean_ctor_get(v___x_2623_, 4);
v_env_2625_ = lean_ctor_get(v___x_2623_, 0);
v_nextMacroScope_2626_ = lean_ctor_get(v___x_2623_, 1);
v_ngen_2627_ = lean_ctor_get(v___x_2623_, 2);
v_auxDeclNGen_2628_ = lean_ctor_get(v___x_2623_, 3);
v_cache_2629_ = lean_ctor_get(v___x_2623_, 5);
v_recordedDeps_2630_ = lean_ctor_get(v___x_2623_, 6);
v_messages_2631_ = lean_ctor_get(v___x_2623_, 7);
v_infoState_2632_ = lean_ctor_get(v___x_2623_, 8);
v_snapshotTasks_2633_ = lean_ctor_get(v___x_2623_, 9);
v_isSharedCheck_2652_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2635_ = v___x_2623_;
v_isShared_2636_ = v_isSharedCheck_2652_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_snapshotTasks_2633_);
lean_inc(v_infoState_2632_);
lean_inc(v_messages_2631_);
lean_inc(v_recordedDeps_2630_);
lean_inc(v_cache_2629_);
lean_inc(v_traceState_2624_);
lean_inc(v_auxDeclNGen_2628_);
lean_inc(v_ngen_2627_);
lean_inc(v_nextMacroScope_2626_);
lean_inc(v_env_2625_);
lean_dec(v___x_2623_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2652_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
uint64_t v_tid_2637_; lean_object* v_traces_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2651_; 
v_tid_2637_ = lean_ctor_get_uint64(v_traceState_2624_, sizeof(void*)*1);
v_traces_2638_ = lean_ctor_get(v_traceState_2624_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v_traceState_2624_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2640_ = v_traceState_2624_;
v_isShared_2641_ = v_isSharedCheck_2651_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_traces_2638_);
lean_dec(v_traceState_2624_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2651_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___x_2642_; lean_object* v___x_2644_; 
v___x_2642_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2585_, v_traces_2638_);
lean_dec_ref(v_traces_2638_);
if (v_isShared_2641_ == 0)
{
lean_ctor_set(v___x_2640_, 0, v___x_2642_);
v___x_2644_ = v___x_2640_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v___x_2642_);
lean_ctor_set_uint64(v_reuseFailAlloc_2650_, sizeof(void*)*1, v_tid_2637_);
v___x_2644_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
lean_object* v___x_2646_; 
if (v_isShared_2636_ == 0)
{
lean_ctor_set(v___x_2635_, 4, v___x_2644_);
v___x_2646_ = v___x_2635_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_env_2625_);
lean_ctor_set(v_reuseFailAlloc_2649_, 1, v_nextMacroScope_2626_);
lean_ctor_set(v_reuseFailAlloc_2649_, 2, v_ngen_2627_);
lean_ctor_set(v_reuseFailAlloc_2649_, 3, v_auxDeclNGen_2628_);
lean_ctor_set(v_reuseFailAlloc_2649_, 4, v___x_2644_);
lean_ctor_set(v_reuseFailAlloc_2649_, 5, v_cache_2629_);
lean_ctor_set(v_reuseFailAlloc_2649_, 6, v_recordedDeps_2630_);
lean_ctor_set(v_reuseFailAlloc_2649_, 7, v_messages_2631_);
lean_ctor_set(v_reuseFailAlloc_2649_, 8, v_infoState_2632_);
lean_ctor_set(v_reuseFailAlloc_2649_, 9, v_snapshotTasks_2633_);
v___x_2646_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
lean_object* v___x_2647_; lean_object* v___x_2648_; 
v___x_2647_ = lean_st_ref_put(v___y_2591_, v___x_2646_);
v___x_2648_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg(v_fst_2593_);
return v___x_2648_;
}
}
}
}
}
else
{
goto v___jp_2616_;
}
}
else
{
goto v___jp_2616_;
}
}
v___jp_2653_:
{
double v___x_2655_; double v___x_2656_; double v___x_2657_; uint8_t v___x_2658_; 
v___x_2655_ = lean_unbox_float(v_snd_2602_);
v___x_2656_ = lean_unbox_float(v_fst_2601_);
v___x_2657_ = lean_float_sub(v___x_2655_, v___x_2656_);
v___x_2658_ = lean_float_decLt(v___y_2654_, v___x_2657_);
v___y_2622_ = v___x_2658_;
goto v___jp_2621_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___boxed(lean_object* v_cls_2669_, lean_object* v_collapsed_2670_, lean_object* v_tag_2671_, lean_object* v_opts_2672_, lean_object* v_clsEnabled_2673_, lean_object* v_oldTraces_2674_, lean_object* v_msg_2675_, lean_object* v_resStartStop_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_){
_start:
{
uint8_t v_collapsed_boxed_2682_; uint8_t v_clsEnabled_boxed_2683_; lean_object* v_res_2684_; 
v_collapsed_boxed_2682_ = lean_unbox(v_collapsed_2670_);
v_clsEnabled_boxed_2683_ = lean_unbox(v_clsEnabled_2673_);
v_res_2684_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_2669_, v_collapsed_boxed_2682_, v_tag_2671_, v_opts_2672_, v_clsEnabled_boxed_2683_, v_oldTraces_2674_, v_msg_2675_, v_resStartStop_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_);
lean_dec(v___y_2680_);
lean_dec_ref(v___y_2679_);
lean_dec(v___y_2678_);
lean_dec_ref(v___y_2677_);
lean_dec_ref(v_opts_2672_);
return v_res_2684_;
}
}
static double _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0(void){
_start:
{
lean_object* v___x_2685_; double v___x_2686_; 
v___x_2685_ = lean_unsigned_to_nat(1000000000u);
v___x_2686_ = lean_float_of_nat(v___x_2685_);
return v___x_2686_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2(void){
_start:
{
lean_object* v___x_2688_; lean_object* v___x_2689_; 
v___x_2688_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1));
v___x_2689_ = l_Lean_stringToMessageData(v___x_2688_);
return v___x_2689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(lean_object* v_ctorVal_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_){
_start:
{
lean_object* v_toConstantVal_2696_; lean_object* v_toCold_2697_; lean_object* v_options_2698_; lean_object* v_name_2699_; lean_object* v_levelParams_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2913_; 
v_toConstantVal_2696_ = lean_ctor_get(v_ctorVal_2690_, 0);
lean_inc_ref(v_toConstantVal_2696_);
v_toCold_2697_ = lean_ctor_get(v_a_2693_, 0);
v_options_2698_ = lean_ctor_get(v_toCold_2697_, 2);
v_name_2699_ = lean_ctor_get(v_toConstantVal_2696_, 0);
v_levelParams_2700_ = lean_ctor_get(v_toConstantVal_2696_, 1);
v_isSharedCheck_2913_ = !lean_is_exclusive(v_toConstantVal_2696_);
if (v_isSharedCheck_2913_ == 0)
{
lean_object* v_unused_2914_; 
v_unused_2914_ = lean_ctor_get(v_toConstantVal_2696_, 2);
lean_dec(v_unused_2914_);
v___x_2702_ = v_toConstantVal_2696_;
v_isShared_2703_ = v_isSharedCheck_2913_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_levelParams_2700_);
lean_inc(v_name_2699_);
lean_dec(v_toConstantVal_2696_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2913_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
lean_object* v_inheritedTraceOptions_2704_; uint8_t v_hasTrace_2705_; lean_object* v_name_2706_; 
v_inheritedTraceOptions_2704_ = lean_ctor_get(v_toCold_2697_, 11);
v_hasTrace_2705_ = lean_ctor_get_uint8(v_options_2698_, sizeof(void*)*1);
lean_inc(v_name_2699_);
v_name_2706_ = l_Lean_Meta_mkInjectiveTheoremNameFor(v_name_2699_);
if (v_hasTrace_2705_ == 0)
{
lean_object* v___x_2707_; 
v___x_2707_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_);
if (lean_obj_tag(v___x_2707_) == 0)
{
lean_object* v_a_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2745_; 
v_a_2708_ = lean_ctor_get(v___x_2707_, 0);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___x_2707_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2710_ = v___x_2707_;
v_isShared_2711_ = v_isSharedCheck_2745_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_a_2708_);
lean_dec(v___x_2707_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2745_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
if (lean_obj_tag(v_a_2708_) == 1)
{
lean_object* v_val_2712_; lean_object* v___x_2713_; 
lean_del_object(v___x_2710_);
v_val_2712_ = lean_ctor_get(v_a_2708_, 0);
lean_inc_n(v_val_2712_, 2);
lean_dec_ref_known(v_a_2708_, 1);
v___x_2713_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2699_, v_val_2712_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_);
if (lean_obj_tag(v___x_2713_) == 0)
{
lean_object* v_a_2714_; lean_object* v___x_2715_; lean_object* v_a_2716_; lean_object* v___x_2717_; lean_object* v_a_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2732_; 
v_a_2714_ = lean_ctor_get(v___x_2713_, 0);
lean_inc(v_a_2714_);
lean_dec_ref_known(v___x_2713_, 1);
v___x_2715_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2712_, v_a_2692_);
v_a_2716_ = lean_ctor_get(v___x_2715_, 0);
lean_inc(v_a_2716_);
lean_dec_ref(v___x_2715_);
v___x_2717_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2714_, v_a_2692_);
v_a_2718_ = lean_ctor_get(v___x_2717_, 0);
v_isSharedCheck_2732_ = !lean_is_exclusive(v___x_2717_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2720_ = v___x_2717_;
v_isShared_2721_ = v_isSharedCheck_2732_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_a_2718_);
lean_dec(v___x_2717_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2732_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v___x_2723_; 
lean_inc(v_name_2706_);
if (v_isShared_2703_ == 0)
{
lean_ctor_set(v___x_2702_, 2, v_a_2716_);
lean_ctor_set(v___x_2702_, 0, v_name_2706_);
v___x_2723_ = v___x_2702_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v_name_2706_);
lean_ctor_set(v_reuseFailAlloc_2731_, 1, v_levelParams_2700_);
lean_ctor_set(v_reuseFailAlloc_2731_, 2, v_a_2716_);
v___x_2723_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2728_; 
v___x_2724_ = lean_box(0);
v___x_2725_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2725_, 0, v_name_2706_);
lean_ctor_set(v___x_2725_, 1, v___x_2724_);
v___x_2726_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2726_, 0, v___x_2723_);
lean_ctor_set(v___x_2726_, 1, v_a_2718_);
lean_ctor_set(v___x_2726_, 2, v___x_2725_);
if (v_isShared_2721_ == 0)
{
lean_ctor_set_tag(v___x_2720_, 2);
lean_ctor_set(v___x_2720_, 0, v___x_2726_);
v___x_2728_ = v___x_2720_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v___x_2726_);
v___x_2728_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
lean_object* v___x_2729_; 
v___x_2729_ = l_Lean_addDecl(v___x_2728_, v_hasTrace_2705_, v_a_2693_, v_a_2694_);
return v___x_2729_;
}
}
}
}
else
{
lean_object* v_a_2733_; lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2740_; 
lean_dec(v_val_2712_);
lean_dec(v_name_2706_);
lean_del_object(v___x_2702_);
lean_dec(v_levelParams_2700_);
v_a_2733_ = lean_ctor_get(v___x_2713_, 0);
v_isSharedCheck_2740_ = !lean_is_exclusive(v___x_2713_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2735_ = v___x_2713_;
v_isShared_2736_ = v_isSharedCheck_2740_;
goto v_resetjp_2734_;
}
else
{
lean_inc(v_a_2733_);
lean_dec(v___x_2713_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2740_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v___x_2738_; 
if (v_isShared_2736_ == 0)
{
v___x_2738_ = v___x_2735_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v_a_2733_);
v___x_2738_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
return v___x_2738_;
}
}
}
}
else
{
lean_object* v___x_2741_; lean_object* v___x_2743_; 
lean_dec(v_a_2708_);
lean_dec(v_name_2706_);
lean_del_object(v___x_2702_);
lean_dec(v_levelParams_2700_);
lean_dec(v_name_2699_);
v___x_2741_ = lean_box(0);
if (v_isShared_2711_ == 0)
{
lean_ctor_set(v___x_2710_, 0, v___x_2741_);
v___x_2743_ = v___x_2710_;
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
}
else
{
lean_object* v_a_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2753_; 
lean_dec(v_name_2706_);
lean_del_object(v___x_2702_);
lean_dec(v_levelParams_2700_);
lean_dec(v_name_2699_);
v_a_2746_ = lean_ctor_get(v___x_2707_, 0);
v_isSharedCheck_2753_ = !lean_is_exclusive(v___x_2707_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2748_ = v___x_2707_;
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_a_2746_);
lean_dec(v___x_2707_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v___x_2751_; 
if (v_isShared_2749_ == 0)
{
v___x_2751_ = v___x_2748_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v_a_2746_);
v___x_2751_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
return v___x_2751_;
}
}
}
}
else
{
lean_object* v___f_2754_; lean_object* v_cls_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; uint8_t v___x_2758_; lean_object* v___y_2760_; lean_object* v___y_2761_; lean_object* v_a_2762_; lean_object* v___y_2772_; lean_object* v___y_2773_; lean_object* v_a_2774_; lean_object* v___y_2777_; lean_object* v___y_2778_; lean_object* v_a_2779_; lean_object* v___y_2782_; lean_object* v___y_2783_; lean_object* v___y_2784_; lean_object* v___y_2788_; lean_object* v___y_2789_; lean_object* v_a_2790_; lean_object* v___y_2803_; lean_object* v___y_2804_; lean_object* v_a_2805_; lean_object* v___y_2808_; lean_object* v___y_2809_; lean_object* v_a_2810_; lean_object* v___y_2813_; lean_object* v___y_2814_; lean_object* v___y_2815_; 
lean_inc(v_name_2706_);
v___f_2754_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2754_, 0, v_name_2706_);
v_cls_2755_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_2756_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_2757_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_2758_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2704_, v_options_2698_, v___x_2757_);
if (v___x_2758_ == 0)
{
lean_object* v___x_2855_; uint8_t v___x_2856_; 
v___x_2855_ = l_Lean_trace_profiler;
v___x_2856_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_2698_, v___x_2855_);
if (v___x_2856_ == 0)
{
lean_object* v___x_2857_; 
lean_dec_ref(v___f_2754_);
v___x_2857_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v_a_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2904_; 
v_a_2858_ = lean_ctor_get(v___x_2857_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2860_ = v___x_2857_;
v_isShared_2861_ = v_isSharedCheck_2904_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_a_2858_);
lean_dec(v___x_2857_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2904_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
if (lean_obj_tag(v_a_2858_) == 1)
{
lean_object* v_val_2862_; lean_object* v___y_2864_; lean_object* v___y_2865_; lean_object* v___y_2866_; lean_object* v___y_2867_; 
lean_del_object(v___x_2860_);
v_val_2862_ = lean_ctor_get(v_a_2858_, 0);
lean_inc(v_val_2862_);
lean_dec_ref_known(v_a_2858_, 1);
if (v___x_2758_ == 0)
{
v___y_2864_ = v_a_2691_;
v___y_2865_ = v_a_2692_;
v___y_2866_ = v_a_2693_;
v___y_2867_ = v_a_2694_;
goto v___jp_2863_;
}
else
{
lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2896_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
lean_inc(v_val_2862_);
v___x_2897_ = l_Lean_MessageData_ofExpr(v_val_2862_);
v___x_2898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2898_, 0, v___x_2896_);
lean_ctor_set(v___x_2898_, 1, v___x_2897_);
v___x_2899_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2755_, v___x_2898_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_);
if (lean_obj_tag(v___x_2899_) == 0)
{
lean_dec_ref_known(v___x_2899_, 1);
v___y_2864_ = v_a_2691_;
v___y_2865_ = v_a_2692_;
v___y_2866_ = v_a_2693_;
v___y_2867_ = v_a_2694_;
goto v___jp_2863_;
}
else
{
lean_dec(v_val_2862_);
lean_dec(v_name_2706_);
lean_del_object(v___x_2702_);
lean_dec(v_levelParams_2700_);
lean_dec(v_name_2699_);
return v___x_2899_;
}
}
v___jp_2863_:
{
lean_object* v___x_2868_; 
lean_inc(v_val_2862_);
v___x_2868_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2699_, v_val_2862_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_);
if (lean_obj_tag(v___x_2868_) == 0)
{
lean_object* v_a_2869_; lean_object* v___x_2870_; lean_object* v_a_2871_; lean_object* v___x_2872_; lean_object* v_a_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2887_; 
v_a_2869_ = lean_ctor_get(v___x_2868_, 0);
lean_inc(v_a_2869_);
lean_dec_ref_known(v___x_2868_, 1);
v___x_2870_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2862_, v___y_2865_);
v_a_2871_ = lean_ctor_get(v___x_2870_, 0);
lean_inc(v_a_2871_);
lean_dec_ref(v___x_2870_);
v___x_2872_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2869_, v___y_2865_);
v_a_2873_ = lean_ctor_get(v___x_2872_, 0);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2872_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2875_ = v___x_2872_;
v_isShared_2876_ = v_isSharedCheck_2887_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_a_2873_);
lean_dec(v___x_2872_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2887_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v___x_2878_; 
lean_inc(v_name_2706_);
if (v_isShared_2703_ == 0)
{
lean_ctor_set(v___x_2702_, 2, v_a_2871_);
lean_ctor_set(v___x_2702_, 0, v_name_2706_);
v___x_2878_ = v___x_2702_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_name_2706_);
lean_ctor_set(v_reuseFailAlloc_2886_, 1, v_levelParams_2700_);
lean_ctor_set(v_reuseFailAlloc_2886_, 2, v_a_2871_);
v___x_2878_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2883_; 
v___x_2879_ = lean_box(0);
v___x_2880_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2880_, 0, v_name_2706_);
lean_ctor_set(v___x_2880_, 1, v___x_2879_);
v___x_2881_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2881_, 0, v___x_2878_);
lean_ctor_set(v___x_2881_, 1, v_a_2873_);
lean_ctor_set(v___x_2881_, 2, v___x_2880_);
if (v_isShared_2876_ == 0)
{
lean_ctor_set_tag(v___x_2875_, 2);
lean_ctor_set(v___x_2875_, 0, v___x_2881_);
v___x_2883_ = v___x_2875_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v___x_2881_);
v___x_2883_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
lean_object* v___x_2884_; 
v___x_2884_ = l_Lean_addDecl(v___x_2883_, v___x_2856_, v___y_2866_, v___y_2867_);
return v___x_2884_;
}
}
}
}
else
{
lean_object* v_a_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2895_; 
lean_dec(v_val_2862_);
lean_dec(v_name_2706_);
lean_del_object(v___x_2702_);
lean_dec(v_levelParams_2700_);
v_a_2888_ = lean_ctor_get(v___x_2868_, 0);
v_isSharedCheck_2895_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2890_ = v___x_2868_;
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_a_2888_);
lean_dec(v___x_2868_);
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
}
else
{
lean_object* v___x_2900_; lean_object* v___x_2902_; 
lean_dec(v_a_2858_);
lean_dec(v_name_2706_);
lean_del_object(v___x_2702_);
lean_dec(v_levelParams_2700_);
lean_dec(v_name_2699_);
v___x_2900_ = lean_box(0);
if (v_isShared_2861_ == 0)
{
lean_ctor_set(v___x_2860_, 0, v___x_2900_);
v___x_2902_ = v___x_2860_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v___x_2900_);
v___x_2902_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
return v___x_2902_;
}
}
}
}
else
{
lean_object* v_a_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2912_; 
lean_dec(v_name_2706_);
lean_del_object(v___x_2702_);
lean_dec(v_levelParams_2700_);
lean_dec(v_name_2699_);
v_a_2905_ = lean_ctor_get(v___x_2857_, 0);
v_isSharedCheck_2912_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2912_ == 0)
{
v___x_2907_ = v___x_2857_;
v_isShared_2908_ = v_isSharedCheck_2912_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_a_2905_);
lean_dec(v___x_2857_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2912_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v___x_2910_; 
if (v_isShared_2908_ == 0)
{
v___x_2910_ = v___x_2907_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v_a_2905_);
v___x_2910_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
return v___x_2910_;
}
}
}
}
else
{
lean_del_object(v___x_2702_);
goto v___jp_2818_;
}
}
else
{
lean_del_object(v___x_2702_);
goto v___jp_2818_;
}
v___jp_2759_:
{
lean_object* v___x_2763_; double v___x_2764_; double v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; 
v___x_2763_ = lean_io_get_num_heartbeats();
v___x_2764_ = lean_float_of_nat(v___y_2761_);
v___x_2765_ = lean_float_of_nat(v___x_2763_);
v___x_2766_ = lean_box_float(v___x_2764_);
v___x_2767_ = lean_box_float(v___x_2765_);
v___x_2768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2768_, 0, v___x_2766_);
lean_ctor_set(v___x_2768_, 1, v___x_2767_);
v___x_2769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2769_, 0, v_a_2762_);
lean_ctor_set(v___x_2769_, 1, v___x_2768_);
v___x_2770_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_2755_, v_hasTrace_2705_, v___x_2756_, v_options_2698_, v___x_2758_, v___y_2760_, v___f_2754_, v___x_2769_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_);
return v___x_2770_;
}
v___jp_2771_:
{
lean_object* v___x_2775_; 
v___x_2775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2775_, 0, v_a_2774_);
v___y_2760_ = v___y_2772_;
v___y_2761_ = v___y_2773_;
v_a_2762_ = v___x_2775_;
goto v___jp_2759_;
}
v___jp_2776_:
{
lean_object* v___x_2780_; 
v___x_2780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2780_, 0, v_a_2779_);
v___y_2760_ = v___y_2777_;
v___y_2761_ = v___y_2778_;
v_a_2762_ = v___x_2780_;
goto v___jp_2759_;
}
v___jp_2781_:
{
if (lean_obj_tag(v___y_2784_) == 0)
{
lean_object* v_a_2785_; 
v_a_2785_ = lean_ctor_get(v___y_2784_, 0);
lean_inc(v_a_2785_);
lean_dec_ref_known(v___y_2784_, 1);
v___y_2777_ = v___y_2782_;
v___y_2778_ = v___y_2783_;
v_a_2779_ = v_a_2785_;
goto v___jp_2776_;
}
else
{
lean_object* v_a_2786_; 
v_a_2786_ = lean_ctor_get(v___y_2784_, 0);
lean_inc(v_a_2786_);
lean_dec_ref_known(v___y_2784_, 1);
v___y_2772_ = v___y_2782_;
v___y_2773_ = v___y_2783_;
v_a_2774_ = v_a_2786_;
goto v___jp_2771_;
}
}
v___jp_2787_:
{
lean_object* v___x_2791_; double v___x_2792_; double v___x_2793_; double v___x_2794_; double v___x_2795_; double v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; 
v___x_2791_ = lean_io_mono_nanos_now();
v___x_2792_ = lean_float_of_nat(v___y_2789_);
v___x_2793_ = lean_float_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0);
v___x_2794_ = lean_float_div(v___x_2792_, v___x_2793_);
v___x_2795_ = lean_float_of_nat(v___x_2791_);
v___x_2796_ = lean_float_div(v___x_2795_, v___x_2793_);
v___x_2797_ = lean_box_float(v___x_2794_);
v___x_2798_ = lean_box_float(v___x_2796_);
v___x_2799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2799_, 0, v___x_2797_);
lean_ctor_set(v___x_2799_, 1, v___x_2798_);
v___x_2800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2800_, 0, v_a_2790_);
lean_ctor_set(v___x_2800_, 1, v___x_2799_);
v___x_2801_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_2755_, v_hasTrace_2705_, v___x_2756_, v_options_2698_, v___x_2758_, v___y_2788_, v___f_2754_, v___x_2800_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_);
return v___x_2801_;
}
v___jp_2802_:
{
lean_object* v___x_2806_; 
v___x_2806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2806_, 0, v_a_2805_);
v___y_2788_ = v___y_2803_;
v___y_2789_ = v___y_2804_;
v_a_2790_ = v___x_2806_;
goto v___jp_2787_;
}
v___jp_2807_:
{
lean_object* v___x_2811_; 
v___x_2811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2811_, 0, v_a_2810_);
v___y_2788_ = v___y_2808_;
v___y_2789_ = v___y_2809_;
v_a_2790_ = v___x_2811_;
goto v___jp_2787_;
}
v___jp_2812_:
{
if (lean_obj_tag(v___y_2815_) == 0)
{
lean_object* v_a_2816_; 
v_a_2816_ = lean_ctor_get(v___y_2815_, 0);
lean_inc(v_a_2816_);
lean_dec_ref_known(v___y_2815_, 1);
v___y_2803_ = v___y_2813_;
v___y_2804_ = v___y_2814_;
v_a_2805_ = v_a_2816_;
goto v___jp_2802_;
}
else
{
lean_object* v_a_2817_; 
v_a_2817_ = lean_ctor_get(v___y_2815_, 0);
lean_inc(v_a_2817_);
lean_dec_ref_known(v___y_2815_, 1);
v___y_2808_ = v___y_2813_;
v___y_2809_ = v___y_2814_;
v_a_2810_ = v_a_2817_;
goto v___jp_2807_;
}
}
v___jp_2818_:
{
lean_object* v___x_2819_; lean_object* v_a_2820_; lean_object* v___x_2821_; uint8_t v___x_2822_; 
v___x_2819_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v_a_2694_);
v_a_2820_ = lean_ctor_get(v___x_2819_, 0);
lean_inc(v_a_2820_);
lean_dec_ref(v___x_2819_);
v___x_2821_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2822_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_2698_, v___x_2821_);
if (v___x_2822_ == 0)
{
lean_object* v___x_2823_; lean_object* v___x_2824_; 
v___x_2823_ = lean_io_mono_nanos_now();
v___x_2824_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_);
if (lean_obj_tag(v___x_2824_) == 0)
{
lean_object* v_a_2825_; 
v_a_2825_ = lean_ctor_get(v___x_2824_, 0);
lean_inc(v_a_2825_);
lean_dec_ref_known(v___x_2824_, 1);
if (lean_obj_tag(v_a_2825_) == 1)
{
if (v___x_2758_ == 0)
{
lean_object* v_val_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; 
v_val_2826_ = lean_ctor_get(v_a_2825_, 0);
lean_inc(v_val_2826_);
lean_dec_ref_known(v_a_2825_, 1);
v___x_2827_ = lean_box(0);
v___x_2828_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(v_name_2699_, v_val_2826_, v_name_2706_, v_levelParams_2700_, v___x_2822_, v___x_2827_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_);
v___y_2813_ = v_a_2820_;
v___y_2814_ = v___x_2823_;
v___y_2815_ = v___x_2828_;
goto v___jp_2812_;
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
v___x_2833_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2755_, v___x_2832_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_);
if (lean_obj_tag(v___x_2833_) == 0)
{
lean_object* v_a_2834_; lean_object* v___x_2835_; 
v_a_2834_ = lean_ctor_get(v___x_2833_, 0);
lean_inc(v_a_2834_);
lean_dec_ref_known(v___x_2833_, 1);
v___x_2835_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(v_name_2699_, v_val_2829_, v_name_2706_, v_levelParams_2700_, v___x_2822_, v_a_2834_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_);
v___y_2813_ = v_a_2820_;
v___y_2814_ = v___x_2823_;
v___y_2815_ = v___x_2835_;
goto v___jp_2812_;
}
else
{
lean_object* v_a_2836_; 
lean_dec(v_val_2829_);
lean_dec(v_name_2706_);
lean_dec(v_levelParams_2700_);
lean_dec(v_name_2699_);
v_a_2836_ = lean_ctor_get(v___x_2833_, 0);
lean_inc(v_a_2836_);
lean_dec_ref_known(v___x_2833_, 1);
v___y_2808_ = v_a_2820_;
v___y_2809_ = v___x_2823_;
v_a_2810_ = v_a_2836_;
goto v___jp_2807_;
}
}
}
else
{
lean_object* v___x_2837_; 
lean_dec(v_a_2825_);
lean_dec(v_name_2706_);
lean_dec(v_levelParams_2700_);
lean_dec(v_name_2699_);
v___x_2837_ = lean_box(0);
v___y_2803_ = v_a_2820_;
v___y_2804_ = v___x_2823_;
v_a_2805_ = v___x_2837_;
goto v___jp_2802_;
}
}
else
{
lean_object* v_a_2838_; 
lean_dec(v_name_2706_);
lean_dec(v_levelParams_2700_);
lean_dec(v_name_2699_);
v_a_2838_ = lean_ctor_get(v___x_2824_, 0);
lean_inc(v_a_2838_);
lean_dec_ref_known(v___x_2824_, 1);
v___y_2808_ = v_a_2820_;
v___y_2809_ = v___x_2823_;
v_a_2810_ = v_a_2838_;
goto v___jp_2807_;
}
}
else
{
lean_object* v___x_2839_; lean_object* v___x_2840_; 
v___x_2839_ = lean_io_get_num_heartbeats();
v___x_2840_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_);
if (lean_obj_tag(v___x_2840_) == 0)
{
lean_object* v_a_2841_; 
v_a_2841_ = lean_ctor_get(v___x_2840_, 0);
lean_inc(v_a_2841_);
lean_dec_ref_known(v___x_2840_, 1);
if (lean_obj_tag(v_a_2841_) == 1)
{
if (v___x_2758_ == 0)
{
lean_object* v_val_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; 
v_val_2842_ = lean_ctor_get(v_a_2841_, 0);
lean_inc(v_val_2842_);
lean_dec_ref_known(v_a_2841_, 1);
v___x_2843_ = lean_box(0);
v___x_2844_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(v_name_2699_, v_val_2842_, v_name_2706_, v_levelParams_2700_, v___x_2843_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_);
v___y_2782_ = v_a_2820_;
v___y_2783_ = v___x_2839_;
v___y_2784_ = v___x_2844_;
goto v___jp_2781_;
}
else
{
lean_object* v_val_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; 
v_val_2845_ = lean_ctor_get(v_a_2841_, 0);
lean_inc_n(v_val_2845_, 2);
lean_dec_ref_known(v_a_2841_, 1);
v___x_2846_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_2847_ = l_Lean_MessageData_ofExpr(v_val_2845_);
v___x_2848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2848_, 0, v___x_2846_);
lean_ctor_set(v___x_2848_, 1, v___x_2847_);
v___x_2849_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2755_, v___x_2848_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_);
if (lean_obj_tag(v___x_2849_) == 0)
{
lean_object* v_a_2850_; lean_object* v___x_2851_; 
v_a_2850_ = lean_ctor_get(v___x_2849_, 0);
lean_inc(v_a_2850_);
lean_dec_ref_known(v___x_2849_, 1);
v___x_2851_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(v_name_2699_, v_val_2845_, v_name_2706_, v_levelParams_2700_, v_a_2850_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_);
v___y_2782_ = v_a_2820_;
v___y_2783_ = v___x_2839_;
v___y_2784_ = v___x_2851_;
goto v___jp_2781_;
}
else
{
lean_object* v_a_2852_; 
lean_dec(v_val_2845_);
lean_dec(v_name_2706_);
lean_dec(v_levelParams_2700_);
lean_dec(v_name_2699_);
v_a_2852_ = lean_ctor_get(v___x_2849_, 0);
lean_inc(v_a_2852_);
lean_dec_ref_known(v___x_2849_, 1);
v___y_2772_ = v_a_2820_;
v___y_2773_ = v___x_2839_;
v_a_2774_ = v_a_2852_;
goto v___jp_2771_;
}
}
}
else
{
lean_object* v___x_2853_; 
lean_dec(v_a_2841_);
lean_dec(v_name_2706_);
lean_dec(v_levelParams_2700_);
lean_dec(v_name_2699_);
v___x_2853_ = lean_box(0);
v___y_2777_ = v_a_2820_;
v___y_2778_ = v___x_2839_;
v_a_2779_ = v___x_2853_;
goto v___jp_2776_;
}
}
else
{
lean_object* v_a_2854_; 
lean_dec(v_name_2706_);
lean_dec(v_levelParams_2700_);
lean_dec(v_name_2699_);
v_a_2854_ = lean_ctor_get(v___x_2840_, 0);
lean_inc(v_a_2854_);
lean_dec_ref_known(v___x_2840_, 1);
v___y_2772_ = v_a_2820_;
v___y_2773_ = v___x_2839_;
v_a_2774_ = v_a_2854_;
goto v___jp_2771_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___boxed(lean_object* v_ctorVal_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_){
_start:
{
lean_object* v_res_2921_; 
v_res_2921_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(v_ctorVal_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_);
lean_dec(v_a_2919_);
lean_dec_ref(v_a_2918_);
lean_dec(v_a_2917_);
lean_dec_ref(v_a_2916_);
return v_res_2921_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4(lean_object* v_00_u03b1_2922_, lean_object* v_x_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
lean_object* v___x_2929_; 
v___x_2929_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg(v_x_2923_);
return v___x_2929_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2930_, lean_object* v_x_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_){
_start:
{
lean_object* v_res_2937_; 
v_res_2937_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4(v_00_u03b1_2930_, v_x_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_);
lean_dec(v___y_2935_);
lean_dec_ref(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
return v_res_2937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveEqTheoremNameFor(lean_object* v_ctorName_2941_){
_start:
{
lean_object* v___x_2942_; lean_object* v___x_2943_; 
v___x_2942_ = ((lean_object*)(l_Lean_Meta_mkInjectiveEqTheoremNameFor___closed__1));
v___x_2943_ = l_Lean_Name_append(v_ctorName_2941_, v___x_2942_);
return v___x_2943_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(lean_object* v_ctorVal_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_){
_start:
{
uint8_t v___x_2950_; lean_object* v___x_2951_; 
v___x_2950_ = 1;
v___x_2951_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(v_ctorVal_2944_, v___x_2950_, v_a_2945_, v_a_2946_, v_a_2947_, v_a_2948_);
return v___x_2951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f___boxed(lean_object* v_ctorVal_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_){
_start:
{
lean_object* v_res_2958_; 
v_res_2958_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_2952_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_);
lean_dec(v_a_2956_);
lean_dec_ref(v_a_2955_);
lean_dec(v_a_2954_);
lean_dec_ref(v_a_2953_);
return v_res_2958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(lean_object* v_e_2959_, lean_object* v_t_2960_, lean_object* v_acc_2961_, lean_object* v_a_2962_){
_start:
{
lean_object* v___x_2967_; 
v___x_2967_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_t_2960_, v_a_2962_);
if (lean_obj_tag(v___x_2967_) == 0)
{
lean_object* v_a_2968_; lean_object* v___x_2969_; uint8_t v___x_2970_; 
v_a_2968_ = lean_ctor_get(v___x_2967_, 0);
lean_inc(v_a_2968_);
lean_dec_ref_known(v___x_2967_, 1);
v___x_2969_ = l_Lean_Expr_cleanupAnnotations(v_a_2968_);
lean_dec(v_a_2968_);
v___x_2970_ = l_Lean_Expr_isApp(v___x_2969_);
if (v___x_2970_ == 0)
{
lean_dec_ref(v___x_2969_);
goto v___jp_2964_;
}
else
{
lean_object* v___x_2971_; uint8_t v___x_2972_; 
v___x_2971_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2969_);
v___x_2972_ = l_Lean_Expr_isApp(v___x_2971_);
if (v___x_2972_ == 0)
{
lean_dec_ref(v___x_2971_);
lean_dec_ref(v___x_2969_);
goto v___jp_2964_;
}
else
{
lean_object* v___x_2973_; lean_object* v___x_2974_; uint8_t v___x_2975_; 
v___x_2973_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2971_);
v___x_2974_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__1));
v___x_2975_ = l_Lean_Expr_isConstOf(v___x_2973_, v___x_2974_);
lean_dec_ref(v___x_2973_);
if (v___x_2975_ == 0)
{
lean_dec_ref(v___x_2971_);
lean_dec_ref(v___x_2969_);
goto v___jp_2964_;
}
else
{
lean_object* v_arg_2976_; lean_object* v_arg_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; 
v_arg_2976_ = lean_ctor_get(v___x_2969_, 1);
lean_inc_ref(v_arg_2976_);
lean_dec_ref(v___x_2969_);
v_arg_2977_ = lean_ctor_get(v___x_2971_, 1);
lean_inc_ref(v_arg_2977_);
lean_dec_ref(v___x_2971_);
v___x_2978_ = lean_unsigned_to_nat(0u);
v___x_2979_ = l_Lean_mkProj(v___x_2974_, v___x_2978_, v_e_2959_);
lean_inc_ref(v___x_2979_);
v___x_2980_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v___x_2979_, v_arg_2977_, v_acc_2961_, v_a_2962_);
if (lean_obj_tag(v___x_2980_) == 0)
{
lean_object* v_a_2981_; 
v_a_2981_ = lean_ctor_get(v___x_2980_, 0);
lean_inc(v_a_2981_);
lean_dec_ref_known(v___x_2980_, 1);
v_e_2959_ = v___x_2979_;
v_t_2960_ = v_arg_2976_;
v_acc_2961_ = v_a_2981_;
goto _start;
}
else
{
lean_dec_ref(v___x_2979_);
lean_dec_ref(v_arg_2976_);
return v___x_2980_;
}
}
}
}
}
else
{
lean_object* v_a_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_2990_; 
lean_dec_ref(v_acc_2961_);
lean_dec_ref(v_e_2959_);
v_a_2983_ = lean_ctor_get(v___x_2967_, 0);
v_isSharedCheck_2990_ = !lean_is_exclusive(v___x_2967_);
if (v_isSharedCheck_2990_ == 0)
{
v___x_2985_ = v___x_2967_;
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_a_2983_);
lean_dec(v___x_2967_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
lean_object* v___x_2988_; 
if (v_isShared_2986_ == 0)
{
v___x_2988_ = v___x_2985_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v_a_2983_);
v___x_2988_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
return v___x_2988_;
}
}
}
v___jp_2964_:
{
lean_object* v___x_2965_; lean_object* v___x_2966_; 
v___x_2965_ = lean_array_push(v_acc_2961_, v_e_2959_);
v___x_2966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2966_, 0, v___x_2965_);
return v___x_2966_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg___boxed(lean_object* v_e_2991_, lean_object* v_t_2992_, lean_object* v_acc_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_){
_start:
{
lean_object* v_res_2996_; 
v_res_2996_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v_e_2991_, v_t_2992_, v_acc_2993_, v_a_2994_);
lean_dec(v_a_2994_);
return v_res_2996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go(lean_object* v_e_2997_, lean_object* v_t_2998_, lean_object* v_acc_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_){
_start:
{
lean_object* v___x_3005_; 
v___x_3005_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v_e_2997_, v_t_2998_, v_acc_2999_, v_a_3001_);
return v___x_3005_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___boxed(lean_object* v_e_3006_, lean_object* v_t_3007_, lean_object* v_acc_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_){
_start:
{
lean_object* v_res_3014_; 
v_res_3014_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go(v_e_3006_, v_t_3007_, v_acc_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_);
lean_dec(v_a_3012_);
lean_dec_ref(v_a_3011_);
lean_dec(v_a_3010_);
lean_dec_ref(v_a_3009_);
return v_res_3014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections(lean_object* v_e_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_){
_start:
{
lean_object* v___x_3021_; 
lean_inc(v_a_3019_);
lean_inc_ref(v_a_3018_);
lean_inc(v_a_3017_);
lean_inc_ref(v_a_3016_);
lean_inc_ref(v_e_3015_);
v___x_3021_ = lean_infer_type(v_e_3015_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_);
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_object* v_a_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; 
v_a_3022_ = lean_ctor_get(v___x_3021_, 0);
lean_inc(v_a_3022_);
lean_dec_ref_known(v___x_3021_, 1);
v___x_3023_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_3024_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v_e_3015_, v_a_3022_, v___x_3023_, v_a_3017_);
return v___x_3024_;
}
else
{
lean_object* v_a_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3032_; 
lean_dec_ref(v_e_3015_);
v_a_3025_ = lean_ctor_get(v___x_3021_, 0);
v_isSharedCheck_3032_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3032_ == 0)
{
v___x_3027_ = v___x_3021_;
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_a_3025_);
lean_dec(v___x_3021_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v___x_3030_; 
if (v_isShared_3028_ == 0)
{
v___x_3030_ = v___x_3027_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_a_3025_);
v___x_3030_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
return v___x_3030_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections___boxed(lean_object* v_e_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_){
_start:
{
lean_object* v_res_3039_; 
v_res_3039_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections(v_e_3033_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_);
lean_dec(v_a_3037_);
lean_dec_ref(v_a_3036_);
lean_dec(v_a_3035_);
lean_dec_ref(v_a_3034_);
return v_res_3039_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_x_3040_, lean_object* v_x_3041_, lean_object* v_x_3042_, lean_object* v_x_3043_){
_start:
{
lean_object* v_ks_3044_; lean_object* v_vs_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3069_; 
v_ks_3044_ = lean_ctor_get(v_x_3040_, 0);
v_vs_3045_ = lean_ctor_get(v_x_3040_, 1);
v_isSharedCheck_3069_ = !lean_is_exclusive(v_x_3040_);
if (v_isSharedCheck_3069_ == 0)
{
v___x_3047_ = v_x_3040_;
v_isShared_3048_ = v_isSharedCheck_3069_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_vs_3045_);
lean_inc(v_ks_3044_);
lean_dec(v_x_3040_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3069_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v___x_3049_; uint8_t v___x_3050_; 
v___x_3049_ = lean_array_get_size(v_ks_3044_);
v___x_3050_ = lean_nat_dec_lt(v_x_3041_, v___x_3049_);
if (v___x_3050_ == 0)
{
lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3054_; 
lean_dec(v_x_3041_);
v___x_3051_ = lean_array_push(v_ks_3044_, v_x_3042_);
v___x_3052_ = lean_array_push(v_vs_3045_, v_x_3043_);
if (v_isShared_3048_ == 0)
{
lean_ctor_set(v___x_3047_, 1, v___x_3052_);
lean_ctor_set(v___x_3047_, 0, v___x_3051_);
v___x_3054_ = v___x_3047_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v___x_3051_);
lean_ctor_set(v_reuseFailAlloc_3055_, 1, v___x_3052_);
v___x_3054_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
return v___x_3054_;
}
}
else
{
lean_object* v_k_x27_3056_; uint8_t v___x_3057_; 
v_k_x27_3056_ = lean_array_fget_borrowed(v_ks_3044_, v_x_3041_);
v___x_3057_ = l_Lean_instBEqMVarId_beq(v_x_3042_, v_k_x27_3056_);
if (v___x_3057_ == 0)
{
lean_object* v___x_3059_; 
if (v_isShared_3048_ == 0)
{
v___x_3059_ = v___x_3047_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v_ks_3044_);
lean_ctor_set(v_reuseFailAlloc_3063_, 1, v_vs_3045_);
v___x_3059_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
lean_object* v___x_3060_; lean_object* v___x_3061_; 
v___x_3060_ = lean_unsigned_to_nat(1u);
v___x_3061_ = lean_nat_add(v_x_3041_, v___x_3060_);
lean_dec(v_x_3041_);
v_x_3040_ = v___x_3059_;
v_x_3041_ = v___x_3061_;
goto _start;
}
}
else
{
lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3067_; 
v___x_3064_ = lean_array_fset(v_ks_3044_, v_x_3041_, v_x_3042_);
v___x_3065_ = lean_array_fset(v_vs_3045_, v_x_3041_, v_x_3043_);
lean_dec(v_x_3041_);
if (v_isShared_3048_ == 0)
{
lean_ctor_set(v___x_3047_, 1, v___x_3065_);
lean_ctor_set(v___x_3047_, 0, v___x_3064_);
v___x_3067_ = v___x_3047_;
goto v_reusejp_3066_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v___x_3064_);
lean_ctor_set(v_reuseFailAlloc_3068_, 1, v___x_3065_);
v___x_3067_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3066_;
}
v_reusejp_3066_:
{
return v___x_3067_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_n_3070_, lean_object* v_k_3071_, lean_object* v_v_3072_){
_start:
{
lean_object* v___x_3073_; lean_object* v___x_3074_; 
v___x_3073_ = lean_unsigned_to_nat(0u);
v___x_3074_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_n_3070_, v___x_3073_, v_k_3071_, v_v_3072_);
return v___x_3074_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_3075_; 
v___x_3075_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_3075_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(lean_object* v_x_3076_, size_t v_x_3077_, size_t v_x_3078_, lean_object* v_x_3079_, lean_object* v_x_3080_){
_start:
{
if (lean_obj_tag(v_x_3076_) == 0)
{
lean_object* v_es_3081_; size_t v___x_3082_; size_t v___x_3083_; lean_object* v_j_3084_; lean_object* v___x_3085_; uint8_t v___x_3086_; 
v_es_3081_ = lean_ctor_get(v_x_3076_, 0);
v___x_3082_ = ((size_t)31ULL);
v___x_3083_ = lean_usize_land(v_x_3077_, v___x_3082_);
v_j_3084_ = lean_usize_to_nat(v___x_3083_);
v___x_3085_ = lean_array_get_size(v_es_3081_);
v___x_3086_ = lean_nat_dec_lt(v_j_3084_, v___x_3085_);
if (v___x_3086_ == 0)
{
lean_dec(v_j_3084_);
lean_dec(v_x_3080_);
lean_dec(v_x_3079_);
return v_x_3076_;
}
else
{
lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3125_; 
lean_inc_ref(v_es_3081_);
v_isSharedCheck_3125_ = !lean_is_exclusive(v_x_3076_);
if (v_isSharedCheck_3125_ == 0)
{
lean_object* v_unused_3126_; 
v_unused_3126_ = lean_ctor_get(v_x_3076_, 0);
lean_dec(v_unused_3126_);
v___x_3088_ = v_x_3076_;
v_isShared_3089_ = v_isSharedCheck_3125_;
goto v_resetjp_3087_;
}
else
{
lean_dec(v_x_3076_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3125_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
lean_object* v_v_3090_; lean_object* v___x_3091_; lean_object* v_xs_x27_3092_; lean_object* v___y_3094_; 
v_v_3090_ = lean_array_fget(v_es_3081_, v_j_3084_);
v___x_3091_ = lean_box(0);
v_xs_x27_3092_ = lean_array_fset(v_es_3081_, v_j_3084_, v___x_3091_);
switch(lean_obj_tag(v_v_3090_))
{
case 0:
{
lean_object* v_key_3099_; lean_object* v_val_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3110_; 
v_key_3099_ = lean_ctor_get(v_v_3090_, 0);
v_val_3100_ = lean_ctor_get(v_v_3090_, 1);
v_isSharedCheck_3110_ = !lean_is_exclusive(v_v_3090_);
if (v_isSharedCheck_3110_ == 0)
{
v___x_3102_ = v_v_3090_;
v_isShared_3103_ = v_isSharedCheck_3110_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_val_3100_);
lean_inc(v_key_3099_);
lean_dec(v_v_3090_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3110_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
uint8_t v___x_3104_; 
v___x_3104_ = l_Lean_instBEqMVarId_beq(v_x_3079_, v_key_3099_);
if (v___x_3104_ == 0)
{
lean_object* v___x_3105_; lean_object* v___x_3106_; 
lean_del_object(v___x_3102_);
v___x_3105_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3099_, v_val_3100_, v_x_3079_, v_x_3080_);
v___x_3106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3106_, 0, v___x_3105_);
v___y_3094_ = v___x_3106_;
goto v___jp_3093_;
}
else
{
lean_object* v___x_3108_; 
lean_dec(v_val_3100_);
lean_dec(v_key_3099_);
if (v_isShared_3103_ == 0)
{
lean_ctor_set(v___x_3102_, 1, v_x_3080_);
lean_ctor_set(v___x_3102_, 0, v_x_3079_);
v___x_3108_ = v___x_3102_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v_x_3079_);
lean_ctor_set(v_reuseFailAlloc_3109_, 1, v_x_3080_);
v___x_3108_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
v___y_3094_ = v___x_3108_;
goto v___jp_3093_;
}
}
}
}
case 1:
{
lean_object* v_node_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3123_; 
v_node_3111_ = lean_ctor_get(v_v_3090_, 0);
v_isSharedCheck_3123_ = !lean_is_exclusive(v_v_3090_);
if (v_isSharedCheck_3123_ == 0)
{
v___x_3113_ = v_v_3090_;
v_isShared_3114_ = v_isSharedCheck_3123_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_node_3111_);
lean_dec(v_v_3090_);
v___x_3113_ = lean_box(0);
v_isShared_3114_ = v_isSharedCheck_3123_;
goto v_resetjp_3112_;
}
v_resetjp_3112_:
{
size_t v___x_3115_; size_t v___x_3116_; size_t v___x_3117_; size_t v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3121_; 
v___x_3115_ = ((size_t)5ULL);
v___x_3116_ = lean_usize_shift_right(v_x_3077_, v___x_3115_);
v___x_3117_ = ((size_t)1ULL);
v___x_3118_ = lean_usize_add(v_x_3078_, v___x_3117_);
v___x_3119_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_node_3111_, v___x_3116_, v___x_3118_, v_x_3079_, v_x_3080_);
if (v_isShared_3114_ == 0)
{
lean_ctor_set(v___x_3113_, 0, v___x_3119_);
v___x_3121_ = v___x_3113_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v___x_3119_);
v___x_3121_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
v___y_3094_ = v___x_3121_;
goto v___jp_3093_;
}
}
}
default: 
{
lean_object* v___x_3124_; 
v___x_3124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3124_, 0, v_x_3079_);
lean_ctor_set(v___x_3124_, 1, v_x_3080_);
v___y_3094_ = v___x_3124_;
goto v___jp_3093_;
}
}
v___jp_3093_:
{
lean_object* v___x_3095_; lean_object* v___x_3097_; 
v___x_3095_ = lean_array_fset(v_xs_x27_3092_, v_j_3084_, v___y_3094_);
lean_dec(v_j_3084_);
if (v_isShared_3089_ == 0)
{
lean_ctor_set(v___x_3088_, 0, v___x_3095_);
v___x_3097_ = v___x_3088_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v___x_3095_);
v___x_3097_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3096_;
}
v_reusejp_3096_:
{
return v___x_3097_;
}
}
}
}
}
else
{
lean_object* v_ks_3127_; lean_object* v_vs_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3146_; 
v_ks_3127_ = lean_ctor_get(v_x_3076_, 0);
v_vs_3128_ = lean_ctor_get(v_x_3076_, 1);
v_isSharedCheck_3146_ = !lean_is_exclusive(v_x_3076_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3130_ = v_x_3076_;
v_isShared_3131_ = v_isSharedCheck_3146_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_vs_3128_);
lean_inc(v_ks_3127_);
lean_dec(v_x_3076_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3146_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v___x_3133_; 
if (v_isShared_3131_ == 0)
{
v___x_3133_ = v___x_3130_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v_ks_3127_);
lean_ctor_set(v_reuseFailAlloc_3145_, 1, v_vs_3128_);
v___x_3133_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
lean_object* v_newNode_3134_; size_t v___x_3135_; uint8_t v___x_3136_; 
v_newNode_3134_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(v___x_3133_, v_x_3079_, v_x_3080_);
v___x_3135_ = ((size_t)7ULL);
v___x_3136_ = lean_usize_dec_le(v___x_3135_, v_x_3078_);
if (v___x_3136_ == 0)
{
lean_object* v___x_3137_; lean_object* v___x_3138_; uint8_t v___x_3139_; 
v___x_3137_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3134_);
v___x_3138_ = lean_unsigned_to_nat(4u);
v___x_3139_ = lean_nat_dec_lt(v___x_3137_, v___x_3138_);
lean_dec(v___x_3137_);
if (v___x_3139_ == 0)
{
lean_object* v_ks_3140_; lean_object* v_vs_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; 
v_ks_3140_ = lean_ctor_get(v_newNode_3134_, 0);
lean_inc_ref(v_ks_3140_);
v_vs_3141_ = lean_ctor_get(v_newNode_3134_, 1);
lean_inc_ref(v_vs_3141_);
lean_dec_ref(v_newNode_3134_);
v___x_3142_ = lean_unsigned_to_nat(0u);
v___x_3143_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_3144_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(v_x_3078_, v_ks_3140_, v_vs_3141_, v___x_3142_, v___x_3143_);
lean_dec_ref(v_vs_3141_);
lean_dec_ref(v_ks_3140_);
return v___x_3144_;
}
else
{
return v_newNode_3134_;
}
}
else
{
return v_newNode_3134_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(size_t v_depth_3147_, lean_object* v_keys_3148_, lean_object* v_vals_3149_, lean_object* v_i_3150_, lean_object* v_entries_3151_){
_start:
{
lean_object* v___x_3152_; uint8_t v___x_3153_; 
v___x_3152_ = lean_array_get_size(v_keys_3148_);
v___x_3153_ = lean_nat_dec_lt(v_i_3150_, v___x_3152_);
if (v___x_3153_ == 0)
{
lean_dec(v_i_3150_);
return v_entries_3151_;
}
else
{
lean_object* v_k_3154_; lean_object* v_v_3155_; uint64_t v___x_3156_; size_t v_h_3157_; size_t v___x_3158_; lean_object* v___x_3159_; size_t v___x_3160_; size_t v___x_3161_; size_t v___x_3162_; size_t v_h_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; 
v_k_3154_ = lean_array_fget_borrowed(v_keys_3148_, v_i_3150_);
v_v_3155_ = lean_array_fget_borrowed(v_vals_3149_, v_i_3150_);
v___x_3156_ = l_Lean_instHashableMVarId_hash(v_k_3154_);
v_h_3157_ = lean_uint64_to_usize(v___x_3156_);
v___x_3158_ = ((size_t)5ULL);
v___x_3159_ = lean_unsigned_to_nat(1u);
v___x_3160_ = ((size_t)1ULL);
v___x_3161_ = lean_usize_sub(v_depth_3147_, v___x_3160_);
v___x_3162_ = lean_usize_mul(v___x_3158_, v___x_3161_);
v_h_3163_ = lean_usize_shift_right(v_h_3157_, v___x_3162_);
v___x_3164_ = lean_nat_add(v_i_3150_, v___x_3159_);
lean_dec(v_i_3150_);
lean_inc(v_v_3155_);
lean_inc(v_k_3154_);
v___x_3165_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_entries_3151_, v_h_3163_, v_depth_3147_, v_k_3154_, v_v_3155_);
v_i_3150_ = v___x_3164_;
v_entries_3151_ = v___x_3165_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_depth_3167_, lean_object* v_keys_3168_, lean_object* v_vals_3169_, lean_object* v_i_3170_, lean_object* v_entries_3171_){
_start:
{
size_t v_depth_boxed_3172_; lean_object* v_res_3173_; 
v_depth_boxed_3172_ = lean_unbox_usize(v_depth_3167_);
lean_dec(v_depth_3167_);
v_res_3173_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_boxed_3172_, v_keys_3168_, v_vals_3169_, v_i_3170_, v_entries_3171_);
lean_dec_ref(v_vals_3169_);
lean_dec_ref(v_keys_3168_);
return v_res_3173_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_3174_, lean_object* v_x_3175_, lean_object* v_x_3176_, lean_object* v_x_3177_, lean_object* v_x_3178_){
_start:
{
size_t v_x_4967__boxed_3179_; size_t v_x_4968__boxed_3180_; lean_object* v_res_3181_; 
v_x_4967__boxed_3179_ = lean_unbox_usize(v_x_3175_);
lean_dec(v_x_3175_);
v_x_4968__boxed_3180_ = lean_unbox_usize(v_x_3176_);
lean_dec(v_x_3176_);
v_res_3181_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_x_3174_, v_x_4967__boxed_3179_, v_x_4968__boxed_3180_, v_x_3177_, v_x_3178_);
return v_res_3181_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(lean_object* v_x_3182_, lean_object* v_x_3183_, lean_object* v_x_3184_){
_start:
{
uint64_t v___x_3185_; size_t v___x_3186_; size_t v___x_3187_; lean_object* v___x_3188_; 
v___x_3185_ = l_Lean_instHashableMVarId_hash(v_x_3183_);
v___x_3186_ = lean_uint64_to_usize(v___x_3185_);
v___x_3187_ = ((size_t)1ULL);
v___x_3188_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_x_3182_, v___x_3186_, v___x_3187_, v_x_3183_, v_x_3184_);
return v___x_3188_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(lean_object* v_mvarId_3189_, lean_object* v_val_3190_, lean_object* v___y_3191_){
_start:
{
lean_object* v___x_3193_; lean_object* v_mctx_3194_; lean_object* v_cache_3195_; lean_object* v_zetaDeltaFVarIds_3196_; lean_object* v_postponed_3197_; lean_object* v_diag_3198_; lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3227_; 
v___x_3193_ = lean_st_ref_take(v___y_3191_);
v_mctx_3194_ = lean_ctor_get(v___x_3193_, 0);
v_cache_3195_ = lean_ctor_get(v___x_3193_, 1);
v_zetaDeltaFVarIds_3196_ = lean_ctor_get(v___x_3193_, 2);
v_postponed_3197_ = lean_ctor_get(v___x_3193_, 3);
v_diag_3198_ = lean_ctor_get(v___x_3193_, 4);
v_isSharedCheck_3227_ = !lean_is_exclusive(v___x_3193_);
if (v_isSharedCheck_3227_ == 0)
{
v___x_3200_ = v___x_3193_;
v_isShared_3201_ = v_isSharedCheck_3227_;
goto v_resetjp_3199_;
}
else
{
lean_inc(v_diag_3198_);
lean_inc(v_postponed_3197_);
lean_inc(v_zetaDeltaFVarIds_3196_);
lean_inc(v_cache_3195_);
lean_inc(v_mctx_3194_);
lean_dec(v___x_3193_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3227_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
lean_object* v_depth_3202_; lean_object* v_levelAssignDepth_3203_; lean_object* v_lmvarCounter_3204_; lean_object* v_mvarCounter_3205_; lean_object* v_lDecls_3206_; lean_object* v_decls_3207_; lean_object* v_userNames_3208_; lean_object* v_lAssignment_3209_; lean_object* v_eAssignment_3210_; lean_object* v_dAssignment_3211_; lean_object* v_instanceTypedMVars_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3226_; 
v_depth_3202_ = lean_ctor_get(v_mctx_3194_, 0);
v_levelAssignDepth_3203_ = lean_ctor_get(v_mctx_3194_, 1);
v_lmvarCounter_3204_ = lean_ctor_get(v_mctx_3194_, 2);
v_mvarCounter_3205_ = lean_ctor_get(v_mctx_3194_, 3);
v_lDecls_3206_ = lean_ctor_get(v_mctx_3194_, 4);
v_decls_3207_ = lean_ctor_get(v_mctx_3194_, 5);
v_userNames_3208_ = lean_ctor_get(v_mctx_3194_, 6);
v_lAssignment_3209_ = lean_ctor_get(v_mctx_3194_, 7);
v_eAssignment_3210_ = lean_ctor_get(v_mctx_3194_, 8);
v_dAssignment_3211_ = lean_ctor_get(v_mctx_3194_, 9);
v_instanceTypedMVars_3212_ = lean_ctor_get(v_mctx_3194_, 10);
v_isSharedCheck_3226_ = !lean_is_exclusive(v_mctx_3194_);
if (v_isSharedCheck_3226_ == 0)
{
v___x_3214_ = v_mctx_3194_;
v_isShared_3215_ = v_isSharedCheck_3226_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_instanceTypedMVars_3212_);
lean_inc(v_dAssignment_3211_);
lean_inc(v_eAssignment_3210_);
lean_inc(v_lAssignment_3209_);
lean_inc(v_userNames_3208_);
lean_inc(v_decls_3207_);
lean_inc(v_lDecls_3206_);
lean_inc(v_mvarCounter_3205_);
lean_inc(v_lmvarCounter_3204_);
lean_inc(v_levelAssignDepth_3203_);
lean_inc(v_depth_3202_);
lean_dec(v_mctx_3194_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3226_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3219_; 
v___x_3216_ = lean_box(0);
v___x_3217_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(v_eAssignment_3210_, v_mvarId_3189_, v_val_3190_);
if (v_isShared_3215_ == 0)
{
lean_ctor_set(v___x_3214_, 8, v___x_3217_);
v___x_3219_ = v___x_3214_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v_depth_3202_);
lean_ctor_set(v_reuseFailAlloc_3225_, 1, v_levelAssignDepth_3203_);
lean_ctor_set(v_reuseFailAlloc_3225_, 2, v_lmvarCounter_3204_);
lean_ctor_set(v_reuseFailAlloc_3225_, 3, v_mvarCounter_3205_);
lean_ctor_set(v_reuseFailAlloc_3225_, 4, v_lDecls_3206_);
lean_ctor_set(v_reuseFailAlloc_3225_, 5, v_decls_3207_);
lean_ctor_set(v_reuseFailAlloc_3225_, 6, v_userNames_3208_);
lean_ctor_set(v_reuseFailAlloc_3225_, 7, v_lAssignment_3209_);
lean_ctor_set(v_reuseFailAlloc_3225_, 8, v___x_3217_);
lean_ctor_set(v_reuseFailAlloc_3225_, 9, v_dAssignment_3211_);
lean_ctor_set(v_reuseFailAlloc_3225_, 10, v_instanceTypedMVars_3212_);
v___x_3219_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
lean_object* v___x_3221_; 
if (v_isShared_3201_ == 0)
{
lean_ctor_set(v___x_3200_, 0, v___x_3219_);
v___x_3221_ = v___x_3200_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v___x_3219_);
lean_ctor_set(v_reuseFailAlloc_3224_, 1, v_cache_3195_);
lean_ctor_set(v_reuseFailAlloc_3224_, 2, v_zetaDeltaFVarIds_3196_);
lean_ctor_set(v_reuseFailAlloc_3224_, 3, v_postponed_3197_);
lean_ctor_set(v_reuseFailAlloc_3224_, 4, v_diag_3198_);
v___x_3221_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3222_ = lean_st_ref_put(v___y_3191_, v___x_3221_);
v___x_3223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3223_, 0, v___x_3216_);
return v___x_3223_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg___boxed(lean_object* v_mvarId_3228_, lean_object* v_val_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_){
_start:
{
lean_object* v_res_3232_; 
v_res_3232_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(v_mvarId_3228_, v_val_3229_, v___y_3230_);
lean_dec(v___y_3230_);
return v_res_3232_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3234_; lean_object* v___x_3235_; 
v___x_3234_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1___closed__0));
v___x_3235_ = l_Lean_stringToMessageData(v___x_3234_);
return v___x_3235_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(lean_object* v___f_3236_, lean_object* v_a_3237_, lean_object* v_x_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_){
_start:
{
lean_object* v___x_3244_; lean_object* v___x_3245_; 
v___x_3244_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1___closed__1, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1___closed__1);
v___x_3245_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_3244_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_);
if (lean_obj_tag(v___x_3245_) == 0)
{
lean_object* v_a_3246_; lean_object* v___x_3247_; 
v_a_3246_ = lean_ctor_get(v___x_3245_, 0);
lean_inc(v_a_3246_);
lean_dec_ref_known(v___x_3245_, 1);
lean_inc(v___y_3242_);
lean_inc_ref(v___y_3241_);
lean_inc(v___y_3240_);
lean_inc_ref(v___y_3239_);
v___x_3247_ = lean_apply_7(v___f_3236_, v_a_3246_, v_a_3237_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_, lean_box(0));
return v___x_3247_;
}
else
{
lean_object* v_a_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3255_; 
lean_dec(v_a_3237_);
lean_dec_ref(v___f_3236_);
v_a_3248_ = lean_ctor_get(v___x_3245_, 0);
v_isSharedCheck_3255_ = !lean_is_exclusive(v___x_3245_);
if (v_isSharedCheck_3255_ == 0)
{
v___x_3250_ = v___x_3245_;
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_a_3248_);
lean_dec(v___x_3245_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
lean_object* v___x_3253_; 
if (v_isShared_3251_ == 0)
{
v___x_3253_ = v___x_3250_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v_a_3248_);
v___x_3253_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
return v___x_3253_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1___boxed(lean_object* v___f_3256_, lean_object* v_a_3257_, lean_object* v_x_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_){
_start:
{
lean_object* v_res_3264_; 
v_res_3264_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(v___f_3256_, v_a_3257_, v_x_3258_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_);
lean_dec(v___y_3262_);
lean_dec_ref(v___y_3261_);
lean_dec(v___y_3260_);
lean_dec_ref(v___y_3259_);
lean_dec(v_x_3258_);
return v_res_3264_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(lean_object* v___f_3265_, lean_object* v_a_3266_, lean_object* v_x_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_){
_start:
{
lean_object* v___x_3273_; lean_object* v___x_3274_; 
v___x_3273_ = lean_box(0);
lean_inc(v___y_3271_);
lean_inc_ref(v___y_3270_);
lean_inc(v___y_3269_);
lean_inc_ref(v___y_3268_);
v___x_3274_ = lean_apply_7(v___f_3265_, v___x_3273_, v_a_3266_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_, lean_box(0));
return v___x_3274_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___boxed(lean_object* v___f_3275_, lean_object* v_a_3276_, lean_object* v_x_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_){
_start:
{
lean_object* v_res_3283_; 
v_res_3283_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(v___f_3275_, v_a_3276_, v_x_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_);
lean_dec(v___y_3281_);
lean_dec_ref(v___y_3280_);
lean_dec(v___y_3279_);
lean_dec_ref(v___y_3278_);
return v_res_3283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0(uint8_t v___x_3284_, lean_object* v_____r_3285_, lean_object* v_mvarId_u2082_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_){
_start:
{
lean_object* v___x_3292_; 
v___x_3292_ = l_Lean_Meta_introSubstEq(v_mvarId_u2082_3286_, v___x_3284_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_);
if (lean_obj_tag(v___x_3292_) == 0)
{
lean_object* v_a_3293_; lean_object* v___x_3295_; uint8_t v_isShared_3296_; uint8_t v_isSharedCheck_3302_; 
v_a_3293_ = lean_ctor_get(v___x_3292_, 0);
v_isSharedCheck_3302_ = !lean_is_exclusive(v___x_3292_);
if (v_isSharedCheck_3302_ == 0)
{
v___x_3295_ = v___x_3292_;
v_isShared_3296_ = v_isSharedCheck_3302_;
goto v_resetjp_3294_;
}
else
{
lean_inc(v_a_3293_);
lean_dec(v___x_3292_);
v___x_3295_ = lean_box(0);
v_isShared_3296_ = v_isSharedCheck_3302_;
goto v_resetjp_3294_;
}
v_resetjp_3294_:
{
lean_object* v_snd_3297_; lean_object* v___x_3298_; lean_object* v___x_3300_; 
v_snd_3297_ = lean_ctor_get(v_a_3293_, 1);
lean_inc(v_snd_3297_);
lean_dec(v_a_3293_);
v___x_3298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3298_, 0, v_snd_3297_);
if (v_isShared_3296_ == 0)
{
lean_ctor_set(v___x_3295_, 0, v___x_3298_);
v___x_3300_ = v___x_3295_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v___x_3298_);
v___x_3300_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
return v___x_3300_;
}
}
}
else
{
lean_object* v_a_3303_; lean_object* v___x_3305_; uint8_t v_isShared_3306_; uint8_t v_isSharedCheck_3310_; 
v_a_3303_ = lean_ctor_get(v___x_3292_, 0);
v_isSharedCheck_3310_ = !lean_is_exclusive(v___x_3292_);
if (v_isSharedCheck_3310_ == 0)
{
v___x_3305_ = v___x_3292_;
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
else
{
lean_inc(v_a_3303_);
lean_dec(v___x_3292_);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0___boxed(lean_object* v___x_3311_, lean_object* v_____r_3312_, lean_object* v_mvarId_u2082_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_){
_start:
{
uint8_t v___x_5255__boxed_3319_; lean_object* v_res_3320_; 
v___x_5255__boxed_3319_ = lean_unbox(v___x_3311_);
v_res_3320_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0(v___x_5255__boxed_3319_, v_____r_3312_, v_mvarId_u2082_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_);
lean_dec(v___y_3317_);
lean_dec_ref(v___y_3316_);
lean_dec(v___y_3315_);
lean_dec_ref(v___y_3314_);
return v_res_3320_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; 
v___x_3329_ = lean_box(0);
v___x_3330_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__3));
v___x_3331_ = l_Lean_mkConst(v___x_3330_, v___x_3329_);
return v___x_3331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg(lean_object* v_a_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_){
_start:
{
lean_object* v___y_3339_; uint8_t v___x_3359_; lean_object* v___f_3360_; uint8_t v___x_3361_; lean_object* v___x_3362_; 
v___x_3359_ = 0;
v___f_3360_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__0));
v___x_3361_ = 1;
lean_inc(v_a_3332_);
v___x_3362_ = l_Lean_MVarId_getType(v_a_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_);
if (lean_obj_tag(v___x_3362_) == 0)
{
lean_object* v_a_3363_; lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3420_; 
v_a_3363_ = lean_ctor_get(v___x_3362_, 0);
v_isSharedCheck_3420_ = !lean_is_exclusive(v___x_3362_);
if (v_isSharedCheck_3420_ == 0)
{
v___x_3365_ = v___x_3362_;
v_isShared_3366_ = v_isSharedCheck_3420_;
goto v_resetjp_3364_;
}
else
{
lean_inc(v_a_3363_);
lean_dec(v___x_3362_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3420_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
if (lean_obj_tag(v_a_3363_) == 7)
{
lean_object* v_binderType_3367_; lean_object* v_body_3368_; uint8_t v___x_3369_; 
v_binderType_3367_ = lean_ctor_get(v_a_3363_, 1);
lean_inc_ref(v_binderType_3367_);
v_body_3368_ = lean_ctor_get(v_a_3363_, 2);
lean_inc_ref(v_body_3368_);
lean_dec_ref_known(v_a_3363_, 3);
v___x_3369_ = l_Lean_Expr_hasLooseBVars(v_body_3368_);
if (v___x_3369_ == 0)
{
lean_object* v___x_3370_; 
lean_del_object(v___x_3365_);
v___x_3370_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_3367_, v___y_3334_);
if (lean_obj_tag(v___x_3370_) == 0)
{
lean_object* v_a_3371_; lean_object* v___x_3372_; uint8_t v___x_3373_; 
v_a_3371_ = lean_ctor_get(v___x_3370_, 0);
lean_inc(v_a_3371_);
lean_dec_ref_known(v___x_3370_, 1);
v___x_3372_ = l_Lean_Expr_cleanupAnnotations(v_a_3371_);
lean_dec(v_a_3371_);
v___x_3373_ = l_Lean_Expr_isApp(v___x_3372_);
if (v___x_3373_ == 0)
{
lean_object* v___x_3374_; lean_object* v___x_3375_; 
lean_dec_ref(v___x_3372_);
lean_dec_ref(v_body_3368_);
v___x_3374_ = lean_box(0);
v___x_3375_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(v___f_3360_, v_a_3332_, v___x_3374_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_);
v___y_3339_ = v___x_3375_;
goto v___jp_3338_;
}
else
{
lean_object* v___x_3376_; uint8_t v___x_3377_; 
v___x_3376_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3372_);
v___x_3377_ = l_Lean_Expr_isApp(v___x_3376_);
if (v___x_3377_ == 0)
{
lean_object* v___x_3378_; lean_object* v___x_3379_; 
lean_dec_ref(v___x_3376_);
lean_dec_ref(v___x_3372_);
lean_dec_ref(v_body_3368_);
v___x_3378_ = lean_box(0);
v___x_3379_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(v___f_3360_, v_a_3332_, v___x_3378_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_);
v___y_3339_ = v___x_3379_;
goto v___jp_3338_;
}
else
{
lean_object* v___x_3380_; lean_object* v___x_3381_; uint8_t v___x_3382_; 
v___x_3380_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3376_);
v___x_3381_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__1));
v___x_3382_ = l_Lean_Expr_isConstOf(v___x_3380_, v___x_3381_);
lean_dec_ref(v___x_3380_);
if (v___x_3382_ == 0)
{
lean_object* v___x_3383_; lean_object* v___x_3384_; 
lean_dec_ref(v___x_3376_);
lean_dec_ref(v___x_3372_);
lean_dec_ref(v_body_3368_);
v___x_3383_ = lean_box(0);
v___x_3384_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(v___f_3360_, v_a_3332_, v___x_3383_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_);
v___y_3339_ = v___x_3384_;
goto v___jp_3338_;
}
else
{
lean_object* v_arg_3385_; lean_object* v_arg_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; 
v_arg_3385_ = lean_ctor_get(v___x_3372_, 1);
lean_inc_ref(v_arg_3385_);
lean_dec_ref(v___x_3372_);
v_arg_3386_ = lean_ctor_get(v___x_3376_, 1);
lean_inc_ref(v_arg_3386_);
lean_dec_ref(v___x_3376_);
v___x_3387_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__4, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__4_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__4);
v___x_3388_ = l_Lean_mkApp3(v___x_3387_, v_arg_3386_, v_arg_3385_, v_body_3368_);
v___x_3389_ = lean_unsigned_to_nat(1u);
lean_inc(v_a_3332_);
v___x_3390_ = l_Lean_MVarId_applyN(v_a_3332_, v___x_3388_, v___x_3389_, v___x_3361_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_);
if (lean_obj_tag(v___x_3390_) == 0)
{
lean_object* v_a_3391_; 
v_a_3391_ = lean_ctor_get(v___x_3390_, 0);
lean_inc(v_a_3391_);
lean_dec_ref_known(v___x_3390_, 1);
if (lean_obj_tag(v_a_3391_) == 1)
{
lean_object* v_tail_3392_; 
v_tail_3392_ = lean_ctor_get(v_a_3391_, 1);
if (lean_obj_tag(v_tail_3392_) == 0)
{
lean_object* v_head_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; 
lean_dec(v_a_3332_);
v_head_3393_ = lean_ctor_get(v_a_3391_, 0);
lean_inc(v_head_3393_);
lean_dec_ref_known(v_a_3391_, 2);
v___x_3394_ = lean_box(0);
v___x_3395_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0(v___x_3359_, v___x_3394_, v_head_3393_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_);
v___y_3339_ = v___x_3395_;
goto v___jp_3338_;
}
else
{
lean_object* v___x_3396_; 
v___x_3396_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(v___f_3360_, v_a_3332_, v_a_3391_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_);
lean_dec_ref_known(v_a_3391_, 2);
v___y_3339_ = v___x_3396_;
goto v___jp_3338_;
}
}
else
{
lean_object* v___x_3397_; 
v___x_3397_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(v___f_3360_, v_a_3332_, v_a_3391_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_);
lean_dec(v_a_3391_);
v___y_3339_ = v___x_3397_;
goto v___jp_3338_;
}
}
else
{
lean_object* v_a_3398_; lean_object* v___x_3400_; uint8_t v_isShared_3401_; uint8_t v_isSharedCheck_3405_; 
lean_dec(v_a_3332_);
v_a_3398_ = lean_ctor_get(v___x_3390_, 0);
v_isSharedCheck_3405_ = !lean_is_exclusive(v___x_3390_);
if (v_isSharedCheck_3405_ == 0)
{
v___x_3400_ = v___x_3390_;
v_isShared_3401_ = v_isSharedCheck_3405_;
goto v_resetjp_3399_;
}
else
{
lean_inc(v_a_3398_);
lean_dec(v___x_3390_);
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
}
}
else
{
lean_object* v_a_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3413_; 
lean_dec_ref(v_body_3368_);
lean_dec(v_a_3332_);
v_a_3406_ = lean_ctor_get(v___x_3370_, 0);
v_isSharedCheck_3413_ = !lean_is_exclusive(v___x_3370_);
if (v_isSharedCheck_3413_ == 0)
{
v___x_3408_ = v___x_3370_;
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_a_3406_);
lean_dec(v___x_3370_);
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
else
{
lean_object* v___x_3415_; 
lean_dec_ref(v_body_3368_);
lean_dec_ref(v_binderType_3367_);
if (v_isShared_3366_ == 0)
{
lean_ctor_set(v___x_3365_, 0, v_a_3332_);
v___x_3415_ = v___x_3365_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v_a_3332_);
v___x_3415_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
return v___x_3415_;
}
}
}
else
{
lean_object* v___x_3418_; 
lean_dec(v_a_3363_);
if (v_isShared_3366_ == 0)
{
lean_ctor_set(v___x_3365_, 0, v_a_3332_);
v___x_3418_ = v___x_3365_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v_a_3332_);
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
else
{
lean_object* v_a_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3428_; 
lean_dec(v_a_3332_);
v_a_3421_ = lean_ctor_get(v___x_3362_, 0);
v_isSharedCheck_3428_ = !lean_is_exclusive(v___x_3362_);
if (v_isSharedCheck_3428_ == 0)
{
v___x_3423_ = v___x_3362_;
v_isShared_3424_ = v_isSharedCheck_3428_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_a_3421_);
lean_dec(v___x_3362_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3428_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
lean_object* v___x_3426_; 
if (v_isShared_3424_ == 0)
{
v___x_3426_ = v___x_3423_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3427_; 
v_reuseFailAlloc_3427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3427_, 0, v_a_3421_);
v___x_3426_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
return v___x_3426_;
}
}
}
v___jp_3338_:
{
if (lean_obj_tag(v___y_3339_) == 0)
{
lean_object* v_a_3340_; lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3350_; 
v_a_3340_ = lean_ctor_get(v___y_3339_, 0);
v_isSharedCheck_3350_ = !lean_is_exclusive(v___y_3339_);
if (v_isSharedCheck_3350_ == 0)
{
v___x_3342_ = v___y_3339_;
v_isShared_3343_ = v_isSharedCheck_3350_;
goto v_resetjp_3341_;
}
else
{
lean_inc(v_a_3340_);
lean_dec(v___y_3339_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3350_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
if (lean_obj_tag(v_a_3340_) == 0)
{
lean_object* v_a_3344_; lean_object* v___x_3346_; 
v_a_3344_ = lean_ctor_get(v_a_3340_, 0);
lean_inc(v_a_3344_);
lean_dec_ref_known(v_a_3340_, 1);
if (v_isShared_3343_ == 0)
{
lean_ctor_set(v___x_3342_, 0, v_a_3344_);
v___x_3346_ = v___x_3342_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v_a_3344_);
v___x_3346_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
return v___x_3346_;
}
}
else
{
lean_object* v_a_3348_; 
lean_del_object(v___x_3342_);
v_a_3348_ = lean_ctor_get(v_a_3340_, 0);
lean_inc(v_a_3348_);
lean_dec_ref_known(v_a_3340_, 1);
v_a_3332_ = v_a_3348_;
goto _start;
}
}
}
else
{
lean_object* v_a_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3358_; 
v_a_3351_ = lean_ctor_get(v___y_3339_, 0);
v_isSharedCheck_3358_ = !lean_is_exclusive(v___y_3339_);
if (v_isSharedCheck_3358_ == 0)
{
v___x_3353_ = v___y_3339_;
v_isShared_3354_ = v_isSharedCheck_3358_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_a_3351_);
lean_dec(v___y_3339_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3358_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
lean_object* v___x_3356_; 
if (v_isShared_3354_ == 0)
{
v___x_3356_ = v___x_3353_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3357_; 
v_reuseFailAlloc_3357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3357_, 0, v_a_3351_);
v___x_3356_ = v_reuseFailAlloc_3357_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
return v___x_3356_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___boxed(lean_object* v_a_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_){
_start:
{
lean_object* v_res_3435_; 
v_res_3435_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg(v_a_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_);
lean_dec(v___y_3433_);
lean_dec_ref(v___y_3432_);
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
return v_res_3435_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3437_; lean_object* v___x_3438_; 
v___x_3437_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__0));
v___x_3438_ = l_Lean_stringToMessageData(v___x_3437_);
return v___x_3438_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; 
v___x_3444_ = lean_box(0);
v___x_3445_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__4));
v___x_3446_ = l_Lean_mkConst(v___x_3445_, v___x_3444_);
return v___x_3446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0(lean_object* v_ctorVal_3451_, lean_object* v_xs_3452_, lean_object* v_type_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_){
_start:
{
lean_object* v___x_3468_; lean_object* v___x_3469_; 
v___x_3468_ = lean_box(0);
v___x_3469_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_3453_, v___x_3468_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_);
if (lean_obj_tag(v___x_3469_) == 0)
{
lean_object* v_a_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; uint8_t v___x_3474_; uint8_t v___x_3475_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; 
v_a_3470_ = lean_ctor_get(v___x_3469_, 0);
lean_inc(v_a_3470_);
lean_dec_ref_known(v___x_3469_, 1);
v___x_3471_ = l_Lean_Expr_mvarId_x21(v_a_3470_);
v___x_3472_ = lean_box(0);
v___x_3473_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__5, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__5_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__5);
v___x_3474_ = 1;
v___x_3475_ = 0;
v___x_3479_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6));
v___x_3480_ = lean_box(0);
v___x_3481_ = l_Lean_MVarId_apply(v___x_3471_, v___x_3473_, v___x_3479_, v___x_3480_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_);
if (lean_obj_tag(v___x_3481_) == 0)
{
lean_object* v_a_3482_; 
v_a_3482_ = lean_ctor_get(v___x_3481_, 0);
lean_inc(v_a_3482_);
lean_dec_ref_known(v___x_3481_, 1);
if (lean_obj_tag(v_a_3482_) == 1)
{
lean_object* v_tail_3483_; 
v_tail_3483_ = lean_ctor_get(v_a_3482_, 1);
lean_inc(v_tail_3483_);
if (lean_obj_tag(v_tail_3483_) == 1)
{
lean_object* v_tail_3484_; 
v_tail_3484_ = lean_ctor_get(v_tail_3483_, 1);
if (lean_obj_tag(v_tail_3484_) == 0)
{
lean_object* v_toConstantVal_3485_; lean_object* v_head_3486_; lean_object* v_head_3487_; lean_object* v_name_3488_; lean_object* v_levelParams_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; 
v_toConstantVal_3485_ = lean_ctor_get(v_ctorVal_3451_, 0);
lean_inc_ref(v_toConstantVal_3485_);
lean_dec_ref(v_ctorVal_3451_);
v_head_3486_ = lean_ctor_get(v_a_3482_, 0);
lean_inc(v_head_3486_);
lean_dec_ref_known(v_a_3482_, 2);
v_head_3487_ = lean_ctor_get(v_tail_3483_, 0);
lean_inc(v_head_3487_);
lean_dec_ref_known(v_tail_3483_, 2);
v_name_3488_ = lean_ctor_get(v_toConstantVal_3485_, 0);
lean_inc_n(v_name_3488_, 2);
v_levelParams_3489_ = lean_ctor_get(v_toConstantVal_3485_, 1);
lean_inc(v_levelParams_3489_);
lean_dec_ref(v_toConstantVal_3485_);
v___x_3490_ = l_Lean_Meta_mkInjectiveTheoremNameFor(v_name_3488_);
v___x_3491_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(v_levelParams_3489_, v___x_3472_);
v___x_3492_ = l_Lean_mkConst(v___x_3490_, v___x_3491_);
v___x_3493_ = l_Lean_mkAppN(v___x_3492_, v_xs_3452_);
v___x_3494_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(v_head_3486_, v___x_3493_, v___y_3455_);
lean_dec_ref(v___x_3494_);
v___x_3495_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg(v_head_3487_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_);
if (lean_obj_tag(v___x_3495_) == 0)
{
lean_object* v_a_3496_; lean_object* v___x_3497_; 
v_a_3496_ = lean_ctor_get(v___x_3495_, 0);
lean_inc(v_a_3496_);
lean_dec_ref_known(v___x_3495_, 1);
v___x_3497_ = l_Lean_MVarId_refl(v_a_3496_, v___x_3474_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_);
if (lean_obj_tag(v___x_3497_) == 0)
{
lean_dec_ref_known(v___x_3497_, 1);
lean_dec(v_name_3488_);
goto v___jp_3476_;
}
else
{
lean_object* v_a_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3520_; 
lean_dec(v_a_3470_);
v_a_3498_ = lean_ctor_get(v___x_3497_, 0);
v_isSharedCheck_3520_ = !lean_is_exclusive(v___x_3497_);
if (v_isSharedCheck_3520_ == 0)
{
v___x_3500_ = v___x_3497_;
v_isShared_3501_ = v_isSharedCheck_3520_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_a_3498_);
lean_dec(v___x_3497_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3520_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
uint8_t v___x_3502_; 
v___x_3502_ = l_Lean_Exception_isInterrupt(v_a_3498_);
if (v___x_3502_ == 0)
{
uint8_t v___x_3503_; 
lean_inc(v_a_3498_);
v___x_3503_ = l_Lean_Exception_isRuntime(v_a_3498_);
if (v___x_3503_ == 0)
{
lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v_a_3506_; lean_object* v___x_3508_; uint8_t v_isShared_3509_; uint8_t v_isSharedCheck_3513_; 
lean_del_object(v___x_3500_);
lean_dec(v_a_3498_);
v___x_3504_ = l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(v_name_3488_);
v___x_3505_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_3504_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_);
v_a_3506_ = lean_ctor_get(v___x_3505_, 0);
v_isSharedCheck_3513_ = !lean_is_exclusive(v___x_3505_);
if (v_isSharedCheck_3513_ == 0)
{
v___x_3508_ = v___x_3505_;
v_isShared_3509_ = v_isSharedCheck_3513_;
goto v_resetjp_3507_;
}
else
{
lean_inc(v_a_3506_);
lean_dec(v___x_3505_);
v___x_3508_ = lean_box(0);
v_isShared_3509_ = v_isSharedCheck_3513_;
goto v_resetjp_3507_;
}
v_resetjp_3507_:
{
lean_object* v___x_3511_; 
if (v_isShared_3509_ == 0)
{
v___x_3511_ = v___x_3508_;
goto v_reusejp_3510_;
}
else
{
lean_object* v_reuseFailAlloc_3512_; 
v_reuseFailAlloc_3512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3512_, 0, v_a_3506_);
v___x_3511_ = v_reuseFailAlloc_3512_;
goto v_reusejp_3510_;
}
v_reusejp_3510_:
{
return v___x_3511_;
}
}
}
else
{
lean_object* v___x_3515_; 
lean_dec(v_name_3488_);
if (v_isShared_3501_ == 0)
{
v___x_3515_ = v___x_3500_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v_a_3498_);
v___x_3515_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
return v___x_3515_;
}
}
}
else
{
lean_object* v___x_3518_; 
lean_dec(v_name_3488_);
if (v_isShared_3501_ == 0)
{
v___x_3518_ = v___x_3500_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3519_; 
v_reuseFailAlloc_3519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3519_, 0, v_a_3498_);
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
else
{
lean_object* v_a_3521_; lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3528_; 
lean_dec(v_name_3488_);
lean_dec(v_a_3470_);
v_a_3521_ = lean_ctor_get(v___x_3495_, 0);
v_isSharedCheck_3528_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3528_ == 0)
{
v___x_3523_ = v___x_3495_;
v_isShared_3524_ = v_isSharedCheck_3528_;
goto v_resetjp_3522_;
}
else
{
lean_inc(v_a_3521_);
lean_dec(v___x_3495_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3528_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v___x_3526_; 
if (v_isShared_3524_ == 0)
{
v___x_3526_ = v___x_3523_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v_a_3521_);
v___x_3526_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
return v___x_3526_;
}
}
}
}
else
{
lean_dec_ref_known(v_tail_3483_, 2);
lean_dec_ref_known(v_a_3482_, 2);
lean_dec(v_a_3470_);
goto v___jp_3459_;
}
}
else
{
lean_dec_ref_known(v_a_3482_, 2);
lean_dec(v_tail_3483_);
lean_dec(v_a_3470_);
goto v___jp_3459_;
}
}
else
{
lean_dec(v_a_3482_);
lean_dec(v_a_3470_);
goto v___jp_3459_;
}
}
else
{
lean_object* v_a_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3536_; 
lean_dec(v_a_3470_);
lean_dec_ref(v_ctorVal_3451_);
v_a_3529_ = lean_ctor_get(v___x_3481_, 0);
v_isSharedCheck_3536_ = !lean_is_exclusive(v___x_3481_);
if (v_isSharedCheck_3536_ == 0)
{
v___x_3531_ = v___x_3481_;
v_isShared_3532_ = v_isSharedCheck_3536_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_a_3529_);
lean_dec(v___x_3481_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3536_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
lean_object* v___x_3534_; 
if (v_isShared_3532_ == 0)
{
v___x_3534_ = v___x_3531_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v_a_3529_);
v___x_3534_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
return v___x_3534_;
}
}
}
v___jp_3476_:
{
uint8_t v___x_3477_; lean_object* v___x_3478_; 
v___x_3477_ = 1;
v___x_3478_ = l_Lean_Meta_mkLambdaFVars(v_xs_3452_, v_a_3470_, v___x_3475_, v___x_3474_, v___x_3475_, v___x_3474_, v___x_3477_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_);
return v___x_3478_;
}
}
else
{
lean_dec_ref(v_ctorVal_3451_);
return v___x_3469_;
}
v___jp_3459_:
{
lean_object* v_toConstantVal_3460_; lean_object* v_name_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; 
v_toConstantVal_3460_ = lean_ctor_get(v_ctorVal_3451_, 0);
lean_inc_ref(v_toConstantVal_3460_);
lean_dec_ref(v_ctorVal_3451_);
v_name_3461_ = lean_ctor_get(v_toConstantVal_3460_, 0);
lean_inc(v_name_3461_);
lean_dec_ref(v_toConstantVal_3460_);
v___x_3462_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__1);
v___x_3463_ = l_Lean_MessageData_ofName(v_name_3461_);
v___x_3464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3464_, 0, v___x_3462_);
lean_ctor_set(v___x_3464_, 1, v___x_3463_);
v___x_3465_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_3466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3466_, 0, v___x_3464_);
lean_ctor_set(v___x_3466_, 1, v___x_3465_);
v___x_3467_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_3466_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_);
return v___x_3467_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___boxed(lean_object* v_ctorVal_3537_, lean_object* v_xs_3538_, lean_object* v_type_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_){
_start:
{
lean_object* v_res_3545_; 
v_res_3545_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0(v_ctorVal_3537_, v_xs_3538_, v_type_3539_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_);
lean_dec(v___y_3543_);
lean_dec_ref(v___y_3542_);
lean_dec(v___y_3541_);
lean_dec_ref(v___y_3540_);
lean_dec_ref(v_xs_3538_);
return v_res_3545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(lean_object* v_ctorVal_3546_, lean_object* v_targetType_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_){
_start:
{
lean_object* v___f_3553_; uint8_t v___x_3554_; lean_object* v___x_3555_; 
v___f_3553_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3553_, 0, v_ctorVal_3546_);
v___x_3554_ = 0;
v___x_3555_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_targetType_3547_, v___f_3553_, v___x_3554_, v___x_3554_, v_a_3548_, v_a_3549_, v_a_3550_, v_a_3551_);
return v___x_3555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___boxed(lean_object* v_ctorVal_3556_, lean_object* v_targetType_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_){
_start:
{
lean_object* v_res_3563_; 
v_res_3563_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3556_, v_targetType_3557_, v_a_3558_, v_a_3559_, v_a_3560_, v_a_3561_);
lean_dec(v_a_3561_);
lean_dec_ref(v_a_3560_);
lean_dec(v_a_3559_);
lean_dec_ref(v_a_3558_);
return v_res_3563_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0(lean_object* v_mvarId_3564_, lean_object* v_val_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_){
_start:
{
lean_object* v___x_3571_; 
v___x_3571_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(v_mvarId_3564_, v_val_3565_, v___y_3567_);
return v___x_3571_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___boxed(lean_object* v_mvarId_3572_, lean_object* v_val_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_){
_start:
{
lean_object* v_res_3579_; 
v_res_3579_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0(v_mvarId_3572_, v_val_3573_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_);
lean_dec(v___y_3577_);
lean_dec_ref(v___y_3576_);
lean_dec(v___y_3575_);
lean_dec_ref(v___y_3574_);
return v_res_3579_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1(lean_object* v_inst_3580_, lean_object* v_a_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_){
_start:
{
lean_object* v___x_3587_; 
v___x_3587_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg(v_a_3581_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_);
return v___x_3587_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___boxed(lean_object* v_inst_3588_, lean_object* v_a_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_){
_start:
{
lean_object* v_res_3595_; 
v_res_3595_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1(v_inst_3588_, v_a_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_);
lean_dec(v___y_3593_);
lean_dec_ref(v___y_3592_);
lean_dec(v___y_3591_);
lean_dec_ref(v___y_3590_);
return v_res_3595_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0(lean_object* v_00_u03b2_3596_, lean_object* v_x_3597_, lean_object* v_x_3598_, lean_object* v_x_3599_){
_start:
{
lean_object* v___x_3600_; 
v___x_3600_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(v_x_3597_, v_x_3598_, v_x_3599_);
return v___x_3600_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3601_, lean_object* v_x_3602_, size_t v_x_3603_, size_t v_x_3604_, lean_object* v_x_3605_, lean_object* v_x_3606_){
_start:
{
lean_object* v___x_3607_; 
v___x_3607_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_x_3602_, v_x_3603_, v_x_3604_, v_x_3605_, v_x_3606_);
return v___x_3607_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3608_, lean_object* v_x_3609_, lean_object* v_x_3610_, lean_object* v_x_3611_, lean_object* v_x_3612_, lean_object* v_x_3613_){
_start:
{
size_t v_x_5821__boxed_3614_; size_t v_x_5822__boxed_3615_; lean_object* v_res_3616_; 
v_x_5821__boxed_3614_ = lean_unbox_usize(v_x_3610_);
lean_dec(v_x_3610_);
v_x_5822__boxed_3615_ = lean_unbox_usize(v_x_3611_);
lean_dec(v_x_3611_);
v_res_3616_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1(v_00_u03b2_3608_, v_x_3609_, v_x_5821__boxed_3614_, v_x_5822__boxed_3615_, v_x_3612_, v_x_3613_);
return v_res_3616_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_3617_, lean_object* v_n_3618_, lean_object* v_k_3619_, lean_object* v_v_3620_){
_start:
{
lean_object* v___x_3621_; 
v___x_3621_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(v_n_3618_, v_k_3619_, v_v_3620_);
return v___x_3621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_3622_, size_t v_depth_3623_, lean_object* v_keys_3624_, lean_object* v_vals_3625_, lean_object* v_heq_3626_, lean_object* v_i_3627_, lean_object* v_entries_3628_){
_start:
{
lean_object* v___x_3629_; 
v___x_3629_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_3623_, v_keys_3624_, v_vals_3625_, v_i_3627_, v_entries_3628_);
return v___x_3629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_3630_, lean_object* v_depth_3631_, lean_object* v_keys_3632_, lean_object* v_vals_3633_, lean_object* v_heq_3634_, lean_object* v_i_3635_, lean_object* v_entries_3636_){
_start:
{
size_t v_depth_boxed_3637_; lean_object* v_res_3638_; 
v_depth_boxed_3637_ = lean_unbox_usize(v_depth_3631_);
lean_dec(v_depth_3631_);
v_res_3638_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_3630_, v_depth_boxed_3637_, v_keys_3632_, v_vals_3633_, v_heq_3634_, v_i_3635_, v_entries_3636_);
lean_dec_ref(v_vals_3633_);
lean_dec_ref(v_keys_3632_);
return v_res_3638_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_3639_, lean_object* v_x_3640_, lean_object* v_x_3641_, lean_object* v_x_3642_, lean_object* v_x_3643_){
_start:
{
lean_object* v___x_3644_; 
v___x_3644_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_x_3640_, v_x_3641_, v_x_3642_, v_x_3643_);
return v___x_3644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(lean_object* v_ctorVal_3645_, lean_object* v_val_3646_, lean_object* v_name_3647_, lean_object* v_levelParams_3648_, uint8_t v___x_3649_, uint8_t v_hasTrace_3650_, lean_object* v_____r_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_){
_start:
{
lean_object* v___x_3657_; 
lean_inc_ref(v_val_3646_);
v___x_3657_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3645_, v_val_3646_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_);
if (lean_obj_tag(v___x_3657_) == 0)
{
lean_object* v_a_3658_; lean_object* v___x_3659_; lean_object* v_a_3660_; lean_object* v___x_3661_; lean_object* v_a_3662_; lean_object* v___x_3664_; uint8_t v_isShared_3665_; uint8_t v_isSharedCheck_3678_; 
v_a_3658_ = lean_ctor_get(v___x_3657_, 0);
lean_inc(v_a_3658_);
lean_dec_ref_known(v___x_3657_, 1);
v___x_3659_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3646_, v___y_3653_);
v_a_3660_ = lean_ctor_get(v___x_3659_, 0);
lean_inc(v_a_3660_);
lean_dec_ref(v___x_3659_);
v___x_3661_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3658_, v___y_3653_);
v_a_3662_ = lean_ctor_get(v___x_3661_, 0);
v_isSharedCheck_3678_ = !lean_is_exclusive(v___x_3661_);
if (v_isSharedCheck_3678_ == 0)
{
v___x_3664_ = v___x_3661_;
v_isShared_3665_ = v_isSharedCheck_3678_;
goto v_resetjp_3663_;
}
else
{
lean_inc(v_a_3662_);
lean_dec(v___x_3661_);
v___x_3664_ = lean_box(0);
v_isShared_3665_ = v_isSharedCheck_3678_;
goto v_resetjp_3663_;
}
v_resetjp_3663_:
{
lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3671_; 
lean_inc_n(v_name_3647_, 2);
v___x_3666_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3666_, 0, v_name_3647_);
lean_ctor_set(v___x_3666_, 1, v_levelParams_3648_);
lean_ctor_set(v___x_3666_, 2, v_a_3660_);
v___x_3667_ = lean_box(0);
v___x_3668_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3668_, 0, v_name_3647_);
lean_ctor_set(v___x_3668_, 1, v___x_3667_);
v___x_3669_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3669_, 0, v___x_3666_);
lean_ctor_set(v___x_3669_, 1, v_a_3662_);
lean_ctor_set(v___x_3669_, 2, v___x_3668_);
if (v_isShared_3665_ == 0)
{
lean_ctor_set_tag(v___x_3664_, 2);
lean_ctor_set(v___x_3664_, 0, v___x_3669_);
v___x_3671_ = v___x_3664_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3677_; 
v_reuseFailAlloc_3677_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3677_, 0, v___x_3669_);
v___x_3671_ = v_reuseFailAlloc_3677_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
lean_object* v___x_3672_; 
v___x_3672_ = l_Lean_addDecl(v___x_3671_, v___x_3649_, v___y_3654_, v___y_3655_);
if (lean_obj_tag(v___x_3672_) == 0)
{
lean_object* v___x_3673_; uint8_t v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; 
lean_dec_ref_known(v___x_3672_, 1);
v___x_3673_ = l_Lean_Meta_simpExtension;
v___x_3674_ = 0;
v___x_3675_ = lean_unsigned_to_nat(1000u);
v___x_3676_ = l_Lean_Meta_addSimpTheorem(v___x_3673_, v_name_3647_, v_hasTrace_3650_, v___x_3649_, v___x_3674_, v___x_3675_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_);
return v___x_3676_;
}
else
{
lean_dec(v_name_3647_);
return v___x_3672_;
}
}
}
}
else
{
lean_object* v_a_3679_; lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3686_; 
lean_dec(v_levelParams_3648_);
lean_dec(v_name_3647_);
lean_dec_ref(v_val_3646_);
v_a_3679_ = lean_ctor_get(v___x_3657_, 0);
v_isSharedCheck_3686_ = !lean_is_exclusive(v___x_3657_);
if (v_isSharedCheck_3686_ == 0)
{
v___x_3681_ = v___x_3657_;
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
else
{
lean_inc(v_a_3679_);
lean_dec(v___x_3657_);
v___x_3681_ = lean_box(0);
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
v_resetjp_3680_:
{
lean_object* v___x_3684_; 
if (v_isShared_3682_ == 0)
{
v___x_3684_ = v___x_3681_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v_a_3679_);
v___x_3684_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
return v___x_3684_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1___boxed(lean_object* v_ctorVal_3687_, lean_object* v_val_3688_, lean_object* v_name_3689_, lean_object* v_levelParams_3690_, lean_object* v___x_3691_, lean_object* v_hasTrace_3692_, lean_object* v_____r_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_){
_start:
{
uint8_t v___x_8728__boxed_3699_; uint8_t v_hasTrace_boxed_3700_; lean_object* v_res_3701_; 
v___x_8728__boxed_3699_ = lean_unbox(v___x_3691_);
v_hasTrace_boxed_3700_ = lean_unbox(v_hasTrace_3692_);
v_res_3701_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(v_ctorVal_3687_, v_val_3688_, v_name_3689_, v_levelParams_3690_, v___x_8728__boxed_3699_, v_hasTrace_boxed_3700_, v_____r_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_);
lean_dec(v___y_3697_);
lean_dec_ref(v___y_3696_);
lean_dec(v___y_3695_);
lean_dec_ref(v___y_3694_);
return v_res_3701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(lean_object* v_ctorVal_3702_, lean_object* v_val_3703_, lean_object* v_name_3704_, lean_object* v_levelParams_3705_, uint8_t v___x_3706_, lean_object* v_____r_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_){
_start:
{
lean_object* v___x_3713_; 
lean_inc_ref(v_val_3703_);
v___x_3713_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3702_, v_val_3703_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_);
if (lean_obj_tag(v___x_3713_) == 0)
{
lean_object* v_a_3714_; lean_object* v___x_3715_; lean_object* v_a_3716_; lean_object* v___x_3717_; lean_object* v_a_3718_; lean_object* v___x_3720_; uint8_t v_isShared_3721_; uint8_t v_isSharedCheck_3735_; 
v_a_3714_ = lean_ctor_get(v___x_3713_, 0);
lean_inc(v_a_3714_);
lean_dec_ref_known(v___x_3713_, 1);
v___x_3715_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3703_, v___y_3709_);
v_a_3716_ = lean_ctor_get(v___x_3715_, 0);
lean_inc(v_a_3716_);
lean_dec_ref(v___x_3715_);
v___x_3717_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3714_, v___y_3709_);
v_a_3718_ = lean_ctor_get(v___x_3717_, 0);
v_isSharedCheck_3735_ = !lean_is_exclusive(v___x_3717_);
if (v_isSharedCheck_3735_ == 0)
{
v___x_3720_ = v___x_3717_;
v_isShared_3721_ = v_isSharedCheck_3735_;
goto v_resetjp_3719_;
}
else
{
lean_inc(v_a_3718_);
lean_dec(v___x_3717_);
v___x_3720_ = lean_box(0);
v_isShared_3721_ = v_isSharedCheck_3735_;
goto v_resetjp_3719_;
}
v_resetjp_3719_:
{
lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3727_; 
lean_inc_n(v_name_3704_, 2);
v___x_3722_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3722_, 0, v_name_3704_);
lean_ctor_set(v___x_3722_, 1, v_levelParams_3705_);
lean_ctor_set(v___x_3722_, 2, v_a_3716_);
v___x_3723_ = lean_box(0);
v___x_3724_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3724_, 0, v_name_3704_);
lean_ctor_set(v___x_3724_, 1, v___x_3723_);
v___x_3725_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3725_, 0, v___x_3722_);
lean_ctor_set(v___x_3725_, 1, v_a_3718_);
lean_ctor_set(v___x_3725_, 2, v___x_3724_);
if (v_isShared_3721_ == 0)
{
lean_ctor_set_tag(v___x_3720_, 2);
lean_ctor_set(v___x_3720_, 0, v___x_3725_);
v___x_3727_ = v___x_3720_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v___x_3725_);
v___x_3727_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
uint8_t v___x_3728_; lean_object* v___x_3729_; 
v___x_3728_ = 0;
v___x_3729_ = l_Lean_addDecl(v___x_3727_, v___x_3728_, v___y_3710_, v___y_3711_);
if (lean_obj_tag(v___x_3729_) == 0)
{
lean_object* v___x_3730_; uint8_t v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; 
lean_dec_ref_known(v___x_3729_, 1);
v___x_3730_ = l_Lean_Meta_simpExtension;
v___x_3731_ = 0;
v___x_3732_ = lean_unsigned_to_nat(1000u);
v___x_3733_ = l_Lean_Meta_addSimpTheorem(v___x_3730_, v_name_3704_, v___x_3706_, v___x_3728_, v___x_3731_, v___x_3732_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_);
return v___x_3733_;
}
else
{
lean_dec(v_name_3704_);
return v___x_3729_;
}
}
}
}
else
{
lean_object* v_a_3736_; lean_object* v___x_3738_; uint8_t v_isShared_3739_; uint8_t v_isSharedCheck_3743_; 
lean_dec(v_levelParams_3705_);
lean_dec(v_name_3704_);
lean_dec_ref(v_val_3703_);
v_a_3736_ = lean_ctor_get(v___x_3713_, 0);
v_isSharedCheck_3743_ = !lean_is_exclusive(v___x_3713_);
if (v_isSharedCheck_3743_ == 0)
{
v___x_3738_ = v___x_3713_;
v_isShared_3739_ = v_isSharedCheck_3743_;
goto v_resetjp_3737_;
}
else
{
lean_inc(v_a_3736_);
lean_dec(v___x_3713_);
v___x_3738_ = lean_box(0);
v_isShared_3739_ = v_isSharedCheck_3743_;
goto v_resetjp_3737_;
}
v_resetjp_3737_:
{
lean_object* v___x_3741_; 
if (v_isShared_3739_ == 0)
{
v___x_3741_ = v___x_3738_;
goto v_reusejp_3740_;
}
else
{
lean_object* v_reuseFailAlloc_3742_; 
v_reuseFailAlloc_3742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3742_, 0, v_a_3736_);
v___x_3741_ = v_reuseFailAlloc_3742_;
goto v_reusejp_3740_;
}
v_reusejp_3740_:
{
return v___x_3741_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0___boxed(lean_object* v_ctorVal_3744_, lean_object* v_val_3745_, lean_object* v_name_3746_, lean_object* v_levelParams_3747_, lean_object* v___x_3748_, lean_object* v_____r_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_){
_start:
{
uint8_t v___x_8816__boxed_3755_; lean_object* v_res_3756_; 
v___x_8816__boxed_3755_ = lean_unbox(v___x_3748_);
v_res_3756_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(v_ctorVal_3744_, v_val_3745_, v_name_3746_, v_levelParams_3747_, v___x_8816__boxed_3755_, v_____r_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_);
lean_dec(v___y_3753_);
lean_dec_ref(v___y_3752_);
lean_dec(v___y_3751_);
lean_dec_ref(v___y_3750_);
return v_res_3756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(lean_object* v_ctorVal_3757_, lean_object* v_a_3758_, lean_object* v_a_3759_, lean_object* v_a_3760_, lean_object* v_a_3761_){
_start:
{
lean_object* v_toConstantVal_3763_; lean_object* v_toCold_3764_; lean_object* v_options_3765_; lean_object* v_name_3766_; lean_object* v_levelParams_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3989_; 
v_toConstantVal_3763_ = lean_ctor_get(v_ctorVal_3757_, 0);
lean_inc_ref(v_toConstantVal_3763_);
v_toCold_3764_ = lean_ctor_get(v_a_3760_, 0);
v_options_3765_ = lean_ctor_get(v_toCold_3764_, 2);
v_name_3766_ = lean_ctor_get(v_toConstantVal_3763_, 0);
v_levelParams_3767_ = lean_ctor_get(v_toConstantVal_3763_, 1);
v_isSharedCheck_3989_ = !lean_is_exclusive(v_toConstantVal_3763_);
if (v_isSharedCheck_3989_ == 0)
{
lean_object* v_unused_3990_; 
v_unused_3990_ = lean_ctor_get(v_toConstantVal_3763_, 2);
lean_dec(v_unused_3990_);
v___x_3769_ = v_toConstantVal_3763_;
v_isShared_3770_ = v_isSharedCheck_3989_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_levelParams_3767_);
lean_inc(v_name_3766_);
lean_dec(v_toConstantVal_3763_);
v___x_3769_ = lean_box(0);
v_isShared_3770_ = v_isSharedCheck_3989_;
goto v_resetjp_3768_;
}
v_resetjp_3768_:
{
lean_object* v_inheritedTraceOptions_3771_; uint8_t v_hasTrace_3772_; lean_object* v_name_3773_; 
v_inheritedTraceOptions_3771_ = lean_ctor_get(v_toCold_3764_, 11);
v_hasTrace_3772_ = lean_ctor_get_uint8(v_options_3765_, sizeof(void*)*1);
v_name_3773_ = l_Lean_Meta_mkInjectiveEqTheoremNameFor(v_name_3766_);
if (v_hasTrace_3772_ == 0)
{
lean_object* v___x_3774_; 
lean_inc_ref(v_ctorVal_3757_);
v___x_3774_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3757_, v_a_3758_, v_a_3759_, v_a_3760_, v_a_3761_);
if (lean_obj_tag(v___x_3774_) == 0)
{
lean_object* v_a_3775_; lean_object* v___x_3777_; uint8_t v_isShared_3778_; uint8_t v_isSharedCheck_3817_; 
v_a_3775_ = lean_ctor_get(v___x_3774_, 0);
v_isSharedCheck_3817_ = !lean_is_exclusive(v___x_3774_);
if (v_isSharedCheck_3817_ == 0)
{
v___x_3777_ = v___x_3774_;
v_isShared_3778_ = v_isSharedCheck_3817_;
goto v_resetjp_3776_;
}
else
{
lean_inc(v_a_3775_);
lean_dec(v___x_3774_);
v___x_3777_ = lean_box(0);
v_isShared_3778_ = v_isSharedCheck_3817_;
goto v_resetjp_3776_;
}
v_resetjp_3776_:
{
if (lean_obj_tag(v_a_3775_) == 1)
{
lean_object* v_val_3779_; lean_object* v___x_3780_; 
lean_del_object(v___x_3777_);
v_val_3779_ = lean_ctor_get(v_a_3775_, 0);
lean_inc_n(v_val_3779_, 2);
lean_dec_ref_known(v_a_3775_, 1);
v___x_3780_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3757_, v_val_3779_, v_a_3758_, v_a_3759_, v_a_3760_, v_a_3761_);
if (lean_obj_tag(v___x_3780_) == 0)
{
lean_object* v_a_3781_; lean_object* v___x_3782_; lean_object* v_a_3783_; lean_object* v___x_3784_; lean_object* v_a_3785_; lean_object* v___x_3787_; uint8_t v_isShared_3788_; uint8_t v_isSharedCheck_3804_; 
v_a_3781_ = lean_ctor_get(v___x_3780_, 0);
lean_inc(v_a_3781_);
lean_dec_ref_known(v___x_3780_, 1);
v___x_3782_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3779_, v_a_3759_);
v_a_3783_ = lean_ctor_get(v___x_3782_, 0);
lean_inc(v_a_3783_);
lean_dec_ref(v___x_3782_);
v___x_3784_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3781_, v_a_3759_);
v_a_3785_ = lean_ctor_get(v___x_3784_, 0);
v_isSharedCheck_3804_ = !lean_is_exclusive(v___x_3784_);
if (v_isSharedCheck_3804_ == 0)
{
v___x_3787_ = v___x_3784_;
v_isShared_3788_ = v_isSharedCheck_3804_;
goto v_resetjp_3786_;
}
else
{
lean_inc(v_a_3785_);
lean_dec(v___x_3784_);
v___x_3787_ = lean_box(0);
v_isShared_3788_ = v_isSharedCheck_3804_;
goto v_resetjp_3786_;
}
v_resetjp_3786_:
{
lean_object* v___x_3790_; 
lean_inc(v_name_3773_);
if (v_isShared_3770_ == 0)
{
lean_ctor_set(v___x_3769_, 2, v_a_3783_);
lean_ctor_set(v___x_3769_, 0, v_name_3773_);
v___x_3790_ = v___x_3769_;
goto v_reusejp_3789_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v_name_3773_);
lean_ctor_set(v_reuseFailAlloc_3803_, 1, v_levelParams_3767_);
lean_ctor_set(v_reuseFailAlloc_3803_, 2, v_a_3783_);
v___x_3790_ = v_reuseFailAlloc_3803_;
goto v_reusejp_3789_;
}
v_reusejp_3789_:
{
lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3795_; 
v___x_3791_ = lean_box(0);
lean_inc(v_name_3773_);
v___x_3792_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3792_, 0, v_name_3773_);
lean_ctor_set(v___x_3792_, 1, v___x_3791_);
v___x_3793_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3793_, 0, v___x_3790_);
lean_ctor_set(v___x_3793_, 1, v_a_3785_);
lean_ctor_set(v___x_3793_, 2, v___x_3792_);
if (v_isShared_3788_ == 0)
{
lean_ctor_set_tag(v___x_3787_, 2);
lean_ctor_set(v___x_3787_, 0, v___x_3793_);
v___x_3795_ = v___x_3787_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3802_; 
v_reuseFailAlloc_3802_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3802_, 0, v___x_3793_);
v___x_3795_ = v_reuseFailAlloc_3802_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
lean_object* v___x_3796_; 
v___x_3796_ = l_Lean_addDecl(v___x_3795_, v_hasTrace_3772_, v_a_3760_, v_a_3761_);
if (lean_obj_tag(v___x_3796_) == 0)
{
lean_object* v___x_3797_; uint8_t v___x_3798_; uint8_t v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; 
lean_dec_ref_known(v___x_3796_, 1);
v___x_3797_ = l_Lean_Meta_simpExtension;
v___x_3798_ = 1;
v___x_3799_ = 0;
v___x_3800_ = lean_unsigned_to_nat(1000u);
v___x_3801_ = l_Lean_Meta_addSimpTheorem(v___x_3797_, v_name_3773_, v___x_3798_, v_hasTrace_3772_, v___x_3799_, v___x_3800_, v_a_3758_, v_a_3759_, v_a_3760_, v_a_3761_);
return v___x_3801_;
}
else
{
lean_dec(v_name_3773_);
return v___x_3796_;
}
}
}
}
}
else
{
lean_object* v_a_3805_; lean_object* v___x_3807_; uint8_t v_isShared_3808_; uint8_t v_isSharedCheck_3812_; 
lean_dec(v_val_3779_);
lean_dec(v_name_3773_);
lean_del_object(v___x_3769_);
lean_dec(v_levelParams_3767_);
v_a_3805_ = lean_ctor_get(v___x_3780_, 0);
v_isSharedCheck_3812_ = !lean_is_exclusive(v___x_3780_);
if (v_isSharedCheck_3812_ == 0)
{
v___x_3807_ = v___x_3780_;
v_isShared_3808_ = v_isSharedCheck_3812_;
goto v_resetjp_3806_;
}
else
{
lean_inc(v_a_3805_);
lean_dec(v___x_3780_);
v___x_3807_ = lean_box(0);
v_isShared_3808_ = v_isSharedCheck_3812_;
goto v_resetjp_3806_;
}
v_resetjp_3806_:
{
lean_object* v___x_3810_; 
if (v_isShared_3808_ == 0)
{
v___x_3810_ = v___x_3807_;
goto v_reusejp_3809_;
}
else
{
lean_object* v_reuseFailAlloc_3811_; 
v_reuseFailAlloc_3811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3811_, 0, v_a_3805_);
v___x_3810_ = v_reuseFailAlloc_3811_;
goto v_reusejp_3809_;
}
v_reusejp_3809_:
{
return v___x_3810_;
}
}
}
}
else
{
lean_object* v___x_3813_; lean_object* v___x_3815_; 
lean_dec(v_a_3775_);
lean_dec(v_name_3773_);
lean_del_object(v___x_3769_);
lean_dec(v_levelParams_3767_);
lean_dec_ref(v_ctorVal_3757_);
v___x_3813_ = lean_box(0);
if (v_isShared_3778_ == 0)
{
lean_ctor_set(v___x_3777_, 0, v___x_3813_);
v___x_3815_ = v___x_3777_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v___x_3813_);
v___x_3815_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3814_;
}
v_reusejp_3814_:
{
return v___x_3815_;
}
}
}
}
else
{
lean_object* v_a_3818_; lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3825_; 
lean_dec(v_name_3773_);
lean_del_object(v___x_3769_);
lean_dec(v_levelParams_3767_);
lean_dec_ref(v_ctorVal_3757_);
v_a_3818_ = lean_ctor_get(v___x_3774_, 0);
v_isSharedCheck_3825_ = !lean_is_exclusive(v___x_3774_);
if (v_isSharedCheck_3825_ == 0)
{
v___x_3820_ = v___x_3774_;
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
else
{
lean_inc(v_a_3818_);
lean_dec(v___x_3774_);
v___x_3820_ = lean_box(0);
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
v_resetjp_3819_:
{
lean_object* v___x_3823_; 
if (v_isShared_3821_ == 0)
{
v___x_3823_ = v___x_3820_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v_a_3818_);
v___x_3823_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
return v___x_3823_;
}
}
}
}
else
{
lean_object* v___f_3826_; lean_object* v_cls_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; uint8_t v___x_3830_; lean_object* v___y_3832_; lean_object* v___y_3833_; lean_object* v_a_3834_; lean_object* v___y_3844_; lean_object* v___y_3845_; lean_object* v_a_3846_; lean_object* v___y_3849_; lean_object* v___y_3850_; lean_object* v_a_3851_; lean_object* v___y_3854_; lean_object* v___y_3855_; lean_object* v___y_3856_; lean_object* v___y_3860_; lean_object* v___y_3861_; lean_object* v_a_3862_; lean_object* v___y_3875_; lean_object* v___y_3876_; lean_object* v_a_3877_; lean_object* v___y_3880_; lean_object* v___y_3881_; lean_object* v_a_3882_; lean_object* v___y_3885_; lean_object* v___y_3886_; lean_object* v___y_3887_; 
lean_inc(v_name_3773_);
v___f_3826_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3826_, 0, v_name_3773_);
v_cls_3827_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_3828_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_3829_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_3830_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3771_, v_options_3765_, v___x_3829_);
if (v___x_3830_ == 0)
{
lean_object* v___x_3927_; uint8_t v___x_3928_; 
v___x_3927_ = l_Lean_trace_profiler;
v___x_3928_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_3765_, v___x_3927_);
if (v___x_3928_ == 0)
{
lean_object* v___x_3929_; 
lean_dec_ref(v___f_3826_);
lean_inc_ref(v_ctorVal_3757_);
v___x_3929_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3757_, v_a_3758_, v_a_3759_, v_a_3760_, v_a_3761_);
if (lean_obj_tag(v___x_3929_) == 0)
{
lean_object* v_a_3930_; lean_object* v___x_3932_; uint8_t v_isShared_3933_; uint8_t v_isSharedCheck_3980_; 
v_a_3930_ = lean_ctor_get(v___x_3929_, 0);
v_isSharedCheck_3980_ = !lean_is_exclusive(v___x_3929_);
if (v_isSharedCheck_3980_ == 0)
{
v___x_3932_ = v___x_3929_;
v_isShared_3933_ = v_isSharedCheck_3980_;
goto v_resetjp_3931_;
}
else
{
lean_inc(v_a_3930_);
lean_dec(v___x_3929_);
v___x_3932_ = lean_box(0);
v_isShared_3933_ = v_isSharedCheck_3980_;
goto v_resetjp_3931_;
}
v_resetjp_3931_:
{
if (lean_obj_tag(v_a_3930_) == 1)
{
lean_object* v_val_3934_; lean_object* v___y_3936_; lean_object* v___y_3937_; lean_object* v___y_3938_; lean_object* v___y_3939_; 
lean_del_object(v___x_3932_);
v_val_3934_ = lean_ctor_get(v_a_3930_, 0);
lean_inc(v_val_3934_);
lean_dec_ref_known(v_a_3930_, 1);
if (v___x_3830_ == 0)
{
v___y_3936_ = v_a_3758_;
v___y_3937_ = v_a_3759_;
v___y_3938_ = v_a_3760_;
v___y_3939_ = v_a_3761_;
goto v___jp_3935_;
}
else
{
lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; 
v___x_3972_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
lean_inc(v_val_3934_);
v___x_3973_ = l_Lean_MessageData_ofExpr(v_val_3934_);
v___x_3974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3974_, 0, v___x_3972_);
lean_ctor_set(v___x_3974_, 1, v___x_3973_);
v___x_3975_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_3827_, v___x_3974_, v_a_3758_, v_a_3759_, v_a_3760_, v_a_3761_);
if (lean_obj_tag(v___x_3975_) == 0)
{
lean_dec_ref_known(v___x_3975_, 1);
v___y_3936_ = v_a_3758_;
v___y_3937_ = v_a_3759_;
v___y_3938_ = v_a_3760_;
v___y_3939_ = v_a_3761_;
goto v___jp_3935_;
}
else
{
lean_dec(v_val_3934_);
lean_dec(v_name_3773_);
lean_del_object(v___x_3769_);
lean_dec(v_levelParams_3767_);
lean_dec_ref(v_ctorVal_3757_);
return v___x_3975_;
}
}
v___jp_3935_:
{
lean_object* v___x_3940_; 
lean_inc(v_val_3934_);
v___x_3940_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3757_, v_val_3934_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_);
if (lean_obj_tag(v___x_3940_) == 0)
{
lean_object* v_a_3941_; lean_object* v___x_3942_; lean_object* v_a_3943_; lean_object* v___x_3944_; lean_object* v_a_3945_; lean_object* v___x_3947_; uint8_t v_isShared_3948_; uint8_t v_isSharedCheck_3963_; 
v_a_3941_ = lean_ctor_get(v___x_3940_, 0);
lean_inc(v_a_3941_);
lean_dec_ref_known(v___x_3940_, 1);
v___x_3942_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3934_, v___y_3937_);
v_a_3943_ = lean_ctor_get(v___x_3942_, 0);
lean_inc(v_a_3943_);
lean_dec_ref(v___x_3942_);
v___x_3944_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3941_, v___y_3937_);
v_a_3945_ = lean_ctor_get(v___x_3944_, 0);
v_isSharedCheck_3963_ = !lean_is_exclusive(v___x_3944_);
if (v_isSharedCheck_3963_ == 0)
{
v___x_3947_ = v___x_3944_;
v_isShared_3948_ = v_isSharedCheck_3963_;
goto v_resetjp_3946_;
}
else
{
lean_inc(v_a_3945_);
lean_dec(v___x_3944_);
v___x_3947_ = lean_box(0);
v_isShared_3948_ = v_isSharedCheck_3963_;
goto v_resetjp_3946_;
}
v_resetjp_3946_:
{
lean_object* v___x_3950_; 
lean_inc(v_name_3773_);
if (v_isShared_3770_ == 0)
{
lean_ctor_set(v___x_3769_, 2, v_a_3943_);
lean_ctor_set(v___x_3769_, 0, v_name_3773_);
v___x_3950_ = v___x_3769_;
goto v_reusejp_3949_;
}
else
{
lean_object* v_reuseFailAlloc_3962_; 
v_reuseFailAlloc_3962_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3962_, 0, v_name_3773_);
lean_ctor_set(v_reuseFailAlloc_3962_, 1, v_levelParams_3767_);
lean_ctor_set(v_reuseFailAlloc_3962_, 2, v_a_3943_);
v___x_3950_ = v_reuseFailAlloc_3962_;
goto v_reusejp_3949_;
}
v_reusejp_3949_:
{
lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3955_; 
v___x_3951_ = lean_box(0);
lean_inc(v_name_3773_);
v___x_3952_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3952_, 0, v_name_3773_);
lean_ctor_set(v___x_3952_, 1, v___x_3951_);
v___x_3953_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3953_, 0, v___x_3950_);
lean_ctor_set(v___x_3953_, 1, v_a_3945_);
lean_ctor_set(v___x_3953_, 2, v___x_3952_);
if (v_isShared_3948_ == 0)
{
lean_ctor_set_tag(v___x_3947_, 2);
lean_ctor_set(v___x_3947_, 0, v___x_3953_);
v___x_3955_ = v___x_3947_;
goto v_reusejp_3954_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v___x_3953_);
v___x_3955_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3954_;
}
v_reusejp_3954_:
{
lean_object* v___x_3956_; 
v___x_3956_ = l_Lean_addDecl(v___x_3955_, v___x_3928_, v___y_3938_, v___y_3939_);
if (lean_obj_tag(v___x_3956_) == 0)
{
lean_object* v___x_3957_; uint8_t v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; 
lean_dec_ref_known(v___x_3956_, 1);
v___x_3957_ = l_Lean_Meta_simpExtension;
v___x_3958_ = 0;
v___x_3959_ = lean_unsigned_to_nat(1000u);
v___x_3960_ = l_Lean_Meta_addSimpTheorem(v___x_3957_, v_name_3773_, v_hasTrace_3772_, v___x_3928_, v___x_3958_, v___x_3959_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_);
return v___x_3960_;
}
else
{
lean_dec(v_name_3773_);
return v___x_3956_;
}
}
}
}
}
else
{
lean_object* v_a_3964_; lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_3971_; 
lean_dec(v_val_3934_);
lean_dec(v_name_3773_);
lean_del_object(v___x_3769_);
lean_dec(v_levelParams_3767_);
v_a_3964_ = lean_ctor_get(v___x_3940_, 0);
v_isSharedCheck_3971_ = !lean_is_exclusive(v___x_3940_);
if (v_isSharedCheck_3971_ == 0)
{
v___x_3966_ = v___x_3940_;
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
else
{
lean_inc(v_a_3964_);
lean_dec(v___x_3940_);
v___x_3966_ = lean_box(0);
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
v_resetjp_3965_:
{
lean_object* v___x_3969_; 
if (v_isShared_3967_ == 0)
{
v___x_3969_ = v___x_3966_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v_a_3964_);
v___x_3969_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
return v___x_3969_;
}
}
}
}
}
else
{
lean_object* v___x_3976_; lean_object* v___x_3978_; 
lean_dec(v_a_3930_);
lean_dec(v_name_3773_);
lean_del_object(v___x_3769_);
lean_dec(v_levelParams_3767_);
lean_dec_ref(v_ctorVal_3757_);
v___x_3976_ = lean_box(0);
if (v_isShared_3933_ == 0)
{
lean_ctor_set(v___x_3932_, 0, v___x_3976_);
v___x_3978_ = v___x_3932_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v___x_3976_);
v___x_3978_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
return v___x_3978_;
}
}
}
}
else
{
lean_object* v_a_3981_; lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_3988_; 
lean_dec(v_name_3773_);
lean_del_object(v___x_3769_);
lean_dec(v_levelParams_3767_);
lean_dec_ref(v_ctorVal_3757_);
v_a_3981_ = lean_ctor_get(v___x_3929_, 0);
v_isSharedCheck_3988_ = !lean_is_exclusive(v___x_3929_);
if (v_isSharedCheck_3988_ == 0)
{
v___x_3983_ = v___x_3929_;
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
else
{
lean_inc(v_a_3981_);
lean_dec(v___x_3929_);
v___x_3983_ = lean_box(0);
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
v_resetjp_3982_:
{
lean_object* v___x_3986_; 
if (v_isShared_3984_ == 0)
{
v___x_3986_ = v___x_3983_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v_a_3981_);
v___x_3986_ = v_reuseFailAlloc_3987_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
return v___x_3986_;
}
}
}
}
else
{
lean_del_object(v___x_3769_);
goto v___jp_3890_;
}
}
else
{
lean_del_object(v___x_3769_);
goto v___jp_3890_;
}
v___jp_3831_:
{
lean_object* v___x_3835_; double v___x_3836_; double v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; 
v___x_3835_ = lean_io_get_num_heartbeats();
v___x_3836_ = lean_float_of_nat(v___y_3832_);
v___x_3837_ = lean_float_of_nat(v___x_3835_);
v___x_3838_ = lean_box_float(v___x_3836_);
v___x_3839_ = lean_box_float(v___x_3837_);
v___x_3840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3840_, 0, v___x_3838_);
lean_ctor_set(v___x_3840_, 1, v___x_3839_);
v___x_3841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3841_, 0, v_a_3834_);
lean_ctor_set(v___x_3841_, 1, v___x_3840_);
v___x_3842_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_3827_, v_hasTrace_3772_, v___x_3828_, v_options_3765_, v___x_3830_, v___y_3833_, v___f_3826_, v___x_3841_, v_a_3758_, v_a_3759_, v_a_3760_, v_a_3761_);
return v___x_3842_;
}
v___jp_3843_:
{
lean_object* v___x_3847_; 
v___x_3847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3847_, 0, v_a_3846_);
v___y_3832_ = v___y_3844_;
v___y_3833_ = v___y_3845_;
v_a_3834_ = v___x_3847_;
goto v___jp_3831_;
}
v___jp_3848_:
{
lean_object* v___x_3852_; 
v___x_3852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3852_, 0, v_a_3851_);
v___y_3832_ = v___y_3849_;
v___y_3833_ = v___y_3850_;
v_a_3834_ = v___x_3852_;
goto v___jp_3831_;
}
v___jp_3853_:
{
if (lean_obj_tag(v___y_3856_) == 0)
{
lean_object* v_a_3857_; 
v_a_3857_ = lean_ctor_get(v___y_3856_, 0);
lean_inc(v_a_3857_);
lean_dec_ref_known(v___y_3856_, 1);
v___y_3849_ = v___y_3854_;
v___y_3850_ = v___y_3855_;
v_a_3851_ = v_a_3857_;
goto v___jp_3848_;
}
else
{
lean_object* v_a_3858_; 
v_a_3858_ = lean_ctor_get(v___y_3856_, 0);
lean_inc(v_a_3858_);
lean_dec_ref_known(v___y_3856_, 1);
v___y_3844_ = v___y_3854_;
v___y_3845_ = v___y_3855_;
v_a_3846_ = v_a_3858_;
goto v___jp_3843_;
}
}
v___jp_3859_:
{
lean_object* v___x_3863_; double v___x_3864_; double v___x_3865_; double v___x_3866_; double v___x_3867_; double v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; 
v___x_3863_ = lean_io_mono_nanos_now();
v___x_3864_ = lean_float_of_nat(v___y_3861_);
v___x_3865_ = lean_float_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0);
v___x_3866_ = lean_float_div(v___x_3864_, v___x_3865_);
v___x_3867_ = lean_float_of_nat(v___x_3863_);
v___x_3868_ = lean_float_div(v___x_3867_, v___x_3865_);
v___x_3869_ = lean_box_float(v___x_3866_);
v___x_3870_ = lean_box_float(v___x_3868_);
v___x_3871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3871_, 0, v___x_3869_);
lean_ctor_set(v___x_3871_, 1, v___x_3870_);
v___x_3872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3872_, 0, v_a_3862_);
lean_ctor_set(v___x_3872_, 1, v___x_3871_);
v___x_3873_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_3827_, v_hasTrace_3772_, v___x_3828_, v_options_3765_, v___x_3830_, v___y_3860_, v___f_3826_, v___x_3872_, v_a_3758_, v_a_3759_, v_a_3760_, v_a_3761_);
return v___x_3873_;
}
v___jp_3874_:
{
lean_object* v___x_3878_; 
v___x_3878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3878_, 0, v_a_3877_);
v___y_3860_ = v___y_3875_;
v___y_3861_ = v___y_3876_;
v_a_3862_ = v___x_3878_;
goto v___jp_3859_;
}
v___jp_3879_:
{
lean_object* v___x_3883_; 
v___x_3883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3883_, 0, v_a_3882_);
v___y_3860_ = v___y_3880_;
v___y_3861_ = v___y_3881_;
v_a_3862_ = v___x_3883_;
goto v___jp_3859_;
}
v___jp_3884_:
{
if (lean_obj_tag(v___y_3887_) == 0)
{
lean_object* v_a_3888_; 
v_a_3888_ = lean_ctor_get(v___y_3887_, 0);
lean_inc(v_a_3888_);
lean_dec_ref_known(v___y_3887_, 1);
v___y_3875_ = v___y_3885_;
v___y_3876_ = v___y_3886_;
v_a_3877_ = v_a_3888_;
goto v___jp_3874_;
}
else
{
lean_object* v_a_3889_; 
v_a_3889_ = lean_ctor_get(v___y_3887_, 0);
lean_inc(v_a_3889_);
lean_dec_ref_known(v___y_3887_, 1);
v___y_3880_ = v___y_3885_;
v___y_3881_ = v___y_3886_;
v_a_3882_ = v_a_3889_;
goto v___jp_3879_;
}
}
v___jp_3890_:
{
lean_object* v___x_3891_; lean_object* v_a_3892_; lean_object* v___x_3893_; uint8_t v___x_3894_; 
v___x_3891_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v_a_3761_);
v_a_3892_ = lean_ctor_get(v___x_3891_, 0);
lean_inc(v_a_3892_);
lean_dec_ref(v___x_3891_);
v___x_3893_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3894_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_3765_, v___x_3893_);
if (v___x_3894_ == 0)
{
lean_object* v___x_3895_; lean_object* v___x_3896_; 
v___x_3895_ = lean_io_mono_nanos_now();
lean_inc_ref(v_ctorVal_3757_);
v___x_3896_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3757_, v_a_3758_, v_a_3759_, v_a_3760_, v_a_3761_);
if (lean_obj_tag(v___x_3896_) == 0)
{
lean_object* v_a_3897_; 
v_a_3897_ = lean_ctor_get(v___x_3896_, 0);
lean_inc(v_a_3897_);
lean_dec_ref_known(v___x_3896_, 1);
if (lean_obj_tag(v_a_3897_) == 1)
{
if (v___x_3830_ == 0)
{
lean_object* v_val_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; 
v_val_3898_ = lean_ctor_get(v_a_3897_, 0);
lean_inc(v_val_3898_);
lean_dec_ref_known(v_a_3897_, 1);
v___x_3899_ = lean_box(0);
v___x_3900_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(v_ctorVal_3757_, v_val_3898_, v_name_3773_, v_levelParams_3767_, v___x_3894_, v_hasTrace_3772_, v___x_3899_, v_a_3758_, v_a_3759_, v_a_3760_, v_a_3761_);
v___y_3885_ = v_a_3892_;
v___y_3886_ = v___x_3895_;
v___y_3887_ = v___x_3900_;
goto v___jp_3884_;
}
else
{
lean_object* v_val_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; 
v_val_3901_ = lean_ctor_get(v_a_3897_, 0);
lean_inc_n(v_val_3901_, 2);
lean_dec_ref_known(v_a_3897_, 1);
v___x_3902_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_3903_ = l_Lean_MessageData_ofExpr(v_val_3901_);
v___x_3904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3904_, 0, v___x_3902_);
lean_ctor_set(v___x_3904_, 1, v___x_3903_);
v___x_3905_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_3827_, v___x_3904_, v_a_3758_, v_a_3759_, v_a_3760_, v_a_3761_);
if (lean_obj_tag(v___x_3905_) == 0)
{
lean_object* v_a_3906_; lean_object* v___x_3907_; 
v_a_3906_ = lean_ctor_get(v___x_3905_, 0);
lean_inc(v_a_3906_);
lean_dec_ref_known(v___x_3905_, 1);
v___x_3907_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(v_ctorVal_3757_, v_val_3901_, v_name_3773_, v_levelParams_3767_, v___x_3894_, v_hasTrace_3772_, v_a_3906_, v_a_3758_, v_a_3759_, v_a_3760_, v_a_3761_);
v___y_3885_ = v_a_3892_;
v___y_3886_ = v___x_3895_;
v___y_3887_ = v___x_3907_;
goto v___jp_3884_;
}
else
{
lean_object* v_a_3908_; 
lean_dec(v_val_3901_);
lean_dec(v_name_3773_);
lean_dec(v_levelParams_3767_);
lean_dec_ref(v_ctorVal_3757_);
v_a_3908_ = lean_ctor_get(v___x_3905_, 0);
lean_inc(v_a_3908_);
lean_dec_ref_known(v___x_3905_, 1);
v___y_3880_ = v_a_3892_;
v___y_3881_ = v___x_3895_;
v_a_3882_ = v_a_3908_;
goto v___jp_3879_;
}
}
}
else
{
lean_object* v___x_3909_; 
lean_dec(v_a_3897_);
lean_dec(v_name_3773_);
lean_dec(v_levelParams_3767_);
lean_dec_ref(v_ctorVal_3757_);
v___x_3909_ = lean_box(0);
v___y_3875_ = v_a_3892_;
v___y_3876_ = v___x_3895_;
v_a_3877_ = v___x_3909_;
goto v___jp_3874_;
}
}
else
{
lean_object* v_a_3910_; 
lean_dec(v_name_3773_);
lean_dec(v_levelParams_3767_);
lean_dec_ref(v_ctorVal_3757_);
v_a_3910_ = lean_ctor_get(v___x_3896_, 0);
lean_inc(v_a_3910_);
lean_dec_ref_known(v___x_3896_, 1);
v___y_3880_ = v_a_3892_;
v___y_3881_ = v___x_3895_;
v_a_3882_ = v_a_3910_;
goto v___jp_3879_;
}
}
else
{
lean_object* v___x_3911_; lean_object* v___x_3912_; 
v___x_3911_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_ctorVal_3757_);
v___x_3912_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3757_, v_a_3758_, v_a_3759_, v_a_3760_, v_a_3761_);
if (lean_obj_tag(v___x_3912_) == 0)
{
lean_object* v_a_3913_; 
v_a_3913_ = lean_ctor_get(v___x_3912_, 0);
lean_inc(v_a_3913_);
lean_dec_ref_known(v___x_3912_, 1);
if (lean_obj_tag(v_a_3913_) == 1)
{
if (v___x_3830_ == 0)
{
lean_object* v_val_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; 
v_val_3914_ = lean_ctor_get(v_a_3913_, 0);
lean_inc(v_val_3914_);
lean_dec_ref_known(v_a_3913_, 1);
v___x_3915_ = lean_box(0);
v___x_3916_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(v_ctorVal_3757_, v_val_3914_, v_name_3773_, v_levelParams_3767_, v___x_3894_, v___x_3915_, v_a_3758_, v_a_3759_, v_a_3760_, v_a_3761_);
v___y_3854_ = v___x_3911_;
v___y_3855_ = v_a_3892_;
v___y_3856_ = v___x_3916_;
goto v___jp_3853_;
}
else
{
lean_object* v_val_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; 
v_val_3917_ = lean_ctor_get(v_a_3913_, 0);
lean_inc_n(v_val_3917_, 2);
lean_dec_ref_known(v_a_3913_, 1);
v___x_3918_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_3919_ = l_Lean_MessageData_ofExpr(v_val_3917_);
v___x_3920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3920_, 0, v___x_3918_);
lean_ctor_set(v___x_3920_, 1, v___x_3919_);
v___x_3921_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_3827_, v___x_3920_, v_a_3758_, v_a_3759_, v_a_3760_, v_a_3761_);
if (lean_obj_tag(v___x_3921_) == 0)
{
lean_object* v_a_3922_; lean_object* v___x_3923_; 
v_a_3922_ = lean_ctor_get(v___x_3921_, 0);
lean_inc(v_a_3922_);
lean_dec_ref_known(v___x_3921_, 1);
v___x_3923_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(v_ctorVal_3757_, v_val_3917_, v_name_3773_, v_levelParams_3767_, v___x_3894_, v_a_3922_, v_a_3758_, v_a_3759_, v_a_3760_, v_a_3761_);
v___y_3854_ = v___x_3911_;
v___y_3855_ = v_a_3892_;
v___y_3856_ = v___x_3923_;
goto v___jp_3853_;
}
else
{
lean_object* v_a_3924_; 
lean_dec(v_val_3917_);
lean_dec(v_name_3773_);
lean_dec(v_levelParams_3767_);
lean_dec_ref(v_ctorVal_3757_);
v_a_3924_ = lean_ctor_get(v___x_3921_, 0);
lean_inc(v_a_3924_);
lean_dec_ref_known(v___x_3921_, 1);
v___y_3844_ = v___x_3911_;
v___y_3845_ = v_a_3892_;
v_a_3846_ = v_a_3924_;
goto v___jp_3843_;
}
}
}
else
{
lean_object* v___x_3925_; 
lean_dec(v_a_3913_);
lean_dec(v_name_3773_);
lean_dec(v_levelParams_3767_);
lean_dec_ref(v_ctorVal_3757_);
v___x_3925_ = lean_box(0);
v___y_3849_ = v___x_3911_;
v___y_3850_ = v_a_3892_;
v_a_3851_ = v___x_3925_;
goto v___jp_3848_;
}
}
else
{
lean_object* v_a_3926_; 
lean_dec(v_name_3773_);
lean_dec(v_levelParams_3767_);
lean_dec_ref(v_ctorVal_3757_);
v_a_3926_ = lean_ctor_get(v___x_3912_, 0);
lean_inc(v_a_3926_);
lean_dec_ref_known(v___x_3912_, 1);
v___y_3844_ = v___x_3911_;
v___y_3845_ = v_a_3892_;
v_a_3846_ = v_a_3926_;
goto v___jp_3843_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___boxed(lean_object* v_ctorVal_3991_, lean_object* v_a_3992_, lean_object* v_a_3993_, lean_object* v_a_3994_, lean_object* v_a_3995_, lean_object* v_a_3996_){
_start:
{
lean_object* v_res_3997_; 
v_res_3997_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(v_ctorVal_3991_, v_a_3992_, v_a_3993_, v_a_3994_, v_a_3995_);
lean_dec(v_a_3995_);
lean_dec_ref(v_a_3994_);
lean_dec(v_a_3993_);
lean_dec_ref(v_a_3992_);
return v_res_3997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(lean_object* v_name_3998_, lean_object* v_decl_3999_, lean_object* v_ref_4000_){
_start:
{
lean_object* v_defValue_4002_; lean_object* v_descr_4003_; lean_object* v_deprecation_x3f_4004_; lean_object* v___x_4005_; uint8_t v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; 
v_defValue_4002_ = lean_ctor_get(v_decl_3999_, 0);
v_descr_4003_ = lean_ctor_get(v_decl_3999_, 1);
v_deprecation_x3f_4004_ = lean_ctor_get(v_decl_3999_, 2);
v___x_4005_ = lean_alloc_ctor(1, 0, 1);
v___x_4006_ = lean_unbox(v_defValue_4002_);
lean_ctor_set_uint8(v___x_4005_, 0, v___x_4006_);
lean_inc(v_deprecation_x3f_4004_);
lean_inc_ref(v_descr_4003_);
lean_inc_n(v_name_3998_, 2);
v___x_4007_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4007_, 0, v_name_3998_);
lean_ctor_set(v___x_4007_, 1, v_ref_4000_);
lean_ctor_set(v___x_4007_, 2, v___x_4005_);
lean_ctor_set(v___x_4007_, 3, v_descr_4003_);
lean_ctor_set(v___x_4007_, 4, v_deprecation_x3f_4004_);
v___x_4008_ = lean_register_option(v_name_3998_, v___x_4007_);
if (lean_obj_tag(v___x_4008_) == 0)
{
lean_object* v___x_4010_; uint8_t v_isShared_4011_; uint8_t v_isSharedCheck_4016_; 
v_isSharedCheck_4016_ = !lean_is_exclusive(v___x_4008_);
if (v_isSharedCheck_4016_ == 0)
{
lean_object* v_unused_4017_; 
v_unused_4017_ = lean_ctor_get(v___x_4008_, 0);
lean_dec(v_unused_4017_);
v___x_4010_ = v___x_4008_;
v_isShared_4011_ = v_isSharedCheck_4016_;
goto v_resetjp_4009_;
}
else
{
lean_dec(v___x_4008_);
v___x_4010_ = lean_box(0);
v_isShared_4011_ = v_isSharedCheck_4016_;
goto v_resetjp_4009_;
}
v_resetjp_4009_:
{
lean_object* v___x_4012_; lean_object* v___x_4014_; 
lean_inc(v_defValue_4002_);
v___x_4012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4012_, 0, v_name_3998_);
lean_ctor_set(v___x_4012_, 1, v_defValue_4002_);
if (v_isShared_4011_ == 0)
{
lean_ctor_set(v___x_4010_, 0, v___x_4012_);
v___x_4014_ = v___x_4010_;
goto v_reusejp_4013_;
}
else
{
lean_object* v_reuseFailAlloc_4015_; 
v_reuseFailAlloc_4015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4015_, 0, v___x_4012_);
v___x_4014_ = v_reuseFailAlloc_4015_;
goto v_reusejp_4013_;
}
v_reusejp_4013_:
{
return v___x_4014_;
}
}
}
else
{
lean_object* v_a_4018_; lean_object* v___x_4020_; uint8_t v_isShared_4021_; uint8_t v_isSharedCheck_4025_; 
lean_dec(v_name_3998_);
v_a_4018_ = lean_ctor_get(v___x_4008_, 0);
v_isSharedCheck_4025_ = !lean_is_exclusive(v___x_4008_);
if (v_isSharedCheck_4025_ == 0)
{
v___x_4020_ = v___x_4008_;
v_isShared_4021_ = v_isSharedCheck_4025_;
goto v_resetjp_4019_;
}
else
{
lean_inc(v_a_4018_);
lean_dec(v___x_4008_);
v___x_4020_ = lean_box(0);
v_isShared_4021_ = v_isSharedCheck_4025_;
goto v_resetjp_4019_;
}
v_resetjp_4019_:
{
lean_object* v___x_4023_; 
if (v_isShared_4021_ == 0)
{
v___x_4023_ = v___x_4020_;
goto v_reusejp_4022_;
}
else
{
lean_object* v_reuseFailAlloc_4024_; 
v_reuseFailAlloc_4024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4024_, 0, v_a_4018_);
v___x_4023_ = v_reuseFailAlloc_4024_;
goto v_reusejp_4022_;
}
v_reusejp_4022_:
{
return v___x_4023_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_4026_, lean_object* v_decl_4027_, lean_object* v_ref_4028_, lean_object* v_a_4029_){
_start:
{
lean_object* v_res_4030_; 
v_res_4030_ = l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(v_name_4026_, v_decl_4027_, v_ref_4028_);
lean_dec_ref(v_decl_4027_);
return v_res_4030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; 
v___x_4045_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_));
v___x_4046_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_));
v___x_4047_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_));
v___x_4048_ = l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(v___x_4045_, v___x_4046_, v___x_4047_);
return v___x_4048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4____boxed(lean_object* v_a_4049_){
_start:
{
lean_object* v_res_4050_; 
v_res_4050_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_();
return v_res_4050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(lean_object* v_lctx_4051_, lean_object* v_localInsts_4052_, lean_object* v_x_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_){
_start:
{
lean_object* v___x_4059_; 
v___x_4059_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_4051_, v_localInsts_4052_, v_x_4053_, v___y_4054_, v___y_4055_, v___y_4056_, v___y_4057_);
if (lean_obj_tag(v___x_4059_) == 0)
{
lean_object* v_a_4060_; lean_object* v___x_4062_; uint8_t v_isShared_4063_; uint8_t v_isSharedCheck_4067_; 
v_a_4060_ = lean_ctor_get(v___x_4059_, 0);
v_isSharedCheck_4067_ = !lean_is_exclusive(v___x_4059_);
if (v_isSharedCheck_4067_ == 0)
{
v___x_4062_ = v___x_4059_;
v_isShared_4063_ = v_isSharedCheck_4067_;
goto v_resetjp_4061_;
}
else
{
lean_inc(v_a_4060_);
lean_dec(v___x_4059_);
v___x_4062_ = lean_box(0);
v_isShared_4063_ = v_isSharedCheck_4067_;
goto v_resetjp_4061_;
}
v_resetjp_4061_:
{
lean_object* v___x_4065_; 
if (v_isShared_4063_ == 0)
{
v___x_4065_ = v___x_4062_;
goto v_reusejp_4064_;
}
else
{
lean_object* v_reuseFailAlloc_4066_; 
v_reuseFailAlloc_4066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4066_, 0, v_a_4060_);
v___x_4065_ = v_reuseFailAlloc_4066_;
goto v_reusejp_4064_;
}
v_reusejp_4064_:
{
return v___x_4065_;
}
}
}
else
{
lean_object* v_a_4068_; lean_object* v___x_4070_; uint8_t v_isShared_4071_; uint8_t v_isSharedCheck_4075_; 
v_a_4068_ = lean_ctor_get(v___x_4059_, 0);
v_isSharedCheck_4075_ = !lean_is_exclusive(v___x_4059_);
if (v_isSharedCheck_4075_ == 0)
{
v___x_4070_ = v___x_4059_;
v_isShared_4071_ = v_isSharedCheck_4075_;
goto v_resetjp_4069_;
}
else
{
lean_inc(v_a_4068_);
lean_dec(v___x_4059_);
v___x_4070_ = lean_box(0);
v_isShared_4071_ = v_isSharedCheck_4075_;
goto v_resetjp_4069_;
}
v_resetjp_4069_:
{
lean_object* v___x_4073_; 
if (v_isShared_4071_ == 0)
{
v___x_4073_ = v___x_4070_;
goto v_reusejp_4072_;
}
else
{
lean_object* v_reuseFailAlloc_4074_; 
v_reuseFailAlloc_4074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4074_, 0, v_a_4068_);
v___x_4073_ = v_reuseFailAlloc_4074_;
goto v_reusejp_4072_;
}
v_reusejp_4072_:
{
return v___x_4073_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg___boxed(lean_object* v_lctx_4076_, lean_object* v_localInsts_4077_, lean_object* v_x_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_){
_start:
{
lean_object* v_res_4084_; 
v_res_4084_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v_lctx_4076_, v_localInsts_4077_, v_x_4078_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_);
lean_dec(v___y_4082_);
lean_dec_ref(v___y_4081_);
lean_dec(v___y_4080_);
lean_dec_ref(v___y_4079_);
return v_res_4084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4(lean_object* v_00_u03b1_4085_, lean_object* v_lctx_4086_, lean_object* v_localInsts_4087_, lean_object* v_x_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_){
_start:
{
lean_object* v___x_4094_; 
v___x_4094_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v_lctx_4086_, v_localInsts_4087_, v_x_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_);
return v___x_4094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___boxed(lean_object* v_00_u03b1_4095_, lean_object* v_lctx_4096_, lean_object* v_localInsts_4097_, lean_object* v_x_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_){
_start:
{
lean_object* v_res_4104_; 
v_res_4104_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4(v_00_u03b1_4095_, v_lctx_4096_, v_localInsts_4097_, v_x_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_);
lean_dec(v___y_4102_);
lean_dec_ref(v___y_4101_);
lean_dec(v___y_4100_);
lean_dec_ref(v___y_4099_);
return v_res_4104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__0(lean_object* v_declName_4105_, lean_object* v_x_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_){
_start:
{
lean_object* v___x_4112_; lean_object* v___x_4113_; 
v___x_4112_ = l_Lean_MessageData_ofName(v_declName_4105_);
v___x_4113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4113_, 0, v___x_4112_);
return v___x_4113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__0___boxed(lean_object* v_declName_4114_, lean_object* v_x_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_){
_start:
{
lean_object* v_res_4121_; 
v_res_4121_ = l_Lean_Meta_mkInjectiveTheorems___lam__0(v_declName_4114_, v_x_4115_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_);
lean_dec(v___y_4119_);
lean_dec_ref(v___y_4118_);
lean_dec(v___y_4117_);
lean_dec_ref(v___y_4116_);
lean_dec_ref(v_x_4115_);
return v_res_4121_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_4122_; 
v___x_4122_ = l_instMonadEIO___redArg();
return v___x_4122_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(lean_object* v_msg_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_){
_start:
{
lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v_toApplicative_4135_; lean_object* v___x_4137_; uint8_t v_isShared_4138_; uint8_t v_isSharedCheck_4196_; 
v___x_4133_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0);
v___x_4134_ = l_StateRefT_x27_instMonad___redArg(v___x_4133_);
v_toApplicative_4135_ = lean_ctor_get(v___x_4134_, 0);
v_isSharedCheck_4196_ = !lean_is_exclusive(v___x_4134_);
if (v_isSharedCheck_4196_ == 0)
{
lean_object* v_unused_4197_; 
v_unused_4197_ = lean_ctor_get(v___x_4134_, 1);
lean_dec(v_unused_4197_);
v___x_4137_ = v___x_4134_;
v_isShared_4138_ = v_isSharedCheck_4196_;
goto v_resetjp_4136_;
}
else
{
lean_inc(v_toApplicative_4135_);
lean_dec(v___x_4134_);
v___x_4137_ = lean_box(0);
v_isShared_4138_ = v_isSharedCheck_4196_;
goto v_resetjp_4136_;
}
v_resetjp_4136_:
{
lean_object* v_toFunctor_4139_; lean_object* v_toSeq_4140_; lean_object* v_toSeqLeft_4141_; lean_object* v_toSeqRight_4142_; lean_object* v___x_4144_; uint8_t v_isShared_4145_; uint8_t v_isSharedCheck_4194_; 
v_toFunctor_4139_ = lean_ctor_get(v_toApplicative_4135_, 0);
v_toSeq_4140_ = lean_ctor_get(v_toApplicative_4135_, 2);
v_toSeqLeft_4141_ = lean_ctor_get(v_toApplicative_4135_, 3);
v_toSeqRight_4142_ = lean_ctor_get(v_toApplicative_4135_, 4);
v_isSharedCheck_4194_ = !lean_is_exclusive(v_toApplicative_4135_);
if (v_isSharedCheck_4194_ == 0)
{
lean_object* v_unused_4195_; 
v_unused_4195_ = lean_ctor_get(v_toApplicative_4135_, 1);
lean_dec(v_unused_4195_);
v___x_4144_ = v_toApplicative_4135_;
v_isShared_4145_ = v_isSharedCheck_4194_;
goto v_resetjp_4143_;
}
else
{
lean_inc(v_toSeqRight_4142_);
lean_inc(v_toSeqLeft_4141_);
lean_inc(v_toSeq_4140_);
lean_inc(v_toFunctor_4139_);
lean_dec(v_toApplicative_4135_);
v___x_4144_ = lean_box(0);
v_isShared_4145_ = v_isSharedCheck_4194_;
goto v_resetjp_4143_;
}
v_resetjp_4143_:
{
lean_object* v___f_4146_; lean_object* v___f_4147_; lean_object* v___f_4148_; lean_object* v___f_4149_; lean_object* v___x_4150_; lean_object* v___f_4151_; lean_object* v___f_4152_; lean_object* v___f_4153_; lean_object* v___x_4155_; 
v___f_4146_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__1));
v___f_4147_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__2));
lean_inc_ref(v_toFunctor_4139_);
v___f_4148_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4148_, 0, v_toFunctor_4139_);
v___f_4149_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4149_, 0, v_toFunctor_4139_);
v___x_4150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4150_, 0, v___f_4148_);
lean_ctor_set(v___x_4150_, 1, v___f_4149_);
v___f_4151_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4151_, 0, v_toSeqRight_4142_);
v___f_4152_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4152_, 0, v_toSeqLeft_4141_);
v___f_4153_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4153_, 0, v_toSeq_4140_);
if (v_isShared_4145_ == 0)
{
lean_ctor_set(v___x_4144_, 4, v___f_4151_);
lean_ctor_set(v___x_4144_, 3, v___f_4152_);
lean_ctor_set(v___x_4144_, 2, v___f_4153_);
lean_ctor_set(v___x_4144_, 1, v___f_4146_);
lean_ctor_set(v___x_4144_, 0, v___x_4150_);
v___x_4155_ = v___x_4144_;
goto v_reusejp_4154_;
}
else
{
lean_object* v_reuseFailAlloc_4193_; 
v_reuseFailAlloc_4193_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4193_, 0, v___x_4150_);
lean_ctor_set(v_reuseFailAlloc_4193_, 1, v___f_4146_);
lean_ctor_set(v_reuseFailAlloc_4193_, 2, v___f_4153_);
lean_ctor_set(v_reuseFailAlloc_4193_, 3, v___f_4152_);
lean_ctor_set(v_reuseFailAlloc_4193_, 4, v___f_4151_);
v___x_4155_ = v_reuseFailAlloc_4193_;
goto v_reusejp_4154_;
}
v_reusejp_4154_:
{
lean_object* v___x_4157_; 
if (v_isShared_4138_ == 0)
{
lean_ctor_set(v___x_4137_, 1, v___f_4147_);
lean_ctor_set(v___x_4137_, 0, v___x_4155_);
v___x_4157_ = v___x_4137_;
goto v_reusejp_4156_;
}
else
{
lean_object* v_reuseFailAlloc_4192_; 
v_reuseFailAlloc_4192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4192_, 0, v___x_4155_);
lean_ctor_set(v_reuseFailAlloc_4192_, 1, v___f_4147_);
v___x_4157_ = v_reuseFailAlloc_4192_;
goto v_reusejp_4156_;
}
v_reusejp_4156_:
{
lean_object* v___x_4158_; lean_object* v_toApplicative_4159_; lean_object* v___x_4161_; uint8_t v_isShared_4162_; uint8_t v_isSharedCheck_4190_; 
v___x_4158_ = l_StateRefT_x27_instMonad___redArg(v___x_4157_);
v_toApplicative_4159_ = lean_ctor_get(v___x_4158_, 0);
v_isSharedCheck_4190_ = !lean_is_exclusive(v___x_4158_);
if (v_isSharedCheck_4190_ == 0)
{
lean_object* v_unused_4191_; 
v_unused_4191_ = lean_ctor_get(v___x_4158_, 1);
lean_dec(v_unused_4191_);
v___x_4161_ = v___x_4158_;
v_isShared_4162_ = v_isSharedCheck_4190_;
goto v_resetjp_4160_;
}
else
{
lean_inc(v_toApplicative_4159_);
lean_dec(v___x_4158_);
v___x_4161_ = lean_box(0);
v_isShared_4162_ = v_isSharedCheck_4190_;
goto v_resetjp_4160_;
}
v_resetjp_4160_:
{
lean_object* v_toFunctor_4163_; lean_object* v_toSeq_4164_; lean_object* v_toSeqLeft_4165_; lean_object* v_toSeqRight_4166_; lean_object* v___x_4168_; uint8_t v_isShared_4169_; uint8_t v_isSharedCheck_4188_; 
v_toFunctor_4163_ = lean_ctor_get(v_toApplicative_4159_, 0);
v_toSeq_4164_ = lean_ctor_get(v_toApplicative_4159_, 2);
v_toSeqLeft_4165_ = lean_ctor_get(v_toApplicative_4159_, 3);
v_toSeqRight_4166_ = lean_ctor_get(v_toApplicative_4159_, 4);
v_isSharedCheck_4188_ = !lean_is_exclusive(v_toApplicative_4159_);
if (v_isSharedCheck_4188_ == 0)
{
lean_object* v_unused_4189_; 
v_unused_4189_ = lean_ctor_get(v_toApplicative_4159_, 1);
lean_dec(v_unused_4189_);
v___x_4168_ = v_toApplicative_4159_;
v_isShared_4169_ = v_isSharedCheck_4188_;
goto v_resetjp_4167_;
}
else
{
lean_inc(v_toSeqRight_4166_);
lean_inc(v_toSeqLeft_4165_);
lean_inc(v_toSeq_4164_);
lean_inc(v_toFunctor_4163_);
lean_dec(v_toApplicative_4159_);
v___x_4168_ = lean_box(0);
v_isShared_4169_ = v_isSharedCheck_4188_;
goto v_resetjp_4167_;
}
v_resetjp_4167_:
{
lean_object* v___f_4170_; lean_object* v___f_4171_; lean_object* v___f_4172_; lean_object* v___f_4173_; lean_object* v___x_4174_; lean_object* v___f_4175_; lean_object* v___f_4176_; lean_object* v___f_4177_; lean_object* v___x_4179_; 
v___f_4170_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__3));
v___f_4171_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__4));
lean_inc_ref(v_toFunctor_4163_);
v___f_4172_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4172_, 0, v_toFunctor_4163_);
v___f_4173_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4173_, 0, v_toFunctor_4163_);
v___x_4174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4174_, 0, v___f_4172_);
lean_ctor_set(v___x_4174_, 1, v___f_4173_);
v___f_4175_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4175_, 0, v_toSeqRight_4166_);
v___f_4176_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4176_, 0, v_toSeqLeft_4165_);
v___f_4177_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4177_, 0, v_toSeq_4164_);
if (v_isShared_4169_ == 0)
{
lean_ctor_set(v___x_4168_, 4, v___f_4175_);
lean_ctor_set(v___x_4168_, 3, v___f_4176_);
lean_ctor_set(v___x_4168_, 2, v___f_4177_);
lean_ctor_set(v___x_4168_, 1, v___f_4170_);
lean_ctor_set(v___x_4168_, 0, v___x_4174_);
v___x_4179_ = v___x_4168_;
goto v_reusejp_4178_;
}
else
{
lean_object* v_reuseFailAlloc_4187_; 
v_reuseFailAlloc_4187_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4187_, 0, v___x_4174_);
lean_ctor_set(v_reuseFailAlloc_4187_, 1, v___f_4170_);
lean_ctor_set(v_reuseFailAlloc_4187_, 2, v___f_4177_);
lean_ctor_set(v_reuseFailAlloc_4187_, 3, v___f_4176_);
lean_ctor_set(v_reuseFailAlloc_4187_, 4, v___f_4175_);
v___x_4179_ = v_reuseFailAlloc_4187_;
goto v_reusejp_4178_;
}
v_reusejp_4178_:
{
lean_object* v___x_4181_; 
if (v_isShared_4162_ == 0)
{
lean_ctor_set(v___x_4161_, 1, v___f_4171_);
lean_ctor_set(v___x_4161_, 0, v___x_4179_);
v___x_4181_ = v___x_4161_;
goto v_reusejp_4180_;
}
else
{
lean_object* v_reuseFailAlloc_4186_; 
v_reuseFailAlloc_4186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4186_, 0, v___x_4179_);
lean_ctor_set(v_reuseFailAlloc_4186_, 1, v___f_4171_);
v___x_4181_ = v_reuseFailAlloc_4186_;
goto v_reusejp_4180_;
}
v_reusejp_4180_:
{
lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_16605__overap_4184_; lean_object* v___x_4185_; 
v___x_4182_ = lean_box(0);
v___x_4183_ = l_instInhabitedOfMonad___redArg(v___x_4181_, v___x_4182_);
v___x_16605__overap_4184_ = lean_panic_fn_borrowed(v___x_4183_, v_msg_4127_);
lean_dec(v___x_4183_);
lean_inc(v___y_4131_);
lean_inc_ref(v___y_4130_);
lean_inc(v___y_4129_);
lean_inc_ref(v___y_4128_);
v___x_4185_ = lean_apply_5(v___x_16605__overap_4184_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, lean_box(0));
return v___x_4185_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___boxed(lean_object* v_msg_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_){
_start:
{
lean_object* v_res_4204_; 
v_res_4204_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(v_msg_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_);
lean_dec(v___y_4202_);
lean_dec_ref(v___y_4201_);
lean_dec(v___y_4200_);
lean_dec_ref(v___y_4199_);
return v_res_4204_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1(void){
_start:
{
lean_object* v___x_4206_; lean_object* v___x_4207_; 
v___x_4206_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__0));
v___x_4207_ = l_Lean_stringToMessageData(v___x_4206_);
return v___x_4207_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4(void){
_start:
{
lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; 
v___x_4210_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__2));
v___x_4211_ = lean_unsigned_to_nat(11u);
v___x_4212_ = lean_unsigned_to_nat(122u);
v___x_4213_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__3));
v___x_4214_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__2));
v___x_4215_ = l_mkPanicMessageWithDecl(v___x_4214_, v___x_4213_, v___x_4212_, v___x_4211_, v___x_4210_);
return v___x_4215_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(lean_object* v_constName_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_){
_start:
{
lean_object* v___x_4230_; lean_object* v_env_4231_; uint8_t v___x_4232_; lean_object* v___x_4233_; 
v___x_4230_ = lean_st_ref_get(v___y_4220_);
v_env_4231_ = lean_ctor_get(v___x_4230_, 0);
lean_inc_ref(v_env_4231_);
lean_dec(v___x_4230_);
v___x_4232_ = 0;
lean_inc(v_constName_4216_);
v___x_4233_ = l_Lean_Environment_findAsync_x3f(v_env_4231_, v_constName_4216_, v___x_4232_);
if (lean_obj_tag(v___x_4233_) == 1)
{
lean_object* v_val_4234_; uint8_t v_kind_4235_; 
v_val_4234_ = lean_ctor_get(v___x_4233_, 0);
lean_inc(v_val_4234_);
lean_dec_ref_known(v___x_4233_, 1);
v_kind_4235_ = lean_ctor_get_uint8(v_val_4234_, sizeof(void*)*3);
if (v_kind_4235_ == 6)
{
lean_object* v___x_4236_; 
v___x_4236_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_4234_);
if (lean_obj_tag(v___x_4236_) == 6)
{
lean_object* v_val_4237_; lean_object* v___x_4239_; uint8_t v_isShared_4240_; uint8_t v_isSharedCheck_4244_; 
lean_dec(v_constName_4216_);
v_val_4237_ = lean_ctor_get(v___x_4236_, 0);
v_isSharedCheck_4244_ = !lean_is_exclusive(v___x_4236_);
if (v_isSharedCheck_4244_ == 0)
{
v___x_4239_ = v___x_4236_;
v_isShared_4240_ = v_isSharedCheck_4244_;
goto v_resetjp_4238_;
}
else
{
lean_inc(v_val_4237_);
lean_dec(v___x_4236_);
v___x_4239_ = lean_box(0);
v_isShared_4240_ = v_isSharedCheck_4244_;
goto v_resetjp_4238_;
}
v_resetjp_4238_:
{
lean_object* v___x_4242_; 
if (v_isShared_4240_ == 0)
{
lean_ctor_set_tag(v___x_4239_, 0);
v___x_4242_ = v___x_4239_;
goto v_reusejp_4241_;
}
else
{
lean_object* v_reuseFailAlloc_4243_; 
v_reuseFailAlloc_4243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4243_, 0, v_val_4237_);
v___x_4242_ = v_reuseFailAlloc_4243_;
goto v_reusejp_4241_;
}
v_reusejp_4241_:
{
return v___x_4242_;
}
}
}
else
{
lean_object* v___x_4245_; lean_object* v___x_4246_; 
lean_dec_ref(v___x_4236_);
v___x_4245_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4);
v___x_4246_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(v___x_4245_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_);
if (lean_obj_tag(v___x_4246_) == 0)
{
lean_object* v_a_4247_; lean_object* v___x_4249_; uint8_t v_isShared_4250_; uint8_t v_isSharedCheck_4255_; 
v_a_4247_ = lean_ctor_get(v___x_4246_, 0);
v_isSharedCheck_4255_ = !lean_is_exclusive(v___x_4246_);
if (v_isSharedCheck_4255_ == 0)
{
v___x_4249_ = v___x_4246_;
v_isShared_4250_ = v_isSharedCheck_4255_;
goto v_resetjp_4248_;
}
else
{
lean_inc(v_a_4247_);
lean_dec(v___x_4246_);
v___x_4249_ = lean_box(0);
v_isShared_4250_ = v_isSharedCheck_4255_;
goto v_resetjp_4248_;
}
v_resetjp_4248_:
{
if (lean_obj_tag(v_a_4247_) == 0)
{
lean_del_object(v___x_4249_);
goto v___jp_4222_;
}
else
{
lean_object* v_val_4251_; lean_object* v___x_4253_; 
lean_dec(v_constName_4216_);
v_val_4251_ = lean_ctor_get(v_a_4247_, 0);
lean_inc(v_val_4251_);
lean_dec_ref_known(v_a_4247_, 1);
if (v_isShared_4250_ == 0)
{
lean_ctor_set(v___x_4249_, 0, v_val_4251_);
v___x_4253_ = v___x_4249_;
goto v_reusejp_4252_;
}
else
{
lean_object* v_reuseFailAlloc_4254_; 
v_reuseFailAlloc_4254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4254_, 0, v_val_4251_);
v___x_4253_ = v_reuseFailAlloc_4254_;
goto v_reusejp_4252_;
}
v_reusejp_4252_:
{
return v___x_4253_;
}
}
}
}
else
{
lean_object* v_a_4256_; lean_object* v___x_4258_; uint8_t v_isShared_4259_; uint8_t v_isSharedCheck_4263_; 
lean_dec(v_constName_4216_);
v_a_4256_ = lean_ctor_get(v___x_4246_, 0);
v_isSharedCheck_4263_ = !lean_is_exclusive(v___x_4246_);
if (v_isSharedCheck_4263_ == 0)
{
v___x_4258_ = v___x_4246_;
v_isShared_4259_ = v_isSharedCheck_4263_;
goto v_resetjp_4257_;
}
else
{
lean_inc(v_a_4256_);
lean_dec(v___x_4246_);
v___x_4258_ = lean_box(0);
v_isShared_4259_ = v_isSharedCheck_4263_;
goto v_resetjp_4257_;
}
v_resetjp_4257_:
{
lean_object* v___x_4261_; 
if (v_isShared_4259_ == 0)
{
v___x_4261_ = v___x_4258_;
goto v_reusejp_4260_;
}
else
{
lean_object* v_reuseFailAlloc_4262_; 
v_reuseFailAlloc_4262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4262_, 0, v_a_4256_);
v___x_4261_ = v_reuseFailAlloc_4262_;
goto v_reusejp_4260_;
}
v_reusejp_4260_:
{
return v___x_4261_;
}
}
}
}
}
else
{
lean_dec(v_val_4234_);
goto v___jp_4222_;
}
}
else
{
lean_dec(v___x_4233_);
goto v___jp_4222_;
}
v___jp_4222_:
{
lean_object* v___x_4223_; uint8_t v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; 
v___x_4223_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_4224_ = 0;
v___x_4225_ = l_Lean_MessageData_ofConstName(v_constName_4216_, v___x_4224_);
v___x_4226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4226_, 0, v___x_4223_);
lean_ctor_set(v___x_4226_, 1, v___x_4225_);
v___x_4227_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1);
v___x_4228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4228_, 0, v___x_4226_);
lean_ctor_set(v___x_4228_, 1, v___x_4227_);
v___x_4229_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_4228_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_);
return v___x_4229_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___boxed(lean_object* v_constName_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_){
_start:
{
lean_object* v_res_4270_; 
v_res_4270_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(v_constName_4264_, v___y_4265_, v___y_4266_, v___y_4267_, v___y_4268_);
lean_dec(v___y_4268_);
lean_dec_ref(v___y_4267_);
lean_dec(v___y_4266_);
lean_dec_ref(v___y_4265_);
return v_res_4270_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0(lean_object* v_head_4271_, lean_object* v___x_4272_, lean_object* v___x_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_){
_start:
{
lean_object* v___x_4279_; 
v___x_4279_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(v_head_4271_, v___y_4274_, v___y_4275_, v___y_4276_, v___y_4277_);
if (lean_obj_tag(v___x_4279_) == 0)
{
lean_object* v_a_4280_; lean_object* v___x_4282_; uint8_t v_isShared_4283_; uint8_t v_isSharedCheck_4291_; 
v_a_4280_ = lean_ctor_get(v___x_4279_, 0);
v_isSharedCheck_4291_ = !lean_is_exclusive(v___x_4279_);
if (v_isSharedCheck_4291_ == 0)
{
v___x_4282_ = v___x_4279_;
v_isShared_4283_ = v_isSharedCheck_4291_;
goto v_resetjp_4281_;
}
else
{
lean_inc(v_a_4280_);
lean_dec(v___x_4279_);
v___x_4282_ = lean_box(0);
v_isShared_4283_ = v_isSharedCheck_4291_;
goto v_resetjp_4281_;
}
v_resetjp_4281_:
{
lean_object* v_numFields_4284_; uint8_t v___x_4285_; 
v_numFields_4284_ = lean_ctor_get(v_a_4280_, 4);
v___x_4285_ = lean_nat_dec_lt(v___x_4272_, v_numFields_4284_);
if (v___x_4285_ == 0)
{
lean_object* v___x_4287_; 
lean_dec(v_a_4280_);
if (v_isShared_4283_ == 0)
{
lean_ctor_set(v___x_4282_, 0, v___x_4273_);
v___x_4287_ = v___x_4282_;
goto v_reusejp_4286_;
}
else
{
lean_object* v_reuseFailAlloc_4288_; 
v_reuseFailAlloc_4288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4288_, 0, v___x_4273_);
v___x_4287_ = v_reuseFailAlloc_4288_;
goto v_reusejp_4286_;
}
v_reusejp_4286_:
{
return v___x_4287_;
}
}
else
{
lean_object* v___x_4289_; 
lean_del_object(v___x_4282_);
lean_inc(v_a_4280_);
v___x_4289_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(v_a_4280_, v___y_4274_, v___y_4275_, v___y_4276_, v___y_4277_);
if (lean_obj_tag(v___x_4289_) == 0)
{
lean_object* v___x_4290_; 
lean_dec_ref_known(v___x_4289_, 1);
v___x_4290_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(v_a_4280_, v___y_4274_, v___y_4275_, v___y_4276_, v___y_4277_);
return v___x_4290_;
}
else
{
lean_dec(v_a_4280_);
return v___x_4289_;
}
}
}
}
else
{
lean_object* v_a_4292_; lean_object* v___x_4294_; uint8_t v_isShared_4295_; uint8_t v_isSharedCheck_4299_; 
v_a_4292_ = lean_ctor_get(v___x_4279_, 0);
v_isSharedCheck_4299_ = !lean_is_exclusive(v___x_4279_);
if (v_isSharedCheck_4299_ == 0)
{
v___x_4294_ = v___x_4279_;
v_isShared_4295_ = v_isSharedCheck_4299_;
goto v_resetjp_4293_;
}
else
{
lean_inc(v_a_4292_);
lean_dec(v___x_4279_);
v___x_4294_ = lean_box(0);
v_isShared_4295_ = v_isSharedCheck_4299_;
goto v_resetjp_4293_;
}
v_resetjp_4293_:
{
lean_object* v___x_4297_; 
if (v_isShared_4295_ == 0)
{
v___x_4297_ = v___x_4294_;
goto v_reusejp_4296_;
}
else
{
lean_object* v_reuseFailAlloc_4298_; 
v_reuseFailAlloc_4298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4298_, 0, v_a_4292_);
v___x_4297_ = v_reuseFailAlloc_4298_;
goto v_reusejp_4296_;
}
v_reusejp_4296_:
{
return v___x_4297_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0___boxed(lean_object* v_head_4300_, lean_object* v___x_4301_, lean_object* v___x_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_){
_start:
{
lean_object* v_res_4308_; 
v_res_4308_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0(v_head_4300_, v___x_4301_, v___x_4302_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_);
lean_dec(v___y_4306_);
lean_dec_ref(v___y_4305_);
lean_dec(v___y_4304_);
lean_dec_ref(v___y_4303_);
lean_dec(v___x_4301_);
return v_res_4308_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2_spec__3_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_4309_; 
v___x_4309_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_4309_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2_spec__3_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_4310_; lean_object* v___x_4311_; 
v___x_4310_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2_spec__3_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2_spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2_spec__3_spec__5___redArg___closed__0);
v___x_4311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4311_, 0, v___x_4310_);
return v___x_4311_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2_spec__3_spec__5___redArg(){
_start:
{
lean_object* v___x_4313_; 
v___x_4313_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2_spec__3_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2_spec__3_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2_spec__3_spec__5___redArg___closed__1);
return v___x_4313_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v___dummy_4314_){
_start:
{
lean_object* v_res_4315_; 
v_res_4315_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2_spec__3_spec__5___redArg();
return v_res_4315_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(lean_object* v___y_4316_, uint8_t v_isExporting_4317_, lean_object* v___x_4318_, lean_object* v___y_4319_, lean_object* v___x_4320_, lean_object* v_a_x3f_4321_){
_start:
{
lean_object* v___x_4323_; lean_object* v_env_4324_; lean_object* v_nextMacroScope_4325_; lean_object* v_ngen_4326_; lean_object* v_auxDeclNGen_4327_; lean_object* v_traceState_4328_; lean_object* v_recordedDeps_4329_; lean_object* v_messages_4330_; lean_object* v_infoState_4331_; lean_object* v_snapshotTasks_4332_; lean_object* v___x_4334_; uint8_t v_isShared_4335_; uint8_t v_isSharedCheck_4357_; 
v___x_4323_ = lean_st_ref_take(v___y_4316_);
v_env_4324_ = lean_ctor_get(v___x_4323_, 0);
v_nextMacroScope_4325_ = lean_ctor_get(v___x_4323_, 1);
v_ngen_4326_ = lean_ctor_get(v___x_4323_, 2);
v_auxDeclNGen_4327_ = lean_ctor_get(v___x_4323_, 3);
v_traceState_4328_ = lean_ctor_get(v___x_4323_, 4);
v_recordedDeps_4329_ = lean_ctor_get(v___x_4323_, 6);
v_messages_4330_ = lean_ctor_get(v___x_4323_, 7);
v_infoState_4331_ = lean_ctor_get(v___x_4323_, 8);
v_snapshotTasks_4332_ = lean_ctor_get(v___x_4323_, 9);
v_isSharedCheck_4357_ = !lean_is_exclusive(v___x_4323_);
if (v_isSharedCheck_4357_ == 0)
{
lean_object* v_unused_4358_; 
v_unused_4358_ = lean_ctor_get(v___x_4323_, 5);
lean_dec(v_unused_4358_);
v___x_4334_ = v___x_4323_;
v_isShared_4335_ = v_isSharedCheck_4357_;
goto v_resetjp_4333_;
}
else
{
lean_inc(v_snapshotTasks_4332_);
lean_inc(v_infoState_4331_);
lean_inc(v_messages_4330_);
lean_inc(v_recordedDeps_4329_);
lean_inc(v_traceState_4328_);
lean_inc(v_auxDeclNGen_4327_);
lean_inc(v_ngen_4326_);
lean_inc(v_nextMacroScope_4325_);
lean_inc(v_env_4324_);
lean_dec(v___x_4323_);
v___x_4334_ = lean_box(0);
v_isShared_4335_ = v_isSharedCheck_4357_;
goto v_resetjp_4333_;
}
v_resetjp_4333_:
{
lean_object* v___x_4336_; lean_object* v___x_4338_; 
v___x_4336_ = l_Lean_Environment_setExporting(v_env_4324_, v_isExporting_4317_);
if (v_isShared_4335_ == 0)
{
lean_ctor_set(v___x_4334_, 5, v___x_4318_);
lean_ctor_set(v___x_4334_, 0, v___x_4336_);
v___x_4338_ = v___x_4334_;
goto v_reusejp_4337_;
}
else
{
lean_object* v_reuseFailAlloc_4356_; 
v_reuseFailAlloc_4356_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4356_, 0, v___x_4336_);
lean_ctor_set(v_reuseFailAlloc_4356_, 1, v_nextMacroScope_4325_);
lean_ctor_set(v_reuseFailAlloc_4356_, 2, v_ngen_4326_);
lean_ctor_set(v_reuseFailAlloc_4356_, 3, v_auxDeclNGen_4327_);
lean_ctor_set(v_reuseFailAlloc_4356_, 4, v_traceState_4328_);
lean_ctor_set(v_reuseFailAlloc_4356_, 5, v___x_4318_);
lean_ctor_set(v_reuseFailAlloc_4356_, 6, v_recordedDeps_4329_);
lean_ctor_set(v_reuseFailAlloc_4356_, 7, v_messages_4330_);
lean_ctor_set(v_reuseFailAlloc_4356_, 8, v_infoState_4331_);
lean_ctor_set(v_reuseFailAlloc_4356_, 9, v_snapshotTasks_4332_);
v___x_4338_ = v_reuseFailAlloc_4356_;
goto v_reusejp_4337_;
}
v_reusejp_4337_:
{
lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v_mctx_4341_; lean_object* v_zetaDeltaFVarIds_4342_; lean_object* v_postponed_4343_; lean_object* v_diag_4344_; lean_object* v___x_4346_; uint8_t v_isShared_4347_; uint8_t v_isSharedCheck_4354_; 
v___x_4339_ = lean_st_ref_put(v___y_4316_, v___x_4338_);
v___x_4340_ = lean_st_ref_take(v___y_4319_);
v_mctx_4341_ = lean_ctor_get(v___x_4340_, 0);
v_zetaDeltaFVarIds_4342_ = lean_ctor_get(v___x_4340_, 2);
v_postponed_4343_ = lean_ctor_get(v___x_4340_, 3);
v_diag_4344_ = lean_ctor_get(v___x_4340_, 4);
v_isSharedCheck_4354_ = !lean_is_exclusive(v___x_4340_);
if (v_isSharedCheck_4354_ == 0)
{
lean_object* v_unused_4355_; 
v_unused_4355_ = lean_ctor_get(v___x_4340_, 1);
lean_dec(v_unused_4355_);
v___x_4346_ = v___x_4340_;
v_isShared_4347_ = v_isSharedCheck_4354_;
goto v_resetjp_4345_;
}
else
{
lean_inc(v_diag_4344_);
lean_inc(v_postponed_4343_);
lean_inc(v_zetaDeltaFVarIds_4342_);
lean_inc(v_mctx_4341_);
lean_dec(v___x_4340_);
v___x_4346_ = lean_box(0);
v_isShared_4347_ = v_isSharedCheck_4354_;
goto v_resetjp_4345_;
}
v_resetjp_4345_:
{
lean_object* v___x_4348_; lean_object* v___x_4350_; 
v___x_4348_ = lean_box(0);
if (v_isShared_4347_ == 0)
{
lean_ctor_set(v___x_4346_, 1, v___x_4320_);
v___x_4350_ = v___x_4346_;
goto v_reusejp_4349_;
}
else
{
lean_object* v_reuseFailAlloc_4353_; 
v_reuseFailAlloc_4353_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4353_, 0, v_mctx_4341_);
lean_ctor_set(v_reuseFailAlloc_4353_, 1, v___x_4320_);
lean_ctor_set(v_reuseFailAlloc_4353_, 2, v_zetaDeltaFVarIds_4342_);
lean_ctor_set(v_reuseFailAlloc_4353_, 3, v_postponed_4343_);
lean_ctor_set(v_reuseFailAlloc_4353_, 4, v_diag_4344_);
v___x_4350_ = v_reuseFailAlloc_4353_;
goto v_reusejp_4349_;
}
v_reusejp_4349_:
{
lean_object* v___x_4351_; lean_object* v___x_4352_; 
v___x_4351_ = lean_st_ref_put(v___y_4319_, v___x_4350_);
v___x_4352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4352_, 0, v___x_4348_);
return v___x_4352_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0___boxed(lean_object* v___y_4359_, lean_object* v_isExporting_4360_, lean_object* v___x_4361_, lean_object* v___y_4362_, lean_object* v___x_4363_, lean_object* v_a_x3f_4364_, lean_object* v___y_4365_){
_start:
{
uint8_t v_isExporting_boxed_4366_; lean_object* v_res_4367_; 
v_isExporting_boxed_4366_ = lean_unbox(v_isExporting_4360_);
v_res_4367_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(v___y_4359_, v_isExporting_boxed_4366_, v___x_4361_, v___y_4362_, v___x_4363_, v_a_x3f_4364_);
lean_dec(v_a_x3f_4364_);
lean_dec(v___y_4362_);
lean_dec(v___y_4359_);
return v_res_4367_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_4368_; lean_object* v___x_4369_; 
v___x_4368_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2_spec__3_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2_spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2_spec__3_spec__5___redArg___closed__0);
v___x_4369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4369_, 0, v___x_4368_);
return v___x_4369_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4370_; lean_object* v___x_4371_; 
v___x_4370_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0);
v___x_4371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4371_, 0, v___x_4370_);
lean_ctor_set(v___x_4371_, 1, v___x_4370_);
return v___x_4371_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_4372_; 
v___x_4372_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2_spec__3_spec__5___redArg();
return v___x_4372_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_4373_; lean_object* v___x_4374_; 
v___x_4373_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0);
v___x_4374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4374_, 0, v___x_4373_);
lean_ctor_set(v___x_4374_, 1, v___x_4373_);
return v___x_4374_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; 
v___x_4375_ = lean_unsigned_to_nat(0u);
v___x_4376_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0);
v___x_4377_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4377_, 0, v___x_4376_);
lean_ctor_set(v___x_4377_, 1, v___x_4376_);
lean_ctor_set(v___x_4377_, 2, v___x_4375_);
return v___x_4377_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; 
v___x_4378_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__4, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__4_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__4);
v___x_4379_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3);
v___x_4380_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0);
v___x_4381_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2);
v___x_4382_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_4382_, 0, v___x_4381_);
lean_ctor_set(v___x_4382_, 1, v___x_4380_);
lean_ctor_set(v___x_4382_, 2, v___x_4379_);
lean_ctor_set(v___x_4382_, 3, v___x_4380_);
lean_ctor_set(v___x_4382_, 4, v___x_4380_);
lean_ctor_set(v___x_4382_, 5, v___x_4380_);
lean_ctor_set(v___x_4382_, 6, v___x_4380_);
lean_ctor_set(v___x_4382_, 7, v___x_4378_);
return v___x_4382_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(lean_object* v_x_4383_, uint8_t v_isExporting_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_){
_start:
{
lean_object* v___x_4390_; lean_object* v_env_4391_; lean_object* v___x_4392_; uint8_t v_isModule_4393_; 
v___x_4390_ = lean_st_ref_get(v___y_4388_);
v_env_4391_ = lean_ctor_get(v___x_4390_, 0);
lean_inc_ref(v_env_4391_);
lean_dec(v___x_4390_);
v___x_4392_ = l_Lean_Environment_header(v_env_4391_);
v_isModule_4393_ = lean_ctor_get_uint8(v___x_4392_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_4392_);
if (v_isModule_4393_ == 0)
{
lean_object* v___x_4394_; 
lean_dec_ref(v_env_4391_);
lean_inc(v___y_4388_);
lean_inc_ref(v___y_4387_);
lean_inc(v___y_4386_);
lean_inc_ref(v___y_4385_);
v___x_4394_ = lean_apply_5(v_x_4383_, v___y_4385_, v___y_4386_, v___y_4387_, v___y_4388_, lean_box(0));
return v___x_4394_;
}
else
{
uint8_t v_isExporting_4395_; 
v_isExporting_4395_ = lean_ctor_get_uint8(v_env_4391_, sizeof(void*)*13);
lean_dec_ref(v_env_4391_);
if (v_isExporting_4384_ == 0)
{
if (v_isExporting_4395_ == 0)
{
lean_object* v___x_4462_; 
lean_inc(v___y_4388_);
lean_inc_ref(v___y_4387_);
lean_inc(v___y_4386_);
lean_inc_ref(v___y_4385_);
v___x_4462_ = lean_apply_5(v_x_4383_, v___y_4385_, v___y_4386_, v___y_4387_, v___y_4388_, lean_box(0));
return v___x_4462_;
}
else
{
goto v___jp_4396_;
}
}
else
{
if (v_isExporting_4395_ == 0)
{
goto v___jp_4396_;
}
else
{
lean_object* v___x_4463_; 
lean_inc(v___y_4388_);
lean_inc_ref(v___y_4387_);
lean_inc(v___y_4386_);
lean_inc_ref(v___y_4385_);
v___x_4463_ = lean_apply_5(v_x_4383_, v___y_4385_, v___y_4386_, v___y_4387_, v___y_4388_, lean_box(0));
return v___x_4463_;
}
}
v___jp_4396_:
{
lean_object* v___x_4397_; lean_object* v_env_4398_; lean_object* v_nextMacroScope_4399_; lean_object* v_ngen_4400_; lean_object* v_auxDeclNGen_4401_; lean_object* v_traceState_4402_; lean_object* v_recordedDeps_4403_; lean_object* v_messages_4404_; lean_object* v_infoState_4405_; lean_object* v_snapshotTasks_4406_; lean_object* v___x_4408_; uint8_t v_isShared_4409_; uint8_t v_isSharedCheck_4460_; 
v___x_4397_ = lean_st_ref_take(v___y_4388_);
v_env_4398_ = lean_ctor_get(v___x_4397_, 0);
v_nextMacroScope_4399_ = lean_ctor_get(v___x_4397_, 1);
v_ngen_4400_ = lean_ctor_get(v___x_4397_, 2);
v_auxDeclNGen_4401_ = lean_ctor_get(v___x_4397_, 3);
v_traceState_4402_ = lean_ctor_get(v___x_4397_, 4);
v_recordedDeps_4403_ = lean_ctor_get(v___x_4397_, 6);
v_messages_4404_ = lean_ctor_get(v___x_4397_, 7);
v_infoState_4405_ = lean_ctor_get(v___x_4397_, 8);
v_snapshotTasks_4406_ = lean_ctor_get(v___x_4397_, 9);
v_isSharedCheck_4460_ = !lean_is_exclusive(v___x_4397_);
if (v_isSharedCheck_4460_ == 0)
{
lean_object* v_unused_4461_; 
v_unused_4461_ = lean_ctor_get(v___x_4397_, 5);
lean_dec(v_unused_4461_);
v___x_4408_ = v___x_4397_;
v_isShared_4409_ = v_isSharedCheck_4460_;
goto v_resetjp_4407_;
}
else
{
lean_inc(v_snapshotTasks_4406_);
lean_inc(v_infoState_4405_);
lean_inc(v_messages_4404_);
lean_inc(v_recordedDeps_4403_);
lean_inc(v_traceState_4402_);
lean_inc(v_auxDeclNGen_4401_);
lean_inc(v_ngen_4400_);
lean_inc(v_nextMacroScope_4399_);
lean_inc(v_env_4398_);
lean_dec(v___x_4397_);
v___x_4408_ = lean_box(0);
v_isShared_4409_ = v_isSharedCheck_4460_;
goto v_resetjp_4407_;
}
v_resetjp_4407_:
{
lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4413_; 
v___x_4410_ = l_Lean_Environment_setExporting(v_env_4398_, v_isExporting_4384_);
v___x_4411_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1);
if (v_isShared_4409_ == 0)
{
lean_ctor_set(v___x_4408_, 5, v___x_4411_);
lean_ctor_set(v___x_4408_, 0, v___x_4410_);
v___x_4413_ = v___x_4408_;
goto v_reusejp_4412_;
}
else
{
lean_object* v_reuseFailAlloc_4459_; 
v_reuseFailAlloc_4459_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4459_, 0, v___x_4410_);
lean_ctor_set(v_reuseFailAlloc_4459_, 1, v_nextMacroScope_4399_);
lean_ctor_set(v_reuseFailAlloc_4459_, 2, v_ngen_4400_);
lean_ctor_set(v_reuseFailAlloc_4459_, 3, v_auxDeclNGen_4401_);
lean_ctor_set(v_reuseFailAlloc_4459_, 4, v_traceState_4402_);
lean_ctor_set(v_reuseFailAlloc_4459_, 5, v___x_4411_);
lean_ctor_set(v_reuseFailAlloc_4459_, 6, v_recordedDeps_4403_);
lean_ctor_set(v_reuseFailAlloc_4459_, 7, v_messages_4404_);
lean_ctor_set(v_reuseFailAlloc_4459_, 8, v_infoState_4405_);
lean_ctor_set(v_reuseFailAlloc_4459_, 9, v_snapshotTasks_4406_);
v___x_4413_ = v_reuseFailAlloc_4459_;
goto v_reusejp_4412_;
}
v_reusejp_4412_:
{
lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v_mctx_4416_; lean_object* v_zetaDeltaFVarIds_4417_; lean_object* v_postponed_4418_; lean_object* v_diag_4419_; lean_object* v___x_4421_; uint8_t v_isShared_4422_; uint8_t v_isSharedCheck_4457_; 
v___x_4414_ = lean_st_ref_put(v___y_4388_, v___x_4413_);
v___x_4415_ = lean_st_ref_take(v___y_4386_);
v_mctx_4416_ = lean_ctor_get(v___x_4415_, 0);
v_zetaDeltaFVarIds_4417_ = lean_ctor_get(v___x_4415_, 2);
v_postponed_4418_ = lean_ctor_get(v___x_4415_, 3);
v_diag_4419_ = lean_ctor_get(v___x_4415_, 4);
v_isSharedCheck_4457_ = !lean_is_exclusive(v___x_4415_);
if (v_isSharedCheck_4457_ == 0)
{
lean_object* v_unused_4458_; 
v_unused_4458_ = lean_ctor_get(v___x_4415_, 1);
lean_dec(v_unused_4458_);
v___x_4421_ = v___x_4415_;
v_isShared_4422_ = v_isSharedCheck_4457_;
goto v_resetjp_4420_;
}
else
{
lean_inc(v_diag_4419_);
lean_inc(v_postponed_4418_);
lean_inc(v_zetaDeltaFVarIds_4417_);
lean_inc(v_mctx_4416_);
lean_dec(v___x_4415_);
v___x_4421_ = lean_box(0);
v_isShared_4422_ = v_isSharedCheck_4457_;
goto v_resetjp_4420_;
}
v_resetjp_4420_:
{
lean_object* v___x_4423_; lean_object* v___x_4425_; 
v___x_4423_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__5, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__5_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__5);
if (v_isShared_4422_ == 0)
{
lean_ctor_set(v___x_4421_, 1, v___x_4423_);
v___x_4425_ = v___x_4421_;
goto v_reusejp_4424_;
}
else
{
lean_object* v_reuseFailAlloc_4456_; 
v_reuseFailAlloc_4456_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4456_, 0, v_mctx_4416_);
lean_ctor_set(v_reuseFailAlloc_4456_, 1, v___x_4423_);
lean_ctor_set(v_reuseFailAlloc_4456_, 2, v_zetaDeltaFVarIds_4417_);
lean_ctor_set(v_reuseFailAlloc_4456_, 3, v_postponed_4418_);
lean_ctor_set(v_reuseFailAlloc_4456_, 4, v_diag_4419_);
v___x_4425_ = v_reuseFailAlloc_4456_;
goto v_reusejp_4424_;
}
v_reusejp_4424_:
{
lean_object* v___x_4426_; lean_object* v_r_4427_; 
v___x_4426_ = lean_st_ref_put(v___y_4386_, v___x_4425_);
lean_inc(v___y_4388_);
lean_inc_ref(v___y_4387_);
lean_inc(v___y_4386_);
lean_inc_ref(v___y_4385_);
v_r_4427_ = lean_apply_5(v_x_4383_, v___y_4385_, v___y_4386_, v___y_4387_, v___y_4388_, lean_box(0));
if (lean_obj_tag(v_r_4427_) == 0)
{
lean_object* v_a_4428_; lean_object* v___x_4430_; uint8_t v_isShared_4431_; uint8_t v_isSharedCheck_4444_; 
v_a_4428_ = lean_ctor_get(v_r_4427_, 0);
v_isSharedCheck_4444_ = !lean_is_exclusive(v_r_4427_);
if (v_isSharedCheck_4444_ == 0)
{
v___x_4430_ = v_r_4427_;
v_isShared_4431_ = v_isSharedCheck_4444_;
goto v_resetjp_4429_;
}
else
{
lean_inc(v_a_4428_);
lean_dec(v_r_4427_);
v___x_4430_ = lean_box(0);
v_isShared_4431_ = v_isSharedCheck_4444_;
goto v_resetjp_4429_;
}
v_resetjp_4429_:
{
lean_object* v___x_4433_; 
lean_inc(v_a_4428_);
if (v_isShared_4431_ == 0)
{
lean_ctor_set_tag(v___x_4430_, 1);
v___x_4433_ = v___x_4430_;
goto v_reusejp_4432_;
}
else
{
lean_object* v_reuseFailAlloc_4443_; 
v_reuseFailAlloc_4443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4443_, 0, v_a_4428_);
v___x_4433_ = v_reuseFailAlloc_4443_;
goto v_reusejp_4432_;
}
v_reusejp_4432_:
{
lean_object* v___x_4434_; lean_object* v___x_4436_; uint8_t v_isShared_4437_; uint8_t v_isSharedCheck_4441_; 
v___x_4434_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(v___y_4388_, v_isExporting_4395_, v___x_4411_, v___y_4386_, v___x_4423_, v___x_4433_);
lean_dec_ref(v___x_4433_);
v_isSharedCheck_4441_ = !lean_is_exclusive(v___x_4434_);
if (v_isSharedCheck_4441_ == 0)
{
lean_object* v_unused_4442_; 
v_unused_4442_ = lean_ctor_get(v___x_4434_, 0);
lean_dec(v_unused_4442_);
v___x_4436_ = v___x_4434_;
v_isShared_4437_ = v_isSharedCheck_4441_;
goto v_resetjp_4435_;
}
else
{
lean_dec(v___x_4434_);
v___x_4436_ = lean_box(0);
v_isShared_4437_ = v_isSharedCheck_4441_;
goto v_resetjp_4435_;
}
v_resetjp_4435_:
{
lean_object* v___x_4439_; 
if (v_isShared_4437_ == 0)
{
lean_ctor_set(v___x_4436_, 0, v_a_4428_);
v___x_4439_ = v___x_4436_;
goto v_reusejp_4438_;
}
else
{
lean_object* v_reuseFailAlloc_4440_; 
v_reuseFailAlloc_4440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4440_, 0, v_a_4428_);
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
else
{
lean_object* v_a_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4449_; uint8_t v_isShared_4450_; uint8_t v_isSharedCheck_4454_; 
v_a_4445_ = lean_ctor_get(v_r_4427_, 0);
lean_inc(v_a_4445_);
lean_dec_ref_known(v_r_4427_, 1);
v___x_4446_ = lean_box(0);
v___x_4447_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(v___y_4388_, v_isExporting_4395_, v___x_4411_, v___y_4386_, v___x_4423_, v___x_4446_);
v_isSharedCheck_4454_ = !lean_is_exclusive(v___x_4447_);
if (v_isSharedCheck_4454_ == 0)
{
lean_object* v_unused_4455_; 
v_unused_4455_ = lean_ctor_get(v___x_4447_, 0);
lean_dec(v_unused_4455_);
v___x_4449_ = v___x_4447_;
v_isShared_4450_ = v_isSharedCheck_4454_;
goto v_resetjp_4448_;
}
else
{
lean_dec(v___x_4447_);
v___x_4449_ = lean_box(0);
v_isShared_4450_ = v_isSharedCheck_4454_;
goto v_resetjp_4448_;
}
v_resetjp_4448_:
{
lean_object* v___x_4452_; 
if (v_isShared_4450_ == 0)
{
lean_ctor_set_tag(v___x_4449_, 1);
lean_ctor_set(v___x_4449_, 0, v_a_4445_);
v___x_4452_ = v___x_4449_;
goto v_reusejp_4451_;
}
else
{
lean_object* v_reuseFailAlloc_4453_; 
v_reuseFailAlloc_4453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4453_, 0, v_a_4445_);
v___x_4452_ = v_reuseFailAlloc_4453_;
goto v_reusejp_4451_;
}
v_reusejp_4451_:
{
return v___x_4452_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___boxed(lean_object* v_x_4464_, lean_object* v_isExporting_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_){
_start:
{
uint8_t v_isExporting_boxed_4471_; lean_object* v_res_4472_; 
v_isExporting_boxed_4471_ = lean_unbox(v_isExporting_4465_);
v_res_4472_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(v_x_4464_, v_isExporting_boxed_4471_, v___y_4466_, v___y_4467_, v___y_4468_, v___y_4469_);
lean_dec(v___y_4469_);
lean_dec_ref(v___y_4468_);
lean_dec(v___y_4467_);
lean_dec_ref(v___y_4466_);
return v_res_4472_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(uint8_t v___x_4473_, uint8_t v___x_4474_, lean_object* v_as_x27_4475_, lean_object* v_b_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_){
_start:
{
if (lean_obj_tag(v_as_x27_4475_) == 0)
{
lean_object* v___x_4482_; 
v___x_4482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4482_, 0, v_b_4476_);
return v___x_4482_;
}
else
{
lean_object* v_head_4483_; lean_object* v_tail_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___f_4487_; uint8_t v___y_4489_; uint8_t v___x_4492_; 
v_head_4483_ = lean_ctor_get(v_as_x27_4475_, 0);
v_tail_4484_ = lean_ctor_get(v_as_x27_4475_, 1);
v___x_4485_ = lean_unsigned_to_nat(0u);
v___x_4486_ = lean_box(0);
lean_inc(v_head_4483_);
v___f_4487_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4487_, 0, v_head_4483_);
lean_closure_set(v___f_4487_, 1, v___x_4485_);
lean_closure_set(v___f_4487_, 2, v___x_4486_);
v___x_4492_ = l_Lean_isPrivateName(v_head_4483_);
if (v___x_4492_ == 0)
{
v___y_4489_ = v___x_4473_;
goto v___jp_4488_;
}
else
{
v___y_4489_ = v___x_4474_;
goto v___jp_4488_;
}
v___jp_4488_:
{
lean_object* v___x_4490_; 
v___x_4490_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(v___f_4487_, v___y_4489_, v___y_4477_, v___y_4478_, v___y_4479_, v___y_4480_);
if (lean_obj_tag(v___x_4490_) == 0)
{
lean_dec_ref_known(v___x_4490_, 1);
v_as_x27_4475_ = v_tail_4484_;
v_b_4476_ = v___x_4486_;
goto _start;
}
else
{
return v___x_4490_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___boxed(lean_object* v___x_4493_, lean_object* v___x_4494_, lean_object* v_as_x27_4495_, lean_object* v_b_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_){
_start:
{
uint8_t v___x_17792__boxed_4502_; uint8_t v___x_17793__boxed_4503_; lean_object* v_res_4504_; 
v___x_17792__boxed_4502_ = lean_unbox(v___x_4493_);
v___x_17793__boxed_4503_ = lean_unbox(v___x_4494_);
v_res_4504_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___x_17792__boxed_4502_, v___x_17793__boxed_4503_, v_as_x27_4495_, v_b_4496_, v___y_4497_, v___y_4498_, v___y_4499_, v___y_4500_);
lean_dec(v___y_4500_);
lean_dec_ref(v___y_4499_);
lean_dec(v___y_4498_);
lean_dec_ref(v___y_4497_);
lean_dec(v_as_x27_4495_);
return v_res_4504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__1(uint8_t v___x_4505_, uint8_t v_isUnsafe_4506_, lean_object* v_ctors_4507_, lean_object* v___x_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_){
_start:
{
lean_object* v___x_4514_; 
v___x_4514_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___x_4505_, v_isUnsafe_4506_, v_ctors_4507_, v___x_4508_, v___y_4509_, v___y_4510_, v___y_4511_, v___y_4512_);
if (lean_obj_tag(v___x_4514_) == 0)
{
lean_object* v___x_4516_; uint8_t v_isShared_4517_; uint8_t v_isSharedCheck_4521_; 
v_isSharedCheck_4521_ = !lean_is_exclusive(v___x_4514_);
if (v_isSharedCheck_4521_ == 0)
{
lean_object* v_unused_4522_; 
v_unused_4522_ = lean_ctor_get(v___x_4514_, 0);
lean_dec(v_unused_4522_);
v___x_4516_ = v___x_4514_;
v_isShared_4517_ = v_isSharedCheck_4521_;
goto v_resetjp_4515_;
}
else
{
lean_dec(v___x_4514_);
v___x_4516_ = lean_box(0);
v_isShared_4517_ = v_isSharedCheck_4521_;
goto v_resetjp_4515_;
}
v_resetjp_4515_:
{
lean_object* v___x_4519_; 
if (v_isShared_4517_ == 0)
{
lean_ctor_set(v___x_4516_, 0, v___x_4508_);
v___x_4519_ = v___x_4516_;
goto v_reusejp_4518_;
}
else
{
lean_object* v_reuseFailAlloc_4520_; 
v_reuseFailAlloc_4520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4520_, 0, v___x_4508_);
v___x_4519_ = v_reuseFailAlloc_4520_;
goto v_reusejp_4518_;
}
v_reusejp_4518_:
{
return v___x_4519_;
}
}
}
else
{
return v___x_4514_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed(lean_object* v___x_4523_, lean_object* v_isUnsafe_4524_, lean_object* v_ctors_4525_, lean_object* v___x_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_){
_start:
{
uint8_t v___x_17837__boxed_4532_; uint8_t v_isUnsafe_boxed_4533_; lean_object* v_res_4534_; 
v___x_17837__boxed_4532_ = lean_unbox(v___x_4523_);
v_isUnsafe_boxed_4533_ = lean_unbox(v_isUnsafe_4524_);
v_res_4534_ = l_Lean_Meta_mkInjectiveTheorems___lam__1(v___x_17837__boxed_4532_, v_isUnsafe_boxed_4533_, v_ctors_4525_, v___x_4526_, v___y_4527_, v___y_4528_, v___y_4529_, v___y_4530_);
lean_dec(v___y_4530_);
lean_dec_ref(v___y_4529_);
lean_dec(v___y_4528_);
lean_dec_ref(v___y_4527_);
lean_dec(v_ctors_4525_);
return v_res_4534_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4536_; lean_object* v___x_4537_; 
v___x_4536_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__0));
v___x_4537_ = l_Lean_stringToMessageData(v___x_4536_);
return v___x_4537_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(lean_object* v_constName_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_){
_start:
{
lean_object* v___x_4544_; lean_object* v_env_4545_; lean_object* v___x_4546_; 
v___x_4544_ = lean_st_ref_get(v___y_4542_);
v_env_4545_ = lean_ctor_get(v___x_4544_, 0);
lean_inc_ref(v_env_4545_);
lean_dec(v___x_4544_);
lean_inc(v_constName_4538_);
v___x_4546_ = l_Lean_isInductiveCore_x3f(v_env_4545_, v_constName_4538_);
if (lean_obj_tag(v___x_4546_) == 0)
{
lean_object* v___x_4547_; uint8_t v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; 
v___x_4547_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_4548_ = 0;
v___x_4549_ = l_Lean_MessageData_ofConstName(v_constName_4538_, v___x_4548_);
v___x_4550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4550_, 0, v___x_4547_);
lean_ctor_set(v___x_4550_, 1, v___x_4549_);
v___x_4551_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1);
v___x_4552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4552_, 0, v___x_4550_);
lean_ctor_set(v___x_4552_, 1, v___x_4551_);
v___x_4553_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_4552_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_);
return v___x_4553_;
}
else
{
lean_object* v_val_4554_; lean_object* v___x_4556_; uint8_t v_isShared_4557_; uint8_t v_isSharedCheck_4561_; 
lean_dec(v_constName_4538_);
v_val_4554_ = lean_ctor_get(v___x_4546_, 0);
v_isSharedCheck_4561_ = !lean_is_exclusive(v___x_4546_);
if (v_isSharedCheck_4561_ == 0)
{
v___x_4556_ = v___x_4546_;
v_isShared_4557_ = v_isSharedCheck_4561_;
goto v_resetjp_4555_;
}
else
{
lean_inc(v_val_4554_);
lean_dec(v___x_4546_);
v___x_4556_ = lean_box(0);
v_isShared_4557_ = v_isSharedCheck_4561_;
goto v_resetjp_4555_;
}
v_resetjp_4555_:
{
lean_object* v___x_4559_; 
if (v_isShared_4557_ == 0)
{
lean_ctor_set_tag(v___x_4556_, 0);
v___x_4559_ = v___x_4556_;
goto v_reusejp_4558_;
}
else
{
lean_object* v_reuseFailAlloc_4560_; 
v_reuseFailAlloc_4560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4560_, 0, v_val_4554_);
v___x_4559_ = v_reuseFailAlloc_4560_;
goto v_reusejp_4558_;
}
v_reusejp_4558_:
{
return v___x_4559_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___boxed(lean_object* v_constName_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_){
_start:
{
lean_object* v_res_4568_; 
v_res_4568_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_constName_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_);
lean_dec(v___y_4566_);
lean_dec_ref(v___y_4565_);
lean_dec(v___y_4564_);
lean_dec_ref(v___y_4563_);
return v_res_4568_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__0(void){
_start:
{
lean_object* v___x_4569_; lean_object* v___x_4570_; 
v___x_4569_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2_spec__3_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2_spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2_spec__3_spec__5___redArg___closed__0);
v___x_4570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4570_, 0, v___x_4569_);
return v___x_4570_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__1(void){
_start:
{
lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; 
v___x_4571_ = lean_unsigned_to_nat(32u);
v___x_4572_ = lean_mk_empty_array_with_capacity(v___x_4571_);
v___x_4573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4573_, 0, v___x_4572_);
return v___x_4573_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__2(void){
_start:
{
size_t v___x_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; 
v___x_4574_ = ((size_t)5ULL);
v___x_4575_ = lean_unsigned_to_nat(0u);
v___x_4576_ = lean_unsigned_to_nat(32u);
v___x_4577_ = lean_mk_empty_array_with_capacity(v___x_4576_);
v___x_4578_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_4579_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4579_, 0, v___x_4578_);
lean_ctor_set(v___x_4579_, 1, v___x_4577_);
lean_ctor_set(v___x_4579_, 2, v___x_4575_);
lean_ctor_set(v___x_4579_, 3, v___x_4575_);
lean_ctor_set_usize(v___x_4579_, 4, v___x_4574_);
return v___x_4579_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__3(void){
_start:
{
lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; 
v___x_4580_ = lean_box(1);
v___x_4581_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__2, &l_Lean_Meta_mkInjectiveTheorems___closed__2_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__2);
v___x_4582_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__0, &l_Lean_Meta_mkInjectiveTheorems___closed__0_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__0);
v___x_4583_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4583_, 0, v___x_4582_);
lean_ctor_set(v___x_4583_, 1, v___x_4581_);
lean_ctor_set(v___x_4583_, 2, v___x_4580_);
return v___x_4583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems(lean_object* v_declName_4586_, lean_object* v_a_4587_, lean_object* v_a_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_){
_start:
{
lean_object* v___f_4592_; lean_object* v___x_4593_; lean_object* v_env_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; 
lean_inc_n(v_declName_4586_, 2);
v___f_4592_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4592_, 0, v_declName_4586_);
v___x_4593_ = lean_st_ref_get(v_a_4590_);
v_env_4594_ = lean_ctor_get(v___x_4593_, 0);
lean_inc_ref(v_env_4594_);
lean_dec(v___x_4593_);
v___x_4595_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_4589_);
v___x_4596_ = l_Lean_Meta_isInductivePredicate(v_declName_4586_, v_a_4587_, v_a_4588_, v_a_4589_, v_a_4590_);
if (lean_obj_tag(v___x_4596_) == 0)
{
lean_object* v_a_4597_; lean_object* v___x_4599_; uint8_t v_isShared_4600_; uint8_t v_isSharedCheck_4760_; 
v_a_4597_ = lean_ctor_get(v___x_4596_, 0);
v_isSharedCheck_4760_ = !lean_is_exclusive(v___x_4596_);
if (v_isSharedCheck_4760_ == 0)
{
v___x_4599_ = v___x_4596_;
v_isShared_4600_ = v_isSharedCheck_4760_;
goto v_resetjp_4598_;
}
else
{
lean_inc(v_a_4597_);
lean_dec(v___x_4596_);
v___x_4599_ = lean_box(0);
v_isShared_4600_ = v_isSharedCheck_4760_;
goto v_resetjp_4598_;
}
v_resetjp_4598_:
{
lean_object* v___x_4606_; uint8_t v___x_4607_; uint8_t v___x_4608_; 
v___x_4606_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__4));
v___x_4607_ = 1;
v___x_4608_ = l_Lean_Environment_contains(v_env_4594_, v___x_4606_, v___x_4607_);
if (v___x_4608_ == 0)
{
lean_dec(v_a_4597_);
lean_dec_ref(v___x_4595_);
lean_dec_ref(v___f_4592_);
lean_dec(v_declName_4586_);
goto v___jp_4601_;
}
else
{
lean_object* v___x_4609_; uint8_t v___x_4610_; 
v___x_4609_ = l_Lean_Meta_genInjectivity;
v___x_4610_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v___x_4595_, v___x_4609_);
lean_dec_ref(v___x_4595_);
if (v___x_4610_ == 0)
{
lean_dec(v_a_4597_);
lean_dec_ref(v___f_4592_);
lean_dec(v_declName_4586_);
goto v___jp_4601_;
}
else
{
uint8_t v___x_4611_; 
v___x_4611_ = lean_unbox(v_a_4597_);
lean_dec(v_a_4597_);
if (v___x_4611_ == 0)
{
lean_object* v_toCold_4612_; lean_object* v_options_4613_; uint8_t v_hasTrace_4614_; 
lean_del_object(v___x_4599_);
v_toCold_4612_ = lean_ctor_get(v_a_4589_, 0);
v_options_4613_ = lean_ctor_get(v_toCold_4612_, 2);
v_hasTrace_4614_ = lean_ctor_get_uint8(v_options_4613_, sizeof(void*)*1);
if (v_hasTrace_4614_ == 0)
{
lean_object* v___x_4615_; 
lean_dec_ref(v___f_4592_);
v___x_4615_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4586_, v_a_4587_, v_a_4588_, v_a_4589_, v_a_4590_);
if (lean_obj_tag(v___x_4615_) == 0)
{
lean_object* v_a_4616_; lean_object* v___x_4618_; uint8_t v_isShared_4619_; uint8_t v_isSharedCheck_4633_; 
v_a_4616_ = lean_ctor_get(v___x_4615_, 0);
v_isSharedCheck_4633_ = !lean_is_exclusive(v___x_4615_);
if (v_isSharedCheck_4633_ == 0)
{
v___x_4618_ = v___x_4615_;
v_isShared_4619_ = v_isSharedCheck_4633_;
goto v_resetjp_4617_;
}
else
{
lean_inc(v_a_4616_);
lean_dec(v___x_4615_);
v___x_4618_ = lean_box(0);
v_isShared_4619_ = v_isSharedCheck_4633_;
goto v_resetjp_4617_;
}
v_resetjp_4617_:
{
uint8_t v_isUnsafe_4620_; 
v_isUnsafe_4620_ = lean_ctor_get_uint8(v_a_4616_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4620_ == 0)
{
lean_object* v_ctors_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; lean_object* v___f_4627_; lean_object* v___x_4628_; 
lean_del_object(v___x_4618_);
v_ctors_4621_ = lean_ctor_get(v_a_4616_, 4);
lean_inc(v_ctors_4621_);
lean_dec(v_a_4616_);
v___x_4622_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_4623_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__4));
v___x_4624_ = lean_box(0);
v___x_4625_ = lean_box(v___x_4610_);
v___x_4626_ = lean_box(v_isUnsafe_4620_);
v___f_4627_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed), 9, 4);
lean_closure_set(v___f_4627_, 0, v___x_4625_);
lean_closure_set(v___f_4627_, 1, v___x_4626_);
lean_closure_set(v___f_4627_, 2, v_ctors_4621_);
lean_closure_set(v___f_4627_, 3, v___x_4624_);
v___x_4628_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4622_, v___x_4623_, v___f_4627_, v_a_4587_, v_a_4588_, v_a_4589_, v_a_4590_);
return v___x_4628_;
}
else
{
lean_object* v___x_4629_; lean_object* v___x_4631_; 
lean_dec(v_a_4616_);
v___x_4629_ = lean_box(0);
if (v_isShared_4619_ == 0)
{
lean_ctor_set(v___x_4618_, 0, v___x_4629_);
v___x_4631_ = v___x_4618_;
goto v_reusejp_4630_;
}
else
{
lean_object* v_reuseFailAlloc_4632_; 
v_reuseFailAlloc_4632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4632_, 0, v___x_4629_);
v___x_4631_ = v_reuseFailAlloc_4632_;
goto v_reusejp_4630_;
}
v_reusejp_4630_:
{
return v___x_4631_;
}
}
}
}
else
{
lean_object* v_a_4634_; lean_object* v___x_4636_; uint8_t v_isShared_4637_; uint8_t v_isSharedCheck_4641_; 
v_a_4634_ = lean_ctor_get(v___x_4615_, 0);
v_isSharedCheck_4641_ = !lean_is_exclusive(v___x_4615_);
if (v_isSharedCheck_4641_ == 0)
{
v___x_4636_ = v___x_4615_;
v_isShared_4637_ = v_isSharedCheck_4641_;
goto v_resetjp_4635_;
}
else
{
lean_inc(v_a_4634_);
lean_dec(v___x_4615_);
v___x_4636_ = lean_box(0);
v_isShared_4637_ = v_isSharedCheck_4641_;
goto v_resetjp_4635_;
}
v_resetjp_4635_:
{
lean_object* v___x_4639_; 
if (v_isShared_4637_ == 0)
{
v___x_4639_ = v___x_4636_;
goto v_reusejp_4638_;
}
else
{
lean_object* v_reuseFailAlloc_4640_; 
v_reuseFailAlloc_4640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4640_, 0, v_a_4634_);
v___x_4639_ = v_reuseFailAlloc_4640_;
goto v_reusejp_4638_;
}
v_reusejp_4638_:
{
return v___x_4639_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; uint8_t v___x_4646_; lean_object* v___y_4648_; lean_object* v___y_4649_; lean_object* v_a_4650_; lean_object* v___y_4663_; lean_object* v___y_4664_; lean_object* v_a_4665_; lean_object* v___y_4668_; lean_object* v___y_4669_; lean_object* v_a_4670_; lean_object* v___y_4673_; lean_object* v___y_4674_; lean_object* v_a_4675_; lean_object* v___y_4685_; lean_object* v___y_4686_; lean_object* v_a_4687_; lean_object* v___y_4690_; lean_object* v___y_4691_; lean_object* v_a_4692_; 
v_inheritedTraceOptions_4642_ = lean_ctor_get(v_toCold_4612_, 11);
v___x_4643_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_4644_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_4645_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_4646_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4642_, v_options_4613_, v___x_4645_);
if (v___x_4646_ == 0)
{
lean_object* v___x_4731_; uint8_t v___x_4732_; 
v___x_4731_ = l_Lean_trace_profiler;
v___x_4732_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_4613_, v___x_4731_);
if (v___x_4732_ == 0)
{
lean_object* v___x_4733_; 
lean_dec_ref(v___f_4592_);
v___x_4733_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4586_, v_a_4587_, v_a_4588_, v_a_4589_, v_a_4590_);
if (lean_obj_tag(v___x_4733_) == 0)
{
lean_object* v_a_4734_; lean_object* v___x_4736_; uint8_t v_isShared_4737_; uint8_t v_isSharedCheck_4751_; 
v_a_4734_ = lean_ctor_get(v___x_4733_, 0);
v_isSharedCheck_4751_ = !lean_is_exclusive(v___x_4733_);
if (v_isSharedCheck_4751_ == 0)
{
v___x_4736_ = v___x_4733_;
v_isShared_4737_ = v_isSharedCheck_4751_;
goto v_resetjp_4735_;
}
else
{
lean_inc(v_a_4734_);
lean_dec(v___x_4733_);
v___x_4736_ = lean_box(0);
v_isShared_4737_ = v_isSharedCheck_4751_;
goto v_resetjp_4735_;
}
v_resetjp_4735_:
{
uint8_t v_isUnsafe_4738_; 
v_isUnsafe_4738_ = lean_ctor_get_uint8(v_a_4734_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4738_ == 0)
{
lean_object* v_ctors_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; lean_object* v___f_4745_; lean_object* v___x_4746_; 
lean_del_object(v___x_4736_);
v_ctors_4739_ = lean_ctor_get(v_a_4734_, 4);
lean_inc(v_ctors_4739_);
lean_dec(v_a_4734_);
v___x_4740_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_4741_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__4));
v___x_4742_ = lean_box(0);
v___x_4743_ = lean_box(v___x_4610_);
v___x_4744_ = lean_box(v_isUnsafe_4738_);
v___f_4745_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed), 9, 4);
lean_closure_set(v___f_4745_, 0, v___x_4743_);
lean_closure_set(v___f_4745_, 1, v___x_4744_);
lean_closure_set(v___f_4745_, 2, v_ctors_4739_);
lean_closure_set(v___f_4745_, 3, v___x_4742_);
v___x_4746_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4740_, v___x_4741_, v___f_4745_, v_a_4587_, v_a_4588_, v_a_4589_, v_a_4590_);
return v___x_4746_;
}
else
{
lean_object* v___x_4747_; lean_object* v___x_4749_; 
lean_dec(v_a_4734_);
v___x_4747_ = lean_box(0);
if (v_isShared_4737_ == 0)
{
lean_ctor_set(v___x_4736_, 0, v___x_4747_);
v___x_4749_ = v___x_4736_;
goto v_reusejp_4748_;
}
else
{
lean_object* v_reuseFailAlloc_4750_; 
v_reuseFailAlloc_4750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4750_, 0, v___x_4747_);
v___x_4749_ = v_reuseFailAlloc_4750_;
goto v_reusejp_4748_;
}
v_reusejp_4748_:
{
return v___x_4749_;
}
}
}
}
else
{
lean_object* v_a_4752_; lean_object* v___x_4754_; uint8_t v_isShared_4755_; uint8_t v_isSharedCheck_4759_; 
v_a_4752_ = lean_ctor_get(v___x_4733_, 0);
v_isSharedCheck_4759_ = !lean_is_exclusive(v___x_4733_);
if (v_isSharedCheck_4759_ == 0)
{
v___x_4754_ = v___x_4733_;
v_isShared_4755_ = v_isSharedCheck_4759_;
goto v_resetjp_4753_;
}
else
{
lean_inc(v_a_4752_);
lean_dec(v___x_4733_);
v___x_4754_ = lean_box(0);
v_isShared_4755_ = v_isSharedCheck_4759_;
goto v_resetjp_4753_;
}
v_resetjp_4753_:
{
lean_object* v___x_4757_; 
if (v_isShared_4755_ == 0)
{
v___x_4757_ = v___x_4754_;
goto v_reusejp_4756_;
}
else
{
lean_object* v_reuseFailAlloc_4758_; 
v_reuseFailAlloc_4758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4758_, 0, v_a_4752_);
v___x_4757_ = v_reuseFailAlloc_4758_;
goto v_reusejp_4756_;
}
v_reusejp_4756_:
{
return v___x_4757_;
}
}
}
}
else
{
goto v___jp_4694_;
}
}
else
{
goto v___jp_4694_;
}
v___jp_4647_:
{
lean_object* v___x_4651_; double v___x_4652_; double v___x_4653_; double v___x_4654_; double v___x_4655_; double v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; 
v___x_4651_ = lean_io_mono_nanos_now();
v___x_4652_ = lean_float_of_nat(v___y_4648_);
v___x_4653_ = lean_float_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0);
v___x_4654_ = lean_float_div(v___x_4652_, v___x_4653_);
v___x_4655_ = lean_float_of_nat(v___x_4651_);
v___x_4656_ = lean_float_div(v___x_4655_, v___x_4653_);
v___x_4657_ = lean_box_float(v___x_4654_);
v___x_4658_ = lean_box_float(v___x_4656_);
v___x_4659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4659_, 0, v___x_4657_);
lean_ctor_set(v___x_4659_, 1, v___x_4658_);
v___x_4660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4660_, 0, v_a_4650_);
lean_ctor_set(v___x_4660_, 1, v___x_4659_);
v___x_4661_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v___x_4643_, v___x_4607_, v___x_4644_, v_options_4613_, v___x_4646_, v___y_4649_, v___f_4592_, v___x_4660_, v_a_4587_, v_a_4588_, v_a_4589_, v_a_4590_);
return v___x_4661_;
}
v___jp_4662_:
{
lean_object* v___x_4666_; 
v___x_4666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4666_, 0, v_a_4665_);
v___y_4648_ = v___y_4663_;
v___y_4649_ = v___y_4664_;
v_a_4650_ = v___x_4666_;
goto v___jp_4647_;
}
v___jp_4667_:
{
lean_object* v___x_4671_; 
v___x_4671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4671_, 0, v_a_4670_);
v___y_4648_ = v___y_4668_;
v___y_4649_ = v___y_4669_;
v_a_4650_ = v___x_4671_;
goto v___jp_4647_;
}
v___jp_4672_:
{
lean_object* v___x_4676_; double v___x_4677_; double v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; 
v___x_4676_ = lean_io_get_num_heartbeats();
v___x_4677_ = lean_float_of_nat(v___y_4673_);
v___x_4678_ = lean_float_of_nat(v___x_4676_);
v___x_4679_ = lean_box_float(v___x_4677_);
v___x_4680_ = lean_box_float(v___x_4678_);
v___x_4681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4681_, 0, v___x_4679_);
lean_ctor_set(v___x_4681_, 1, v___x_4680_);
v___x_4682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4682_, 0, v_a_4675_);
lean_ctor_set(v___x_4682_, 1, v___x_4681_);
v___x_4683_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v___x_4643_, v___x_4607_, v___x_4644_, v_options_4613_, v___x_4646_, v___y_4674_, v___f_4592_, v___x_4682_, v_a_4587_, v_a_4588_, v_a_4589_, v_a_4590_);
return v___x_4683_;
}
v___jp_4684_:
{
lean_object* v___x_4688_; 
v___x_4688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4688_, 0, v_a_4687_);
v___y_4673_ = v___y_4685_;
v___y_4674_ = v___y_4686_;
v_a_4675_ = v___x_4688_;
goto v___jp_4672_;
}
v___jp_4689_:
{
lean_object* v___x_4693_; 
v___x_4693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4693_, 0, v_a_4692_);
v___y_4673_ = v___y_4690_;
v___y_4674_ = v___y_4691_;
v_a_4675_ = v___x_4693_;
goto v___jp_4672_;
}
v___jp_4694_:
{
lean_object* v___x_4695_; lean_object* v_a_4696_; lean_object* v___x_4697_; uint8_t v___x_4698_; 
v___x_4695_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v_a_4590_);
v_a_4696_ = lean_ctor_get(v___x_4695_, 0);
lean_inc(v_a_4696_);
lean_dec_ref(v___x_4695_);
v___x_4697_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4698_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_4613_, v___x_4697_);
if (v___x_4698_ == 0)
{
lean_object* v___x_4699_; lean_object* v___x_4700_; 
v___x_4699_ = lean_io_mono_nanos_now();
v___x_4700_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4586_, v_a_4587_, v_a_4588_, v_a_4589_, v_a_4590_);
if (lean_obj_tag(v___x_4700_) == 0)
{
lean_object* v_a_4701_; uint8_t v_isUnsafe_4702_; 
v_a_4701_ = lean_ctor_get(v___x_4700_, 0);
lean_inc(v_a_4701_);
lean_dec_ref_known(v___x_4700_, 1);
v_isUnsafe_4702_ = lean_ctor_get_uint8(v_a_4701_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4702_ == 0)
{
lean_object* v_ctors_4703_; lean_object* v___x_4704_; lean_object* v___x_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___f_4709_; lean_object* v___x_4710_; 
v_ctors_4703_ = lean_ctor_get(v_a_4701_, 4);
lean_inc(v_ctors_4703_);
lean_dec(v_a_4701_);
v___x_4704_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_4705_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__4));
v___x_4706_ = lean_box(0);
v___x_4707_ = lean_box(v___x_4610_);
v___x_4708_ = lean_box(v_isUnsafe_4702_);
v___f_4709_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed), 9, 4);
lean_closure_set(v___f_4709_, 0, v___x_4707_);
lean_closure_set(v___f_4709_, 1, v___x_4708_);
lean_closure_set(v___f_4709_, 2, v_ctors_4703_);
lean_closure_set(v___f_4709_, 3, v___x_4706_);
v___x_4710_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4704_, v___x_4705_, v___f_4709_, v_a_4587_, v_a_4588_, v_a_4589_, v_a_4590_);
if (lean_obj_tag(v___x_4710_) == 0)
{
lean_object* v_a_4711_; 
v_a_4711_ = lean_ctor_get(v___x_4710_, 0);
lean_inc(v_a_4711_);
lean_dec_ref_known(v___x_4710_, 1);
v___y_4668_ = v___x_4699_;
v___y_4669_ = v_a_4696_;
v_a_4670_ = v_a_4711_;
goto v___jp_4667_;
}
else
{
lean_object* v_a_4712_; 
v_a_4712_ = lean_ctor_get(v___x_4710_, 0);
lean_inc(v_a_4712_);
lean_dec_ref_known(v___x_4710_, 1);
v___y_4663_ = v___x_4699_;
v___y_4664_ = v_a_4696_;
v_a_4665_ = v_a_4712_;
goto v___jp_4662_;
}
}
else
{
lean_object* v___x_4713_; 
lean_dec(v_a_4701_);
v___x_4713_ = lean_box(0);
v___y_4668_ = v___x_4699_;
v___y_4669_ = v_a_4696_;
v_a_4670_ = v___x_4713_;
goto v___jp_4667_;
}
}
else
{
lean_object* v_a_4714_; 
v_a_4714_ = lean_ctor_get(v___x_4700_, 0);
lean_inc(v_a_4714_);
lean_dec_ref_known(v___x_4700_, 1);
v___y_4663_ = v___x_4699_;
v___y_4664_ = v_a_4696_;
v_a_4665_ = v_a_4714_;
goto v___jp_4662_;
}
}
else
{
lean_object* v___x_4715_; lean_object* v___x_4716_; 
v___x_4715_ = lean_io_get_num_heartbeats();
v___x_4716_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4586_, v_a_4587_, v_a_4588_, v_a_4589_, v_a_4590_);
if (lean_obj_tag(v___x_4716_) == 0)
{
lean_object* v_a_4717_; uint8_t v_isUnsafe_4718_; 
v_a_4717_ = lean_ctor_get(v___x_4716_, 0);
lean_inc(v_a_4717_);
lean_dec_ref_known(v___x_4716_, 1);
v_isUnsafe_4718_ = lean_ctor_get_uint8(v_a_4717_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4718_ == 0)
{
lean_object* v_ctors_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; lean_object* v___f_4725_; lean_object* v___x_4726_; 
v_ctors_4719_ = lean_ctor_get(v_a_4717_, 4);
lean_inc(v_ctors_4719_);
lean_dec(v_a_4717_);
v___x_4720_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_4721_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__4));
v___x_4722_ = lean_box(0);
v___x_4723_ = lean_box(v___x_4610_);
v___x_4724_ = lean_box(v_isUnsafe_4718_);
v___f_4725_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed), 9, 4);
lean_closure_set(v___f_4725_, 0, v___x_4723_);
lean_closure_set(v___f_4725_, 1, v___x_4724_);
lean_closure_set(v___f_4725_, 2, v_ctors_4719_);
lean_closure_set(v___f_4725_, 3, v___x_4722_);
v___x_4726_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4720_, v___x_4721_, v___f_4725_, v_a_4587_, v_a_4588_, v_a_4589_, v_a_4590_);
if (lean_obj_tag(v___x_4726_) == 0)
{
lean_object* v_a_4727_; 
v_a_4727_ = lean_ctor_get(v___x_4726_, 0);
lean_inc(v_a_4727_);
lean_dec_ref_known(v___x_4726_, 1);
v___y_4685_ = v___x_4715_;
v___y_4686_ = v_a_4696_;
v_a_4687_ = v_a_4727_;
goto v___jp_4684_;
}
else
{
lean_object* v_a_4728_; 
v_a_4728_ = lean_ctor_get(v___x_4726_, 0);
lean_inc(v_a_4728_);
lean_dec_ref_known(v___x_4726_, 1);
v___y_4690_ = v___x_4715_;
v___y_4691_ = v_a_4696_;
v_a_4692_ = v_a_4728_;
goto v___jp_4689_;
}
}
else
{
lean_object* v___x_4729_; 
lean_dec(v_a_4717_);
v___x_4729_ = lean_box(0);
v___y_4685_ = v___x_4715_;
v___y_4686_ = v_a_4696_;
v_a_4687_ = v___x_4729_;
goto v___jp_4684_;
}
}
else
{
lean_object* v_a_4730_; 
v_a_4730_ = lean_ctor_get(v___x_4716_, 0);
lean_inc(v_a_4730_);
lean_dec_ref_known(v___x_4716_, 1);
v___y_4690_ = v___x_4715_;
v___y_4691_ = v_a_4696_;
v_a_4692_ = v_a_4730_;
goto v___jp_4689_;
}
}
}
}
}
else
{
lean_dec_ref(v___f_4592_);
lean_dec(v_declName_4586_);
goto v___jp_4601_;
}
}
}
v___jp_4601_:
{
lean_object* v___x_4602_; lean_object* v___x_4604_; 
v___x_4602_ = lean_box(0);
if (v_isShared_4600_ == 0)
{
lean_ctor_set(v___x_4599_, 0, v___x_4602_);
v___x_4604_ = v___x_4599_;
goto v_reusejp_4603_;
}
else
{
lean_object* v_reuseFailAlloc_4605_; 
v_reuseFailAlloc_4605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4605_, 0, v___x_4602_);
v___x_4604_ = v_reuseFailAlloc_4605_;
goto v_reusejp_4603_;
}
v_reusejp_4603_:
{
return v___x_4604_;
}
}
}
}
else
{
lean_object* v_a_4761_; lean_object* v___x_4763_; uint8_t v_isShared_4764_; uint8_t v_isSharedCheck_4768_; 
lean_dec_ref(v___x_4595_);
lean_dec_ref(v_env_4594_);
lean_dec_ref(v___f_4592_);
lean_dec(v_declName_4586_);
v_a_4761_ = lean_ctor_get(v___x_4596_, 0);
v_isSharedCheck_4768_ = !lean_is_exclusive(v___x_4596_);
if (v_isSharedCheck_4768_ == 0)
{
v___x_4763_ = v___x_4596_;
v_isShared_4764_ = v_isSharedCheck_4768_;
goto v_resetjp_4762_;
}
else
{
lean_inc(v_a_4761_);
lean_dec(v___x_4596_);
v___x_4763_ = lean_box(0);
v_isShared_4764_ = v_isSharedCheck_4768_;
goto v_resetjp_4762_;
}
v_resetjp_4762_:
{
lean_object* v___x_4766_; 
if (v_isShared_4764_ == 0)
{
v___x_4766_ = v___x_4763_;
goto v_reusejp_4765_;
}
else
{
lean_object* v_reuseFailAlloc_4767_; 
v_reuseFailAlloc_4767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4767_, 0, v_a_4761_);
v___x_4766_ = v_reuseFailAlloc_4767_;
goto v_reusejp_4765_;
}
v_reusejp_4765_:
{
return v___x_4766_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___boxed(lean_object* v_declName_4769_, lean_object* v_a_4770_, lean_object* v_a_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_, lean_object* v_a_4774_){
_start:
{
lean_object* v_res_4775_; 
v_res_4775_ = l_Lean_Meta_mkInjectiveTheorems(v_declName_4769_, v_a_4770_, v_a_4771_, v_a_4772_, v_a_4773_);
lean_dec(v_a_4773_);
lean_dec_ref(v_a_4772_);
lean_dec(v_a_4771_);
lean_dec_ref(v_a_4770_);
return v_res_4775_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2(lean_object* v_00_u03b1_4776_, lean_object* v_x_4777_, uint8_t v_isExporting_4778_, lean_object* v___y_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_, lean_object* v___y_4782_){
_start:
{
lean_object* v___x_4784_; 
v___x_4784_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(v_x_4777_, v_isExporting_4778_, v___y_4779_, v___y_4780_, v___y_4781_, v___y_4782_);
return v___x_4784_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___boxed(lean_object* v_00_u03b1_4785_, lean_object* v_x_4786_, lean_object* v_isExporting_4787_, lean_object* v___y_4788_, lean_object* v___y_4789_, lean_object* v___y_4790_, lean_object* v___y_4791_, lean_object* v___y_4792_){
_start:
{
uint8_t v_isExporting_boxed_4793_; lean_object* v_res_4794_; 
v_isExporting_boxed_4793_ = lean_unbox(v_isExporting_4787_);
v_res_4794_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2(v_00_u03b1_4785_, v_x_4786_, v_isExporting_boxed_4793_, v___y_4788_, v___y_4789_, v___y_4790_, v___y_4791_);
lean_dec(v___y_4791_);
lean_dec_ref(v___y_4790_);
lean_dec(v___y_4789_);
lean_dec_ref(v___y_4788_);
return v_res_4794_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3(uint8_t v___x_4795_, uint8_t v___x_4796_, lean_object* v_as_4797_, lean_object* v_as_x27_4798_, lean_object* v_b_4799_, lean_object* v_a_4800_, lean_object* v___y_4801_, lean_object* v___y_4802_, lean_object* v___y_4803_, lean_object* v___y_4804_){
_start:
{
lean_object* v___x_4806_; 
v___x_4806_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___x_4795_, v___x_4796_, v_as_x27_4798_, v_b_4799_, v___y_4801_, v___y_4802_, v___y_4803_, v___y_4804_);
return v___x_4806_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___boxed(lean_object* v___x_4807_, lean_object* v___x_4808_, lean_object* v_as_4809_, lean_object* v_as_x27_4810_, lean_object* v_b_4811_, lean_object* v_a_4812_, lean_object* v___y_4813_, lean_object* v___y_4814_, lean_object* v___y_4815_, lean_object* v___y_4816_, lean_object* v___y_4817_){
_start:
{
uint8_t v___x_18418__boxed_4818_; uint8_t v___x_18419__boxed_4819_; lean_object* v_res_4820_; 
v___x_18418__boxed_4818_ = lean_unbox(v___x_4807_);
v___x_18419__boxed_4819_ = lean_unbox(v___x_4808_);
v_res_4820_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3(v___x_18418__boxed_4818_, v___x_18419__boxed_4819_, v_as_4809_, v_as_x27_4810_, v_b_4811_, v_a_4812_, v___y_4813_, v___y_4814_, v___y_4815_, v___y_4816_);
lean_dec(v___y_4816_);
lean_dec_ref(v___y_4815_);
lean_dec(v___y_4814_);
lean_dec_ref(v___y_4813_);
lean_dec(v_as_x27_4810_);
lean_dec(v_as_4809_);
return v_res_4820_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_4821_){
_start:
{
lean_object* v___x_4822_; 
v___x_4822_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2);
return v___x_4822_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2_spec__3___redArg(){
_start:
{
lean_object* v___x_4824_; 
v___x_4824_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2);
return v___x_4824_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2_spec__3___redArg___boxed(lean_object* v___dummy_4825_){
_start:
{
lean_object* v_res_4826_; 
v_res_4826_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2_spec__3___redArg();
return v_res_4826_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2_spec__3(lean_object* v_00_u03b2_4827_){
_start:
{
lean_object* v___x_4828_; 
v___x_4828_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2);
return v___x_4828_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; 
v___x_4869_ = lean_unsigned_to_nat(4172903888u);
v___x_4870_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_));
v___x_4871_ = l_Lean_Name_num___override(v___x_4870_, v___x_4869_);
return v___x_4871_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4873_; lean_object* v___x_4874_; lean_object* v___x_4875_; 
v___x_4873_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_));
v___x_4874_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4875_ = l_Lean_Name_str___override(v___x_4874_, v___x_4873_);
return v___x_4875_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; 
v___x_4877_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_));
v___x_4878_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4879_ = l_Lean_Name_str___override(v___x_4878_, v___x_4877_);
return v___x_4879_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4880_; lean_object* v___x_4881_; lean_object* v___x_4882_; 
v___x_4880_ = lean_unsigned_to_nat(2u);
v___x_4881_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4882_ = l_Lean_Name_num___override(v___x_4881_, v___x_4880_);
return v___x_4882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4884_; uint8_t v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; 
v___x_4884_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_4885_ = 0;
v___x_4886_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4887_ = l_Lean_registerTraceClass(v___x_4884_, v___x_4885_, v___x_4886_);
return v___x_4887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2____boxed(lean_object* v_a_4888_){
_start:
{
lean_object* v_res_4889_; 
v_res_4889_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_();
return v_res_4889_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(lean_object* v_a_4890_, lean_object* v_b_4891_){
_start:
{
lean_object* v_array_4892_; lean_object* v_start_4893_; lean_object* v_stop_4894_; lean_object* v___x_4896_; uint8_t v_isShared_4897_; uint8_t v_isSharedCheck_4907_; 
v_array_4892_ = lean_ctor_get(v_a_4890_, 0);
v_start_4893_ = lean_ctor_get(v_a_4890_, 1);
v_stop_4894_ = lean_ctor_get(v_a_4890_, 2);
v_isSharedCheck_4907_ = !lean_is_exclusive(v_a_4890_);
if (v_isSharedCheck_4907_ == 0)
{
v___x_4896_ = v_a_4890_;
v_isShared_4897_ = v_isSharedCheck_4907_;
goto v_resetjp_4895_;
}
else
{
lean_inc(v_stop_4894_);
lean_inc(v_start_4893_);
lean_inc(v_array_4892_);
lean_dec(v_a_4890_);
v___x_4896_ = lean_box(0);
v_isShared_4897_ = v_isSharedCheck_4907_;
goto v_resetjp_4895_;
}
v_resetjp_4895_:
{
uint8_t v___x_4898_; 
v___x_4898_ = lean_nat_dec_lt(v_start_4893_, v_stop_4894_);
if (v___x_4898_ == 0)
{
lean_del_object(v___x_4896_);
lean_dec(v_stop_4894_);
lean_dec(v_start_4893_);
lean_dec_ref(v_array_4892_);
return v_b_4891_;
}
else
{
lean_object* v___x_4899_; lean_object* v___x_4900_; lean_object* v___x_4902_; 
v___x_4899_ = lean_unsigned_to_nat(1u);
v___x_4900_ = lean_nat_add(v_start_4893_, v___x_4899_);
lean_inc_ref(v_array_4892_);
if (v_isShared_4897_ == 0)
{
lean_ctor_set(v___x_4896_, 1, v___x_4900_);
v___x_4902_ = v___x_4896_;
goto v_reusejp_4901_;
}
else
{
lean_object* v_reuseFailAlloc_4906_; 
v_reuseFailAlloc_4906_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4906_, 0, v_array_4892_);
lean_ctor_set(v_reuseFailAlloc_4906_, 1, v___x_4900_);
lean_ctor_set(v_reuseFailAlloc_4906_, 2, v_stop_4894_);
v___x_4902_ = v_reuseFailAlloc_4906_;
goto v_reusejp_4901_;
}
v_reusejp_4901_:
{
lean_object* v___x_4903_; lean_object* v___x_4904_; 
v___x_4903_ = lean_array_fget(v_array_4892_, v_start_4893_);
lean_dec(v_start_4893_);
lean_dec_ref(v_array_4892_);
v___x_4904_ = lean_array_push(v_b_4891_, v___x_4903_);
v_a_4890_ = v___x_4902_;
v_b_4891_ = v___x_4904_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_4908_; lean_object* v___x_4909_; 
v___x_4908_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2_spec__3_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2_spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2_spec__3_spec__5___redArg___closed__0);
v___x_4909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4909_, 0, v___x_4908_);
return v___x_4909_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; 
v___x_4910_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_4911_ = lean_unsigned_to_nat(0u);
v___x_4912_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_4912_, 0, v___x_4911_);
lean_ctor_set(v___x_4912_, 1, v___x_4911_);
lean_ctor_set(v___x_4912_, 2, v___x_4911_);
lean_ctor_set(v___x_4912_, 3, v___x_4911_);
lean_ctor_set(v___x_4912_, 4, v___x_4910_);
lean_ctor_set(v___x_4912_, 5, v___x_4910_);
lean_ctor_set(v___x_4912_, 6, v___x_4910_);
lean_ctor_set(v___x_4912_, 7, v___x_4910_);
lean_ctor_set(v___x_4912_, 8, v___x_4910_);
lean_ctor_set(v___x_4912_, 9, v___x_4910_);
lean_ctor_set(v___x_4912_, 10, v___x_4910_);
return v___x_4912_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; 
v___x_4913_ = lean_box(1);
v___x_4914_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__2, &l_Lean_Meta_mkInjectiveTheorems___closed__2_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__2);
v___x_4915_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_4916_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4916_, 0, v___x_4915_);
lean_ctor_set(v___x_4916_, 1, v___x_4914_);
lean_ctor_set(v___x_4916_, 2, v___x_4913_);
return v___x_4916_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_4918_; lean_object* v___x_4919_; 
v___x_4918_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3));
v___x_4919_ = l_Lean_stringToMessageData(v___x_4918_);
return v___x_4919_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6(void){
_start:
{
lean_object* v___x_4921_; lean_object* v___x_4922_; 
v___x_4921_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5));
v___x_4922_ = l_Lean_stringToMessageData(v___x_4921_);
return v___x_4922_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8(void){
_start:
{
lean_object* v___x_4924_; lean_object* v___x_4925_; 
v___x_4924_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7));
v___x_4925_ = l_Lean_stringToMessageData(v___x_4924_);
return v___x_4925_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10(void){
_start:
{
lean_object* v___x_4927_; lean_object* v___x_4928_; 
v___x_4927_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9));
v___x_4928_ = l_Lean_stringToMessageData(v___x_4927_);
return v___x_4928_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12(void){
_start:
{
lean_object* v___x_4930_; lean_object* v___x_4931_; 
v___x_4930_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11));
v___x_4931_ = l_Lean_stringToMessageData(v___x_4930_);
return v___x_4931_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14(void){
_start:
{
lean_object* v___x_4933_; lean_object* v___x_4934_; 
v___x_4933_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13));
v___x_4934_ = l_Lean_stringToMessageData(v___x_4933_);
return v___x_4934_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16(void){
_start:
{
lean_object* v___x_4936_; lean_object* v___x_4937_; 
v___x_4936_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15));
v___x_4937_ = l_Lean_stringToMessageData(v___x_4936_);
return v___x_4937_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_4938_, lean_object* v_declHint_4939_, lean_object* v___y_4940_){
_start:
{
lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v_env_4944_; uint8_t v___x_4945_; 
v___x_4942_ = lean_box(0);
v___x_4943_ = lean_st_ref_get(v___y_4940_);
v_env_4944_ = lean_ctor_get(v___x_4943_, 0);
lean_inc_ref(v_env_4944_);
lean_dec(v___x_4943_);
v___x_4945_ = l_Lean_Name_isAnonymous(v_declHint_4939_);
if (v___x_4945_ == 0)
{
uint8_t v_isExporting_4946_; 
v_isExporting_4946_ = lean_ctor_get_uint8(v_env_4944_, sizeof(void*)*13);
if (v_isExporting_4946_ == 0)
{
lean_object* v___x_4947_; 
lean_dec_ref(v_env_4944_);
lean_dec(v_declHint_4939_);
v___x_4947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4947_, 0, v_msg_4938_);
return v___x_4947_;
}
else
{
lean_object* v___x_4948_; uint8_t v___x_4949_; 
lean_inc_ref(v_env_4944_);
v___x_4948_ = l_Lean_Environment_setExporting(v_env_4944_, v___x_4945_);
lean_inc(v_declHint_4939_);
lean_inc_ref(v___x_4948_);
v___x_4949_ = l_Lean_Environment_contains(v___x_4948_, v_declHint_4939_, v_isExporting_4946_);
if (v___x_4949_ == 0)
{
lean_object* v___x_4950_; 
lean_dec_ref(v___x_4948_);
lean_dec_ref(v_env_4944_);
lean_dec(v_declHint_4939_);
v___x_4950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4950_, 0, v_msg_4938_);
return v___x_4950_;
}
else
{
lean_object* v___x_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; lean_object* v_c_4956_; lean_object* v___x_4957_; 
v___x_4951_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_4952_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_4953_ = l_Lean_Options_empty;
lean_inc_ref(v___x_4948_);
v___x_4954_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4954_, 0, v___x_4948_);
lean_ctor_set(v___x_4954_, 1, v___x_4951_);
lean_ctor_set(v___x_4954_, 2, v___x_4952_);
lean_ctor_set(v___x_4954_, 3, v___x_4953_);
lean_inc(v_declHint_4939_);
v___x_4955_ = l_Lean_MessageData_ofConstName(v_declHint_4939_, v___x_4945_);
v_c_4956_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_4956_, 0, v___x_4954_);
lean_ctor_set(v_c_4956_, 1, v___x_4955_);
v___x_4957_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_4948_, v_declHint_4939_);
lean_dec_ref(v___x_4948_);
if (lean_obj_tag(v___x_4957_) == 0)
{
lean_object* v___x_4958_; lean_object* v___x_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; lean_object* v___x_4963_; lean_object* v___x_4964_; 
lean_dec_ref(v_env_4944_);
lean_dec(v_declHint_4939_);
v___x_4958_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_4959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4959_, 0, v___x_4958_);
lean_ctor_set(v___x_4959_, 1, v_c_4956_);
v___x_4960_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6);
v___x_4961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4961_, 0, v___x_4959_);
lean_ctor_set(v___x_4961_, 1, v___x_4960_);
v___x_4962_ = l_Lean_MessageData_note(v___x_4961_);
v___x_4963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4963_, 0, v_msg_4938_);
lean_ctor_set(v___x_4963_, 1, v___x_4962_);
v___x_4964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4964_, 0, v___x_4963_);
return v___x_4964_;
}
else
{
lean_object* v_val_4965_; lean_object* v___x_4967_; uint8_t v_isShared_4968_; uint8_t v_isSharedCheck_4999_; 
v_val_4965_ = lean_ctor_get(v___x_4957_, 0);
v_isSharedCheck_4999_ = !lean_is_exclusive(v___x_4957_);
if (v_isSharedCheck_4999_ == 0)
{
v___x_4967_ = v___x_4957_;
v_isShared_4968_ = v_isSharedCheck_4999_;
goto v_resetjp_4966_;
}
else
{
lean_inc(v_val_4965_);
lean_dec(v___x_4957_);
v___x_4967_ = lean_box(0);
v_isShared_4968_ = v_isSharedCheck_4999_;
goto v_resetjp_4966_;
}
v_resetjp_4966_:
{
lean_object* v___x_4969_; lean_object* v_moduleNames_4970_; lean_object* v_mod_4971_; uint8_t v___x_4972_; 
v___x_4969_ = l_Lean_Environment_header(v_env_4944_);
lean_dec_ref(v_env_4944_);
v_moduleNames_4970_ = lean_ctor_get(v___x_4969_, 4);
lean_inc_ref(v_moduleNames_4970_);
lean_dec_ref(v___x_4969_);
v_mod_4971_ = lean_array_get(v___x_4942_, v_moduleNames_4970_, v_val_4965_);
lean_dec(v_val_4965_);
lean_dec_ref(v_moduleNames_4970_);
v___x_4972_ = l_Lean_isPrivateName(v_declHint_4939_);
lean_dec(v_declHint_4939_);
if (v___x_4972_ == 0)
{
lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; lean_object* v___x_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; lean_object* v___x_4984_; 
v___x_4973_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8);
v___x_4974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4974_, 0, v___x_4973_);
lean_ctor_set(v___x_4974_, 1, v_c_4956_);
v___x_4975_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10);
v___x_4976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4976_, 0, v___x_4974_);
lean_ctor_set(v___x_4976_, 1, v___x_4975_);
v___x_4977_ = l_Lean_MessageData_ofName(v_mod_4971_);
v___x_4978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4978_, 0, v___x_4976_);
lean_ctor_set(v___x_4978_, 1, v___x_4977_);
v___x_4979_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12);
v___x_4980_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4980_, 0, v___x_4978_);
lean_ctor_set(v___x_4980_, 1, v___x_4979_);
v___x_4981_ = l_Lean_MessageData_note(v___x_4980_);
v___x_4982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4982_, 0, v_msg_4938_);
lean_ctor_set(v___x_4982_, 1, v___x_4981_);
if (v_isShared_4968_ == 0)
{
lean_ctor_set_tag(v___x_4967_, 0);
lean_ctor_set(v___x_4967_, 0, v___x_4982_);
v___x_4984_ = v___x_4967_;
goto v_reusejp_4983_;
}
else
{
lean_object* v_reuseFailAlloc_4985_; 
v_reuseFailAlloc_4985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4985_, 0, v___x_4982_);
v___x_4984_ = v_reuseFailAlloc_4985_;
goto v_reusejp_4983_;
}
v_reusejp_4983_:
{
return v___x_4984_;
}
}
else
{
lean_object* v___x_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; lean_object* v___x_4997_; 
v___x_4986_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4);
v___x_4987_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4987_, 0, v___x_4986_);
lean_ctor_set(v___x_4987_, 1, v_c_4956_);
v___x_4988_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14);
v___x_4989_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4989_, 0, v___x_4987_);
lean_ctor_set(v___x_4989_, 1, v___x_4988_);
v___x_4990_ = l_Lean_MessageData_ofName(v_mod_4971_);
v___x_4991_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4991_, 0, v___x_4989_);
lean_ctor_set(v___x_4991_, 1, v___x_4990_);
v___x_4992_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16);
v___x_4993_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4993_, 0, v___x_4991_);
lean_ctor_set(v___x_4993_, 1, v___x_4992_);
v___x_4994_ = l_Lean_MessageData_note(v___x_4993_);
v___x_4995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4995_, 0, v_msg_4938_);
lean_ctor_set(v___x_4995_, 1, v___x_4994_);
if (v_isShared_4968_ == 0)
{
lean_ctor_set_tag(v___x_4967_, 0);
lean_ctor_set(v___x_4967_, 0, v___x_4995_);
v___x_4997_ = v___x_4967_;
goto v_reusejp_4996_;
}
else
{
lean_object* v_reuseFailAlloc_4998_; 
v_reuseFailAlloc_4998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4998_, 0, v___x_4995_);
v___x_4997_ = v_reuseFailAlloc_4998_;
goto v_reusejp_4996_;
}
v_reusejp_4996_:
{
return v___x_4997_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_5000_; 
lean_dec_ref(v_env_4944_);
lean_dec(v_declHint_4939_);
v___x_5000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5000_, 0, v_msg_4938_);
return v___x_5000_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_5001_, lean_object* v_declHint_5002_, lean_object* v___y_5003_, lean_object* v___y_5004_){
_start:
{
lean_object* v_res_5005_; 
v_res_5005_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_5001_, v_declHint_5002_, v___y_5003_);
lean_dec(v___y_5003_);
return v_res_5005_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_msg_5006_, lean_object* v_declHint_5007_, lean_object* v___y_5008_, lean_object* v___y_5009_, lean_object* v___y_5010_, lean_object* v___y_5011_){
_start:
{
lean_object* v___x_5013_; lean_object* v_a_5014_; lean_object* v___x_5016_; uint8_t v_isShared_5017_; uint8_t v_isSharedCheck_5023_; 
v___x_5013_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_5006_, v_declHint_5007_, v___y_5011_);
v_a_5014_ = lean_ctor_get(v___x_5013_, 0);
v_isSharedCheck_5023_ = !lean_is_exclusive(v___x_5013_);
if (v_isSharedCheck_5023_ == 0)
{
v___x_5016_ = v___x_5013_;
v_isShared_5017_ = v_isSharedCheck_5023_;
goto v_resetjp_5015_;
}
else
{
lean_inc(v_a_5014_);
lean_dec(v___x_5013_);
v___x_5016_ = lean_box(0);
v_isShared_5017_ = v_isSharedCheck_5023_;
goto v_resetjp_5015_;
}
v_resetjp_5015_:
{
lean_object* v___x_5018_; lean_object* v___x_5019_; lean_object* v___x_5021_; 
v___x_5018_ = l_Lean_unknownIdentifierMessageTag;
v___x_5019_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_5019_, 0, v___x_5018_);
lean_ctor_set(v___x_5019_, 1, v_a_5014_);
if (v_isShared_5017_ == 0)
{
lean_ctor_set(v___x_5016_, 0, v___x_5019_);
v___x_5021_ = v___x_5016_;
goto v_reusejp_5020_;
}
else
{
lean_object* v_reuseFailAlloc_5022_; 
v_reuseFailAlloc_5022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5022_, 0, v___x_5019_);
v___x_5021_ = v_reuseFailAlloc_5022_;
goto v_reusejp_5020_;
}
v_reusejp_5020_:
{
return v___x_5021_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v_msg_5024_, lean_object* v_declHint_5025_, lean_object* v___y_5026_, lean_object* v___y_5027_, lean_object* v___y_5028_, lean_object* v___y_5029_, lean_object* v___y_5030_){
_start:
{
lean_object* v_res_5031_; 
v_res_5031_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_5024_, v_declHint_5025_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_);
lean_dec(v___y_5029_);
lean_dec_ref(v___y_5028_);
lean_dec(v___y_5027_);
lean_dec_ref(v___y_5026_);
return v_res_5031_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_5032_, lean_object* v_msg_5033_, lean_object* v___y_5034_, lean_object* v___y_5035_, lean_object* v___y_5036_, lean_object* v___y_5037_){
_start:
{
lean_object* v_toCold_5039_; lean_object* v_currRecDepth_5040_; lean_object* v_ref_5041_; uint16_t v_optionFlags_5042_; uint8_t v_suppressElabErrors_5043_; uint8_t v_checkDeprecated_5044_; uint8_t v_isRecordingDeps_5045_; lean_object* v_ref_5046_; lean_object* v___x_5047_; lean_object* v___x_5048_; 
v_toCold_5039_ = lean_ctor_get(v___y_5036_, 0);
v_currRecDepth_5040_ = lean_ctor_get(v___y_5036_, 1);
v_ref_5041_ = lean_ctor_get(v___y_5036_, 2);
v_optionFlags_5042_ = lean_ctor_get_uint16(v___y_5036_, sizeof(void*)*3);
v_suppressElabErrors_5043_ = lean_ctor_get_uint8(v___y_5036_, sizeof(void*)*3 + 2);
v_checkDeprecated_5044_ = lean_ctor_get_uint8(v___y_5036_, sizeof(void*)*3 + 3);
v_isRecordingDeps_5045_ = lean_ctor_get_uint8(v___y_5036_, sizeof(void*)*3 + 4);
v_ref_5046_ = l_Lean_replaceRef(v_ref_5032_, v_ref_5041_);
lean_inc(v_currRecDepth_5040_);
lean_inc_ref(v_toCold_5039_);
v___x_5047_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_5047_, 0, v_toCold_5039_);
lean_ctor_set(v___x_5047_, 1, v_currRecDepth_5040_);
lean_ctor_set(v___x_5047_, 2, v_ref_5046_);
lean_ctor_set_uint16(v___x_5047_, sizeof(void*)*3, v_optionFlags_5042_);
lean_ctor_set_uint8(v___x_5047_, sizeof(void*)*3 + 2, v_suppressElabErrors_5043_);
lean_ctor_set_uint8(v___x_5047_, sizeof(void*)*3 + 3, v_checkDeprecated_5044_);
lean_ctor_set_uint8(v___x_5047_, sizeof(void*)*3 + 4, v_isRecordingDeps_5045_);
v___x_5048_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v_msg_5033_, v___y_5034_, v___y_5035_, v___x_5047_, v___y_5037_);
lean_dec_ref_known(v___x_5047_, 3);
return v___x_5048_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_5049_, lean_object* v_msg_5050_, lean_object* v___y_5051_, lean_object* v___y_5052_, lean_object* v___y_5053_, lean_object* v___y_5054_, lean_object* v___y_5055_){
_start:
{
lean_object* v_res_5056_; 
v_res_5056_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5049_, v_msg_5050_, v___y_5051_, v___y_5052_, v___y_5053_, v___y_5054_);
lean_dec(v___y_5054_);
lean_dec_ref(v___y_5053_);
lean_dec(v___y_5052_);
lean_dec_ref(v___y_5051_);
lean_dec(v_ref_5049_);
return v_res_5056_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_5057_, lean_object* v_msg_5058_, lean_object* v_declHint_5059_, lean_object* v___y_5060_, lean_object* v___y_5061_, lean_object* v___y_5062_, lean_object* v___y_5063_){
_start:
{
lean_object* v___x_5065_; lean_object* v_a_5066_; lean_object* v___x_5067_; 
v___x_5065_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_5058_, v_declHint_5059_, v___y_5060_, v___y_5061_, v___y_5062_, v___y_5063_);
v_a_5066_ = lean_ctor_get(v___x_5065_, 0);
lean_inc(v_a_5066_);
lean_dec_ref(v___x_5065_);
v___x_5067_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5057_, v_a_5066_, v___y_5060_, v___y_5061_, v___y_5062_, v___y_5063_);
return v___x_5067_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_5068_, lean_object* v_msg_5069_, lean_object* v_declHint_5070_, lean_object* v___y_5071_, lean_object* v___y_5072_, lean_object* v___y_5073_, lean_object* v___y_5074_, lean_object* v___y_5075_){
_start:
{
lean_object* v_res_5076_; 
v_res_5076_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5068_, v_msg_5069_, v_declHint_5070_, v___y_5071_, v___y_5072_, v___y_5073_, v___y_5074_);
lean_dec(v___y_5074_);
lean_dec_ref(v___y_5073_);
lean_dec(v___y_5072_);
lean_dec_ref(v___y_5071_);
lean_dec(v_ref_5068_);
return v_res_5076_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_5078_; lean_object* v___x_5079_; 
v___x_5078_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_5079_ = l_Lean_stringToMessageData(v___x_5078_);
return v___x_5079_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_5080_, lean_object* v_constName_5081_, lean_object* v___y_5082_, lean_object* v___y_5083_, lean_object* v___y_5084_, lean_object* v___y_5085_){
_start:
{
lean_object* v___x_5087_; uint8_t v___x_5088_; lean_object* v___x_5089_; lean_object* v___x_5090_; lean_object* v___x_5091_; lean_object* v___x_5092_; lean_object* v___x_5093_; 
v___x_5087_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_5088_ = 0;
lean_inc(v_constName_5081_);
v___x_5089_ = l_Lean_MessageData_ofConstName(v_constName_5081_, v___x_5088_);
v___x_5090_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5090_, 0, v___x_5087_);
lean_ctor_set(v___x_5090_, 1, v___x_5089_);
v___x_5091_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_5092_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5092_, 0, v___x_5090_);
lean_ctor_set(v___x_5092_, 1, v___x_5091_);
v___x_5093_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5080_, v___x_5092_, v_constName_5081_, v___y_5082_, v___y_5083_, v___y_5084_, v___y_5085_);
return v___x_5093_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_5094_, lean_object* v_constName_5095_, lean_object* v___y_5096_, lean_object* v___y_5097_, lean_object* v___y_5098_, lean_object* v___y_5099_, lean_object* v___y_5100_){
_start:
{
lean_object* v_res_5101_; 
v_res_5101_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(v_ref_5094_, v_constName_5095_, v___y_5096_, v___y_5097_, v___y_5098_, v___y_5099_);
lean_dec(v___y_5099_);
lean_dec_ref(v___y_5098_);
lean_dec(v___y_5097_);
lean_dec_ref(v___y_5096_);
lean_dec(v_ref_5094_);
return v_res_5101_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(lean_object* v_constName_5102_, lean_object* v___y_5103_, lean_object* v___y_5104_, lean_object* v___y_5105_, lean_object* v___y_5106_){
_start:
{
lean_object* v_ref_5108_; lean_object* v___x_5109_; 
v_ref_5108_ = lean_ctor_get(v___y_5105_, 2);
v___x_5109_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(v_ref_5108_, v_constName_5102_, v___y_5103_, v___y_5104_, v___y_5105_, v___y_5106_);
return v___x_5109_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_constName_5110_, lean_object* v___y_5111_, lean_object* v___y_5112_, lean_object* v___y_5113_, lean_object* v___y_5114_, lean_object* v___y_5115_){
_start:
{
lean_object* v_res_5116_; 
v_res_5116_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(v_constName_5110_, v___y_5111_, v___y_5112_, v___y_5113_, v___y_5114_);
lean_dec(v___y_5114_);
lean_dec_ref(v___y_5113_);
lean_dec(v___y_5112_);
lean_dec_ref(v___y_5111_);
return v_res_5116_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(lean_object* v_constName_5117_, lean_object* v___y_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_){
_start:
{
lean_object* v___x_5123_; lean_object* v_env_5124_; uint8_t v___x_5125_; lean_object* v___x_5126_; 
v___x_5123_ = lean_st_ref_get(v___y_5121_);
v_env_5124_ = lean_ctor_get(v___x_5123_, 0);
lean_inc_ref(v_env_5124_);
lean_dec(v___x_5123_);
v___x_5125_ = 0;
lean_inc(v_constName_5117_);
v___x_5126_ = l_Lean_Environment_find_x3f(v_env_5124_, v_constName_5117_, v___x_5125_);
if (lean_obj_tag(v___x_5126_) == 0)
{
lean_object* v___x_5127_; 
v___x_5127_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(v_constName_5117_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_);
return v___x_5127_;
}
else
{
lean_object* v_val_5128_; lean_object* v___x_5130_; uint8_t v_isShared_5131_; uint8_t v_isSharedCheck_5135_; 
lean_dec(v_constName_5117_);
v_val_5128_ = lean_ctor_get(v___x_5126_, 0);
v_isSharedCheck_5135_ = !lean_is_exclusive(v___x_5126_);
if (v_isSharedCheck_5135_ == 0)
{
v___x_5130_ = v___x_5126_;
v_isShared_5131_ = v_isSharedCheck_5135_;
goto v_resetjp_5129_;
}
else
{
lean_inc(v_val_5128_);
lean_dec(v___x_5126_);
v___x_5130_ = lean_box(0);
v_isShared_5131_ = v_isSharedCheck_5135_;
goto v_resetjp_5129_;
}
v_resetjp_5129_:
{
lean_object* v___x_5133_; 
if (v_isShared_5131_ == 0)
{
lean_ctor_set_tag(v___x_5130_, 0);
v___x_5133_ = v___x_5130_;
goto v_reusejp_5132_;
}
else
{
lean_object* v_reuseFailAlloc_5134_; 
v_reuseFailAlloc_5134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5134_, 0, v_val_5128_);
v___x_5133_ = v_reuseFailAlloc_5134_;
goto v_reusejp_5132_;
}
v_reusejp_5132_:
{
return v___x_5133_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0___boxed(lean_object* v_constName_5136_, lean_object* v___y_5137_, lean_object* v___y_5138_, lean_object* v___y_5139_, lean_object* v___y_5140_, lean_object* v___y_5141_){
_start:
{
lean_object* v_res_5142_; 
v_res_5142_ = l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(v_constName_5136_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_);
lean_dec(v___y_5140_);
lean_dec_ref(v___y_5139_);
lean_dec(v___y_5138_);
lean_dec_ref(v___y_5137_);
return v_res_5142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(lean_object* v_x_5145_, lean_object* v_x_5146_, lean_object* v_x_5147_, lean_object* v___y_5148_, lean_object* v___y_5149_, lean_object* v___y_5150_, lean_object* v___y_5151_){
_start:
{
if (lean_obj_tag(v_x_5145_) == 5)
{
lean_object* v_fn_5153_; lean_object* v_arg_5154_; lean_object* v___x_5155_; lean_object* v___x_5156_; lean_object* v___x_5157_; 
v_fn_5153_ = lean_ctor_get(v_x_5145_, 0);
lean_inc_ref(v_fn_5153_);
v_arg_5154_ = lean_ctor_get(v_x_5145_, 1);
lean_inc_ref(v_arg_5154_);
lean_dec_ref_known(v_x_5145_, 2);
v___x_5155_ = lean_array_set(v_x_5146_, v_x_5147_, v_arg_5154_);
v___x_5156_ = lean_unsigned_to_nat(1u);
v___x_5157_ = lean_nat_sub(v_x_5147_, v___x_5156_);
lean_dec(v_x_5147_);
v_x_5145_ = v_fn_5153_;
v_x_5146_ = v___x_5155_;
v_x_5147_ = v___x_5157_;
goto _start;
}
else
{
lean_dec(v_x_5147_);
if (lean_obj_tag(v_x_5145_) == 4)
{
lean_object* v_declName_5159_; lean_object* v___x_5160_; 
v_declName_5159_ = lean_ctor_get(v_x_5145_, 0);
lean_inc(v_declName_5159_);
lean_dec_ref_known(v_x_5145_, 2);
v___x_5160_ = l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(v_declName_5159_, v___y_5148_, v___y_5149_, v___y_5150_, v___y_5151_);
if (lean_obj_tag(v___x_5160_) == 0)
{
lean_object* v_a_5161_; lean_object* v___x_5163_; uint8_t v_isShared_5164_; uint8_t v_isSharedCheck_5192_; 
v_a_5161_ = lean_ctor_get(v___x_5160_, 0);
v_isSharedCheck_5192_ = !lean_is_exclusive(v___x_5160_);
if (v_isSharedCheck_5192_ == 0)
{
v___x_5163_ = v___x_5160_;
v_isShared_5164_ = v_isSharedCheck_5192_;
goto v_resetjp_5162_;
}
else
{
lean_inc(v_a_5161_);
lean_dec(v___x_5160_);
v___x_5163_ = lean_box(0);
v_isShared_5164_ = v_isSharedCheck_5192_;
goto v_resetjp_5162_;
}
v_resetjp_5162_:
{
lean_object* v_lower_5166_; lean_object* v_upper_5167_; 
if (lean_obj_tag(v_a_5161_) == 5)
{
lean_object* v_val_5175_; lean_object* v___x_5177_; uint8_t v_isShared_5178_; uint8_t v_isSharedCheck_5189_; 
v_val_5175_ = lean_ctor_get(v_a_5161_, 0);
v_isSharedCheck_5189_ = !lean_is_exclusive(v_a_5161_);
if (v_isSharedCheck_5189_ == 0)
{
v___x_5177_ = v_a_5161_;
v_isShared_5178_ = v_isSharedCheck_5189_;
goto v_resetjp_5176_;
}
else
{
lean_inc(v_val_5175_);
lean_dec(v_a_5161_);
v___x_5177_ = lean_box(0);
v_isShared_5178_ = v_isSharedCheck_5189_;
goto v_resetjp_5176_;
}
v_resetjp_5176_:
{
lean_object* v_numParams_5179_; lean_object* v_numIndices_5180_; lean_object* v___x_5181_; uint8_t v___x_5182_; 
v_numParams_5179_ = lean_ctor_get(v_val_5175_, 1);
lean_inc(v_numParams_5179_);
v_numIndices_5180_ = lean_ctor_get(v_val_5175_, 2);
lean_inc(v_numIndices_5180_);
lean_dec_ref(v_val_5175_);
v___x_5181_ = lean_unsigned_to_nat(0u);
v___x_5182_ = lean_nat_dec_eq(v_numIndices_5180_, v___x_5181_);
lean_dec(v_numIndices_5180_);
if (v___x_5182_ == 0)
{
lean_object* v___x_5183_; uint8_t v___x_5184_; 
lean_del_object(v___x_5177_);
v___x_5183_ = lean_array_get_size(v_x_5146_);
v___x_5184_ = lean_nat_dec_le(v_numParams_5179_, v___x_5181_);
if (v___x_5184_ == 0)
{
v_lower_5166_ = v_numParams_5179_;
v_upper_5167_ = v___x_5183_;
goto v___jp_5165_;
}
else
{
lean_dec(v_numParams_5179_);
v_lower_5166_ = v___x_5181_;
v_upper_5167_ = v___x_5183_;
goto v___jp_5165_;
}
}
else
{
lean_object* v___x_5185_; lean_object* v___x_5187_; 
lean_dec(v_numParams_5179_);
lean_del_object(v___x_5163_);
lean_dec_ref(v_x_5146_);
v___x_5185_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2___closed__0));
if (v_isShared_5178_ == 0)
{
lean_ctor_set_tag(v___x_5177_, 0);
lean_ctor_set(v___x_5177_, 0, v___x_5185_);
v___x_5187_ = v___x_5177_;
goto v_reusejp_5186_;
}
else
{
lean_object* v_reuseFailAlloc_5188_; 
v_reuseFailAlloc_5188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5188_, 0, v___x_5185_);
v___x_5187_ = v_reuseFailAlloc_5188_;
goto v_reusejp_5186_;
}
v_reusejp_5186_:
{
return v___x_5187_;
}
}
}
}
else
{
lean_object* v___x_5190_; lean_object* v___x_5191_; 
lean_del_object(v___x_5163_);
lean_dec(v_a_5161_);
lean_dec_ref(v_x_5146_);
v___x_5190_ = lean_box(0);
v___x_5191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5191_, 0, v___x_5190_);
return v___x_5191_;
}
v___jp_5165_:
{
lean_object* v___x_5168_; lean_object* v___x_5169_; lean_object* v___x_5170_; lean_object* v___x_5171_; lean_object* v___x_5173_; 
v___x_5168_ = l_Array_toSubarray___redArg(v_x_5146_, v_lower_5166_, v_upper_5167_);
v___x_5169_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_5170_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(v___x_5168_, v___x_5169_);
v___x_5171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5171_, 0, v___x_5170_);
if (v_isShared_5164_ == 0)
{
lean_ctor_set(v___x_5163_, 0, v___x_5171_);
v___x_5173_ = v___x_5163_;
goto v_reusejp_5172_;
}
else
{
lean_object* v_reuseFailAlloc_5174_; 
v_reuseFailAlloc_5174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5174_, 0, v___x_5171_);
v___x_5173_ = v_reuseFailAlloc_5174_;
goto v_reusejp_5172_;
}
v_reusejp_5172_:
{
return v___x_5173_;
}
}
}
}
else
{
lean_object* v_a_5193_; lean_object* v___x_5195_; uint8_t v_isShared_5196_; uint8_t v_isSharedCheck_5200_; 
lean_dec_ref(v_x_5146_);
v_a_5193_ = lean_ctor_get(v___x_5160_, 0);
v_isSharedCheck_5200_ = !lean_is_exclusive(v___x_5160_);
if (v_isSharedCheck_5200_ == 0)
{
v___x_5195_ = v___x_5160_;
v_isShared_5196_ = v_isSharedCheck_5200_;
goto v_resetjp_5194_;
}
else
{
lean_inc(v_a_5193_);
lean_dec(v___x_5160_);
v___x_5195_ = lean_box(0);
v_isShared_5196_ = v_isSharedCheck_5200_;
goto v_resetjp_5194_;
}
v_resetjp_5194_:
{
lean_object* v___x_5198_; 
if (v_isShared_5196_ == 0)
{
v___x_5198_ = v___x_5195_;
goto v_reusejp_5197_;
}
else
{
lean_object* v_reuseFailAlloc_5199_; 
v_reuseFailAlloc_5199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5199_, 0, v_a_5193_);
v___x_5198_ = v_reuseFailAlloc_5199_;
goto v_reusejp_5197_;
}
v_reusejp_5197_:
{
return v___x_5198_;
}
}
}
}
else
{
lean_object* v___x_5201_; lean_object* v___x_5202_; 
lean_dec_ref(v_x_5146_);
lean_dec_ref(v_x_5145_);
v___x_5201_ = lean_box(0);
v___x_5202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5202_, 0, v___x_5201_);
return v___x_5202_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2___boxed(lean_object* v_x_5203_, lean_object* v_x_5204_, lean_object* v_x_5205_, lean_object* v___y_5206_, lean_object* v___y_5207_, lean_object* v___y_5208_, lean_object* v___y_5209_, lean_object* v___y_5210_){
_start:
{
lean_object* v_res_5211_; 
v_res_5211_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(v_x_5203_, v_x_5204_, v_x_5205_, v___y_5206_, v___y_5207_, v___y_5208_, v___y_5209_);
lean_dec(v___y_5209_);
lean_dec_ref(v___y_5208_);
lean_dec(v___y_5207_);
lean_dec_ref(v___y_5206_);
return v_res_5211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorAppIndices_x3f(lean_object* v_ctorApp_5212_, lean_object* v_a_5213_, lean_object* v_a_5214_, lean_object* v_a_5215_, lean_object* v_a_5216_){
_start:
{
lean_object* v___x_5218_; 
lean_inc(v_a_5216_);
lean_inc_ref(v_a_5215_);
lean_inc(v_a_5214_);
lean_inc_ref(v_a_5213_);
v___x_5218_ = lean_infer_type(v_ctorApp_5212_, v_a_5213_, v_a_5214_, v_a_5215_, v_a_5216_);
if (lean_obj_tag(v___x_5218_) == 0)
{
lean_object* v_a_5219_; lean_object* v___x_5220_; 
v_a_5219_ = lean_ctor_get(v___x_5218_, 0);
lean_inc(v_a_5219_);
lean_dec_ref_known(v___x_5218_, 1);
v___x_5220_ = l_Lean_Meta_whnfD(v_a_5219_, v_a_5213_, v_a_5214_, v_a_5215_, v_a_5216_);
if (lean_obj_tag(v___x_5220_) == 0)
{
lean_object* v_a_5221_; lean_object* v_dummy_5222_; lean_object* v_nargs_5223_; lean_object* v___x_5224_; lean_object* v___x_5225_; lean_object* v___x_5226_; lean_object* v___x_5227_; 
v_a_5221_ = lean_ctor_get(v___x_5220_, 0);
lean_inc(v_a_5221_);
lean_dec_ref_known(v___x_5220_, 1);
v_dummy_5222_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0);
v_nargs_5223_ = l_Lean_Expr_getAppNumArgs(v_a_5221_);
lean_inc(v_nargs_5223_);
v___x_5224_ = lean_mk_array(v_nargs_5223_, v_dummy_5222_);
v___x_5225_ = lean_unsigned_to_nat(1u);
v___x_5226_ = lean_nat_sub(v_nargs_5223_, v___x_5225_);
lean_dec(v_nargs_5223_);
v___x_5227_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(v_a_5221_, v___x_5224_, v___x_5226_, v_a_5213_, v_a_5214_, v_a_5215_, v_a_5216_);
return v___x_5227_;
}
else
{
lean_object* v_a_5228_; lean_object* v___x_5230_; uint8_t v_isShared_5231_; uint8_t v_isSharedCheck_5235_; 
v_a_5228_ = lean_ctor_get(v___x_5220_, 0);
v_isSharedCheck_5235_ = !lean_is_exclusive(v___x_5220_);
if (v_isSharedCheck_5235_ == 0)
{
v___x_5230_ = v___x_5220_;
v_isShared_5231_ = v_isSharedCheck_5235_;
goto v_resetjp_5229_;
}
else
{
lean_inc(v_a_5228_);
lean_dec(v___x_5220_);
v___x_5230_ = lean_box(0);
v_isShared_5231_ = v_isSharedCheck_5235_;
goto v_resetjp_5229_;
}
v_resetjp_5229_:
{
lean_object* v___x_5233_; 
if (v_isShared_5231_ == 0)
{
v___x_5233_ = v___x_5230_;
goto v_reusejp_5232_;
}
else
{
lean_object* v_reuseFailAlloc_5234_; 
v_reuseFailAlloc_5234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5234_, 0, v_a_5228_);
v___x_5233_ = v_reuseFailAlloc_5234_;
goto v_reusejp_5232_;
}
v_reusejp_5232_:
{
return v___x_5233_;
}
}
}
}
else
{
lean_object* v_a_5236_; lean_object* v___x_5238_; uint8_t v_isShared_5239_; uint8_t v_isSharedCheck_5243_; 
v_a_5236_ = lean_ctor_get(v___x_5218_, 0);
v_isSharedCheck_5243_ = !lean_is_exclusive(v___x_5218_);
if (v_isSharedCheck_5243_ == 0)
{
v___x_5238_ = v___x_5218_;
v_isShared_5239_ = v_isSharedCheck_5243_;
goto v_resetjp_5237_;
}
else
{
lean_inc(v_a_5236_);
lean_dec(v___x_5218_);
v___x_5238_ = lean_box(0);
v_isShared_5239_ = v_isSharedCheck_5243_;
goto v_resetjp_5237_;
}
v_resetjp_5237_:
{
lean_object* v___x_5241_; 
if (v_isShared_5239_ == 0)
{
v___x_5241_ = v___x_5238_;
goto v_reusejp_5240_;
}
else
{
lean_object* v_reuseFailAlloc_5242_; 
v_reuseFailAlloc_5242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5242_, 0, v_a_5236_);
v___x_5241_ = v_reuseFailAlloc_5242_;
goto v_reusejp_5240_;
}
v_reusejp_5240_:
{
return v___x_5241_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorAppIndices_x3f___boxed(lean_object* v_ctorApp_5244_, lean_object* v_a_5245_, lean_object* v_a_5246_, lean_object* v_a_5247_, lean_object* v_a_5248_, lean_object* v_a_5249_){
_start:
{
lean_object* v_res_5250_; 
v_res_5250_ = l_Lean_Meta_getCtorAppIndices_x3f(v_ctorApp_5244_, v_a_5245_, v_a_5246_, v_a_5247_, v_a_5248_);
lean_dec(v_a_5248_);
lean_dec_ref(v_a_5247_);
lean_dec(v_a_5246_);
lean_dec_ref(v_a_5245_);
return v_res_5250_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1(lean_object* v_inst_5251_, lean_object* v_R_5252_, lean_object* v_a_5253_, lean_object* v_b_5254_){
_start:
{
lean_object* v___x_5255_; 
v___x_5255_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(v_a_5253_, v_b_5254_);
return v___x_5255_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0(lean_object* v_00_u03b1_5256_, lean_object* v_constName_5257_, lean_object* v___y_5258_, lean_object* v___y_5259_, lean_object* v___y_5260_, lean_object* v___y_5261_){
_start:
{
lean_object* v___x_5263_; 
v___x_5263_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(v_constName_5257_, v___y_5258_, v___y_5259_, v___y_5260_, v___y_5261_);
return v___x_5263_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b1_5264_, lean_object* v_constName_5265_, lean_object* v___y_5266_, lean_object* v___y_5267_, lean_object* v___y_5268_, lean_object* v___y_5269_, lean_object* v___y_5270_){
_start:
{
lean_object* v_res_5271_; 
v_res_5271_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0(v_00_u03b1_5264_, v_constName_5265_, v___y_5266_, v___y_5267_, v___y_5268_, v___y_5269_);
lean_dec(v___y_5269_);
lean_dec_ref(v___y_5268_);
lean_dec(v___y_5267_);
lean_dec_ref(v___y_5266_);
return v_res_5271_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_5272_, lean_object* v_ref_5273_, lean_object* v_constName_5274_, lean_object* v___y_5275_, lean_object* v___y_5276_, lean_object* v___y_5277_, lean_object* v___y_5278_){
_start:
{
lean_object* v___x_5280_; 
v___x_5280_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(v_ref_5273_, v_constName_5274_, v___y_5275_, v___y_5276_, v___y_5277_, v___y_5278_);
return v___x_5280_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_5281_, lean_object* v_ref_5282_, lean_object* v_constName_5283_, lean_object* v___y_5284_, lean_object* v___y_5285_, lean_object* v___y_5286_, lean_object* v___y_5287_, lean_object* v___y_5288_){
_start:
{
lean_object* v_res_5289_; 
v_res_5289_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1(v_00_u03b1_5281_, v_ref_5282_, v_constName_5283_, v___y_5284_, v___y_5285_, v___y_5286_, v___y_5287_);
lean_dec(v___y_5287_);
lean_dec_ref(v___y_5286_);
lean_dec(v___y_5285_);
lean_dec_ref(v___y_5284_);
lean_dec(v_ref_5282_);
return v_res_5289_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_5290_, lean_object* v_ref_5291_, lean_object* v_msg_5292_, lean_object* v_declHint_5293_, lean_object* v___y_5294_, lean_object* v___y_5295_, lean_object* v___y_5296_, lean_object* v___y_5297_){
_start:
{
lean_object* v___x_5299_; 
v___x_5299_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5291_, v_msg_5292_, v_declHint_5293_, v___y_5294_, v___y_5295_, v___y_5296_, v___y_5297_);
return v___x_5299_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_5300_, lean_object* v_ref_5301_, lean_object* v_msg_5302_, lean_object* v_declHint_5303_, lean_object* v___y_5304_, lean_object* v___y_5305_, lean_object* v___y_5306_, lean_object* v___y_5307_, lean_object* v___y_5308_){
_start:
{
lean_object* v_res_5309_; 
v_res_5309_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_5300_, v_ref_5301_, v_msg_5302_, v_declHint_5303_, v___y_5304_, v___y_5305_, v___y_5306_, v___y_5307_);
lean_dec(v___y_5307_);
lean_dec_ref(v___y_5306_);
lean_dec(v___y_5305_);
lean_dec_ref(v___y_5304_);
lean_dec(v_ref_5301_);
return v_res_5309_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_msg_5310_, lean_object* v_declHint_5311_, lean_object* v___y_5312_, lean_object* v___y_5313_, lean_object* v___y_5314_, lean_object* v___y_5315_){
_start:
{
lean_object* v___x_5317_; 
v___x_5317_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_5310_, v_declHint_5311_, v___y_5315_);
return v___x_5317_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_5318_, lean_object* v_declHint_5319_, lean_object* v___y_5320_, lean_object* v___y_5321_, lean_object* v___y_5322_, lean_object* v___y_5323_, lean_object* v___y_5324_){
_start:
{
lean_object* v_res_5325_; 
v_res_5325_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_5318_, v_declHint_5319_, v___y_5320_, v___y_5321_, v___y_5322_, v___y_5323_);
lean_dec(v___y_5323_);
lean_dec_ref(v___y_5322_);
lean_dec(v___y_5321_);
lean_dec_ref(v___y_5320_);
return v_res_5325_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_5326_, lean_object* v_ref_5327_, lean_object* v_msg_5328_, lean_object* v___y_5329_, lean_object* v___y_5330_, lean_object* v___y_5331_, lean_object* v___y_5332_){
_start:
{
lean_object* v___x_5334_; 
v___x_5334_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5327_, v_msg_5328_, v___y_5329_, v___y_5330_, v___y_5331_, v___y_5332_);
return v___x_5334_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_5335_, lean_object* v_ref_5336_, lean_object* v_msg_5337_, lean_object* v___y_5338_, lean_object* v___y_5339_, lean_object* v___y_5340_, lean_object* v___y_5341_, lean_object* v___y_5342_){
_start:
{
lean_object* v_res_5343_; 
v_res_5343_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_5335_, v_ref_5336_, v_msg_5337_, v___y_5338_, v___y_5339_, v___y_5340_, v___y_5341_);
lean_dec(v___y_5341_);
lean_dec_ref(v___y_5340_);
lean_dec(v___y_5339_);
lean_dec_ref(v___y_5338_);
lean_dec(v_ref_5336_);
return v_res_5343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0___boxed(lean_object* v_i_5344_, lean_object* v_body_5345_, lean_object* v_args2_5346_, lean_object* v_ctorVal_5347_, lean_object* v_args1_5348_, lean_object* v_k_5349_, lean_object* v_arg2_5350_, lean_object* v___y_5351_, lean_object* v___y_5352_, lean_object* v___y_5353_, lean_object* v___y_5354_, lean_object* v___y_5355_){
_start:
{
lean_object* v_res_5356_; 
v_res_5356_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0(v_i_5344_, v_body_5345_, v_args2_5346_, v_ctorVal_5347_, v_args1_5348_, v_k_5349_, v_arg2_5350_, v___y_5351_, v___y_5352_, v___y_5353_, v___y_5354_);
lean_dec(v___y_5354_);
lean_dec_ref(v___y_5353_);
lean_dec(v___y_5352_);
lean_dec_ref(v___y_5351_);
lean_dec_ref(v_body_5345_);
lean_dec(v_i_5344_);
return v_res_5356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(lean_object* v_ctorVal_5357_, lean_object* v_args1_5358_, lean_object* v_k_5359_, lean_object* v_i_5360_, lean_object* v_type_5361_, lean_object* v_args2_5362_, lean_object* v_a_5363_, lean_object* v_a_5364_, lean_object* v_a_5365_, lean_object* v_a_5366_){
_start:
{
lean_object* v___x_5368_; uint8_t v___x_5369_; 
v___x_5368_ = lean_array_get_size(v_args1_5358_);
v___x_5369_ = lean_nat_dec_lt(v_i_5360_, v___x_5368_);
if (v___x_5369_ == 0)
{
lean_object* v___x_5370_; 
lean_dec_ref(v_type_5361_);
lean_dec(v_i_5360_);
lean_dec_ref(v_args1_5358_);
lean_dec_ref(v_ctorVal_5357_);
lean_inc(v_a_5366_);
lean_inc_ref(v_a_5365_);
lean_inc(v_a_5364_);
lean_inc_ref(v_a_5363_);
v___x_5370_ = lean_apply_6(v_k_5359_, v_args2_5362_, v_a_5363_, v_a_5364_, v_a_5365_, v_a_5366_, lean_box(0));
return v___x_5370_;
}
else
{
lean_object* v___x_5371_; 
lean_inc(v_a_5366_);
lean_inc_ref(v_a_5365_);
lean_inc(v_a_5364_);
lean_inc_ref(v_a_5363_);
v___x_5371_ = lean_whnf(v_type_5361_, v_a_5363_, v_a_5364_, v_a_5365_, v_a_5366_);
if (lean_obj_tag(v___x_5371_) == 0)
{
lean_object* v_a_5372_; 
v_a_5372_ = lean_ctor_get(v___x_5371_, 0);
lean_inc(v_a_5372_);
lean_dec_ref_known(v___x_5371_, 1);
if (lean_obj_tag(v_a_5372_) == 7)
{
lean_object* v_binderName_5373_; lean_object* v_binderType_5374_; lean_object* v_body_5375_; lean_object* v___f_5376_; uint8_t v___x_5377_; uint8_t v___x_5378_; lean_object* v___x_5379_; 
v_binderName_5373_ = lean_ctor_get(v_a_5372_, 0);
lean_inc(v_binderName_5373_);
v_binderType_5374_ = lean_ctor_get(v_a_5372_, 1);
lean_inc_ref(v_binderType_5374_);
v_body_5375_ = lean_ctor_get(v_a_5372_, 2);
lean_inc_ref(v_body_5375_);
lean_dec_ref_known(v_a_5372_, 3);
v___f_5376_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0___boxed), 12, 6);
lean_closure_set(v___f_5376_, 0, v_i_5360_);
lean_closure_set(v___f_5376_, 1, v_body_5375_);
lean_closure_set(v___f_5376_, 2, v_args2_5362_);
lean_closure_set(v___f_5376_, 3, v_ctorVal_5357_);
lean_closure_set(v___f_5376_, 4, v_args1_5358_);
lean_closure_set(v___f_5376_, 5, v_k_5359_);
v___x_5377_ = 1;
v___x_5378_ = 0;
v___x_5379_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_binderName_5373_, v___x_5377_, v_binderType_5374_, v___f_5376_, v___x_5378_, v_a_5363_, v_a_5364_, v_a_5365_, v_a_5366_);
return v___x_5379_;
}
else
{
lean_object* v_toConstantVal_5380_; lean_object* v_name_5381_; lean_object* v___x_5382_; lean_object* v___x_5383_; lean_object* v___x_5384_; lean_object* v___x_5385_; lean_object* v___x_5386_; lean_object* v___x_5387_; 
lean_dec(v_a_5372_);
lean_dec_ref(v_args2_5362_);
lean_dec(v_i_5360_);
lean_dec_ref(v_k_5359_);
lean_dec_ref(v_args1_5358_);
v_toConstantVal_5380_ = lean_ctor_get(v_ctorVal_5357_, 0);
lean_inc_ref(v_toConstantVal_5380_);
lean_dec_ref(v_ctorVal_5357_);
v_name_5381_ = lean_ctor_get(v_toConstantVal_5380_, 0);
lean_inc(v_name_5381_);
lean_dec_ref(v_toConstantVal_5380_);
v___x_5382_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1);
v___x_5383_ = l_Lean_MessageData_ofName(v_name_5381_);
v___x_5384_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5384_, 0, v___x_5382_);
lean_ctor_set(v___x_5384_, 1, v___x_5383_);
v___x_5385_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_5386_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5386_, 0, v___x_5384_);
lean_ctor_set(v___x_5386_, 1, v___x_5385_);
v___x_5387_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_5386_, v_a_5363_, v_a_5364_, v_a_5365_, v_a_5366_);
return v___x_5387_;
}
}
else
{
lean_object* v_a_5388_; lean_object* v___x_5390_; uint8_t v_isShared_5391_; uint8_t v_isSharedCheck_5395_; 
lean_dec_ref(v_args2_5362_);
lean_dec(v_i_5360_);
lean_dec_ref(v_k_5359_);
lean_dec_ref(v_args1_5358_);
lean_dec_ref(v_ctorVal_5357_);
v_a_5388_ = lean_ctor_get(v___x_5371_, 0);
v_isSharedCheck_5395_ = !lean_is_exclusive(v___x_5371_);
if (v_isSharedCheck_5395_ == 0)
{
v___x_5390_ = v___x_5371_;
v_isShared_5391_ = v_isSharedCheck_5395_;
goto v_resetjp_5389_;
}
else
{
lean_inc(v_a_5388_);
lean_dec(v___x_5371_);
v___x_5390_ = lean_box(0);
v_isShared_5391_ = v_isSharedCheck_5395_;
goto v_resetjp_5389_;
}
v_resetjp_5389_:
{
lean_object* v___x_5393_; 
if (v_isShared_5391_ == 0)
{
v___x_5393_ = v___x_5390_;
goto v_reusejp_5392_;
}
else
{
lean_object* v_reuseFailAlloc_5394_; 
v_reuseFailAlloc_5394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5394_, 0, v_a_5388_);
v___x_5393_ = v_reuseFailAlloc_5394_;
goto v_reusejp_5392_;
}
v_reusejp_5392_:
{
return v___x_5393_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0(lean_object* v_i_5396_, lean_object* v_body_5397_, lean_object* v_args2_5398_, lean_object* v_ctorVal_5399_, lean_object* v_args1_5400_, lean_object* v_k_5401_, lean_object* v_arg2_5402_, lean_object* v___y_5403_, lean_object* v___y_5404_, lean_object* v___y_5405_, lean_object* v___y_5406_){
_start:
{
lean_object* v___x_5408_; lean_object* v___x_5409_; lean_object* v___x_5410_; lean_object* v___x_5411_; lean_object* v___x_5412_; 
v___x_5408_ = lean_unsigned_to_nat(1u);
v___x_5409_ = lean_nat_add(v_i_5396_, v___x_5408_);
v___x_5410_ = lean_expr_instantiate1(v_body_5397_, v_arg2_5402_);
v___x_5411_ = lean_array_push(v_args2_5398_, v_arg2_5402_);
v___x_5412_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(v_ctorVal_5399_, v_args1_5400_, v_k_5401_, v___x_5409_, v___x_5410_, v___x_5411_, v___y_5403_, v___y_5404_, v___y_5405_, v___y_5406_);
return v___x_5412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___boxed(lean_object* v_ctorVal_5413_, lean_object* v_args1_5414_, lean_object* v_k_5415_, lean_object* v_i_5416_, lean_object* v_type_5417_, lean_object* v_args2_5418_, lean_object* v_a_5419_, lean_object* v_a_5420_, lean_object* v_a_5421_, lean_object* v_a_5422_, lean_object* v_a_5423_){
_start:
{
lean_object* v_res_5424_; 
v_res_5424_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(v_ctorVal_5413_, v_args1_5414_, v_k_5415_, v_i_5416_, v_type_5417_, v_args2_5418_, v_a_5419_, v_a_5420_, v_a_5421_, v_a_5422_);
lean_dec(v_a_5422_);
lean_dec_ref(v_a_5421_);
lean_dec(v_a_5420_);
lean_dec_ref(v_a_5419_);
return v_res_5424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0(lean_object* v___x_5425_, lean_object* v_numParams_5426_, lean_object* v_name_5427_, lean_object* v_us_5428_, lean_object* v_args1_5429_, lean_object* v___x_5430_, lean_object* v_args2_5431_, lean_object* v___y_5432_, lean_object* v___y_5433_, lean_object* v___y_5434_, lean_object* v___y_5435_){
_start:
{
lean_object* v___x_5437_; lean_object* v___x_5438_; lean_object* v___x_5439_; lean_object* v___x_5440_; lean_object* v___x_5441_; 
lean_inc_ref(v_args2_5431_);
v___x_5437_ = l_Array_toSubarray___redArg(v_args2_5431_, v___x_5425_, v_numParams_5426_);
lean_inc(v_us_5428_);
v___x_5438_ = l_Lean_mkConst(v_name_5427_, v_us_5428_);
lean_inc_ref(v___x_5438_);
v___x_5439_ = l_Lean_mkAppN(v___x_5438_, v_args1_5429_);
v___x_5440_ = l_Lean_mkAppN(v___x_5438_, v_args2_5431_);
lean_inc_ref(v___x_5440_);
lean_inc_ref(v___x_5439_);
v___x_5441_ = l_Lean_Meta_mkEqHEq(v___x_5439_, v___x_5440_, v___y_5432_, v___y_5433_, v___y_5434_, v___y_5435_);
if (lean_obj_tag(v___x_5441_) == 0)
{
lean_object* v_a_5442_; uint8_t v___x_5443_; lean_object* v___x_5444_; 
v_a_5442_ = lean_ctor_get(v___x_5441_, 0);
lean_inc(v_a_5442_);
lean_dec_ref_known(v___x_5441_, 1);
v___x_5443_ = 1;
lean_inc_ref(v_args2_5431_);
v___x_5444_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v_args1_5429_, v_args2_5431_, v___x_5443_, v___y_5432_, v___y_5433_, v___y_5434_, v___y_5435_);
if (lean_obj_tag(v___x_5444_) == 0)
{
lean_object* v_a_5445_; lean_object* v___x_5447_; uint8_t v_isShared_5448_; uint8_t v_isSharedCheck_5565_; 
v_a_5445_ = lean_ctor_get(v___x_5444_, 0);
v_isSharedCheck_5565_ = !lean_is_exclusive(v___x_5444_);
if (v_isSharedCheck_5565_ == 0)
{
v___x_5447_ = v___x_5444_;
v_isShared_5448_ = v_isSharedCheck_5565_;
goto v_resetjp_5446_;
}
else
{
lean_inc(v_a_5445_);
lean_dec(v___x_5444_);
v___x_5447_ = lean_box(0);
v_isShared_5448_ = v_isSharedCheck_5565_;
goto v_resetjp_5446_;
}
v_resetjp_5446_:
{
lean_object* v___x_5449_; 
v___x_5449_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f(v_a_5445_);
if (lean_obj_tag(v___x_5449_) == 1)
{
lean_object* v_val_5450_; lean_object* v___x_5451_; 
lean_del_object(v___x_5447_);
v_val_5450_ = lean_ctor_get(v___x_5449_, 0);
lean_inc(v_val_5450_);
lean_dec_ref_known(v___x_5449_, 1);
v___x_5451_ = l_Lean_mkArrow(v_a_5442_, v_val_5450_, v___y_5434_, v___y_5435_);
if (lean_obj_tag(v___x_5451_) == 0)
{
lean_object* v_a_5452_; lean_object* v___x_5453_; 
v_a_5452_ = lean_ctor_get(v___x_5451_, 0);
lean_inc(v_a_5452_);
lean_dec_ref_known(v___x_5451_, 1);
v___x_5453_ = l_Lean_Meta_getCtorAppIndices_x3f(v___x_5439_, v___y_5432_, v___y_5433_, v___y_5434_, v___y_5435_);
if (lean_obj_tag(v___x_5453_) == 0)
{
lean_object* v_a_5454_; lean_object* v___x_5456_; uint8_t v_isShared_5457_; uint8_t v_isSharedCheck_5544_; 
v_a_5454_ = lean_ctor_get(v___x_5453_, 0);
v_isSharedCheck_5544_ = !lean_is_exclusive(v___x_5453_);
if (v_isSharedCheck_5544_ == 0)
{
v___x_5456_ = v___x_5453_;
v_isShared_5457_ = v_isSharedCheck_5544_;
goto v_resetjp_5455_;
}
else
{
lean_inc(v_a_5454_);
lean_dec(v___x_5453_);
v___x_5456_ = lean_box(0);
v_isShared_5457_ = v_isSharedCheck_5544_;
goto v_resetjp_5455_;
}
v_resetjp_5455_:
{
if (lean_obj_tag(v_a_5454_) == 1)
{
lean_object* v_val_5458_; lean_object* v___x_5459_; 
lean_del_object(v___x_5456_);
v_val_5458_ = lean_ctor_get(v_a_5454_, 0);
lean_inc(v_val_5458_);
lean_dec_ref_known(v_a_5454_, 1);
v___x_5459_ = l_Lean_Meta_getCtorAppIndices_x3f(v___x_5440_, v___y_5432_, v___y_5433_, v___y_5434_, v___y_5435_);
if (lean_obj_tag(v___x_5459_) == 0)
{
lean_object* v_a_5460_; lean_object* v___x_5462_; uint8_t v_isShared_5463_; uint8_t v_isSharedCheck_5531_; 
v_a_5460_ = lean_ctor_get(v___x_5459_, 0);
v_isSharedCheck_5531_ = !lean_is_exclusive(v___x_5459_);
if (v_isSharedCheck_5531_ == 0)
{
v___x_5462_ = v___x_5459_;
v_isShared_5463_ = v_isSharedCheck_5531_;
goto v_resetjp_5461_;
}
else
{
lean_inc(v_a_5460_);
lean_dec(v___x_5459_);
v___x_5462_ = lean_box(0);
v_isShared_5463_ = v_isSharedCheck_5531_;
goto v_resetjp_5461_;
}
v_resetjp_5461_:
{
if (lean_obj_tag(v_a_5460_) == 1)
{
lean_object* v_val_5464_; lean_object* v___x_5466_; uint8_t v_isShared_5467_; uint8_t v_isSharedCheck_5526_; 
lean_del_object(v___x_5462_);
v_val_5464_ = lean_ctor_get(v_a_5460_, 0);
v_isSharedCheck_5526_ = !lean_is_exclusive(v_a_5460_);
if (v_isSharedCheck_5526_ == 0)
{
v___x_5466_ = v_a_5460_;
v_isShared_5467_ = v_isSharedCheck_5526_;
goto v_resetjp_5465_;
}
else
{
lean_inc(v_val_5464_);
lean_dec(v_a_5460_);
v___x_5466_ = lean_box(0);
v_isShared_5467_ = v_isSharedCheck_5526_;
goto v_resetjp_5465_;
}
v_resetjp_5465_:
{
lean_object* v___x_5468_; lean_object* v___x_5469_; lean_object* v___x_5470_; lean_object* v___x_5471_; uint8_t v___x_5472_; lean_object* v___x_5473_; 
v___x_5468_ = l_Subarray_copy___redArg(v___x_5430_);
v___x_5469_ = l_Array_append___redArg(v___x_5468_, v_val_5458_);
v___x_5470_ = l_Subarray_copy___redArg(v___x_5437_);
v___x_5471_ = l_Array_append___redArg(v___x_5470_, v_val_5464_);
lean_dec(v_val_5464_);
v___x_5472_ = 0;
v___x_5473_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v___x_5469_, v___x_5471_, v___x_5472_, v___y_5432_, v___y_5433_, v___y_5434_, v___y_5435_);
lean_dec_ref(v___x_5469_);
if (lean_obj_tag(v___x_5473_) == 0)
{
lean_object* v_a_5474_; lean_object* v___x_5475_; 
v_a_5474_ = lean_ctor_get(v___x_5473_, 0);
lean_inc(v_a_5474_);
lean_dec_ref_known(v___x_5473_, 1);
v___x_5475_ = l_Lean_mkArrowN(v_a_5474_, v_a_5452_, v___y_5434_, v___y_5435_);
lean_dec(v_a_5474_);
if (lean_obj_tag(v___x_5475_) == 0)
{
lean_object* v_a_5476_; uint8_t v___x_5477_; lean_object* v___x_5478_; 
v_a_5476_ = lean_ctor_get(v___x_5475_, 0);
lean_inc(v_a_5476_);
lean_dec_ref_known(v___x_5475_, 1);
v___x_5477_ = 1;
v___x_5478_ = l_Lean_Meta_mkForallFVars(v_args2_5431_, v_a_5476_, v___x_5472_, v___x_5443_, v___x_5443_, v___x_5477_, v___y_5432_, v___y_5433_, v___y_5434_, v___y_5435_);
lean_dec_ref(v_args2_5431_);
if (lean_obj_tag(v___x_5478_) == 0)
{
lean_object* v_a_5479_; lean_object* v___x_5480_; 
v_a_5479_ = lean_ctor_get(v___x_5478_, 0);
lean_inc(v_a_5479_);
lean_dec_ref_known(v___x_5478_, 1);
v___x_5480_ = l_Lean_Meta_mkForallFVars(v_args1_5429_, v_a_5479_, v___x_5472_, v___x_5443_, v___x_5443_, v___x_5477_, v___y_5432_, v___y_5433_, v___y_5434_, v___y_5435_);
if (lean_obj_tag(v___x_5480_) == 0)
{
lean_object* v_a_5481_; lean_object* v___x_5483_; uint8_t v_isShared_5484_; uint8_t v_isSharedCheck_5493_; 
v_a_5481_ = lean_ctor_get(v___x_5480_, 0);
v_isSharedCheck_5493_ = !lean_is_exclusive(v___x_5480_);
if (v_isSharedCheck_5493_ == 0)
{
v___x_5483_ = v___x_5480_;
v_isShared_5484_ = v_isSharedCheck_5493_;
goto v_resetjp_5482_;
}
else
{
lean_inc(v_a_5481_);
lean_dec(v___x_5480_);
v___x_5483_ = lean_box(0);
v_isShared_5484_ = v_isSharedCheck_5493_;
goto v_resetjp_5482_;
}
v_resetjp_5482_:
{
lean_object* v___x_5485_; lean_object* v___x_5486_; lean_object* v___x_5488_; 
v___x_5485_ = lean_array_get_size(v_val_5458_);
lean_dec(v_val_5458_);
v___x_5486_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5486_, 0, v_a_5481_);
lean_ctor_set(v___x_5486_, 1, v_us_5428_);
lean_ctor_set(v___x_5486_, 2, v___x_5485_);
if (v_isShared_5467_ == 0)
{
lean_ctor_set(v___x_5466_, 0, v___x_5486_);
v___x_5488_ = v___x_5466_;
goto v_reusejp_5487_;
}
else
{
lean_object* v_reuseFailAlloc_5492_; 
v_reuseFailAlloc_5492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5492_, 0, v___x_5486_);
v___x_5488_ = v_reuseFailAlloc_5492_;
goto v_reusejp_5487_;
}
v_reusejp_5487_:
{
lean_object* v___x_5490_; 
if (v_isShared_5484_ == 0)
{
lean_ctor_set(v___x_5483_, 0, v___x_5488_);
v___x_5490_ = v___x_5483_;
goto v_reusejp_5489_;
}
else
{
lean_object* v_reuseFailAlloc_5491_; 
v_reuseFailAlloc_5491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5491_, 0, v___x_5488_);
v___x_5490_ = v_reuseFailAlloc_5491_;
goto v_reusejp_5489_;
}
v_reusejp_5489_:
{
return v___x_5490_;
}
}
}
}
else
{
lean_object* v_a_5494_; lean_object* v___x_5496_; uint8_t v_isShared_5497_; uint8_t v_isSharedCheck_5501_; 
lean_del_object(v___x_5466_);
lean_dec(v_val_5458_);
lean_dec(v_us_5428_);
v_a_5494_ = lean_ctor_get(v___x_5480_, 0);
v_isSharedCheck_5501_ = !lean_is_exclusive(v___x_5480_);
if (v_isSharedCheck_5501_ == 0)
{
v___x_5496_ = v___x_5480_;
v_isShared_5497_ = v_isSharedCheck_5501_;
goto v_resetjp_5495_;
}
else
{
lean_inc(v_a_5494_);
lean_dec(v___x_5480_);
v___x_5496_ = lean_box(0);
v_isShared_5497_ = v_isSharedCheck_5501_;
goto v_resetjp_5495_;
}
v_resetjp_5495_:
{
lean_object* v___x_5499_; 
if (v_isShared_5497_ == 0)
{
v___x_5499_ = v___x_5496_;
goto v_reusejp_5498_;
}
else
{
lean_object* v_reuseFailAlloc_5500_; 
v_reuseFailAlloc_5500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5500_, 0, v_a_5494_);
v___x_5499_ = v_reuseFailAlloc_5500_;
goto v_reusejp_5498_;
}
v_reusejp_5498_:
{
return v___x_5499_;
}
}
}
}
else
{
lean_object* v_a_5502_; lean_object* v___x_5504_; uint8_t v_isShared_5505_; uint8_t v_isSharedCheck_5509_; 
lean_del_object(v___x_5466_);
lean_dec(v_val_5458_);
lean_dec(v_us_5428_);
v_a_5502_ = lean_ctor_get(v___x_5478_, 0);
v_isSharedCheck_5509_ = !lean_is_exclusive(v___x_5478_);
if (v_isSharedCheck_5509_ == 0)
{
v___x_5504_ = v___x_5478_;
v_isShared_5505_ = v_isSharedCheck_5509_;
goto v_resetjp_5503_;
}
else
{
lean_inc(v_a_5502_);
lean_dec(v___x_5478_);
v___x_5504_ = lean_box(0);
v_isShared_5505_ = v_isSharedCheck_5509_;
goto v_resetjp_5503_;
}
v_resetjp_5503_:
{
lean_object* v___x_5507_; 
if (v_isShared_5505_ == 0)
{
v___x_5507_ = v___x_5504_;
goto v_reusejp_5506_;
}
else
{
lean_object* v_reuseFailAlloc_5508_; 
v_reuseFailAlloc_5508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5508_, 0, v_a_5502_);
v___x_5507_ = v_reuseFailAlloc_5508_;
goto v_reusejp_5506_;
}
v_reusejp_5506_:
{
return v___x_5507_;
}
}
}
}
else
{
lean_object* v_a_5510_; lean_object* v___x_5512_; uint8_t v_isShared_5513_; uint8_t v_isSharedCheck_5517_; 
lean_del_object(v___x_5466_);
lean_dec(v_val_5458_);
lean_dec_ref(v_args2_5431_);
lean_dec(v_us_5428_);
v_a_5510_ = lean_ctor_get(v___x_5475_, 0);
v_isSharedCheck_5517_ = !lean_is_exclusive(v___x_5475_);
if (v_isSharedCheck_5517_ == 0)
{
v___x_5512_ = v___x_5475_;
v_isShared_5513_ = v_isSharedCheck_5517_;
goto v_resetjp_5511_;
}
else
{
lean_inc(v_a_5510_);
lean_dec(v___x_5475_);
v___x_5512_ = lean_box(0);
v_isShared_5513_ = v_isSharedCheck_5517_;
goto v_resetjp_5511_;
}
v_resetjp_5511_:
{
lean_object* v___x_5515_; 
if (v_isShared_5513_ == 0)
{
v___x_5515_ = v___x_5512_;
goto v_reusejp_5514_;
}
else
{
lean_object* v_reuseFailAlloc_5516_; 
v_reuseFailAlloc_5516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5516_, 0, v_a_5510_);
v___x_5515_ = v_reuseFailAlloc_5516_;
goto v_reusejp_5514_;
}
v_reusejp_5514_:
{
return v___x_5515_;
}
}
}
}
else
{
lean_object* v_a_5518_; lean_object* v___x_5520_; uint8_t v_isShared_5521_; uint8_t v_isSharedCheck_5525_; 
lean_del_object(v___x_5466_);
lean_dec(v_val_5458_);
lean_dec(v_a_5452_);
lean_dec_ref(v_args2_5431_);
lean_dec(v_us_5428_);
v_a_5518_ = lean_ctor_get(v___x_5473_, 0);
v_isSharedCheck_5525_ = !lean_is_exclusive(v___x_5473_);
if (v_isSharedCheck_5525_ == 0)
{
v___x_5520_ = v___x_5473_;
v_isShared_5521_ = v_isSharedCheck_5525_;
goto v_resetjp_5519_;
}
else
{
lean_inc(v_a_5518_);
lean_dec(v___x_5473_);
v___x_5520_ = lean_box(0);
v_isShared_5521_ = v_isSharedCheck_5525_;
goto v_resetjp_5519_;
}
v_resetjp_5519_:
{
lean_object* v___x_5523_; 
if (v_isShared_5521_ == 0)
{
v___x_5523_ = v___x_5520_;
goto v_reusejp_5522_;
}
else
{
lean_object* v_reuseFailAlloc_5524_; 
v_reuseFailAlloc_5524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5524_, 0, v_a_5518_);
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
}
else
{
lean_object* v___x_5527_; lean_object* v___x_5529_; 
lean_dec(v_a_5460_);
lean_dec(v_val_5458_);
lean_dec(v_a_5452_);
lean_dec_ref(v___x_5437_);
lean_dec_ref(v_args2_5431_);
lean_dec_ref(v___x_5430_);
lean_dec(v_us_5428_);
v___x_5527_ = lean_box(0);
if (v_isShared_5463_ == 0)
{
lean_ctor_set(v___x_5462_, 0, v___x_5527_);
v___x_5529_ = v___x_5462_;
goto v_reusejp_5528_;
}
else
{
lean_object* v_reuseFailAlloc_5530_; 
v_reuseFailAlloc_5530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5530_, 0, v___x_5527_);
v___x_5529_ = v_reuseFailAlloc_5530_;
goto v_reusejp_5528_;
}
v_reusejp_5528_:
{
return v___x_5529_;
}
}
}
}
else
{
lean_object* v_a_5532_; lean_object* v___x_5534_; uint8_t v_isShared_5535_; uint8_t v_isSharedCheck_5539_; 
lean_dec(v_val_5458_);
lean_dec(v_a_5452_);
lean_dec_ref(v___x_5437_);
lean_dec_ref(v_args2_5431_);
lean_dec_ref(v___x_5430_);
lean_dec(v_us_5428_);
v_a_5532_ = lean_ctor_get(v___x_5459_, 0);
v_isSharedCheck_5539_ = !lean_is_exclusive(v___x_5459_);
if (v_isSharedCheck_5539_ == 0)
{
v___x_5534_ = v___x_5459_;
v_isShared_5535_ = v_isSharedCheck_5539_;
goto v_resetjp_5533_;
}
else
{
lean_inc(v_a_5532_);
lean_dec(v___x_5459_);
v___x_5534_ = lean_box(0);
v_isShared_5535_ = v_isSharedCheck_5539_;
goto v_resetjp_5533_;
}
v_resetjp_5533_:
{
lean_object* v___x_5537_; 
if (v_isShared_5535_ == 0)
{
v___x_5537_ = v___x_5534_;
goto v_reusejp_5536_;
}
else
{
lean_object* v_reuseFailAlloc_5538_; 
v_reuseFailAlloc_5538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5538_, 0, v_a_5532_);
v___x_5537_ = v_reuseFailAlloc_5538_;
goto v_reusejp_5536_;
}
v_reusejp_5536_:
{
return v___x_5537_;
}
}
}
}
else
{
lean_object* v___x_5540_; lean_object* v___x_5542_; 
lean_dec(v_a_5454_);
lean_dec(v_a_5452_);
lean_dec_ref(v___x_5440_);
lean_dec_ref(v___x_5437_);
lean_dec_ref(v_args2_5431_);
lean_dec_ref(v___x_5430_);
lean_dec(v_us_5428_);
v___x_5540_ = lean_box(0);
if (v_isShared_5457_ == 0)
{
lean_ctor_set(v___x_5456_, 0, v___x_5540_);
v___x_5542_ = v___x_5456_;
goto v_reusejp_5541_;
}
else
{
lean_object* v_reuseFailAlloc_5543_; 
v_reuseFailAlloc_5543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5543_, 0, v___x_5540_);
v___x_5542_ = v_reuseFailAlloc_5543_;
goto v_reusejp_5541_;
}
v_reusejp_5541_:
{
return v___x_5542_;
}
}
}
}
else
{
lean_object* v_a_5545_; lean_object* v___x_5547_; uint8_t v_isShared_5548_; uint8_t v_isSharedCheck_5552_; 
lean_dec(v_a_5452_);
lean_dec_ref(v___x_5440_);
lean_dec_ref(v___x_5437_);
lean_dec_ref(v_args2_5431_);
lean_dec_ref(v___x_5430_);
lean_dec(v_us_5428_);
v_a_5545_ = lean_ctor_get(v___x_5453_, 0);
v_isSharedCheck_5552_ = !lean_is_exclusive(v___x_5453_);
if (v_isSharedCheck_5552_ == 0)
{
v___x_5547_ = v___x_5453_;
v_isShared_5548_ = v_isSharedCheck_5552_;
goto v_resetjp_5546_;
}
else
{
lean_inc(v_a_5545_);
lean_dec(v___x_5453_);
v___x_5547_ = lean_box(0);
v_isShared_5548_ = v_isSharedCheck_5552_;
goto v_resetjp_5546_;
}
v_resetjp_5546_:
{
lean_object* v___x_5550_; 
if (v_isShared_5548_ == 0)
{
v___x_5550_ = v___x_5547_;
goto v_reusejp_5549_;
}
else
{
lean_object* v_reuseFailAlloc_5551_; 
v_reuseFailAlloc_5551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5551_, 0, v_a_5545_);
v___x_5550_ = v_reuseFailAlloc_5551_;
goto v_reusejp_5549_;
}
v_reusejp_5549_:
{
return v___x_5550_;
}
}
}
}
else
{
lean_object* v_a_5553_; lean_object* v___x_5555_; uint8_t v_isShared_5556_; uint8_t v_isSharedCheck_5560_; 
lean_dec_ref(v___x_5440_);
lean_dec_ref(v___x_5439_);
lean_dec_ref(v___x_5437_);
lean_dec_ref(v_args2_5431_);
lean_dec_ref(v___x_5430_);
lean_dec(v_us_5428_);
v_a_5553_ = lean_ctor_get(v___x_5451_, 0);
v_isSharedCheck_5560_ = !lean_is_exclusive(v___x_5451_);
if (v_isSharedCheck_5560_ == 0)
{
v___x_5555_ = v___x_5451_;
v_isShared_5556_ = v_isSharedCheck_5560_;
goto v_resetjp_5554_;
}
else
{
lean_inc(v_a_5553_);
lean_dec(v___x_5451_);
v___x_5555_ = lean_box(0);
v_isShared_5556_ = v_isSharedCheck_5560_;
goto v_resetjp_5554_;
}
v_resetjp_5554_:
{
lean_object* v___x_5558_; 
if (v_isShared_5556_ == 0)
{
v___x_5558_ = v___x_5555_;
goto v_reusejp_5557_;
}
else
{
lean_object* v_reuseFailAlloc_5559_; 
v_reuseFailAlloc_5559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5559_, 0, v_a_5553_);
v___x_5558_ = v_reuseFailAlloc_5559_;
goto v_reusejp_5557_;
}
v_reusejp_5557_:
{
return v___x_5558_;
}
}
}
}
else
{
lean_object* v___x_5561_; lean_object* v___x_5563_; 
lean_dec(v___x_5449_);
lean_dec(v_a_5442_);
lean_dec_ref(v___x_5440_);
lean_dec_ref(v___x_5439_);
lean_dec_ref(v___x_5437_);
lean_dec_ref(v_args2_5431_);
lean_dec_ref(v___x_5430_);
lean_dec(v_us_5428_);
v___x_5561_ = lean_box(0);
if (v_isShared_5448_ == 0)
{
lean_ctor_set(v___x_5447_, 0, v___x_5561_);
v___x_5563_ = v___x_5447_;
goto v_reusejp_5562_;
}
else
{
lean_object* v_reuseFailAlloc_5564_; 
v_reuseFailAlloc_5564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5564_, 0, v___x_5561_);
v___x_5563_ = v_reuseFailAlloc_5564_;
goto v_reusejp_5562_;
}
v_reusejp_5562_:
{
return v___x_5563_;
}
}
}
}
else
{
lean_object* v_a_5566_; lean_object* v___x_5568_; uint8_t v_isShared_5569_; uint8_t v_isSharedCheck_5573_; 
lean_dec(v_a_5442_);
lean_dec_ref(v___x_5440_);
lean_dec_ref(v___x_5439_);
lean_dec_ref(v___x_5437_);
lean_dec_ref(v_args2_5431_);
lean_dec_ref(v___x_5430_);
lean_dec(v_us_5428_);
v_a_5566_ = lean_ctor_get(v___x_5444_, 0);
v_isSharedCheck_5573_ = !lean_is_exclusive(v___x_5444_);
if (v_isSharedCheck_5573_ == 0)
{
v___x_5568_ = v___x_5444_;
v_isShared_5569_ = v_isSharedCheck_5573_;
goto v_resetjp_5567_;
}
else
{
lean_inc(v_a_5566_);
lean_dec(v___x_5444_);
v___x_5568_ = lean_box(0);
v_isShared_5569_ = v_isSharedCheck_5573_;
goto v_resetjp_5567_;
}
v_resetjp_5567_:
{
lean_object* v___x_5571_; 
if (v_isShared_5569_ == 0)
{
v___x_5571_ = v___x_5568_;
goto v_reusejp_5570_;
}
else
{
lean_object* v_reuseFailAlloc_5572_; 
v_reuseFailAlloc_5572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5572_, 0, v_a_5566_);
v___x_5571_ = v_reuseFailAlloc_5572_;
goto v_reusejp_5570_;
}
v_reusejp_5570_:
{
return v___x_5571_;
}
}
}
}
else
{
lean_object* v_a_5574_; lean_object* v___x_5576_; uint8_t v_isShared_5577_; uint8_t v_isSharedCheck_5581_; 
lean_dec_ref(v___x_5440_);
lean_dec_ref(v___x_5439_);
lean_dec_ref(v___x_5437_);
lean_dec_ref(v_args2_5431_);
lean_dec_ref(v___x_5430_);
lean_dec(v_us_5428_);
v_a_5574_ = lean_ctor_get(v___x_5441_, 0);
v_isSharedCheck_5581_ = !lean_is_exclusive(v___x_5441_);
if (v_isSharedCheck_5581_ == 0)
{
v___x_5576_ = v___x_5441_;
v_isShared_5577_ = v_isSharedCheck_5581_;
goto v_resetjp_5575_;
}
else
{
lean_inc(v_a_5574_);
lean_dec(v___x_5441_);
v___x_5576_ = lean_box(0);
v_isShared_5577_ = v_isSharedCheck_5581_;
goto v_resetjp_5575_;
}
v_resetjp_5575_:
{
lean_object* v___x_5579_; 
if (v_isShared_5577_ == 0)
{
v___x_5579_ = v___x_5576_;
goto v_reusejp_5578_;
}
else
{
lean_object* v_reuseFailAlloc_5580_; 
v_reuseFailAlloc_5580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5580_, 0, v_a_5574_);
v___x_5579_ = v_reuseFailAlloc_5580_;
goto v_reusejp_5578_;
}
v_reusejp_5578_:
{
return v___x_5579_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0___boxed(lean_object* v___x_5582_, lean_object* v_numParams_5583_, lean_object* v_name_5584_, lean_object* v_us_5585_, lean_object* v_args1_5586_, lean_object* v___x_5587_, lean_object* v_args2_5588_, lean_object* v___y_5589_, lean_object* v___y_5590_, lean_object* v___y_5591_, lean_object* v___y_5592_, lean_object* v___y_5593_){
_start:
{
lean_object* v_res_5594_; 
v_res_5594_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0(v___x_5582_, v_numParams_5583_, v_name_5584_, v_us_5585_, v_args1_5586_, v___x_5587_, v_args2_5588_, v___y_5589_, v___y_5590_, v___y_5591_, v___y_5592_);
lean_dec(v___y_5592_);
lean_dec_ref(v___y_5591_);
lean_dec(v___y_5590_);
lean_dec_ref(v___y_5589_);
lean_dec_ref(v_args1_5586_);
return v_res_5594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1(lean_object* v_numParams_5595_, lean_object* v_name_5596_, lean_object* v_us_5597_, lean_object* v_ctorVal_5598_, lean_object* v_a_5599_, lean_object* v_args1_5600_, lean_object* v_x_5601_, lean_object* v___y_5602_, lean_object* v___y_5603_, lean_object* v___y_5604_, lean_object* v___y_5605_){
_start:
{
lean_object* v___x_5607_; lean_object* v___x_5608_; lean_object* v___f_5609_; lean_object* v___x_5610_; lean_object* v___x_5611_; lean_object* v___x_5612_; 
v___x_5607_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_5595_);
lean_inc_ref_n(v_args1_5600_, 3);
v___x_5608_ = l_Array_toSubarray___redArg(v_args1_5600_, v___x_5607_, v_numParams_5595_);
v___f_5609_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0___boxed), 12, 6);
lean_closure_set(v___f_5609_, 0, v___x_5607_);
lean_closure_set(v___f_5609_, 1, v_numParams_5595_);
lean_closure_set(v___f_5609_, 2, v_name_5596_);
lean_closure_set(v___f_5609_, 3, v_us_5597_);
lean_closure_set(v___f_5609_, 4, v_args1_5600_);
lean_closure_set(v___f_5609_, 5, v___x_5608_);
v___x_5610_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_5611_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___boxed), 11, 6);
lean_closure_set(v___x_5611_, 0, v_ctorVal_5598_);
lean_closure_set(v___x_5611_, 1, v_args1_5600_);
lean_closure_set(v___x_5611_, 2, v___f_5609_);
lean_closure_set(v___x_5611_, 3, v___x_5607_);
lean_closure_set(v___x_5611_, 4, v_a_5599_);
lean_closure_set(v___x_5611_, 5, v___x_5610_);
v___x_5612_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v_args1_5600_, v___x_5611_, v___y_5602_, v___y_5603_, v___y_5604_, v___y_5605_);
return v___x_5612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1___boxed(lean_object* v_numParams_5613_, lean_object* v_name_5614_, lean_object* v_us_5615_, lean_object* v_ctorVal_5616_, lean_object* v_a_5617_, lean_object* v_args1_5618_, lean_object* v_x_5619_, lean_object* v___y_5620_, lean_object* v___y_5621_, lean_object* v___y_5622_, lean_object* v___y_5623_, lean_object* v___y_5624_){
_start:
{
lean_object* v_res_5625_; 
v_res_5625_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1(v_numParams_5613_, v_name_5614_, v_us_5615_, v_ctorVal_5616_, v_a_5617_, v_args1_5618_, v_x_5619_, v___y_5620_, v___y_5621_, v___y_5622_, v___y_5623_);
lean_dec(v___y_5623_);
lean_dec_ref(v___y_5622_);
lean_dec(v___y_5621_);
lean_dec_ref(v___y_5620_);
lean_dec_ref(v_x_5619_);
return v_res_5625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(lean_object* v_ctorVal_5626_, lean_object* v_a_5627_, lean_object* v_a_5628_, lean_object* v_a_5629_, lean_object* v_a_5630_){
_start:
{
lean_object* v_toConstantVal_5632_; lean_object* v_numParams_5633_; lean_object* v_name_5634_; lean_object* v_levelParams_5635_; lean_object* v_type_5636_; lean_object* v___x_5637_; lean_object* v_us_5638_; lean_object* v___x_5639_; 
v_toConstantVal_5632_ = lean_ctor_get(v_ctorVal_5626_, 0);
v_numParams_5633_ = lean_ctor_get(v_ctorVal_5626_, 3);
lean_inc(v_numParams_5633_);
v_name_5634_ = lean_ctor_get(v_toConstantVal_5632_, 0);
lean_inc(v_name_5634_);
v_levelParams_5635_ = lean_ctor_get(v_toConstantVal_5632_, 1);
v_type_5636_ = lean_ctor_get(v_toConstantVal_5632_, 2);
v___x_5637_ = lean_box(0);
lean_inc(v_levelParams_5635_);
v_us_5638_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(v_levelParams_5635_, v___x_5637_);
lean_inc_ref(v_type_5636_);
v___x_5639_ = l_Lean_Meta_elimOptParam(v_type_5636_, v_a_5629_, v_a_5630_);
if (lean_obj_tag(v___x_5639_) == 0)
{
lean_object* v_a_5640_; lean_object* v___f_5641_; uint8_t v___x_5642_; lean_object* v___x_5643_; 
v_a_5640_ = lean_ctor_get(v___x_5639_, 0);
lean_inc_n(v_a_5640_, 2);
lean_dec_ref_known(v___x_5639_, 1);
v___f_5641_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1___boxed), 12, 5);
lean_closure_set(v___f_5641_, 0, v_numParams_5633_);
lean_closure_set(v___f_5641_, 1, v_name_5634_);
lean_closure_set(v___f_5641_, 2, v_us_5638_);
lean_closure_set(v___f_5641_, 3, v_ctorVal_5626_);
lean_closure_set(v___f_5641_, 4, v_a_5640_);
v___x_5642_ = 0;
v___x_5643_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_a_5640_, v___f_5641_, v___x_5642_, v_a_5627_, v_a_5628_, v_a_5629_, v_a_5630_);
return v___x_5643_;
}
else
{
lean_object* v_a_5644_; lean_object* v___x_5646_; uint8_t v_isShared_5647_; uint8_t v_isSharedCheck_5651_; 
lean_dec(v_us_5638_);
lean_dec(v_name_5634_);
lean_dec(v_numParams_5633_);
lean_dec_ref(v_ctorVal_5626_);
v_a_5644_ = lean_ctor_get(v___x_5639_, 0);
v_isSharedCheck_5651_ = !lean_is_exclusive(v___x_5639_);
if (v_isSharedCheck_5651_ == 0)
{
v___x_5646_ = v___x_5639_;
v_isShared_5647_ = v_isSharedCheck_5651_;
goto v_resetjp_5645_;
}
else
{
lean_inc(v_a_5644_);
lean_dec(v___x_5639_);
v___x_5646_ = lean_box(0);
v_isShared_5647_ = v_isSharedCheck_5651_;
goto v_resetjp_5645_;
}
v_resetjp_5645_:
{
lean_object* v___x_5649_; 
if (v_isShared_5647_ == 0)
{
v___x_5649_ = v___x_5646_;
goto v_reusejp_5648_;
}
else
{
lean_object* v_reuseFailAlloc_5650_; 
v_reuseFailAlloc_5650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5650_, 0, v_a_5644_);
v___x_5649_ = v_reuseFailAlloc_5650_;
goto v_reusejp_5648_;
}
v_reusejp_5648_:
{
return v___x_5649_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___boxed(lean_object* v_ctorVal_5652_, lean_object* v_a_5653_, lean_object* v_a_5654_, lean_object* v_a_5655_, lean_object* v_a_5656_, lean_object* v_a_5657_){
_start:
{
lean_object* v_res_5658_; 
v_res_5658_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(v_ctorVal_5652_, v_a_5653_, v_a_5654_, v_a_5655_, v_a_5656_);
lean_dec(v_a_5656_);
lean_dec_ref(v_a_5655_);
lean_dec(v_a_5654_);
lean_dec_ref(v_a_5653_);
return v_res_5658_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1(void){
_start:
{
lean_object* v___x_5660_; lean_object* v___x_5661_; 
v___x_5660_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__0));
v___x_5661_ = l_Lean_stringToMessageData(v___x_5660_);
return v___x_5661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(lean_object* v_ctorVal_5662_, lean_object* v_a_5663_, lean_object* v_a_5664_, lean_object* v_a_5665_, lean_object* v_a_5666_){
_start:
{
lean_object* v_toConstantVal_5668_; lean_object* v_name_5669_; lean_object* v___x_5670_; lean_object* v___x_5671_; lean_object* v___x_5672_; lean_object* v___x_5673_; lean_object* v___x_5674_; lean_object* v___x_5675_; 
v_toConstantVal_5668_ = lean_ctor_get(v_ctorVal_5662_, 0);
lean_inc_ref(v_toConstantVal_5668_);
lean_dec_ref(v_ctorVal_5662_);
v_name_5669_ = lean_ctor_get(v_toConstantVal_5668_, 0);
lean_inc(v_name_5669_);
lean_dec_ref(v_toConstantVal_5668_);
v___x_5670_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1);
v___x_5671_ = l_Lean_MessageData_ofName(v_name_5669_);
v___x_5672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5672_, 0, v___x_5670_);
lean_ctor_set(v___x_5672_, 1, v___x_5671_);
v___x_5673_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_5674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5674_, 0, v___x_5672_);
lean_ctor_set(v___x_5674_, 1, v___x_5673_);
v___x_5675_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_5674_, v_a_5663_, v_a_5664_, v_a_5665_, v_a_5666_);
return v___x_5675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___boxed(lean_object* v_ctorVal_5676_, lean_object* v_a_5677_, lean_object* v_a_5678_, lean_object* v_a_5679_, lean_object* v_a_5680_, lean_object* v_a_5681_){
_start:
{
lean_object* v_res_5682_; 
v_res_5682_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5676_, v_a_5677_, v_a_5678_, v_a_5679_, v_a_5680_);
lean_dec(v_a_5680_);
lean_dec_ref(v_a_5679_);
lean_dec(v_a_5678_);
lean_dec_ref(v_a_5677_);
return v_res_5682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj(lean_object* v_00_u03b1_5683_, lean_object* v_ctorVal_5684_, lean_object* v_a_5685_, lean_object* v_a_5686_, lean_object* v_a_5687_, lean_object* v_a_5688_){
_start:
{
lean_object* v___x_5690_; 
v___x_5690_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5684_, v_a_5685_, v_a_5686_, v_a_5687_, v_a_5688_);
return v___x_5690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___boxed(lean_object* v_00_u03b1_5691_, lean_object* v_ctorVal_5692_, lean_object* v_a_5693_, lean_object* v_a_5694_, lean_object* v_a_5695_, lean_object* v_a_5696_, lean_object* v_a_5697_){
_start:
{
lean_object* v_res_5698_; 
v_res_5698_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj(v_00_u03b1_5691_, v_ctorVal_5692_, v_a_5693_, v_a_5694_, v_a_5695_, v_a_5696_);
lean_dec(v_a_5696_);
lean_dec_ref(v_a_5695_);
lean_dec(v_a_5694_);
lean_dec_ref(v_a_5693_);
return v_res_5698_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(lean_object* v_ctorVal_5704_, size_t v_sz_5705_, size_t v_i_5706_, lean_object* v_bs_5707_, lean_object* v___y_5708_, lean_object* v___y_5709_, lean_object* v___y_5710_, lean_object* v___y_5711_){
_start:
{
uint8_t v___x_5713_; 
v___x_5713_ = lean_usize_dec_lt(v_i_5706_, v_sz_5705_);
if (v___x_5713_ == 0)
{
lean_object* v___x_5714_; 
lean_dec_ref(v_ctorVal_5704_);
v___x_5714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5714_, 0, v_bs_5707_);
return v___x_5714_;
}
else
{
lean_object* v_v_5715_; lean_object* v___x_5716_; lean_object* v_bs_x27_5717_; lean_object* v_a_5719_; lean_object* v___y_5725_; lean_object* v_lhs_5736_; lean_object* v_rhs_5737_; lean_object* v___x_5739_; 
v_v_5715_ = lean_array_uget(v_bs_5707_, v_i_5706_);
v___x_5716_ = lean_unsigned_to_nat(0u);
v_bs_x27_5717_ = lean_array_uset(v_bs_5707_, v_i_5706_, v___x_5716_);
lean_inc(v___y_5711_);
lean_inc_ref(v___y_5710_);
lean_inc(v___y_5709_);
lean_inc_ref(v___y_5708_);
v___x_5739_ = lean_infer_type(v_v_5715_, v___y_5708_, v___y_5709_, v___y_5710_, v___y_5711_);
if (lean_obj_tag(v___x_5739_) == 0)
{
lean_object* v_a_5740_; lean_object* v___x_5741_; 
v_a_5740_ = lean_ctor_get(v___x_5739_, 0);
lean_inc(v_a_5740_);
lean_dec_ref_known(v___x_5739_, 1);
v___x_5741_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_5740_, v___y_5709_);
if (lean_obj_tag(v___x_5741_) == 0)
{
lean_object* v_a_5742_; lean_object* v___x_5743_; uint8_t v___x_5744_; 
v_a_5742_ = lean_ctor_get(v___x_5741_, 0);
lean_inc(v_a_5742_);
lean_dec_ref_known(v___x_5741_, 1);
v___x_5743_ = l_Lean_Expr_cleanupAnnotations(v_a_5742_);
lean_dec(v_a_5742_);
v___x_5744_ = l_Lean_Expr_isApp(v___x_5743_);
if (v___x_5744_ == 0)
{
lean_object* v___x_5745_; 
lean_dec_ref(v___x_5743_);
lean_inc_ref(v_ctorVal_5704_);
v___x_5745_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5704_, v___y_5708_, v___y_5709_, v___y_5710_, v___y_5711_);
v___y_5725_ = v___x_5745_;
goto v___jp_5724_;
}
else
{
lean_object* v___x_5746_; uint8_t v___x_5747_; 
v___x_5746_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5743_);
v___x_5747_ = l_Lean_Expr_isApp(v___x_5746_);
if (v___x_5747_ == 0)
{
lean_object* v___x_5748_; 
lean_dec_ref(v___x_5746_);
lean_dec_ref(v___x_5743_);
lean_inc_ref(v_ctorVal_5704_);
v___x_5748_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5704_, v___y_5708_, v___y_5709_, v___y_5710_, v___y_5711_);
v___y_5725_ = v___x_5748_;
goto v___jp_5724_;
}
else
{
lean_object* v___x_5749_; uint8_t v___x_5750_; 
v___x_5749_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5746_);
v___x_5750_ = l_Lean_Expr_isApp(v___x_5749_);
if (v___x_5750_ == 0)
{
lean_object* v___x_5751_; 
lean_dec_ref(v___x_5749_);
lean_dec_ref(v___x_5746_);
lean_dec_ref(v___x_5743_);
lean_inc_ref(v_ctorVal_5704_);
v___x_5751_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5704_, v___y_5708_, v___y_5709_, v___y_5710_, v___y_5711_);
v___y_5725_ = v___x_5751_;
goto v___jp_5724_;
}
else
{
lean_object* v_arg_5752_; lean_object* v___x_5753_; lean_object* v___x_5754_; uint8_t v___x_5755_; 
v_arg_5752_ = lean_ctor_get(v___x_5743_, 1);
lean_inc_ref(v_arg_5752_);
lean_dec_ref(v___x_5743_);
v___x_5753_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5749_);
v___x_5754_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__0));
v___x_5755_ = l_Lean_Expr_isConstOf(v___x_5753_, v___x_5754_);
if (v___x_5755_ == 0)
{
uint8_t v___x_5756_; 
lean_dec_ref(v___x_5746_);
v___x_5756_ = l_Lean_Expr_isApp(v___x_5753_);
if (v___x_5756_ == 0)
{
lean_object* v___x_5757_; 
lean_dec_ref(v___x_5753_);
lean_dec_ref(v_arg_5752_);
lean_dec_ref(v___x_5749_);
lean_inc_ref(v_ctorVal_5704_);
v___x_5757_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5704_, v___y_5708_, v___y_5709_, v___y_5710_, v___y_5711_);
v___y_5725_ = v___x_5757_;
goto v___jp_5724_;
}
else
{
lean_object* v___x_5758_; lean_object* v___x_5759_; uint8_t v___x_5760_; 
v___x_5758_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5753_);
lean_dec_ref(v___x_5753_);
v___x_5759_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__2));
v___x_5760_ = l_Lean_Expr_isConstOf(v___x_5758_, v___x_5759_);
lean_dec_ref(v___x_5758_);
if (v___x_5760_ == 0)
{
lean_object* v___x_5761_; 
lean_dec_ref(v_arg_5752_);
lean_dec_ref(v___x_5749_);
lean_inc_ref(v_ctorVal_5704_);
v___x_5761_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5704_, v___y_5708_, v___y_5709_, v___y_5710_, v___y_5711_);
v___y_5725_ = v___x_5761_;
goto v___jp_5724_;
}
else
{
lean_object* v_arg_5762_; 
v_arg_5762_ = lean_ctor_get(v___x_5749_, 1);
lean_inc_ref(v_arg_5762_);
lean_dec_ref(v___x_5749_);
v_lhs_5736_ = v_arg_5762_;
v_rhs_5737_ = v_arg_5752_;
goto v___jp_5735_;
}
}
}
else
{
lean_object* v_arg_5763_; 
lean_dec_ref(v___x_5753_);
lean_dec_ref(v___x_5749_);
v_arg_5763_ = lean_ctor_get(v___x_5746_, 1);
lean_inc_ref(v_arg_5763_);
lean_dec_ref(v___x_5746_);
v_lhs_5736_ = v_arg_5763_;
v_rhs_5737_ = v_arg_5752_;
goto v___jp_5735_;
}
}
}
}
}
else
{
lean_object* v_a_5764_; lean_object* v___x_5766_; uint8_t v_isShared_5767_; uint8_t v_isSharedCheck_5771_; 
lean_dec_ref(v_bs_x27_5717_);
lean_dec_ref(v_ctorVal_5704_);
v_a_5764_ = lean_ctor_get(v___x_5741_, 0);
v_isSharedCheck_5771_ = !lean_is_exclusive(v___x_5741_);
if (v_isSharedCheck_5771_ == 0)
{
v___x_5766_ = v___x_5741_;
v_isShared_5767_ = v_isSharedCheck_5771_;
goto v_resetjp_5765_;
}
else
{
lean_inc(v_a_5764_);
lean_dec(v___x_5741_);
v___x_5766_ = lean_box(0);
v_isShared_5767_ = v_isSharedCheck_5771_;
goto v_resetjp_5765_;
}
v_resetjp_5765_:
{
lean_object* v___x_5769_; 
if (v_isShared_5767_ == 0)
{
v___x_5769_ = v___x_5766_;
goto v_reusejp_5768_;
}
else
{
lean_object* v_reuseFailAlloc_5770_; 
v_reuseFailAlloc_5770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5770_, 0, v_a_5764_);
v___x_5769_ = v_reuseFailAlloc_5770_;
goto v_reusejp_5768_;
}
v_reusejp_5768_:
{
return v___x_5769_;
}
}
}
}
else
{
lean_object* v_a_5772_; lean_object* v___x_5774_; uint8_t v_isShared_5775_; uint8_t v_isSharedCheck_5779_; 
lean_dec_ref(v_bs_x27_5717_);
lean_dec_ref(v_ctorVal_5704_);
v_a_5772_ = lean_ctor_get(v___x_5739_, 0);
v_isSharedCheck_5779_ = !lean_is_exclusive(v___x_5739_);
if (v_isSharedCheck_5779_ == 0)
{
v___x_5774_ = v___x_5739_;
v_isShared_5775_ = v_isSharedCheck_5779_;
goto v_resetjp_5773_;
}
else
{
lean_inc(v_a_5772_);
lean_dec(v___x_5739_);
v___x_5774_ = lean_box(0);
v_isShared_5775_ = v_isSharedCheck_5779_;
goto v_resetjp_5773_;
}
v_resetjp_5773_:
{
lean_object* v___x_5777_; 
if (v_isShared_5775_ == 0)
{
v___x_5777_ = v___x_5774_;
goto v_reusejp_5776_;
}
else
{
lean_object* v_reuseFailAlloc_5778_; 
v_reuseFailAlloc_5778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5778_, 0, v_a_5772_);
v___x_5777_ = v_reuseFailAlloc_5778_;
goto v_reusejp_5776_;
}
v_reusejp_5776_:
{
return v___x_5777_;
}
}
}
v___jp_5718_:
{
size_t v___x_5720_; size_t v___x_5721_; lean_object* v___x_5722_; 
v___x_5720_ = ((size_t)1ULL);
v___x_5721_ = lean_usize_add(v_i_5706_, v___x_5720_);
v___x_5722_ = lean_array_uset(v_bs_x27_5717_, v_i_5706_, v_a_5719_);
v_i_5706_ = v___x_5721_;
v_bs_5707_ = v___x_5722_;
goto _start;
}
v___jp_5724_:
{
if (lean_obj_tag(v___y_5725_) == 0)
{
lean_object* v_a_5726_; 
v_a_5726_ = lean_ctor_get(v___y_5725_, 0);
lean_inc(v_a_5726_);
lean_dec_ref_known(v___y_5725_, 1);
v_a_5719_ = v_a_5726_;
goto v___jp_5718_;
}
else
{
lean_object* v_a_5727_; lean_object* v___x_5729_; uint8_t v_isShared_5730_; uint8_t v_isSharedCheck_5734_; 
lean_dec_ref(v_bs_x27_5717_);
lean_dec_ref(v_ctorVal_5704_);
v_a_5727_ = lean_ctor_get(v___y_5725_, 0);
v_isSharedCheck_5734_ = !lean_is_exclusive(v___y_5725_);
if (v_isSharedCheck_5734_ == 0)
{
v___x_5729_ = v___y_5725_;
v_isShared_5730_ = v_isSharedCheck_5734_;
goto v_resetjp_5728_;
}
else
{
lean_inc(v_a_5727_);
lean_dec(v___y_5725_);
v___x_5729_ = lean_box(0);
v_isShared_5730_ = v_isSharedCheck_5734_;
goto v_resetjp_5728_;
}
v_resetjp_5728_:
{
lean_object* v___x_5732_; 
if (v_isShared_5730_ == 0)
{
v___x_5732_ = v___x_5729_;
goto v_reusejp_5731_;
}
else
{
lean_object* v_reuseFailAlloc_5733_; 
v_reuseFailAlloc_5733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5733_, 0, v_a_5727_);
v___x_5732_ = v_reuseFailAlloc_5733_;
goto v_reusejp_5731_;
}
v_reusejp_5731_:
{
return v___x_5732_;
}
}
}
}
v___jp_5735_:
{
lean_object* v___x_5738_; 
v___x_5738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5738_, 0, v_lhs_5736_);
lean_ctor_set(v___x_5738_, 1, v_rhs_5737_);
v_a_5719_ = v___x_5738_;
goto v___jp_5718_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___boxed(lean_object* v_ctorVal_5780_, lean_object* v_sz_5781_, lean_object* v_i_5782_, lean_object* v_bs_5783_, lean_object* v___y_5784_, lean_object* v___y_5785_, lean_object* v___y_5786_, lean_object* v___y_5787_, lean_object* v___y_5788_){
_start:
{
size_t v_sz_boxed_5789_; size_t v_i_boxed_5790_; lean_object* v_res_5791_; 
v_sz_boxed_5789_ = lean_unbox_usize(v_sz_5781_);
lean_dec(v_sz_5781_);
v_i_boxed_5790_ = lean_unbox_usize(v_i_5782_);
lean_dec(v_i_5782_);
v_res_5791_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(v_ctorVal_5780_, v_sz_boxed_5789_, v_i_boxed_5790_, v_bs_5783_, v___y_5784_, v___y_5785_, v___y_5786_, v___y_5787_);
lean_dec(v___y_5787_);
lean_dec_ref(v___y_5786_);
lean_dec(v___y_5785_);
lean_dec_ref(v___y_5784_);
return v_res_5791_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5793_; lean_object* v___x_5794_; 
v___x_5793_ = lean_unsigned_to_nat(0u);
v___x_5794_ = l_Lean_Level_ofNat(v___x_5793_);
return v___x_5794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0(lean_object* v_ctorVal_5795_, lean_object* v_us_5796_, lean_object* v_numIndices_5797_, lean_object* v_xs_5798_, lean_object* v_type_5799_, lean_object* v___y_5800_, lean_object* v___y_5801_, lean_object* v___y_5802_, lean_object* v___y_5803_){
_start:
{
lean_object* v_toConstantVal_5805_; lean_object* v_induct_5806_; lean_object* v_numParams_5807_; lean_object* v___x_5808_; lean_object* v_noConfusionName_5809_; lean_object* v___x_5810_; lean_object* v___x_5811_; lean_object* v___x_5812_; lean_object* v_noConfusion_5813_; lean_object* v_noConfusion_5814_; lean_object* v_lower_5816_; lean_object* v_upper_5817_; lean_object* v___x_5924_; lean_object* v___x_5925_; lean_object* v___x_5926_; lean_object* v___x_5927_; lean_object* v_n_5928_; uint8_t v___x_5929_; 
v_toConstantVal_5805_ = lean_ctor_get(v_ctorVal_5795_, 0);
v_induct_5806_ = lean_ctor_get(v_ctorVal_5795_, 1);
v_numParams_5807_ = lean_ctor_get(v_ctorVal_5795_, 3);
v___x_5808_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__0));
lean_inc(v_induct_5806_);
v_noConfusionName_5809_ = l_Lean_Name_str___override(v_induct_5806_, v___x_5808_);
v___x_5810_ = lean_unsigned_to_nat(0u);
v___x_5811_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1);
v___x_5812_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5812_, 0, v___x_5811_);
lean_ctor_set(v___x_5812_, 1, v_us_5796_);
v_noConfusion_5813_ = l_Lean_mkConst(v_noConfusionName_5809_, v___x_5812_);
v_noConfusion_5814_ = l_Lean_Expr_app___override(v_noConfusion_5813_, v_type_5799_);
v___x_5924_ = lean_array_get_size(v_xs_5798_);
v___x_5925_ = lean_nat_sub(v___x_5924_, v_numParams_5807_);
v___x_5926_ = lean_nat_sub(v___x_5925_, v_numIndices_5797_);
lean_dec(v___x_5925_);
v___x_5927_ = lean_unsigned_to_nat(1u);
v_n_5928_ = lean_nat_sub(v___x_5926_, v___x_5927_);
lean_dec(v___x_5926_);
v___x_5929_ = lean_nat_dec_le(v_n_5928_, v___x_5810_);
if (v___x_5929_ == 0)
{
v_lower_5816_ = v_n_5928_;
v_upper_5817_ = v___x_5924_;
goto v___jp_5815_;
}
else
{
lean_dec(v_n_5928_);
v_lower_5816_ = v___x_5810_;
v_upper_5817_ = v___x_5924_;
goto v___jp_5815_;
}
v___jp_5815_:
{
lean_object* v___x_5818_; lean_object* v___x_5819_; lean_object* v_eqs_5820_; size_t v_sz_5821_; size_t v___x_5822_; lean_object* v___x_5823_; 
lean_inc_ref(v_xs_5798_);
v___x_5818_ = l_Array_toSubarray___redArg(v_xs_5798_, v_lower_5816_, v_upper_5817_);
v___x_5819_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v_eqs_5820_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(v___x_5818_, v___x_5819_);
v_sz_5821_ = lean_array_size(v_eqs_5820_);
v___x_5822_ = ((size_t)0ULL);
lean_inc_ref(v_eqs_5820_);
lean_inc_ref(v_ctorVal_5795_);
v___x_5823_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(v_ctorVal_5795_, v_sz_5821_, v___x_5822_, v_eqs_5820_, v___y_5800_, v___y_5801_, v___y_5802_, v___y_5803_);
if (lean_obj_tag(v___x_5823_) == 0)
{
lean_object* v_a_5824_; lean_object* v___x_5825_; lean_object* v_fst_5826_; lean_object* v_snd_5827_; lean_object* v___x_5828_; lean_object* v___x_5829_; lean_object* v___x_5830_; lean_object* v___x_5831_; 
v_a_5824_ = lean_ctor_get(v___x_5823_, 0);
lean_inc(v_a_5824_);
lean_dec_ref_known(v___x_5823_, 1);
v___x_5825_ = l_Array_unzip___redArg(v_a_5824_);
lean_dec(v_a_5824_);
v_fst_5826_ = lean_ctor_get(v___x_5825_, 0);
lean_inc(v_fst_5826_);
v_snd_5827_ = lean_ctor_get(v___x_5825_, 1);
lean_inc(v_snd_5827_);
lean_dec_ref(v___x_5825_);
v___x_5828_ = l_Lean_mkAppN(v_noConfusion_5814_, v_fst_5826_);
lean_dec(v_fst_5826_);
v___x_5829_ = l_Lean_mkAppN(v___x_5828_, v_snd_5827_);
lean_dec(v_snd_5827_);
v___x_5830_ = l_Lean_mkAppN(v___x_5829_, v_eqs_5820_);
lean_dec_ref(v_eqs_5820_);
lean_inc(v___y_5803_);
lean_inc_ref(v___y_5802_);
lean_inc(v___y_5801_);
lean_inc_ref(v___y_5800_);
lean_inc_ref(v___x_5830_);
v___x_5831_ = lean_infer_type(v___x_5830_, v___y_5800_, v___y_5801_, v___y_5802_, v___y_5803_);
if (lean_obj_tag(v___x_5831_) == 0)
{
lean_object* v_a_5832_; lean_object* v___x_5833_; 
v_a_5832_ = lean_ctor_get(v___x_5831_, 0);
lean_inc(v_a_5832_);
lean_dec_ref_known(v___x_5831_, 1);
lean_inc(v___y_5803_);
lean_inc_ref(v___y_5802_);
lean_inc(v___y_5801_);
lean_inc_ref(v___y_5800_);
v___x_5833_ = lean_whnf(v_a_5832_, v___y_5800_, v___y_5801_, v___y_5802_, v___y_5803_);
if (lean_obj_tag(v___x_5833_) == 0)
{
lean_object* v_a_5834_; 
v_a_5834_ = lean_ctor_get(v___x_5833_, 0);
lean_inc(v_a_5834_);
lean_dec_ref_known(v___x_5833_, 1);
if (lean_obj_tag(v_a_5834_) == 7)
{
lean_object* v_binderType_5835_; lean_object* v___x_5836_; lean_object* v___x_5837_; 
lean_inc_ref(v_toConstantVal_5805_);
lean_dec_ref(v_ctorVal_5795_);
v_binderType_5835_ = lean_ctor_get(v_a_5834_, 1);
lean_inc_ref(v_binderType_5835_);
lean_dec_ref_known(v_a_5834_, 3);
v___x_5836_ = lean_box(0);
v___x_5837_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_binderType_5835_, v___x_5836_, v___y_5800_, v___y_5801_, v___y_5802_, v___y_5803_);
if (lean_obj_tag(v___x_5837_) == 0)
{
lean_object* v_a_5838_; lean_object* v___x_5839_; lean_object* v___x_5840_; lean_object* v___x_5841_; 
v_a_5838_ = lean_ctor_get(v___x_5837_, 0);
lean_inc_n(v_a_5838_, 2);
lean_dec_ref_known(v___x_5837_, 1);
v___x_5839_ = l_Lean_Expr_app___override(v___x_5830_, v_a_5838_);
v___x_5840_ = l_Lean_Expr_mvarId_x21(v_a_5838_);
lean_dec(v_a_5838_);
v___x_5841_ = l_Lean_MVarId_intros(v___x_5840_, v___y_5800_, v___y_5801_, v___y_5802_, v___y_5803_);
if (lean_obj_tag(v___x_5841_) == 0)
{
lean_object* v_a_5842_; lean_object* v_snd_5843_; lean_object* v_name_5844_; lean_object* v___x_5845_; 
v_a_5842_ = lean_ctor_get(v___x_5841_, 0);
lean_inc(v_a_5842_);
lean_dec_ref_known(v___x_5841_, 1);
v_snd_5843_ = lean_ctor_get(v_a_5842_, 1);
lean_inc(v_snd_5843_);
lean_dec(v_a_5842_);
v_name_5844_ = lean_ctor_get(v_toConstantVal_5805_, 0);
lean_inc(v_name_5844_);
lean_dec_ref(v_toConstantVal_5805_);
v___x_5845_ = l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(v_snd_5843_, v_name_5844_, v___y_5800_, v___y_5801_, v___y_5802_, v___y_5803_);
if (lean_obj_tag(v___x_5845_) == 0)
{
lean_object* v___x_5846_; lean_object* v_a_5847_; lean_object* v___x_5849_; uint8_t v_isShared_5850_; uint8_t v_isSharedCheck_5874_; 
lean_dec_ref_known(v___x_5845_, 1);
v___x_5846_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v___x_5839_, v___y_5801_);
v_a_5847_ = lean_ctor_get(v___x_5846_, 0);
v_isSharedCheck_5874_ = !lean_is_exclusive(v___x_5846_);
if (v_isSharedCheck_5874_ == 0)
{
v___x_5849_ = v___x_5846_;
v_isShared_5850_ = v_isSharedCheck_5874_;
goto v_resetjp_5848_;
}
else
{
lean_inc(v_a_5847_);
lean_dec(v___x_5846_);
v___x_5849_ = lean_box(0);
v_isShared_5850_ = v_isSharedCheck_5874_;
goto v_resetjp_5848_;
}
v_resetjp_5848_:
{
uint8_t v___x_5851_; uint8_t v___x_5852_; uint8_t v___x_5853_; lean_object* v___x_5854_; 
v___x_5851_ = 0;
v___x_5852_ = 1;
v___x_5853_ = 1;
v___x_5854_ = l_Lean_Meta_mkLambdaFVars(v_xs_5798_, v_a_5847_, v___x_5851_, v___x_5852_, v___x_5851_, v___x_5852_, v___x_5853_, v___y_5800_, v___y_5801_, v___y_5802_, v___y_5803_);
lean_dec_ref(v_xs_5798_);
if (lean_obj_tag(v___x_5854_) == 0)
{
lean_object* v_a_5855_; lean_object* v___x_5857_; uint8_t v_isShared_5858_; uint8_t v_isSharedCheck_5865_; 
v_a_5855_ = lean_ctor_get(v___x_5854_, 0);
v_isSharedCheck_5865_ = !lean_is_exclusive(v___x_5854_);
if (v_isSharedCheck_5865_ == 0)
{
v___x_5857_ = v___x_5854_;
v_isShared_5858_ = v_isSharedCheck_5865_;
goto v_resetjp_5856_;
}
else
{
lean_inc(v_a_5855_);
lean_dec(v___x_5854_);
v___x_5857_ = lean_box(0);
v_isShared_5858_ = v_isSharedCheck_5865_;
goto v_resetjp_5856_;
}
v_resetjp_5856_:
{
lean_object* v___x_5860_; 
if (v_isShared_5850_ == 0)
{
lean_ctor_set_tag(v___x_5849_, 1);
lean_ctor_set(v___x_5849_, 0, v_a_5855_);
v___x_5860_ = v___x_5849_;
goto v_reusejp_5859_;
}
else
{
lean_object* v_reuseFailAlloc_5864_; 
v_reuseFailAlloc_5864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5864_, 0, v_a_5855_);
v___x_5860_ = v_reuseFailAlloc_5864_;
goto v_reusejp_5859_;
}
v_reusejp_5859_:
{
lean_object* v___x_5862_; 
if (v_isShared_5858_ == 0)
{
lean_ctor_set(v___x_5857_, 0, v___x_5860_);
v___x_5862_ = v___x_5857_;
goto v_reusejp_5861_;
}
else
{
lean_object* v_reuseFailAlloc_5863_; 
v_reuseFailAlloc_5863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5863_, 0, v___x_5860_);
v___x_5862_ = v_reuseFailAlloc_5863_;
goto v_reusejp_5861_;
}
v_reusejp_5861_:
{
return v___x_5862_;
}
}
}
}
else
{
lean_object* v_a_5866_; lean_object* v___x_5868_; uint8_t v_isShared_5869_; uint8_t v_isSharedCheck_5873_; 
lean_del_object(v___x_5849_);
v_a_5866_ = lean_ctor_get(v___x_5854_, 0);
v_isSharedCheck_5873_ = !lean_is_exclusive(v___x_5854_);
if (v_isSharedCheck_5873_ == 0)
{
v___x_5868_ = v___x_5854_;
v_isShared_5869_ = v_isSharedCheck_5873_;
goto v_resetjp_5867_;
}
else
{
lean_inc(v_a_5866_);
lean_dec(v___x_5854_);
v___x_5868_ = lean_box(0);
v_isShared_5869_ = v_isSharedCheck_5873_;
goto v_resetjp_5867_;
}
v_resetjp_5867_:
{
lean_object* v___x_5871_; 
if (v_isShared_5869_ == 0)
{
v___x_5871_ = v___x_5868_;
goto v_reusejp_5870_;
}
else
{
lean_object* v_reuseFailAlloc_5872_; 
v_reuseFailAlloc_5872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5872_, 0, v_a_5866_);
v___x_5871_ = v_reuseFailAlloc_5872_;
goto v_reusejp_5870_;
}
v_reusejp_5870_:
{
return v___x_5871_;
}
}
}
}
}
else
{
lean_object* v_a_5875_; lean_object* v___x_5877_; uint8_t v_isShared_5878_; uint8_t v_isSharedCheck_5882_; 
lean_dec_ref(v___x_5839_);
lean_dec_ref(v_xs_5798_);
v_a_5875_ = lean_ctor_get(v___x_5845_, 0);
v_isSharedCheck_5882_ = !lean_is_exclusive(v___x_5845_);
if (v_isSharedCheck_5882_ == 0)
{
v___x_5877_ = v___x_5845_;
v_isShared_5878_ = v_isSharedCheck_5882_;
goto v_resetjp_5876_;
}
else
{
lean_inc(v_a_5875_);
lean_dec(v___x_5845_);
v___x_5877_ = lean_box(0);
v_isShared_5878_ = v_isSharedCheck_5882_;
goto v_resetjp_5876_;
}
v_resetjp_5876_:
{
lean_object* v___x_5880_; 
if (v_isShared_5878_ == 0)
{
v___x_5880_ = v___x_5877_;
goto v_reusejp_5879_;
}
else
{
lean_object* v_reuseFailAlloc_5881_; 
v_reuseFailAlloc_5881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5881_, 0, v_a_5875_);
v___x_5880_ = v_reuseFailAlloc_5881_;
goto v_reusejp_5879_;
}
v_reusejp_5879_:
{
return v___x_5880_;
}
}
}
}
else
{
lean_object* v_a_5883_; lean_object* v___x_5885_; uint8_t v_isShared_5886_; uint8_t v_isSharedCheck_5890_; 
lean_dec_ref(v___x_5839_);
lean_dec_ref(v_toConstantVal_5805_);
lean_dec_ref(v_xs_5798_);
v_a_5883_ = lean_ctor_get(v___x_5841_, 0);
v_isSharedCheck_5890_ = !lean_is_exclusive(v___x_5841_);
if (v_isSharedCheck_5890_ == 0)
{
v___x_5885_ = v___x_5841_;
v_isShared_5886_ = v_isSharedCheck_5890_;
goto v_resetjp_5884_;
}
else
{
lean_inc(v_a_5883_);
lean_dec(v___x_5841_);
v___x_5885_ = lean_box(0);
v_isShared_5886_ = v_isSharedCheck_5890_;
goto v_resetjp_5884_;
}
v_resetjp_5884_:
{
lean_object* v___x_5888_; 
if (v_isShared_5886_ == 0)
{
v___x_5888_ = v___x_5885_;
goto v_reusejp_5887_;
}
else
{
lean_object* v_reuseFailAlloc_5889_; 
v_reuseFailAlloc_5889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5889_, 0, v_a_5883_);
v___x_5888_ = v_reuseFailAlloc_5889_;
goto v_reusejp_5887_;
}
v_reusejp_5887_:
{
return v___x_5888_;
}
}
}
}
else
{
lean_object* v_a_5891_; lean_object* v___x_5893_; uint8_t v_isShared_5894_; uint8_t v_isSharedCheck_5898_; 
lean_dec_ref(v___x_5830_);
lean_dec_ref(v_toConstantVal_5805_);
lean_dec_ref(v_xs_5798_);
v_a_5891_ = lean_ctor_get(v___x_5837_, 0);
v_isSharedCheck_5898_ = !lean_is_exclusive(v___x_5837_);
if (v_isSharedCheck_5898_ == 0)
{
v___x_5893_ = v___x_5837_;
v_isShared_5894_ = v_isSharedCheck_5898_;
goto v_resetjp_5892_;
}
else
{
lean_inc(v_a_5891_);
lean_dec(v___x_5837_);
v___x_5893_ = lean_box(0);
v_isShared_5894_ = v_isSharedCheck_5898_;
goto v_resetjp_5892_;
}
v_resetjp_5892_:
{
lean_object* v___x_5896_; 
if (v_isShared_5894_ == 0)
{
v___x_5896_ = v___x_5893_;
goto v_reusejp_5895_;
}
else
{
lean_object* v_reuseFailAlloc_5897_; 
v_reuseFailAlloc_5897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5897_, 0, v_a_5891_);
v___x_5896_ = v_reuseFailAlloc_5897_;
goto v_reusejp_5895_;
}
v_reusejp_5895_:
{
return v___x_5896_;
}
}
}
}
else
{
lean_object* v___x_5899_; 
lean_dec(v_a_5834_);
lean_dec_ref(v___x_5830_);
lean_dec_ref(v_xs_5798_);
v___x_5899_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5795_, v___y_5800_, v___y_5801_, v___y_5802_, v___y_5803_);
return v___x_5899_;
}
}
else
{
lean_object* v_a_5900_; lean_object* v___x_5902_; uint8_t v_isShared_5903_; uint8_t v_isSharedCheck_5907_; 
lean_dec_ref(v___x_5830_);
lean_dec_ref(v_xs_5798_);
lean_dec_ref(v_ctorVal_5795_);
v_a_5900_ = lean_ctor_get(v___x_5833_, 0);
v_isSharedCheck_5907_ = !lean_is_exclusive(v___x_5833_);
if (v_isSharedCheck_5907_ == 0)
{
v___x_5902_ = v___x_5833_;
v_isShared_5903_ = v_isSharedCheck_5907_;
goto v_resetjp_5901_;
}
else
{
lean_inc(v_a_5900_);
lean_dec(v___x_5833_);
v___x_5902_ = lean_box(0);
v_isShared_5903_ = v_isSharedCheck_5907_;
goto v_resetjp_5901_;
}
v_resetjp_5901_:
{
lean_object* v___x_5905_; 
if (v_isShared_5903_ == 0)
{
v___x_5905_ = v___x_5902_;
goto v_reusejp_5904_;
}
else
{
lean_object* v_reuseFailAlloc_5906_; 
v_reuseFailAlloc_5906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5906_, 0, v_a_5900_);
v___x_5905_ = v_reuseFailAlloc_5906_;
goto v_reusejp_5904_;
}
v_reusejp_5904_:
{
return v___x_5905_;
}
}
}
}
else
{
lean_object* v_a_5908_; lean_object* v___x_5910_; uint8_t v_isShared_5911_; uint8_t v_isSharedCheck_5915_; 
lean_dec_ref(v___x_5830_);
lean_dec_ref(v_xs_5798_);
lean_dec_ref(v_ctorVal_5795_);
v_a_5908_ = lean_ctor_get(v___x_5831_, 0);
v_isSharedCheck_5915_ = !lean_is_exclusive(v___x_5831_);
if (v_isSharedCheck_5915_ == 0)
{
v___x_5910_ = v___x_5831_;
v_isShared_5911_ = v_isSharedCheck_5915_;
goto v_resetjp_5909_;
}
else
{
lean_inc(v_a_5908_);
lean_dec(v___x_5831_);
v___x_5910_ = lean_box(0);
v_isShared_5911_ = v_isSharedCheck_5915_;
goto v_resetjp_5909_;
}
v_resetjp_5909_:
{
lean_object* v___x_5913_; 
if (v_isShared_5911_ == 0)
{
v___x_5913_ = v___x_5910_;
goto v_reusejp_5912_;
}
else
{
lean_object* v_reuseFailAlloc_5914_; 
v_reuseFailAlloc_5914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5914_, 0, v_a_5908_);
v___x_5913_ = v_reuseFailAlloc_5914_;
goto v_reusejp_5912_;
}
v_reusejp_5912_:
{
return v___x_5913_;
}
}
}
}
else
{
lean_object* v_a_5916_; lean_object* v___x_5918_; uint8_t v_isShared_5919_; uint8_t v_isSharedCheck_5923_; 
lean_dec_ref(v_eqs_5820_);
lean_dec_ref(v_noConfusion_5814_);
lean_dec_ref(v_xs_5798_);
lean_dec_ref(v_ctorVal_5795_);
v_a_5916_ = lean_ctor_get(v___x_5823_, 0);
v_isSharedCheck_5923_ = !lean_is_exclusive(v___x_5823_);
if (v_isSharedCheck_5923_ == 0)
{
v___x_5918_ = v___x_5823_;
v_isShared_5919_ = v_isSharedCheck_5923_;
goto v_resetjp_5917_;
}
else
{
lean_inc(v_a_5916_);
lean_dec(v___x_5823_);
v___x_5918_ = lean_box(0);
v_isShared_5919_ = v_isSharedCheck_5923_;
goto v_resetjp_5917_;
}
v_resetjp_5917_:
{
lean_object* v___x_5921_; 
if (v_isShared_5919_ == 0)
{
v___x_5921_ = v___x_5918_;
goto v_reusejp_5920_;
}
else
{
lean_object* v_reuseFailAlloc_5922_; 
v_reuseFailAlloc_5922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5922_, 0, v_a_5916_);
v___x_5921_ = v_reuseFailAlloc_5922_;
goto v_reusejp_5920_;
}
v_reusejp_5920_:
{
return v___x_5921_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___boxed(lean_object* v_ctorVal_5930_, lean_object* v_us_5931_, lean_object* v_numIndices_5932_, lean_object* v_xs_5933_, lean_object* v_type_5934_, lean_object* v___y_5935_, lean_object* v___y_5936_, lean_object* v___y_5937_, lean_object* v___y_5938_, lean_object* v___y_5939_){
_start:
{
lean_object* v_res_5940_; 
v_res_5940_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0(v_ctorVal_5930_, v_us_5931_, v_numIndices_5932_, v_xs_5933_, v_type_5934_, v___y_5935_, v___y_5936_, v___y_5937_, v___y_5938_);
lean_dec(v___y_5938_);
lean_dec_ref(v___y_5937_);
lean_dec(v___y_5936_);
lean_dec_ref(v___y_5935_);
lean_dec(v_numIndices_5932_);
return v_res_5940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(lean_object* v_ctorVal_5941_, lean_object* v_typeInfo_5942_, lean_object* v_a_5943_, lean_object* v_a_5944_, lean_object* v_a_5945_, lean_object* v_a_5946_){
_start:
{
lean_object* v_thmType_5948_; lean_object* v_us_5949_; lean_object* v_numIndices_5950_; lean_object* v___f_5951_; uint8_t v___x_5952_; lean_object* v___x_5953_; 
v_thmType_5948_ = lean_ctor_get(v_typeInfo_5942_, 0);
lean_inc_ref(v_thmType_5948_);
v_us_5949_ = lean_ctor_get(v_typeInfo_5942_, 1);
lean_inc(v_us_5949_);
v_numIndices_5950_ = lean_ctor_get(v_typeInfo_5942_, 2);
lean_inc(v_numIndices_5950_);
lean_dec_ref(v_typeInfo_5942_);
v___f_5951_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___boxed), 10, 3);
lean_closure_set(v___f_5951_, 0, v_ctorVal_5941_);
lean_closure_set(v___f_5951_, 1, v_us_5949_);
lean_closure_set(v___f_5951_, 2, v_numIndices_5950_);
v___x_5952_ = 0;
v___x_5953_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_thmType_5948_, v___f_5951_, v___x_5952_, v___x_5952_, v_a_5943_, v_a_5944_, v_a_5945_, v_a_5946_);
return v___x_5953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___boxed(lean_object* v_ctorVal_5954_, lean_object* v_typeInfo_5955_, lean_object* v_a_5956_, lean_object* v_a_5957_, lean_object* v_a_5958_, lean_object* v_a_5959_, lean_object* v_a_5960_){
_start:
{
lean_object* v_res_5961_; 
v_res_5961_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(v_ctorVal_5954_, v_typeInfo_5955_, v_a_5956_, v_a_5957_, v_a_5958_, v_a_5959_);
lean_dec(v_a_5959_);
lean_dec_ref(v_a_5958_);
lean_dec(v_a_5957_);
lean_dec_ref(v_a_5956_);
return v_res_5961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHInjectiveTheoremNameFor(lean_object* v_ctorName_5964_){
_start:
{
lean_object* v___x_5965_; lean_object* v___x_5966_; 
v___x_5965_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0));
v___x_5966_ = l_Lean_Name_str___override(v_ctorName_5964_, v___x_5965_);
return v___x_5966_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(lean_object* v_thmName_5967_, lean_object* v_ctorVal_5968_, lean_object* v_a_5969_, lean_object* v_a_5970_, lean_object* v_a_5971_, lean_object* v_a_5972_){
_start:
{
lean_object* v___x_5974_; 
lean_inc_ref(v_ctorVal_5968_);
v___x_5974_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(v_ctorVal_5968_, v_a_5969_, v_a_5970_, v_a_5971_, v_a_5972_);
if (lean_obj_tag(v___x_5974_) == 0)
{
lean_object* v_a_5975_; lean_object* v___x_5977_; uint8_t v_isShared_5978_; uint8_t v_isSharedCheck_6036_; 
v_a_5975_ = lean_ctor_get(v___x_5974_, 0);
v_isSharedCheck_6036_ = !lean_is_exclusive(v___x_5974_);
if (v_isSharedCheck_6036_ == 0)
{
v___x_5977_ = v___x_5974_;
v_isShared_5978_ = v_isSharedCheck_6036_;
goto v_resetjp_5976_;
}
else
{
lean_inc(v_a_5975_);
lean_dec(v___x_5974_);
v___x_5977_ = lean_box(0);
v_isShared_5978_ = v_isSharedCheck_6036_;
goto v_resetjp_5976_;
}
v_resetjp_5976_:
{
if (lean_obj_tag(v_a_5975_) == 1)
{
lean_object* v_val_5979_; lean_object* v___x_5980_; 
lean_del_object(v___x_5977_);
v_val_5979_ = lean_ctor_get(v_a_5975_, 0);
lean_inc_n(v_val_5979_, 2);
lean_dec_ref_known(v_a_5975_, 1);
lean_inc_ref(v_ctorVal_5968_);
v___x_5980_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(v_ctorVal_5968_, v_val_5979_, v_a_5969_, v_a_5970_, v_a_5971_, v_a_5972_);
if (lean_obj_tag(v___x_5980_) == 0)
{
lean_object* v_a_5981_; lean_object* v___x_5983_; uint8_t v_isShared_5984_; uint8_t v_isSharedCheck_6023_; 
v_a_5981_ = lean_ctor_get(v___x_5980_, 0);
v_isSharedCheck_6023_ = !lean_is_exclusive(v___x_5980_);
if (v_isSharedCheck_6023_ == 0)
{
v___x_5983_ = v___x_5980_;
v_isShared_5984_ = v_isSharedCheck_6023_;
goto v_resetjp_5982_;
}
else
{
lean_inc(v_a_5981_);
lean_dec(v___x_5980_);
v___x_5983_ = lean_box(0);
v_isShared_5984_ = v_isSharedCheck_6023_;
goto v_resetjp_5982_;
}
v_resetjp_5982_:
{
if (lean_obj_tag(v_a_5981_) == 1)
{
lean_object* v_toConstantVal_5985_; lean_object* v_val_5986_; lean_object* v___x_5988_; uint8_t v_isShared_5989_; uint8_t v_isSharedCheck_6018_; 
v_toConstantVal_5985_ = lean_ctor_get(v_ctorVal_5968_, 0);
lean_inc_ref(v_toConstantVal_5985_);
lean_dec_ref(v_ctorVal_5968_);
v_val_5986_ = lean_ctor_get(v_a_5981_, 0);
v_isSharedCheck_6018_ = !lean_is_exclusive(v_a_5981_);
if (v_isSharedCheck_6018_ == 0)
{
v___x_5988_ = v_a_5981_;
v_isShared_5989_ = v_isSharedCheck_6018_;
goto v_resetjp_5987_;
}
else
{
lean_inc(v_val_5986_);
lean_dec(v_a_5981_);
v___x_5988_ = lean_box(0);
v_isShared_5989_ = v_isSharedCheck_6018_;
goto v_resetjp_5987_;
}
v_resetjp_5987_:
{
lean_object* v_levelParams_5990_; lean_object* v___x_5992_; uint8_t v_isShared_5993_; uint8_t v_isSharedCheck_6015_; 
v_levelParams_5990_ = lean_ctor_get(v_toConstantVal_5985_, 1);
v_isSharedCheck_6015_ = !lean_is_exclusive(v_toConstantVal_5985_);
if (v_isSharedCheck_6015_ == 0)
{
lean_object* v_unused_6016_; lean_object* v_unused_6017_; 
v_unused_6016_ = lean_ctor_get(v_toConstantVal_5985_, 2);
lean_dec(v_unused_6016_);
v_unused_6017_ = lean_ctor_get(v_toConstantVal_5985_, 0);
lean_dec(v_unused_6017_);
v___x_5992_ = v_toConstantVal_5985_;
v_isShared_5993_ = v_isSharedCheck_6015_;
goto v_resetjp_5991_;
}
else
{
lean_inc(v_levelParams_5990_);
lean_dec(v_toConstantVal_5985_);
v___x_5992_ = lean_box(0);
v_isShared_5993_ = v_isSharedCheck_6015_;
goto v_resetjp_5991_;
}
v_resetjp_5991_:
{
lean_object* v_thmType_5994_; lean_object* v___x_5996_; uint8_t v_isShared_5997_; uint8_t v_isSharedCheck_6012_; 
v_thmType_5994_ = lean_ctor_get(v_val_5979_, 0);
v_isSharedCheck_6012_ = !lean_is_exclusive(v_val_5979_);
if (v_isSharedCheck_6012_ == 0)
{
lean_object* v_unused_6013_; lean_object* v_unused_6014_; 
v_unused_6013_ = lean_ctor_get(v_val_5979_, 2);
lean_dec(v_unused_6013_);
v_unused_6014_ = lean_ctor_get(v_val_5979_, 1);
lean_dec(v_unused_6014_);
v___x_5996_ = v_val_5979_;
v_isShared_5997_ = v_isSharedCheck_6012_;
goto v_resetjp_5995_;
}
else
{
lean_inc(v_thmType_5994_);
lean_dec(v_val_5979_);
v___x_5996_ = lean_box(0);
v_isShared_5997_ = v_isSharedCheck_6012_;
goto v_resetjp_5995_;
}
v_resetjp_5995_:
{
lean_object* v___x_5999_; 
lean_inc(v_thmName_5967_);
if (v_isShared_5993_ == 0)
{
lean_ctor_set(v___x_5992_, 2, v_thmType_5994_);
lean_ctor_set(v___x_5992_, 0, v_thmName_5967_);
v___x_5999_ = v___x_5992_;
goto v_reusejp_5998_;
}
else
{
lean_object* v_reuseFailAlloc_6011_; 
v_reuseFailAlloc_6011_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6011_, 0, v_thmName_5967_);
lean_ctor_set(v_reuseFailAlloc_6011_, 1, v_levelParams_5990_);
lean_ctor_set(v_reuseFailAlloc_6011_, 2, v_thmType_5994_);
v___x_5999_ = v_reuseFailAlloc_6011_;
goto v_reusejp_5998_;
}
v_reusejp_5998_:
{
lean_object* v___x_6000_; lean_object* v___x_6001_; lean_object* v___x_6003_; 
v___x_6000_ = lean_box(0);
v___x_6001_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6001_, 0, v_thmName_5967_);
lean_ctor_set(v___x_6001_, 1, v___x_6000_);
if (v_isShared_5997_ == 0)
{
lean_ctor_set(v___x_5996_, 2, v___x_6001_);
lean_ctor_set(v___x_5996_, 1, v_val_5986_);
lean_ctor_set(v___x_5996_, 0, v___x_5999_);
v___x_6003_ = v___x_5996_;
goto v_reusejp_6002_;
}
else
{
lean_object* v_reuseFailAlloc_6010_; 
v_reuseFailAlloc_6010_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6010_, 0, v___x_5999_);
lean_ctor_set(v_reuseFailAlloc_6010_, 1, v_val_5986_);
lean_ctor_set(v_reuseFailAlloc_6010_, 2, v___x_6001_);
v___x_6003_ = v_reuseFailAlloc_6010_;
goto v_reusejp_6002_;
}
v_reusejp_6002_:
{
lean_object* v___x_6005_; 
if (v_isShared_5989_ == 0)
{
lean_ctor_set(v___x_5988_, 0, v___x_6003_);
v___x_6005_ = v___x_5988_;
goto v_reusejp_6004_;
}
else
{
lean_object* v_reuseFailAlloc_6009_; 
v_reuseFailAlloc_6009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6009_, 0, v___x_6003_);
v___x_6005_ = v_reuseFailAlloc_6009_;
goto v_reusejp_6004_;
}
v_reusejp_6004_:
{
lean_object* v___x_6007_; 
if (v_isShared_5984_ == 0)
{
lean_ctor_set(v___x_5983_, 0, v___x_6005_);
v___x_6007_ = v___x_5983_;
goto v_reusejp_6006_;
}
else
{
lean_object* v_reuseFailAlloc_6008_; 
v_reuseFailAlloc_6008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6008_, 0, v___x_6005_);
v___x_6007_ = v_reuseFailAlloc_6008_;
goto v_reusejp_6006_;
}
v_reusejp_6006_:
{
return v___x_6007_;
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
lean_object* v___x_6019_; lean_object* v___x_6021_; 
lean_dec(v_a_5981_);
lean_dec(v_val_5979_);
lean_dec_ref(v_ctorVal_5968_);
lean_dec(v_thmName_5967_);
v___x_6019_ = lean_box(0);
if (v_isShared_5984_ == 0)
{
lean_ctor_set(v___x_5983_, 0, v___x_6019_);
v___x_6021_ = v___x_5983_;
goto v_reusejp_6020_;
}
else
{
lean_object* v_reuseFailAlloc_6022_; 
v_reuseFailAlloc_6022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6022_, 0, v___x_6019_);
v___x_6021_ = v_reuseFailAlloc_6022_;
goto v_reusejp_6020_;
}
v_reusejp_6020_:
{
return v___x_6021_;
}
}
}
}
else
{
lean_object* v_a_6024_; lean_object* v___x_6026_; uint8_t v_isShared_6027_; uint8_t v_isSharedCheck_6031_; 
lean_dec(v_val_5979_);
lean_dec_ref(v_ctorVal_5968_);
lean_dec(v_thmName_5967_);
v_a_6024_ = lean_ctor_get(v___x_5980_, 0);
v_isSharedCheck_6031_ = !lean_is_exclusive(v___x_5980_);
if (v_isSharedCheck_6031_ == 0)
{
v___x_6026_ = v___x_5980_;
v_isShared_6027_ = v_isSharedCheck_6031_;
goto v_resetjp_6025_;
}
else
{
lean_inc(v_a_6024_);
lean_dec(v___x_5980_);
v___x_6026_ = lean_box(0);
v_isShared_6027_ = v_isSharedCheck_6031_;
goto v_resetjp_6025_;
}
v_resetjp_6025_:
{
lean_object* v___x_6029_; 
if (v_isShared_6027_ == 0)
{
v___x_6029_ = v___x_6026_;
goto v_reusejp_6028_;
}
else
{
lean_object* v_reuseFailAlloc_6030_; 
v_reuseFailAlloc_6030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6030_, 0, v_a_6024_);
v___x_6029_ = v_reuseFailAlloc_6030_;
goto v_reusejp_6028_;
}
v_reusejp_6028_:
{
return v___x_6029_;
}
}
}
}
else
{
lean_object* v___x_6032_; lean_object* v___x_6034_; 
lean_dec(v_a_5975_);
lean_dec_ref(v_ctorVal_5968_);
lean_dec(v_thmName_5967_);
v___x_6032_ = lean_box(0);
if (v_isShared_5978_ == 0)
{
lean_ctor_set(v___x_5977_, 0, v___x_6032_);
v___x_6034_ = v___x_5977_;
goto v_reusejp_6033_;
}
else
{
lean_object* v_reuseFailAlloc_6035_; 
v_reuseFailAlloc_6035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6035_, 0, v___x_6032_);
v___x_6034_ = v_reuseFailAlloc_6035_;
goto v_reusejp_6033_;
}
v_reusejp_6033_:
{
return v___x_6034_;
}
}
}
}
else
{
lean_object* v_a_6037_; lean_object* v___x_6039_; uint8_t v_isShared_6040_; uint8_t v_isSharedCheck_6044_; 
lean_dec_ref(v_ctorVal_5968_);
lean_dec(v_thmName_5967_);
v_a_6037_ = lean_ctor_get(v___x_5974_, 0);
v_isSharedCheck_6044_ = !lean_is_exclusive(v___x_5974_);
if (v_isSharedCheck_6044_ == 0)
{
v___x_6039_ = v___x_5974_;
v_isShared_6040_ = v_isSharedCheck_6044_;
goto v_resetjp_6038_;
}
else
{
lean_inc(v_a_6037_);
lean_dec(v___x_5974_);
v___x_6039_ = lean_box(0);
v_isShared_6040_ = v_isSharedCheck_6044_;
goto v_resetjp_6038_;
}
v_resetjp_6038_:
{
lean_object* v___x_6042_; 
if (v_isShared_6040_ == 0)
{
v___x_6042_ = v___x_6039_;
goto v_reusejp_6041_;
}
else
{
lean_object* v_reuseFailAlloc_6043_; 
v_reuseFailAlloc_6043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6043_, 0, v_a_6037_);
v___x_6042_ = v_reuseFailAlloc_6043_;
goto v_reusejp_6041_;
}
v_reusejp_6041_:
{
return v___x_6042_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f___boxed(lean_object* v_thmName_6045_, lean_object* v_ctorVal_6046_, lean_object* v_a_6047_, lean_object* v_a_6048_, lean_object* v_a_6049_, lean_object* v_a_6050_, lean_object* v_a_6051_){
_start:
{
lean_object* v_res_6052_; 
v_res_6052_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(v_thmName_6045_, v_ctorVal_6046_, v_a_6047_, v_a_6048_, v_a_6049_, v_a_6050_);
lean_dec(v_a_6050_);
lean_dec_ref(v_a_6049_);
lean_dec(v_a_6048_);
lean_dec_ref(v_a_6047_);
return v_res_6052_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(lean_object* v_env_6053_, lean_object* v_n_6054_){
_start:
{
if (lean_obj_tag(v_n_6054_) == 1)
{
lean_object* v_pre_6055_; lean_object* v_str_6056_; lean_object* v___x_6057_; uint8_t v___x_6058_; 
v_pre_6055_ = lean_ctor_get(v_n_6054_, 0);
lean_inc(v_pre_6055_);
v_str_6056_ = lean_ctor_get(v_n_6054_, 1);
lean_inc_ref(v_str_6056_);
lean_dec_ref_known(v_n_6054_, 2);
v___x_6057_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0));
v___x_6058_ = lean_string_dec_eq(v_str_6056_, v___x_6057_);
lean_dec_ref(v_str_6056_);
if (v___x_6058_ == 0)
{
lean_dec(v_pre_6055_);
lean_dec_ref(v_env_6053_);
return v___x_6058_;
}
else
{
uint8_t v___x_6059_; lean_object* v___x_6060_; 
v___x_6059_ = 0;
v___x_6060_ = l_Lean_Environment_find_x3f(v_env_6053_, v_pre_6055_, v___x_6059_);
if (lean_obj_tag(v___x_6060_) == 1)
{
lean_object* v_val_6061_; 
v_val_6061_ = lean_ctor_get(v___x_6060_, 0);
lean_inc(v_val_6061_);
lean_dec_ref_known(v___x_6060_, 1);
if (lean_obj_tag(v_val_6061_) == 6)
{
lean_dec_ref_known(v_val_6061_, 1);
return v___x_6058_;
}
else
{
lean_dec(v_val_6061_);
return v___x_6059_;
}
}
else
{
lean_dec(v___x_6060_);
return v___x_6059_;
}
}
}
else
{
uint8_t v___x_6062_; 
lean_dec(v_n_6054_);
lean_dec_ref(v_env_6053_);
v___x_6062_ = 0;
return v___x_6062_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2____boxed(lean_object* v_env_6063_, lean_object* v_n_6064_){
_start:
{
uint8_t v_res_6065_; lean_object* v_r_6066_; 
v_res_6065_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(v_env_6063_, v_n_6064_);
v_r_6066_ = lean_box(v_res_6065_);
return v_r_6066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_6069_; lean_object* v___x_6070_; 
v___f_6069_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_));
v___x_6070_ = l_Lean_registerReservedNamePredicate(v___f_6069_);
return v___x_6070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2____boxed(lean_object* v_a_6071_){
_start:
{
lean_object* v_res_6072_; 
v_res_6072_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_();
return v_res_6072_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(lean_object* v_thm_6073_, lean_object* v___y_6074_){
_start:
{
lean_object* v___x_6076_; lean_object* v_env_6077_; lean_object* v_toConstantVal_6078_; lean_object* v_value_6079_; lean_object* v_all_6080_; lean_object* v_type_6087_; uint8_t v___x_6088_; 
v___x_6076_ = lean_st_ref_get(v___y_6074_);
v_env_6077_ = lean_ctor_get(v___x_6076_, 0);
lean_inc_ref_n(v_env_6077_, 2);
lean_dec(v___x_6076_);
v_toConstantVal_6078_ = lean_ctor_get(v_thm_6073_, 0);
v_value_6079_ = lean_ctor_get(v_thm_6073_, 1);
v_all_6080_ = lean_ctor_get(v_thm_6073_, 2);
v_type_6087_ = lean_ctor_get(v_toConstantVal_6078_, 2);
v___x_6088_ = l_Lean_Environment_hasUnsafe(v_env_6077_, v_type_6087_);
if (v___x_6088_ == 0)
{
uint8_t v___x_6089_; 
v___x_6089_ = l_Lean_Environment_hasUnsafe(v_env_6077_, v_value_6079_);
if (v___x_6089_ == 0)
{
lean_object* v___x_6090_; lean_object* v___x_6091_; 
v___x_6090_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_6090_, 0, v_thm_6073_);
v___x_6091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6091_, 0, v___x_6090_);
return v___x_6091_;
}
else
{
lean_inc(v_all_6080_);
lean_inc_ref(v_value_6079_);
lean_inc_ref(v_toConstantVal_6078_);
lean_dec_ref(v_thm_6073_);
goto v___jp_6081_;
}
}
else
{
lean_inc(v_all_6080_);
lean_inc_ref(v_value_6079_);
lean_inc_ref(v_toConstantVal_6078_);
lean_dec_ref(v_env_6077_);
lean_dec_ref(v_thm_6073_);
goto v___jp_6081_;
}
v___jp_6081_:
{
lean_object* v___x_6082_; uint8_t v___x_6083_; lean_object* v___x_6084_; lean_object* v___x_6085_; lean_object* v___x_6086_; 
v___x_6082_ = lean_box(0);
v___x_6083_ = 0;
v___x_6084_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_6084_, 0, v_toConstantVal_6078_);
lean_ctor_set(v___x_6084_, 1, v_value_6079_);
lean_ctor_set(v___x_6084_, 2, v___x_6082_);
lean_ctor_set(v___x_6084_, 3, v_all_6080_);
lean_ctor_set_uint8(v___x_6084_, sizeof(void*)*4, v___x_6083_);
v___x_6085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6085_, 0, v___x_6084_);
v___x_6086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6086_, 0, v___x_6085_);
return v___x_6086_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_thm_6092_, lean_object* v___y_6093_, lean_object* v___y_6094_){
_start:
{
lean_object* v_res_6095_; 
v_res_6095_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(v_thm_6092_, v___y_6093_);
lean_dec(v___y_6093_);
return v_res_6095_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0(lean_object* v_thm_6096_, lean_object* v___y_6097_, lean_object* v___y_6098_, lean_object* v___y_6099_, lean_object* v___y_6100_){
_start:
{
lean_object* v___x_6102_; 
v___x_6102_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(v_thm_6096_, v___y_6100_);
return v___x_6102_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___boxed(lean_object* v_thm_6103_, lean_object* v___y_6104_, lean_object* v___y_6105_, lean_object* v___y_6106_, lean_object* v___y_6107_, lean_object* v___y_6108_){
_start:
{
lean_object* v_res_6109_; 
v_res_6109_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0(v_thm_6103_, v___y_6104_, v___y_6105_, v___y_6106_, v___y_6107_);
lean_dec(v___y_6107_);
lean_dec_ref(v___y_6106_);
lean_dec(v___y_6105_);
lean_dec_ref(v___y_6104_);
return v_res_6109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(lean_object* v_val_6110_, uint8_t v___x_6111_, lean_object* v___y_6112_, lean_object* v___y_6113_, lean_object* v___y_6114_, lean_object* v___y_6115_){
_start:
{
lean_object* v___x_6117_; lean_object* v_a_6118_; lean_object* v___x_6119_; 
v___x_6117_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(v_val_6110_, v___y_6115_);
v_a_6118_ = lean_ctor_get(v___x_6117_, 0);
lean_inc(v_a_6118_);
lean_dec_ref(v___x_6117_);
v___x_6119_ = l_Lean_addDecl(v_a_6118_, v___x_6111_, v___y_6114_, v___y_6115_);
return v___x_6119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object* v_val_6120_, lean_object* v___x_6121_, lean_object* v___y_6122_, lean_object* v___y_6123_, lean_object* v___y_6124_, lean_object* v___y_6125_, lean_object* v___y_6126_){
_start:
{
uint8_t v___x_2233__boxed_6127_; lean_object* v_res_6128_; 
v___x_2233__boxed_6127_ = lean_unbox(v___x_6121_);
v_res_6128_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(v_val_6120_, v___x_2233__boxed_6127_, v___y_6122_, v___y_6123_, v___y_6124_, v___y_6125_);
lean_dec(v___y_6125_);
lean_dec_ref(v___y_6124_);
lean_dec(v___y_6123_);
lean_dec_ref(v___y_6122_);
return v_res_6128_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6131_; lean_object* v___x_6132_; lean_object* v___x_6133_; 
v___x_6131_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__0, &l_Lean_Meta_mkInjectiveTheorems___closed__0_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__0);
v___x_6132_ = lean_unsigned_to_nat(0u);
v___x_6133_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_6133_, 0, v___x_6132_);
lean_ctor_set(v___x_6133_, 1, v___x_6132_);
lean_ctor_set(v___x_6133_, 2, v___x_6132_);
lean_ctor_set(v___x_6133_, 3, v___x_6132_);
lean_ctor_set(v___x_6133_, 4, v___x_6131_);
lean_ctor_set(v___x_6133_, 5, v___x_6131_);
lean_ctor_set(v___x_6133_, 6, v___x_6131_);
lean_ctor_set(v___x_6133_, 7, v___x_6131_);
lean_ctor_set(v___x_6133_, 8, v___x_6131_);
lean_ctor_set(v___x_6133_, 9, v___x_6131_);
lean_ctor_set(v___x_6133_, 10, v___x_6131_);
return v___x_6133_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6134_; lean_object* v___x_6135_; 
v___x_6134_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__0, &l_Lean_Meta_mkInjectiveTheorems___closed__0_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__0);
v___x_6135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6135_, 0, v___x_6134_);
lean_ctor_set(v___x_6135_, 1, v___x_6134_);
return v___x_6135_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6136_; lean_object* v___x_6137_; lean_object* v___x_6138_; 
v___x_6136_ = lean_unsigned_to_nat(0u);
v___x_6137_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__0, &l_Lean_Meta_mkInjectiveTheorems___closed__0_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__0);
v___x_6138_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6138_, 0, v___x_6137_);
lean_ctor_set(v___x_6138_, 1, v___x_6137_);
lean_ctor_set(v___x_6138_, 2, v___x_6136_);
return v___x_6138_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6139_; lean_object* v___x_6140_; lean_object* v___x_6141_; lean_object* v___x_6142_; lean_object* v___x_6143_; 
v___x_6139_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6140_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6141_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__0, &l_Lean_Meta_mkInjectiveTheorems___closed__0_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__0);
v___x_6142_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2);
v___x_6143_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_6143_, 0, v___x_6142_);
lean_ctor_set(v___x_6143_, 1, v___x_6141_);
lean_ctor_set(v___x_6143_, 2, v___x_6140_);
lean_ctor_set(v___x_6143_, 3, v___x_6141_);
lean_ctor_set(v___x_6143_, 4, v___x_6141_);
lean_ctor_set(v___x_6143_, 5, v___x_6141_);
lean_ctor_set(v___x_6143_, 6, v___x_6141_);
lean_ctor_set(v___x_6143_, 7, v___x_6139_);
return v___x_6143_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6144_; lean_object* v___x_6145_; 
v___x_6144_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__0, &l_Lean_Meta_mkInjectiveTheorems___closed__0_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__0);
v___x_6145_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6145_, 0, v___x_6144_);
lean_ctor_set(v___x_6145_, 1, v___x_6144_);
lean_ctor_set(v___x_6145_, 2, v___x_6144_);
lean_ctor_set(v___x_6145_, 3, v___x_6144_);
lean_ctor_set(v___x_6145_, 4, v___x_6144_);
return v___x_6145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(lean_object* v___x_6146_, lean_object* v_name_6147_, lean_object* v___y_6148_, lean_object* v___y_6149_){
_start:
{
if (lean_obj_tag(v_name_6147_) == 1)
{
lean_object* v_pre_6159_; lean_object* v_str_6160_; lean_object* v___x_6161_; uint8_t v___x_6162_; 
v_pre_6159_ = lean_ctor_get(v_name_6147_, 0);
lean_inc(v_pre_6159_);
v_str_6160_ = lean_ctor_get(v_name_6147_, 1);
v___x_6161_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0));
v___x_6162_ = lean_string_dec_eq(v_str_6160_, v___x_6161_);
if (v___x_6162_ == 0)
{
lean_dec(v_pre_6159_);
lean_dec_ref_known(v_name_6147_, 2);
lean_dec(v___x_6146_);
goto v___jp_6155_;
}
else
{
lean_object* v___x_6163_; lean_object* v_env_6164_; uint8_t v___x_6165_; lean_object* v___x_6166_; 
v___x_6163_ = lean_st_ref_get(v___y_6149_);
v_env_6164_ = lean_ctor_get(v___x_6163_, 0);
lean_inc_ref(v_env_6164_);
lean_dec(v___x_6163_);
v___x_6165_ = 0;
lean_inc(v_pre_6159_);
v___x_6166_ = l_Lean_Environment_find_x3f(v_env_6164_, v_pre_6159_, v___x_6165_);
if (lean_obj_tag(v___x_6166_) == 1)
{
lean_object* v_val_6167_; 
v_val_6167_ = lean_ctor_get(v___x_6166_, 0);
lean_inc(v_val_6167_);
lean_dec_ref_known(v___x_6166_, 1);
if (lean_obj_tag(v_val_6167_) == 6)
{
lean_object* v_val_6168_; lean_object* v___x_6170_; uint8_t v_isShared_6171_; uint8_t v_isSharedCheck_6218_; 
v_val_6168_ = lean_ctor_get(v_val_6167_, 0);
v_isSharedCheck_6218_ = !lean_is_exclusive(v_val_6167_);
if (v_isSharedCheck_6218_ == 0)
{
v___x_6170_ = v_val_6167_;
v_isShared_6171_ = v_isSharedCheck_6218_;
goto v_resetjp_6169_;
}
else
{
lean_inc(v_val_6168_);
lean_dec(v_val_6167_);
v___x_6170_ = lean_box(0);
v_isShared_6171_ = v_isSharedCheck_6218_;
goto v_resetjp_6169_;
}
v_resetjp_6169_:
{
uint8_t v___x_6172_; uint8_t v___x_6173_; uint8_t v___x_6174_; lean_object* v___x_6175_; uint64_t v___x_6176_; lean_object* v___x_6177_; lean_object* v___x_6178_; lean_object* v___x_6179_; lean_object* v___x_6180_; lean_object* v___x_6181_; lean_object* v___x_6182_; lean_object* v___x_6183_; lean_object* v___x_6184_; lean_object* v___x_6185_; lean_object* v___x_6186_; lean_object* v___x_6187_; lean_object* v___x_6188_; uint8_t v_a_6190_; lean_object* v___x_6196_; 
v___x_6172_ = 1;
v___x_6173_ = 0;
v___x_6174_ = 2;
v___x_6175_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_6175_, 0, v___x_6165_);
lean_ctor_set_uint8(v___x_6175_, 1, v___x_6165_);
lean_ctor_set_uint8(v___x_6175_, 2, v___x_6165_);
lean_ctor_set_uint8(v___x_6175_, 3, v___x_6165_);
lean_ctor_set_uint8(v___x_6175_, 4, v___x_6165_);
lean_ctor_set_uint8(v___x_6175_, 5, v___x_6162_);
lean_ctor_set_uint8(v___x_6175_, 6, v___x_6162_);
lean_ctor_set_uint8(v___x_6175_, 7, v___x_6165_);
lean_ctor_set_uint8(v___x_6175_, 8, v___x_6162_);
lean_ctor_set_uint8(v___x_6175_, 9, v___x_6172_);
lean_ctor_set_uint8(v___x_6175_, 10, v___x_6173_);
lean_ctor_set_uint8(v___x_6175_, 11, v___x_6162_);
lean_ctor_set_uint8(v___x_6175_, 12, v___x_6162_);
lean_ctor_set_uint8(v___x_6175_, 13, v___x_6162_);
lean_ctor_set_uint8(v___x_6175_, 14, v___x_6174_);
lean_ctor_set_uint8(v___x_6175_, 15, v___x_6162_);
lean_ctor_set_uint8(v___x_6175_, 16, v___x_6162_);
lean_ctor_set_uint8(v___x_6175_, 17, v___x_6162_);
lean_ctor_set_uint8(v___x_6175_, 18, v___x_6162_);
lean_ctor_set_uint8(v___x_6175_, 19, v___x_6165_);
v___x_6176_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_6175_);
v___x_6177_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_6177_, 0, v___x_6175_);
lean_ctor_set_uint64(v___x_6177_, sizeof(void*)*1, v___x_6176_);
v___x_6178_ = lean_unsigned_to_nat(0u);
v___x_6179_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__2, &l_Lean_Meta_mkInjectiveTheorems___closed__2_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__2);
v___x_6180_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_6181_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_));
v___x_6182_ = lean_box(0);
lean_inc(v___x_6146_);
v___x_6183_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_6183_, 0, v___x_6177_);
lean_ctor_set(v___x_6183_, 1, v___x_6146_);
lean_ctor_set(v___x_6183_, 2, v___x_6180_);
lean_ctor_set(v___x_6183_, 3, v___x_6181_);
lean_ctor_set(v___x_6183_, 4, v___x_6182_);
lean_ctor_set(v___x_6183_, 5, v___x_6178_);
lean_ctor_set(v___x_6183_, 6, v___x_6182_);
lean_ctor_set_uint8(v___x_6183_, sizeof(void*)*7, v___x_6165_);
lean_ctor_set_uint8(v___x_6183_, sizeof(void*)*7 + 1, v___x_6165_);
lean_ctor_set_uint8(v___x_6183_, sizeof(void*)*7 + 2, v___x_6165_);
lean_ctor_set_uint8(v___x_6183_, sizeof(void*)*7 + 3, v___x_6162_);
v___x_6184_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6185_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6186_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6187_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6187_, 0, v___x_6184_);
lean_ctor_set(v___x_6187_, 1, v___x_6185_);
lean_ctor_set(v___x_6187_, 2, v___x_6146_);
lean_ctor_set(v___x_6187_, 3, v___x_6179_);
lean_ctor_set(v___x_6187_, 4, v___x_6186_);
v___x_6188_ = lean_st_mk_ref(v___x_6187_);
lean_inc_ref(v_name_6147_);
v___x_6196_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(v_name_6147_, v_val_6168_, v___x_6183_, v___x_6188_, v___y_6148_, v___y_6149_);
if (lean_obj_tag(v___x_6196_) == 0)
{
lean_object* v_a_6197_; 
v_a_6197_ = lean_ctor_get(v___x_6196_, 0);
lean_inc(v_a_6197_);
lean_dec_ref_known(v___x_6196_, 1);
if (lean_obj_tag(v_a_6197_) == 1)
{
lean_object* v_val_6198_; lean_object* v___x_6199_; lean_object* v___f_6200_; lean_object* v___x_6201_; 
v_val_6198_ = lean_ctor_get(v_a_6197_, 0);
lean_inc(v_val_6198_);
lean_dec_ref_known(v_a_6197_, 1);
v___x_6199_ = lean_box(v___x_6165_);
v___f_6200_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed), 7, 2);
lean_closure_set(v___f_6200_, 0, v_val_6198_);
lean_closure_set(v___f_6200_, 1, v___x_6199_);
v___x_6201_ = l_Lean_Meta_realizeConst(v_pre_6159_, v_name_6147_, v___f_6200_, v___x_6183_, v___x_6188_, v___y_6148_, v___y_6149_);
lean_dec_ref_known(v___x_6183_, 7);
if (lean_obj_tag(v___x_6201_) == 0)
{
lean_dec_ref_known(v___x_6201_, 1);
v_a_6190_ = v___x_6162_;
goto v___jp_6189_;
}
else
{
lean_object* v_a_6202_; lean_object* v___x_6204_; uint8_t v_isShared_6205_; uint8_t v_isSharedCheck_6209_; 
lean_dec(v___x_6188_);
lean_del_object(v___x_6170_);
v_a_6202_ = lean_ctor_get(v___x_6201_, 0);
v_isSharedCheck_6209_ = !lean_is_exclusive(v___x_6201_);
if (v_isSharedCheck_6209_ == 0)
{
v___x_6204_ = v___x_6201_;
v_isShared_6205_ = v_isSharedCheck_6209_;
goto v_resetjp_6203_;
}
else
{
lean_inc(v_a_6202_);
lean_dec(v___x_6201_);
v___x_6204_ = lean_box(0);
v_isShared_6205_ = v_isSharedCheck_6209_;
goto v_resetjp_6203_;
}
v_resetjp_6203_:
{
lean_object* v___x_6207_; 
if (v_isShared_6205_ == 0)
{
v___x_6207_ = v___x_6204_;
goto v_reusejp_6206_;
}
else
{
lean_object* v_reuseFailAlloc_6208_; 
v_reuseFailAlloc_6208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6208_, 0, v_a_6202_);
v___x_6207_ = v_reuseFailAlloc_6208_;
goto v_reusejp_6206_;
}
v_reusejp_6206_:
{
return v___x_6207_;
}
}
}
}
else
{
lean_dec(v_a_6197_);
lean_dec_ref_known(v___x_6183_, 7);
lean_dec_ref_known(v_name_6147_, 2);
lean_dec(v_pre_6159_);
v_a_6190_ = v___x_6165_;
goto v___jp_6189_;
}
}
else
{
lean_object* v_a_6210_; lean_object* v___x_6212_; uint8_t v_isShared_6213_; uint8_t v_isSharedCheck_6217_; 
lean_dec(v___x_6188_);
lean_dec_ref_known(v___x_6183_, 7);
lean_del_object(v___x_6170_);
lean_dec_ref_known(v_name_6147_, 2);
lean_dec(v_pre_6159_);
v_a_6210_ = lean_ctor_get(v___x_6196_, 0);
v_isSharedCheck_6217_ = !lean_is_exclusive(v___x_6196_);
if (v_isSharedCheck_6217_ == 0)
{
v___x_6212_ = v___x_6196_;
v_isShared_6213_ = v_isSharedCheck_6217_;
goto v_resetjp_6211_;
}
else
{
lean_inc(v_a_6210_);
lean_dec(v___x_6196_);
v___x_6212_ = lean_box(0);
v_isShared_6213_ = v_isSharedCheck_6217_;
goto v_resetjp_6211_;
}
v_resetjp_6211_:
{
lean_object* v___x_6215_; 
if (v_isShared_6213_ == 0)
{
v___x_6215_ = v___x_6212_;
goto v_reusejp_6214_;
}
else
{
lean_object* v_reuseFailAlloc_6216_; 
v_reuseFailAlloc_6216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6216_, 0, v_a_6210_);
v___x_6215_ = v_reuseFailAlloc_6216_;
goto v_reusejp_6214_;
}
v_reusejp_6214_:
{
return v___x_6215_;
}
}
}
v___jp_6189_:
{
lean_object* v___x_6191_; lean_object* v___x_6192_; lean_object* v___x_6194_; 
v___x_6191_ = lean_st_ref_get(v___x_6188_);
lean_dec(v___x_6188_);
lean_dec(v___x_6191_);
v___x_6192_ = lean_box(v_a_6190_);
if (v_isShared_6171_ == 0)
{
lean_ctor_set_tag(v___x_6170_, 0);
lean_ctor_set(v___x_6170_, 0, v___x_6192_);
v___x_6194_ = v___x_6170_;
goto v_reusejp_6193_;
}
else
{
lean_object* v_reuseFailAlloc_6195_; 
v_reuseFailAlloc_6195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6195_, 0, v___x_6192_);
v___x_6194_ = v_reuseFailAlloc_6195_;
goto v_reusejp_6193_;
}
v_reusejp_6193_:
{
return v___x_6194_;
}
}
}
}
else
{
lean_dec(v_val_6167_);
lean_dec(v_pre_6159_);
lean_dec_ref_known(v_name_6147_, 2);
lean_dec(v___x_6146_);
goto v___jp_6151_;
}
}
else
{
lean_dec(v___x_6166_);
lean_dec(v_pre_6159_);
lean_dec_ref_known(v_name_6147_, 2);
lean_dec(v___x_6146_);
goto v___jp_6151_;
}
}
}
else
{
lean_dec(v_name_6147_);
lean_dec(v___x_6146_);
goto v___jp_6155_;
}
v___jp_6151_:
{
uint8_t v___x_6152_; lean_object* v___x_6153_; lean_object* v___x_6154_; 
v___x_6152_ = 0;
v___x_6153_ = lean_box(v___x_6152_);
v___x_6154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6154_, 0, v___x_6153_);
return v___x_6154_;
}
v___jp_6155_:
{
uint8_t v___x_6156_; lean_object* v___x_6157_; lean_object* v___x_6158_; 
v___x_6156_ = 0;
v___x_6157_ = lean_box(v___x_6156_);
v___x_6158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6158_, 0, v___x_6157_);
return v___x_6158_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object* v___x_6219_, lean_object* v_name_6220_, lean_object* v___y_6221_, lean_object* v___y_6222_, lean_object* v___y_6223_){
_start:
{
lean_object* v_res_6224_; 
v_res_6224_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(v___x_6219_, v_name_6220_, v___y_6221_, v___y_6222_);
lean_dec(v___y_6222_);
lean_dec_ref(v___y_6221_);
return v_res_6224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_6228_; lean_object* v___x_6229_; 
v___f_6228_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_));
v___x_6229_ = l_Lean_registerReservedNameAction(v___f_6228_);
return v___x_6229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object* v_a_6230_){
_start:
{
lean_object* v_res_6231_; 
v_res_6231_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_();
return v_res_6231_;
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
