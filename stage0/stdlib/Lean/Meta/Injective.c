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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
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
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Meta_introSubstEq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_applyN(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
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
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
lean_object* lean_io_mono_nanos_now();
lean_object* l_Lean_MVarId_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
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
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* l_Lean_Meta_realizeConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInductivePredicate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__3;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__4;
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "unexpected number of goals after applying `Lean.and_imp`"};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___closed__0 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___closed__0_value;
static lean_once_cell_t l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___closed__1;
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__0_value;
static const lean_string_object l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "injEq_helper"};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__1_value;
static const lean_ctor_object l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(167, 111, 180, 146, 132, 58, 155, 57)}};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__2 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__2_value;
static lean_once_cell_t l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "propIntro"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(189, 136, 38, 165, 207, 169, 133, 34)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 1, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "unexpected number of subgoals when proving injective theorem for constructor `"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__2(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__3(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Meta_mkInjectiveTheorems___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkInjectiveTheorems___closed__4;
static const lean_array_object l_Lean_Meta_mkInjectiveTheorems___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_mkInjectiveTheorems___closed__5 = (const lean_object*)&l_Lean_Meta_mkInjectiveTheorems___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__4_value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Injective"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(55, 101, 109, 194, 24, 99, 201, 78)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(74, 76, 255, 124, 31, 108, 47, 16)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 106, 16, 37, 3, 60, 11, 157)}};
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
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 151, 10, 103, 183, 199, 62, 165)}};
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
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17;
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
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
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
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v_nbuckets_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_123_ = lean_array_get_size(v_data_122_);
v___x_124_ = lean_unsigned_to_nat(2u);
v_nbuckets_125_ = lean_nat_mul(v___x_123_, v___x_124_);
v___x_126_ = lean_unsigned_to_nat(0u);
v___x_127_ = lean_box(0);
v___x_128_ = lean_mk_array(v_nbuckets_125_, v___x_127_);
v___x_129_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v___x_126_, v_data_122_, v___x_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__12___redArg(lean_object* v_a_130_, lean_object* v_b_131_, lean_object* v_x_132_){
_start:
{
if (lean_obj_tag(v_x_132_) == 0)
{
lean_dec(v_b_131_);
lean_dec_ref(v_a_130_);
return v_x_132_;
}
else
{
lean_object* v_key_133_; lean_object* v_value_134_; lean_object* v_tail_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_147_; 
v_key_133_ = lean_ctor_get(v_x_132_, 0);
v_value_134_ = lean_ctor_get(v_x_132_, 1);
v_tail_135_ = lean_ctor_get(v_x_132_, 2);
v_isSharedCheck_147_ = !lean_is_exclusive(v_x_132_);
if (v_isSharedCheck_147_ == 0)
{
v___x_137_ = v_x_132_;
v_isShared_138_ = v_isSharedCheck_147_;
goto v_resetjp_136_;
}
else
{
lean_inc(v_tail_135_);
lean_inc(v_value_134_);
lean_inc(v_key_133_);
lean_dec(v_x_132_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_147_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
uint8_t v___x_139_; 
v___x_139_ = l_Lean_ExprStructEq_beq(v_key_133_, v_a_130_);
if (v___x_139_ == 0)
{
lean_object* v___x_140_; lean_object* v___x_142_; 
v___x_140_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__12___redArg(v_a_130_, v_b_131_, v_tail_135_);
if (v_isShared_138_ == 0)
{
lean_ctor_set(v___x_137_, 2, v___x_140_);
v___x_142_ = v___x_137_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_key_133_);
lean_ctor_set(v_reuseFailAlloc_143_, 1, v_value_134_);
lean_ctor_set(v_reuseFailAlloc_143_, 2, v___x_140_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
return v___x_142_;
}
}
else
{
lean_object* v___x_145_; 
lean_dec(v_value_134_);
lean_dec(v_key_133_);
if (v_isShared_138_ == 0)
{
lean_ctor_set(v___x_137_, 1, v_b_131_);
lean_ctor_set(v___x_137_, 0, v_a_130_);
v___x_145_ = v___x_137_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_a_130_);
lean_ctor_set(v_reuseFailAlloc_146_, 1, v_b_131_);
lean_ctor_set(v_reuseFailAlloc_146_, 2, v_tail_135_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___redArg(lean_object* v_a_148_, lean_object* v_x_149_){
_start:
{
if (lean_obj_tag(v_x_149_) == 0)
{
uint8_t v___x_150_; 
v___x_150_ = 0;
return v___x_150_;
}
else
{
lean_object* v_key_151_; lean_object* v_tail_152_; uint8_t v___x_153_; 
v_key_151_ = lean_ctor_get(v_x_149_, 0);
v_tail_152_ = lean_ctor_get(v_x_149_, 2);
v___x_153_ = l_Lean_ExprStructEq_beq(v_key_151_, v_a_148_);
if (v___x_153_ == 0)
{
v_x_149_ = v_tail_152_;
goto _start;
}
else
{
return v___x_153_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___redArg___boxed(lean_object* v_a_155_, lean_object* v_x_156_){
_start:
{
uint8_t v_res_157_; lean_object* v_r_158_; 
v_res_157_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___redArg(v_a_155_, v_x_156_);
lean_dec(v_x_156_);
lean_dec_ref(v_a_155_);
v_r_158_ = lean_box(v_res_157_);
return v_r_158_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6___redArg(lean_object* v_m_159_, lean_object* v_a_160_, lean_object* v_b_161_){
_start:
{
lean_object* v_size_162_; lean_object* v_buckets_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_206_; 
v_size_162_ = lean_ctor_get(v_m_159_, 0);
v_buckets_163_ = lean_ctor_get(v_m_159_, 1);
v_isSharedCheck_206_ = !lean_is_exclusive(v_m_159_);
if (v_isSharedCheck_206_ == 0)
{
v___x_165_ = v_m_159_;
v_isShared_166_ = v_isSharedCheck_206_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_buckets_163_);
lean_inc(v_size_162_);
lean_dec(v_m_159_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_206_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v___x_167_; uint64_t v___x_168_; uint64_t v___x_169_; uint64_t v___x_170_; uint64_t v_fold_171_; uint64_t v___x_172_; uint64_t v___x_173_; uint64_t v___x_174_; size_t v___x_175_; size_t v___x_176_; size_t v___x_177_; size_t v___x_178_; size_t v___x_179_; lean_object* v_bkt_180_; uint8_t v___x_181_; 
v___x_167_ = lean_array_get_size(v_buckets_163_);
v___x_168_ = l_Lean_ExprStructEq_hash(v_a_160_);
v___x_169_ = 32ULL;
v___x_170_ = lean_uint64_shift_right(v___x_168_, v___x_169_);
v_fold_171_ = lean_uint64_xor(v___x_168_, v___x_170_);
v___x_172_ = 16ULL;
v___x_173_ = lean_uint64_shift_right(v_fold_171_, v___x_172_);
v___x_174_ = lean_uint64_xor(v_fold_171_, v___x_173_);
v___x_175_ = lean_uint64_to_usize(v___x_174_);
v___x_176_ = lean_usize_of_nat(v___x_167_);
v___x_177_ = ((size_t)1ULL);
v___x_178_ = lean_usize_sub(v___x_176_, v___x_177_);
v___x_179_ = lean_usize_land(v___x_175_, v___x_178_);
v_bkt_180_ = lean_array_uget_borrowed(v_buckets_163_, v___x_179_);
v___x_181_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___redArg(v_a_160_, v_bkt_180_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; lean_object* v_size_x27_183_; lean_object* v___x_184_; lean_object* v_buckets_x27_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; uint8_t v___x_191_; 
v___x_182_ = lean_unsigned_to_nat(1u);
v_size_x27_183_ = lean_nat_add(v_size_162_, v___x_182_);
lean_dec(v_size_162_);
lean_inc(v_bkt_180_);
v___x_184_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_184_, 0, v_a_160_);
lean_ctor_set(v___x_184_, 1, v_b_161_);
lean_ctor_set(v___x_184_, 2, v_bkt_180_);
v_buckets_x27_185_ = lean_array_uset(v_buckets_163_, v___x_179_, v___x_184_);
v___x_186_ = lean_unsigned_to_nat(4u);
v___x_187_ = lean_nat_mul(v_size_x27_183_, v___x_186_);
v___x_188_ = lean_unsigned_to_nat(3u);
v___x_189_ = lean_nat_div(v___x_187_, v___x_188_);
lean_dec(v___x_187_);
v___x_190_ = lean_array_get_size(v_buckets_x27_185_);
v___x_191_ = lean_nat_dec_le(v___x_189_, v___x_190_);
lean_dec(v___x_189_);
if (v___x_191_ == 0)
{
lean_object* v_val_192_; lean_object* v___x_194_; 
v_val_192_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11___redArg(v_buckets_x27_185_);
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 1, v_val_192_);
lean_ctor_set(v___x_165_, 0, v_size_x27_183_);
v___x_194_ = v___x_165_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_size_x27_183_);
lean_ctor_set(v_reuseFailAlloc_195_, 1, v_val_192_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
else
{
lean_object* v___x_197_; 
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 1, v_buckets_x27_185_);
lean_ctor_set(v___x_165_, 0, v_size_x27_183_);
v___x_197_ = v___x_165_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_size_x27_183_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v_buckets_x27_185_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
else
{
lean_object* v___x_199_; lean_object* v_buckets_x27_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_204_; 
lean_inc(v_bkt_180_);
v___x_199_ = lean_box(0);
v_buckets_x27_200_ = lean_array_uset(v_buckets_163_, v___x_179_, v___x_199_);
v___x_201_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__12___redArg(v_a_160_, v_b_161_, v_bkt_180_);
v___x_202_ = lean_array_uset(v_buckets_x27_200_, v___x_179_, v___x_201_);
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 1, v___x_202_);
v___x_204_ = v___x_165_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_size_162_);
lean_ctor_set(v_reuseFailAlloc_205_, 1, v___x_202_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__2(lean_object* v_a_207_, lean_object* v_e_208_, lean_object* v_a_209_){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_211_ = lean_st_ref_take(v_a_207_);
v___x_212_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6___redArg(v___x_211_, v_e_208_, v_a_209_);
v___x_213_ = lean_st_ref_set(v_a_207_, v___x_212_);
v___x_214_ = lean_box(0);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__2___boxed(lean_object* v_a_215_, lean_object* v_e_216_, lean_object* v_a_217_, lean_object* v___y_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__2(v_a_215_, v_e_216_, v_a_217_);
lean_dec(v_a_215_);
return v_res_219_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_220_ = lean_box(0);
v___x_221_ = l_Lean_interruptExceptionId;
v___x_222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
lean_ctor_set(v___x_222_, 1, v___x_220_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg(){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg___closed__0);
v___x_225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg___boxed(lean_object* v___y_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg();
return v_res_227_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = l_Lean_maxRecDepthErrorMessage;
v___x_234_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
return v___x_234_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_235_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__3);
v___x_236_ = l_Lean_MessageData_ofFormat(v___x_235_);
return v___x_236_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_237_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__4);
v___x_238_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__2));
v___x_239_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
lean_ctor_set(v___x_239_, 1, v___x_237_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_ref_240_){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_242_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_243_, 0, v_ref_240_);
lean_ctor_set(v___x_243_, 1, v___x_242_);
v___x_244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_ref_245_, lean_object* v___y_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_245_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(lean_object* v_x_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v___y_254_; lean_object* v___y_264_; lean_object* v___y_265_; uint8_t v___y_266_; lean_object* v___y_267_; lean_object* v___y_268_; lean_object* v___y_269_; lean_object* v___y_270_; lean_object* v___y_271_; lean_object* v___y_272_; lean_object* v___y_273_; lean_object* v___y_274_; lean_object* v___y_275_; lean_object* v___y_276_; lean_object* v___y_277_; uint8_t v___y_278_; lean_object* v___y_279_; lean_object* v_fileName_284_; lean_object* v_fileMap_285_; lean_object* v_options_286_; lean_object* v_currRecDepth_287_; lean_object* v_maxRecDepth_288_; lean_object* v_ref_289_; lean_object* v_currNamespace_290_; lean_object* v_openDecls_291_; lean_object* v_initHeartbeats_292_; lean_object* v_maxHeartbeats_293_; lean_object* v_quotContext_294_; lean_object* v_currMacroScope_295_; uint8_t v_diag_296_; lean_object* v_cancelTk_x3f_297_; uint8_t v_suppressElabErrors_298_; lean_object* v_inheritedTraceOptions_299_; 
v_fileName_284_ = lean_ctor_get(v___y_250_, 0);
v_fileMap_285_ = lean_ctor_get(v___y_250_, 1);
v_options_286_ = lean_ctor_get(v___y_250_, 2);
v_currRecDepth_287_ = lean_ctor_get(v___y_250_, 3);
v_maxRecDepth_288_ = lean_ctor_get(v___y_250_, 4);
v_ref_289_ = lean_ctor_get(v___y_250_, 5);
v_currNamespace_290_ = lean_ctor_get(v___y_250_, 6);
v_openDecls_291_ = lean_ctor_get(v___y_250_, 7);
v_initHeartbeats_292_ = lean_ctor_get(v___y_250_, 8);
v_maxHeartbeats_293_ = lean_ctor_get(v___y_250_, 9);
v_quotContext_294_ = lean_ctor_get(v___y_250_, 10);
v_currMacroScope_295_ = lean_ctor_get(v___y_250_, 11);
v_diag_296_ = lean_ctor_get_uint8(v___y_250_, sizeof(void*)*14);
v_cancelTk_x3f_297_ = lean_ctor_get(v___y_250_, 12);
v_suppressElabErrors_298_ = lean_ctor_get_uint8(v___y_250_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_299_ = lean_ctor_get(v___y_250_, 13);
if (lean_obj_tag(v_cancelTk_x3f_297_) == 1)
{
lean_object* v_val_305_; uint8_t v___x_306_; 
v_val_305_ = lean_ctor_get(v_cancelTk_x3f_297_, 0);
v___x_306_ = l_IO_CancelToken_isSet(v_val_305_);
if (v___x_306_ == 0)
{
goto v___jp_300_;
}
else
{
lean_object* v___x_307_; lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_315_; 
lean_dec_ref(v_x_248_);
v___x_307_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg();
v_a_308_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_315_ == 0)
{
v___x_310_ = v___x_307_;
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_dec(v___x_307_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_313_; 
if (v_isShared_311_ == 0)
{
v___x_313_ = v___x_310_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_a_308_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
else
{
goto v___jp_300_;
}
v___jp_253_:
{
if (lean_obj_tag(v___y_254_) == 0)
{
return v___y_254_;
}
else
{
lean_object* v_a_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_262_; 
v_a_255_ = lean_ctor_get(v___y_254_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v___y_254_);
if (v_isSharedCheck_262_ == 0)
{
v___x_257_ = v___y_254_;
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_a_255_);
lean_dec(v___y_254_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_260_; 
if (v_isShared_258_ == 0)
{
v___x_260_ = v___x_257_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_a_255_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
}
v___jp_263_:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_280_ = lean_unsigned_to_nat(1u);
v___x_281_ = lean_nat_add(v___y_268_, v___x_280_);
lean_inc_ref(v___y_270_);
lean_inc(v___y_272_);
lean_inc(v___y_264_);
lean_inc(v___y_269_);
lean_inc(v___y_265_);
lean_inc(v___y_273_);
lean_inc(v___y_267_);
lean_inc(v___y_279_);
lean_inc(v___y_271_);
lean_inc_ref(v___y_277_);
lean_inc_ref(v___y_276_);
lean_inc_ref(v___y_274_);
v___x_282_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_282_, 0, v___y_274_);
lean_ctor_set(v___x_282_, 1, v___y_276_);
lean_ctor_set(v___x_282_, 2, v___y_277_);
lean_ctor_set(v___x_282_, 3, v___x_281_);
lean_ctor_set(v___x_282_, 4, v___y_271_);
lean_ctor_set(v___x_282_, 5, v___y_275_);
lean_ctor_set(v___x_282_, 6, v___y_279_);
lean_ctor_set(v___x_282_, 7, v___y_267_);
lean_ctor_set(v___x_282_, 8, v___y_273_);
lean_ctor_set(v___x_282_, 9, v___y_265_);
lean_ctor_set(v___x_282_, 10, v___y_269_);
lean_ctor_set(v___x_282_, 11, v___y_264_);
lean_ctor_set(v___x_282_, 12, v___y_272_);
lean_ctor_set(v___x_282_, 13, v___y_270_);
lean_ctor_set_uint8(v___x_282_, sizeof(void*)*14, v___y_278_);
lean_ctor_set_uint8(v___x_282_, sizeof(void*)*14 + 1, v___y_266_);
lean_inc(v___y_251_);
lean_inc(v___y_249_);
v___x_283_ = lean_apply_4(v_x_248_, v___y_249_, v___x_282_, v___y_251_, lean_box(0));
v___y_254_ = v___x_283_;
goto v___jp_253_;
}
v___jp_300_:
{
lean_object* v___x_301_; uint8_t v___x_302_; 
v___x_301_ = lean_unsigned_to_nat(0u);
v___x_302_ = lean_nat_dec_eq(v_maxRecDepth_288_, v___x_301_);
if (v___x_302_ == 0)
{
uint8_t v___x_303_; 
v___x_303_ = lean_nat_dec_eq(v_currRecDepth_287_, v_maxRecDepth_288_);
if (v___x_303_ == 0)
{
lean_inc(v_ref_289_);
v___y_264_ = v_currMacroScope_295_;
v___y_265_ = v_maxHeartbeats_293_;
v___y_266_ = v_suppressElabErrors_298_;
v___y_267_ = v_openDecls_291_;
v___y_268_ = v_currRecDepth_287_;
v___y_269_ = v_quotContext_294_;
v___y_270_ = v_inheritedTraceOptions_299_;
v___y_271_ = v_maxRecDepth_288_;
v___y_272_ = v_cancelTk_x3f_297_;
v___y_273_ = v_initHeartbeats_292_;
v___y_274_ = v_fileName_284_;
v___y_275_ = v_ref_289_;
v___y_276_ = v_fileMap_285_;
v___y_277_ = v_options_286_;
v___y_278_ = v_diag_296_;
v___y_279_ = v_currNamespace_290_;
goto v___jp_263_;
}
else
{
lean_object* v___x_304_; 
lean_dec_ref(v_x_248_);
lean_inc(v_ref_289_);
v___x_304_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_289_);
v___y_254_ = v___x_304_;
goto v___jp_253_;
}
}
else
{
lean_inc(v_ref_289_);
v___y_264_ = v_currMacroScope_295_;
v___y_265_ = v_maxHeartbeats_293_;
v___y_266_ = v_suppressElabErrors_298_;
v___y_267_ = v_openDecls_291_;
v___y_268_ = v_currRecDepth_287_;
v___y_269_ = v_quotContext_294_;
v___y_270_ = v_inheritedTraceOptions_299_;
v___y_271_ = v_maxRecDepth_288_;
v___y_272_ = v_cancelTk_x3f_297_;
v___y_273_ = v_initHeartbeats_292_;
v___y_274_ = v_fileName_284_;
v___y_275_ = v_ref_289_;
v___y_276_ = v_fileMap_285_;
v___y_277_ = v_options_286_;
v___y_278_ = v_diag_296_;
v___y_279_ = v_currNamespace_290_;
goto v___jp_263_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(v_x_316_, v___y_317_, v___y_318_, v___y_319_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
lean_dec(v___y_317_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_322_, lean_object* v_x_323_, lean_object* v___y_324_, lean_object* v___y_325_){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_327_ = lean_apply_1(v_x_323_, lean_box(0));
v___x_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_329_, lean_object* v_x_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(v_00_u03b1_329_, v_x_330_, v___y_331_, v___y_332_);
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_a_335_, lean_object* v_x_336_){
_start:
{
if (lean_obj_tag(v_x_336_) == 0)
{
lean_object* v___x_337_; 
v___x_337_ = lean_box(0);
return v___x_337_;
}
else
{
lean_object* v_key_338_; lean_object* v_value_339_; lean_object* v_tail_340_; uint8_t v___x_341_; 
v_key_338_ = lean_ctor_get(v_x_336_, 0);
v_value_339_ = lean_ctor_get(v_x_336_, 1);
v_tail_340_ = lean_ctor_get(v_x_336_, 2);
v___x_341_ = l_Lean_ExprStructEq_beq(v_key_338_, v_a_335_);
if (v___x_341_ == 0)
{
v_x_336_ = v_tail_340_;
goto _start;
}
else
{
lean_object* v___x_343_; 
lean_inc(v_value_339_);
v___x_343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_343_, 0, v_value_339_);
return v___x_343_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_a_344_, lean_object* v_x_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(v_a_344_, v_x_345_);
lean_dec(v_x_345_);
lean_dec_ref(v_a_344_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(lean_object* v_m_347_, lean_object* v_a_348_){
_start:
{
lean_object* v_buckets_349_; lean_object* v___x_350_; uint64_t v___x_351_; uint64_t v___x_352_; uint64_t v___x_353_; uint64_t v_fold_354_; uint64_t v___x_355_; uint64_t v___x_356_; uint64_t v___x_357_; size_t v___x_358_; size_t v___x_359_; size_t v___x_360_; size_t v___x_361_; size_t v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v_buckets_349_ = lean_ctor_get(v_m_347_, 1);
v___x_350_ = lean_array_get_size(v_buckets_349_);
v___x_351_ = l_Lean_ExprStructEq_hash(v_a_348_);
v___x_352_ = 32ULL;
v___x_353_ = lean_uint64_shift_right(v___x_351_, v___x_352_);
v_fold_354_ = lean_uint64_xor(v___x_351_, v___x_353_);
v___x_355_ = 16ULL;
v___x_356_ = lean_uint64_shift_right(v_fold_354_, v___x_355_);
v___x_357_ = lean_uint64_xor(v_fold_354_, v___x_356_);
v___x_358_ = lean_uint64_to_usize(v___x_357_);
v___x_359_ = lean_usize_of_nat(v___x_350_);
v___x_360_ = ((size_t)1ULL);
v___x_361_ = lean_usize_sub(v___x_359_, v___x_360_);
v___x_362_ = lean_usize_land(v___x_358_, v___x_361_);
v___x_363_ = lean_array_uget_borrowed(v_buckets_349_, v___x_362_);
v___x_364_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(v_a_348_, v___x_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_365_, lean_object* v_a_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(v_m_365_, v_a_366_);
lean_dec_ref(v_a_366_);
lean_dec_ref(v_m_365_);
return v_res_367_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0(void){
_start:
{
lean_object* v___x_369_; lean_object* v_dummy_370_; 
v___x_369_ = lean_box(0);
v_dummy_370_ = l_Lean_Expr_sort___override(v___x_369_);
return v_dummy_370_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1(lean_object* v_pre_371_, lean_object* v_post_372_, size_t v_sz_373_, size_t v_i_374_, lean_object* v_bs_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
uint8_t v___x_380_; 
v___x_380_ = lean_usize_dec_lt(v_i_374_, v_sz_373_);
if (v___x_380_ == 0)
{
lean_object* v___x_381_; 
lean_dec_ref(v_post_372_);
lean_dec_ref(v_pre_371_);
v___x_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_381_, 0, v_bs_375_);
return v___x_381_;
}
else
{
lean_object* v_v_382_; lean_object* v___x_383_; 
v_v_382_ = lean_array_uget_borrowed(v_bs_375_, v_i_374_);
lean_inc(v_v_382_);
lean_inc_ref(v_post_372_);
lean_inc_ref(v_pre_371_);
v___x_383_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_371_, v_post_372_, v_v_382_, v___y_376_, v___y_377_, v___y_378_);
if (lean_obj_tag(v___x_383_) == 0)
{
lean_object* v_a_384_; lean_object* v___x_385_; lean_object* v_bs_x27_386_; size_t v___x_387_; size_t v___x_388_; lean_object* v___x_389_; 
v_a_384_ = lean_ctor_get(v___x_383_, 0);
lean_inc(v_a_384_);
lean_dec_ref(v___x_383_);
v___x_385_ = lean_unsigned_to_nat(0u);
v_bs_x27_386_ = lean_array_uset(v_bs_375_, v_i_374_, v___x_385_);
v___x_387_ = ((size_t)1ULL);
v___x_388_ = lean_usize_add(v_i_374_, v___x_387_);
v___x_389_ = lean_array_uset(v_bs_x27_386_, v_i_374_, v_a_384_);
v_i_374_ = v___x_388_;
v_bs_375_ = v___x_389_;
goto _start;
}
else
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_398_; 
lean_dec_ref(v_bs_375_);
lean_dec_ref(v_post_372_);
lean_dec_ref(v_pre_371_);
v_a_391_ = lean_ctor_get(v___x_383_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_398_ == 0)
{
v___x_393_ = v___x_383_;
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_383_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_398_;
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
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_a_391_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4(lean_object* v_pre_399_, lean_object* v_post_400_, lean_object* v_x_401_, lean_object* v_x_402_, lean_object* v_x_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_){
_start:
{
if (lean_obj_tag(v_x_401_) == 5)
{
lean_object* v_fn_408_; lean_object* v_arg_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v_fn_408_ = lean_ctor_get(v_x_401_, 0);
lean_inc_ref(v_fn_408_);
v_arg_409_ = lean_ctor_get(v_x_401_, 1);
lean_inc_ref(v_arg_409_);
lean_dec_ref(v_x_401_);
v___x_410_ = lean_array_set(v_x_402_, v_x_403_, v_arg_409_);
v___x_411_ = lean_unsigned_to_nat(1u);
v___x_412_ = lean_nat_sub(v_x_403_, v___x_411_);
lean_dec(v_x_403_);
v_x_401_ = v_fn_408_;
v_x_402_ = v___x_410_;
v_x_403_ = v___x_412_;
goto _start;
}
else
{
lean_object* v___x_414_; 
lean_dec(v_x_403_);
lean_inc_ref(v_post_400_);
lean_inc_ref(v_pre_399_);
v___x_414_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_399_, v_post_400_, v_x_401_, v___y_404_, v___y_405_, v___y_406_);
if (lean_obj_tag(v___x_414_) == 0)
{
lean_object* v_a_415_; size_t v_sz_416_; size_t v___x_417_; lean_object* v___x_418_; 
v_a_415_ = lean_ctor_get(v___x_414_, 0);
lean_inc(v_a_415_);
lean_dec_ref(v___x_414_);
v_sz_416_ = lean_array_size(v_x_402_);
v___x_417_ = ((size_t)0ULL);
lean_inc_ref(v_post_400_);
lean_inc_ref(v_pre_399_);
v___x_418_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1(v_pre_399_, v_post_400_, v_sz_416_, v___x_417_, v_x_402_, v___y_404_, v___y_405_, v___y_406_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v_a_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v_a_419_ = lean_ctor_get(v___x_418_, 0);
lean_inc(v_a_419_);
lean_dec_ref(v___x_418_);
v___x_420_ = l_Lean_mkAppN(v_a_415_, v_a_419_);
lean_dec(v_a_419_);
v___x_421_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_399_, v_post_400_, v___x_420_, v___y_404_, v___y_405_, v___y_406_);
return v___x_421_;
}
else
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_429_; 
lean_dec(v_a_415_);
lean_dec_ref(v_post_400_);
lean_dec_ref(v_pre_399_);
v_a_422_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_429_ == 0)
{
v___x_424_ = v___x_418_;
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_418_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_427_; 
if (v_isShared_425_ == 0)
{
v___x_427_ = v___x_424_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_a_422_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
else
{
lean_dec_ref(v_x_402_);
lean_dec_ref(v_post_400_);
lean_dec_ref(v_pre_399_);
return v___x_414_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1(lean_object* v___x_430_, lean_object* v_pre_431_, lean_object* v_e_432_, lean_object* v_post_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
lean_object* v___y_439_; lean_object* v___y_440_; uint8_t v___y_441_; lean_object* v___y_442_; lean_object* v___y_443_; lean_object* v___y_444_; lean_object* v___y_445_; uint8_t v___y_446_; lean_object* v___y_456_; uint8_t v___y_457_; lean_object* v___y_458_; lean_object* v___y_459_; lean_object* v___y_460_; uint8_t v___y_461_; lean_object* v___y_469_; lean_object* v___y_470_; uint8_t v___y_471_; lean_object* v___y_472_; lean_object* v___y_473_; uint8_t v___y_474_; lean_object* v___x_481_; 
v___x_481_ = l_Lean_Core_checkSystem(v___x_430_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v___x_482_; 
lean_dec_ref(v___x_481_);
lean_inc_ref(v_pre_431_);
lean_inc(v___y_436_);
lean_inc_ref(v___y_435_);
lean_inc_ref(v_e_432_);
v___x_482_ = lean_apply_4(v_pre_431_, v_e_432_, v___y_435_, v___y_436_, lean_box(0));
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_572_; 
v_a_483_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_572_ == 0)
{
v___x_485_ = v___x_482_;
v_isShared_486_ = v_isSharedCheck_572_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v___x_482_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_572_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___y_488_; 
switch(lean_obj_tag(v_a_483_))
{
case 0:
{
lean_object* v_e_562_; lean_object* v___x_564_; 
lean_dec_ref(v_post_433_);
lean_dec_ref(v_e_432_);
lean_dec_ref(v_pre_431_);
v_e_562_ = lean_ctor_get(v_a_483_, 0);
lean_inc_ref(v_e_562_);
lean_dec_ref(v_a_483_);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 0, v_e_562_);
v___x_564_ = v___x_485_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_e_562_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
case 1:
{
lean_object* v_e_566_; lean_object* v___x_567_; 
lean_del_object(v___x_485_);
lean_dec_ref(v_e_432_);
v_e_566_ = lean_ctor_get(v_a_483_, 0);
lean_inc_ref(v_e_566_);
lean_dec_ref(v_a_483_);
lean_inc_ref(v_post_433_);
lean_inc_ref(v_pre_431_);
v___x_567_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_431_, v_post_433_, v_e_566_, v___y_434_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_567_) == 0)
{
lean_object* v_a_568_; lean_object* v___x_569_; 
v_a_568_ = lean_ctor_get(v___x_567_, 0);
lean_inc(v_a_568_);
lean_dec_ref(v___x_567_);
v___x_569_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_431_, v_post_433_, v_a_568_, v___y_434_, v___y_435_, v___y_436_);
return v___x_569_;
}
else
{
lean_dec_ref(v_post_433_);
lean_dec_ref(v_pre_431_);
return v___x_567_;
}
}
default: 
{
lean_object* v_e_x3f_570_; 
lean_del_object(v___x_485_);
v_e_x3f_570_ = lean_ctor_get(v_a_483_, 0);
lean_inc(v_e_x3f_570_);
lean_dec_ref(v_a_483_);
if (lean_obj_tag(v_e_x3f_570_) == 0)
{
v___y_488_ = v_e_432_;
goto v___jp_487_;
}
else
{
lean_object* v_val_571_; 
lean_dec_ref(v_e_432_);
v_val_571_ = lean_ctor_get(v_e_x3f_570_, 0);
lean_inc(v_val_571_);
lean_dec_ref(v_e_x3f_570_);
v___y_488_ = v_val_571_;
goto v___jp_487_;
}
}
}
v___jp_487_:
{
switch(lean_obj_tag(v___y_488_))
{
case 7:
{
lean_object* v_binderName_489_; lean_object* v_binderType_490_; lean_object* v_body_491_; uint8_t v_binderInfo_492_; lean_object* v___x_493_; 
v_binderName_489_ = lean_ctor_get(v___y_488_, 0);
lean_inc(v_binderName_489_);
v_binderType_490_ = lean_ctor_get(v___y_488_, 1);
v_body_491_ = lean_ctor_get(v___y_488_, 2);
v_binderInfo_492_ = lean_ctor_get_uint8(v___y_488_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_490_);
lean_inc_ref(v_post_433_);
lean_inc_ref(v_pre_431_);
v___x_493_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_431_, v_post_433_, v_binderType_490_, v___y_434_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_a_494_; lean_object* v___x_495_; 
v_a_494_ = lean_ctor_get(v___x_493_, 0);
lean_inc(v_a_494_);
lean_dec_ref(v___x_493_);
lean_inc_ref(v_body_491_);
lean_inc_ref(v_post_433_);
lean_inc_ref(v_pre_431_);
v___x_495_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_431_, v_post_433_, v_body_491_, v___y_434_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v_a_496_; size_t v___x_497_; size_t v___x_498_; uint8_t v___x_499_; 
v_a_496_ = lean_ctor_get(v___x_495_, 0);
lean_inc(v_a_496_);
lean_dec_ref(v___x_495_);
v___x_497_ = lean_ptr_addr(v_binderType_490_);
v___x_498_ = lean_ptr_addr(v_a_494_);
v___x_499_ = lean_usize_dec_eq(v___x_497_, v___x_498_);
if (v___x_499_ == 0)
{
v___y_469_ = v_a_496_;
v___y_470_ = v_binderName_489_;
v___y_471_ = v_binderInfo_492_;
v___y_472_ = v___y_488_;
v___y_473_ = v_a_494_;
v___y_474_ = v___x_499_;
goto v___jp_468_;
}
else
{
size_t v___x_500_; size_t v___x_501_; uint8_t v___x_502_; 
v___x_500_ = lean_ptr_addr(v_body_491_);
v___x_501_ = lean_ptr_addr(v_a_496_);
v___x_502_ = lean_usize_dec_eq(v___x_500_, v___x_501_);
v___y_469_ = v_a_496_;
v___y_470_ = v_binderName_489_;
v___y_471_ = v_binderInfo_492_;
v___y_472_ = v___y_488_;
v___y_473_ = v_a_494_;
v___y_474_ = v___x_502_;
goto v___jp_468_;
}
}
else
{
lean_dec(v_a_494_);
lean_dec_ref(v___y_488_);
lean_dec(v_binderName_489_);
lean_dec_ref(v_post_433_);
lean_dec_ref(v_pre_431_);
return v___x_495_;
}
}
else
{
lean_dec_ref(v___y_488_);
lean_dec(v_binderName_489_);
lean_dec_ref(v_post_433_);
lean_dec_ref(v_pre_431_);
return v___x_493_;
}
}
case 6:
{
lean_object* v_binderName_503_; lean_object* v_binderType_504_; lean_object* v_body_505_; uint8_t v_binderInfo_506_; lean_object* v___x_507_; 
v_binderName_503_ = lean_ctor_get(v___y_488_, 0);
lean_inc(v_binderName_503_);
v_binderType_504_ = lean_ctor_get(v___y_488_, 1);
v_body_505_ = lean_ctor_get(v___y_488_, 2);
v_binderInfo_506_ = lean_ctor_get_uint8(v___y_488_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_504_);
lean_inc_ref(v_post_433_);
lean_inc_ref(v_pre_431_);
v___x_507_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_431_, v_post_433_, v_binderType_504_, v___y_434_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_507_) == 0)
{
lean_object* v_a_508_; lean_object* v___x_509_; 
v_a_508_ = lean_ctor_get(v___x_507_, 0);
lean_inc(v_a_508_);
lean_dec_ref(v___x_507_);
lean_inc_ref(v_body_505_);
lean_inc_ref(v_post_433_);
lean_inc_ref(v_pre_431_);
v___x_509_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_431_, v_post_433_, v_body_505_, v___y_434_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v_a_510_; size_t v___x_511_; size_t v___x_512_; uint8_t v___x_513_; 
v_a_510_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_a_510_);
lean_dec_ref(v___x_509_);
v___x_511_ = lean_ptr_addr(v_binderType_504_);
v___x_512_ = lean_ptr_addr(v_a_508_);
v___x_513_ = lean_usize_dec_eq(v___x_511_, v___x_512_);
if (v___x_513_ == 0)
{
v___y_456_ = v_a_510_;
v___y_457_ = v_binderInfo_506_;
v___y_458_ = v_a_508_;
v___y_459_ = v___y_488_;
v___y_460_ = v_binderName_503_;
v___y_461_ = v___x_513_;
goto v___jp_455_;
}
else
{
size_t v___x_514_; size_t v___x_515_; uint8_t v___x_516_; 
v___x_514_ = lean_ptr_addr(v_body_505_);
v___x_515_ = lean_ptr_addr(v_a_510_);
v___x_516_ = lean_usize_dec_eq(v___x_514_, v___x_515_);
v___y_456_ = v_a_510_;
v___y_457_ = v_binderInfo_506_;
v___y_458_ = v_a_508_;
v___y_459_ = v___y_488_;
v___y_460_ = v_binderName_503_;
v___y_461_ = v___x_516_;
goto v___jp_455_;
}
}
else
{
lean_dec(v_a_508_);
lean_dec(v_binderName_503_);
lean_dec_ref(v___y_488_);
lean_dec_ref(v_post_433_);
lean_dec_ref(v_pre_431_);
return v___x_509_;
}
}
else
{
lean_dec_ref(v___y_488_);
lean_dec(v_binderName_503_);
lean_dec_ref(v_post_433_);
lean_dec_ref(v_pre_431_);
return v___x_507_;
}
}
case 8:
{
lean_object* v_declName_517_; lean_object* v_type_518_; lean_object* v_value_519_; lean_object* v_body_520_; uint8_t v_nondep_521_; lean_object* v___x_522_; 
v_declName_517_ = lean_ctor_get(v___y_488_, 0);
lean_inc(v_declName_517_);
v_type_518_ = lean_ctor_get(v___y_488_, 1);
v_value_519_ = lean_ctor_get(v___y_488_, 2);
v_body_520_ = lean_ctor_get(v___y_488_, 3);
lean_inc_ref(v_body_520_);
v_nondep_521_ = lean_ctor_get_uint8(v___y_488_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_518_);
lean_inc_ref(v_post_433_);
lean_inc_ref(v_pre_431_);
v___x_522_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_431_, v_post_433_, v_type_518_, v___y_434_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v_a_523_; lean_object* v___x_524_; 
v_a_523_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_a_523_);
lean_dec_ref(v___x_522_);
lean_inc_ref(v_value_519_);
lean_inc_ref(v_post_433_);
lean_inc_ref(v_pre_431_);
v___x_524_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_431_, v_post_433_, v_value_519_, v___y_434_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_object* v_a_525_; lean_object* v___x_526_; 
v_a_525_ = lean_ctor_get(v___x_524_, 0);
lean_inc(v_a_525_);
lean_dec_ref(v___x_524_);
lean_inc_ref(v_body_520_);
lean_inc_ref(v_post_433_);
lean_inc_ref(v_pre_431_);
v___x_526_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_431_, v_post_433_, v_body_520_, v___y_434_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_object* v_a_527_; size_t v___x_528_; size_t v___x_529_; uint8_t v___x_530_; 
v_a_527_ = lean_ctor_get(v___x_526_, 0);
lean_inc(v_a_527_);
lean_dec_ref(v___x_526_);
v___x_528_ = lean_ptr_addr(v_type_518_);
v___x_529_ = lean_ptr_addr(v_a_523_);
v___x_530_ = lean_usize_dec_eq(v___x_528_, v___x_529_);
if (v___x_530_ == 0)
{
v___y_439_ = v_a_527_;
v___y_440_ = v_declName_517_;
v___y_441_ = v_nondep_521_;
v___y_442_ = v_a_523_;
v___y_443_ = v___y_488_;
v___y_444_ = v_body_520_;
v___y_445_ = v_a_525_;
v___y_446_ = v___x_530_;
goto v___jp_438_;
}
else
{
size_t v___x_531_; size_t v___x_532_; uint8_t v___x_533_; 
v___x_531_ = lean_ptr_addr(v_value_519_);
v___x_532_ = lean_ptr_addr(v_a_525_);
v___x_533_ = lean_usize_dec_eq(v___x_531_, v___x_532_);
v___y_439_ = v_a_527_;
v___y_440_ = v_declName_517_;
v___y_441_ = v_nondep_521_;
v___y_442_ = v_a_523_;
v___y_443_ = v___y_488_;
v___y_444_ = v_body_520_;
v___y_445_ = v_a_525_;
v___y_446_ = v___x_533_;
goto v___jp_438_;
}
}
else
{
lean_dec(v_a_525_);
lean_dec(v_a_523_);
lean_dec_ref(v_body_520_);
lean_dec_ref(v___y_488_);
lean_dec(v_declName_517_);
lean_dec_ref(v_post_433_);
lean_dec_ref(v_pre_431_);
return v___x_526_;
}
}
else
{
lean_dec(v_a_523_);
lean_dec_ref(v_body_520_);
lean_dec(v_declName_517_);
lean_dec_ref(v___y_488_);
lean_dec_ref(v_post_433_);
lean_dec_ref(v_pre_431_);
return v___x_524_;
}
}
else
{
lean_dec_ref(v_body_520_);
lean_dec(v_declName_517_);
lean_dec_ref(v___y_488_);
lean_dec_ref(v_post_433_);
lean_dec_ref(v_pre_431_);
return v___x_522_;
}
}
case 5:
{
lean_object* v_dummy_534_; lean_object* v_nargs_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v_dummy_534_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0);
v_nargs_535_ = l_Lean_Expr_getAppNumArgs(v___y_488_);
lean_inc(v_nargs_535_);
v___x_536_ = lean_mk_array(v_nargs_535_, v_dummy_534_);
v___x_537_ = lean_unsigned_to_nat(1u);
v___x_538_ = lean_nat_sub(v_nargs_535_, v___x_537_);
lean_dec(v_nargs_535_);
v___x_539_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4(v_pre_431_, v_post_433_, v___y_488_, v___x_536_, v___x_538_, v___y_434_, v___y_435_, v___y_436_);
return v___x_539_;
}
case 10:
{
lean_object* v_data_540_; lean_object* v_expr_541_; lean_object* v___x_542_; 
v_data_540_ = lean_ctor_get(v___y_488_, 0);
v_expr_541_ = lean_ctor_get(v___y_488_, 1);
lean_inc_ref(v_expr_541_);
lean_inc_ref(v_post_433_);
lean_inc_ref(v_pre_431_);
v___x_542_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_431_, v_post_433_, v_expr_541_, v___y_434_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_542_) == 0)
{
lean_object* v_a_543_; size_t v___x_544_; size_t v___x_545_; uint8_t v___x_546_; 
v_a_543_ = lean_ctor_get(v___x_542_, 0);
lean_inc(v_a_543_);
lean_dec_ref(v___x_542_);
v___x_544_ = lean_ptr_addr(v_expr_541_);
v___x_545_ = lean_ptr_addr(v_a_543_);
v___x_546_ = lean_usize_dec_eq(v___x_544_, v___x_545_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; lean_object* v___x_548_; 
lean_inc(v_data_540_);
lean_dec_ref(v___y_488_);
v___x_547_ = l_Lean_Expr_mdata___override(v_data_540_, v_a_543_);
v___x_548_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_431_, v_post_433_, v___x_547_, v___y_434_, v___y_435_, v___y_436_);
return v___x_548_;
}
else
{
lean_object* v___x_549_; 
lean_dec(v_a_543_);
v___x_549_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_431_, v_post_433_, v___y_488_, v___y_434_, v___y_435_, v___y_436_);
return v___x_549_;
}
}
else
{
lean_dec_ref(v___y_488_);
lean_dec_ref(v_post_433_);
lean_dec_ref(v_pre_431_);
return v___x_542_;
}
}
case 11:
{
lean_object* v_typeName_550_; lean_object* v_idx_551_; lean_object* v_struct_552_; lean_object* v___x_553_; 
v_typeName_550_ = lean_ctor_get(v___y_488_, 0);
v_idx_551_ = lean_ctor_get(v___y_488_, 1);
v_struct_552_ = lean_ctor_get(v___y_488_, 2);
lean_inc_ref(v_struct_552_);
lean_inc_ref(v_post_433_);
lean_inc_ref(v_pre_431_);
v___x_553_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_431_, v_post_433_, v_struct_552_, v___y_434_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v_a_554_; size_t v___x_555_; size_t v___x_556_; uint8_t v___x_557_; 
v_a_554_ = lean_ctor_get(v___x_553_, 0);
lean_inc(v_a_554_);
lean_dec_ref(v___x_553_);
v___x_555_ = lean_ptr_addr(v_struct_552_);
v___x_556_ = lean_ptr_addr(v_a_554_);
v___x_557_ = lean_usize_dec_eq(v___x_555_, v___x_556_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; lean_object* v___x_559_; 
lean_inc(v_idx_551_);
lean_inc(v_typeName_550_);
lean_dec_ref(v___y_488_);
v___x_558_ = l_Lean_Expr_proj___override(v_typeName_550_, v_idx_551_, v_a_554_);
v___x_559_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_431_, v_post_433_, v___x_558_, v___y_434_, v___y_435_, v___y_436_);
return v___x_559_;
}
else
{
lean_object* v___x_560_; 
lean_dec(v_a_554_);
v___x_560_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_431_, v_post_433_, v___y_488_, v___y_434_, v___y_435_, v___y_436_);
return v___x_560_;
}
}
else
{
lean_dec_ref(v___y_488_);
lean_dec_ref(v_post_433_);
lean_dec_ref(v_pre_431_);
return v___x_553_;
}
}
default: 
{
lean_object* v___x_561_; 
v___x_561_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_431_, v_post_433_, v___y_488_, v___y_434_, v___y_435_, v___y_436_);
return v___x_561_;
}
}
}
}
}
else
{
lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_580_; 
lean_dec_ref(v_post_433_);
lean_dec_ref(v_e_432_);
lean_dec_ref(v_pre_431_);
v_a_573_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_580_ == 0)
{
v___x_575_ = v___x_482_;
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_dec(v___x_482_);
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
else
{
lean_object* v_a_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_588_; 
lean_dec_ref(v_post_433_);
lean_dec_ref(v_e_432_);
lean_dec_ref(v_pre_431_);
v_a_581_ = lean_ctor_get(v___x_481_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_588_ == 0)
{
v___x_583_ = v___x_481_;
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_a_581_);
lean_dec(v___x_481_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_586_; 
if (v_isShared_584_ == 0)
{
v___x_586_ = v___x_583_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_a_581_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
v___jp_438_:
{
if (v___y_446_ == 0)
{
lean_object* v___x_447_; lean_object* v___x_448_; 
lean_dec_ref(v___y_444_);
lean_dec_ref(v___y_443_);
v___x_447_ = l_Lean_Expr_letE___override(v___y_440_, v___y_442_, v___y_445_, v___y_439_, v___y_441_);
v___x_448_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_431_, v_post_433_, v___x_447_, v___y_434_, v___y_435_, v___y_436_);
return v___x_448_;
}
else
{
size_t v___x_449_; size_t v___x_450_; uint8_t v___x_451_; 
v___x_449_ = lean_ptr_addr(v___y_444_);
lean_dec_ref(v___y_444_);
v___x_450_ = lean_ptr_addr(v___y_439_);
v___x_451_ = lean_usize_dec_eq(v___x_449_, v___x_450_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; lean_object* v___x_453_; 
lean_dec_ref(v___y_443_);
v___x_452_ = l_Lean_Expr_letE___override(v___y_440_, v___y_442_, v___y_445_, v___y_439_, v___y_441_);
v___x_453_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_431_, v_post_433_, v___x_452_, v___y_434_, v___y_435_, v___y_436_);
return v___x_453_;
}
else
{
lean_object* v___x_454_; 
lean_dec_ref(v___y_445_);
lean_dec_ref(v___y_442_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
v___x_454_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_431_, v_post_433_, v___y_443_, v___y_434_, v___y_435_, v___y_436_);
return v___x_454_;
}
}
}
v___jp_455_:
{
if (v___y_461_ == 0)
{
lean_object* v___x_462_; lean_object* v___x_463_; 
lean_dec_ref(v___y_459_);
v___x_462_ = l_Lean_Expr_lam___override(v___y_460_, v___y_458_, v___y_456_, v___y_457_);
v___x_463_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_431_, v_post_433_, v___x_462_, v___y_434_, v___y_435_, v___y_436_);
return v___x_463_;
}
else
{
uint8_t v___x_464_; 
v___x_464_ = l_Lean_instBEqBinderInfo_beq(v___y_457_, v___y_457_);
if (v___x_464_ == 0)
{
lean_object* v___x_465_; lean_object* v___x_466_; 
lean_dec_ref(v___y_459_);
v___x_465_ = l_Lean_Expr_lam___override(v___y_460_, v___y_458_, v___y_456_, v___y_457_);
v___x_466_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_431_, v_post_433_, v___x_465_, v___y_434_, v___y_435_, v___y_436_);
return v___x_466_;
}
else
{
lean_object* v___x_467_; 
lean_dec(v___y_460_);
lean_dec_ref(v___y_458_);
lean_dec_ref(v___y_456_);
v___x_467_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_431_, v_post_433_, v___y_459_, v___y_434_, v___y_435_, v___y_436_);
return v___x_467_;
}
}
}
v___jp_468_:
{
if (v___y_474_ == 0)
{
lean_object* v___x_475_; lean_object* v___x_476_; 
lean_dec_ref(v___y_472_);
v___x_475_ = l_Lean_Expr_forallE___override(v___y_470_, v___y_473_, v___y_469_, v___y_471_);
v___x_476_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_431_, v_post_433_, v___x_475_, v___y_434_, v___y_435_, v___y_436_);
return v___x_476_;
}
else
{
uint8_t v___x_477_; 
v___x_477_ = l_Lean_instBEqBinderInfo_beq(v___y_471_, v___y_471_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; lean_object* v___x_479_; 
lean_dec_ref(v___y_472_);
v___x_478_ = l_Lean_Expr_forallE___override(v___y_470_, v___y_473_, v___y_469_, v___y_471_);
v___x_479_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_431_, v_post_433_, v___x_478_, v___y_434_, v___y_435_, v___y_436_);
return v___x_479_;
}
else
{
lean_object* v___x_480_; 
lean_dec_ref(v___y_473_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
v___x_480_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_431_, v_post_433_, v___y_472_, v___y_434_, v___y_435_, v___y_436_);
return v___x_480_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___boxed(lean_object* v___x_589_, lean_object* v_pre_590_, lean_object* v_e_591_, lean_object* v_post_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1(v___x_589_, v_pre_590_, v_e_591_, v_post_592_, v___y_593_, v___y_594_, v___y_595_);
lean_dec(v___y_595_);
lean_dec_ref(v___y_594_);
lean_dec(v___y_593_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(lean_object* v_pre_598_, lean_object* v_post_599_, lean_object* v_e_600_, lean_object* v_a_601_, lean_object* v___y_602_, lean_object* v___y_603_){
_start:
{
lean_object* v___x_605_; lean_object* v___x_606_; 
lean_inc(v_a_601_);
v___x_605_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_605_, 0, lean_box(0));
lean_closure_set(v___x_605_, 1, lean_box(0));
lean_closure_set(v___x_605_, 2, v_a_601_);
v___x_606_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(lean_box(0), v___x_605_, v___y_602_, v___y_603_);
if (lean_obj_tag(v___x_606_) == 0)
{
lean_object* v_a_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_638_; 
v_a_607_ = lean_ctor_get(v___x_606_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_638_ == 0)
{
v___x_609_ = v___x_606_;
v_isShared_610_ = v_isSharedCheck_638_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_a_607_);
lean_dec(v___x_606_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_638_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_611_; 
v___x_611_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(v_a_607_, v_e_600_);
lean_dec(v_a_607_);
if (lean_obj_tag(v___x_611_) == 0)
{
lean_object* v___x_612_; lean_object* v___f_613_; lean_object* v___x_614_; 
lean_del_object(v___x_609_);
v___x_612_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___closed__0));
lean_inc_ref(v_e_600_);
v___f_613_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___boxed), 8, 4);
lean_closure_set(v___f_613_, 0, v___x_612_);
lean_closure_set(v___f_613_, 1, v_pre_598_);
lean_closure_set(v___f_613_, 2, v_e_600_);
lean_closure_set(v___f_613_, 3, v_post_599_);
v___x_614_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(v___f_613_, v_a_601_, v___y_602_, v___y_603_);
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v_a_615_; lean_object* v___f_616_; lean_object* v___x_617_; 
v_a_615_ = lean_ctor_get(v___x_614_, 0);
lean_inc_n(v_a_615_, 2);
lean_dec_ref(v___x_614_);
lean_inc(v_a_601_);
v___f_616_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_616_, 0, v_a_601_);
lean_closure_set(v___f_616_, 1, v_e_600_);
lean_closure_set(v___f_616_, 2, v_a_615_);
v___x_617_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(lean_box(0), v___f_616_, v___y_602_, v___y_603_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_624_; 
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_624_ == 0)
{
lean_object* v_unused_625_; 
v_unused_625_ = lean_ctor_get(v___x_617_, 0);
lean_dec(v_unused_625_);
v___x_619_ = v___x_617_;
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
else
{
lean_dec(v___x_617_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_622_; 
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 0, v_a_615_);
v___x_622_ = v___x_619_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_a_615_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
else
{
lean_object* v_a_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_633_; 
lean_dec(v_a_615_);
v_a_626_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_633_ == 0)
{
v___x_628_ = v___x_617_;
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_a_626_);
lean_dec(v___x_617_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_631_; 
if (v_isShared_629_ == 0)
{
v___x_631_ = v___x_628_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_a_626_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
else
{
lean_dec_ref(v_e_600_);
return v___x_614_;
}
}
else
{
lean_object* v_val_634_; lean_object* v___x_636_; 
lean_dec_ref(v_e_600_);
lean_dec_ref(v_post_599_);
lean_dec_ref(v_pre_598_);
v_val_634_ = lean_ctor_get(v___x_611_, 0);
lean_inc(v_val_634_);
lean_dec_ref(v___x_611_);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 0, v_val_634_);
v___x_636_ = v___x_609_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_val_634_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
}
else
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_646_; 
lean_dec_ref(v_e_600_);
lean_dec_ref(v_post_599_);
lean_dec_ref(v_pre_598_);
v_a_639_ = lean_ctor_get(v___x_606_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_646_ == 0)
{
v___x_641_ = v___x_606_;
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_606_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_644_; 
if (v_isShared_642_ == 0)
{
v___x_644_ = v___x_641_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_a_639_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(lean_object* v_pre_647_, lean_object* v_post_648_, lean_object* v_e_649_, lean_object* v_a_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
lean_object* v___x_654_; 
lean_inc_ref(v_post_648_);
lean_inc(v___y_652_);
lean_inc_ref(v___y_651_);
lean_inc_ref(v_e_649_);
v___x_654_ = lean_apply_4(v_post_648_, v_e_649_, v___y_651_, v___y_652_, lean_box(0));
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_673_; 
v_a_655_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_673_ == 0)
{
v___x_657_ = v___x_654_;
v_isShared_658_ = v_isSharedCheck_673_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_654_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_673_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
switch(lean_obj_tag(v_a_655_))
{
case 0:
{
lean_object* v_e_659_; lean_object* v___x_661_; 
lean_dec_ref(v_e_649_);
lean_dec_ref(v_post_648_);
lean_dec_ref(v_pre_647_);
v_e_659_ = lean_ctor_get(v_a_655_, 0);
lean_inc_ref(v_e_659_);
lean_dec_ref(v_a_655_);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 0, v_e_659_);
v___x_661_ = v___x_657_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_e_659_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
case 1:
{
lean_object* v_e_663_; lean_object* v___x_664_; 
lean_del_object(v___x_657_);
lean_dec_ref(v_e_649_);
v_e_663_ = lean_ctor_get(v_a_655_, 0);
lean_inc_ref(v_e_663_);
lean_dec_ref(v_a_655_);
v___x_664_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_647_, v_post_648_, v_e_663_, v_a_650_, v___y_651_, v___y_652_);
return v___x_664_;
}
default: 
{
lean_object* v_e_x3f_665_; 
lean_dec_ref(v_post_648_);
lean_dec_ref(v_pre_647_);
v_e_x3f_665_ = lean_ctor_get(v_a_655_, 0);
lean_inc(v_e_x3f_665_);
lean_dec_ref(v_a_655_);
if (lean_obj_tag(v_e_x3f_665_) == 0)
{
lean_object* v___x_667_; 
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 0, v_e_649_);
v___x_667_ = v___x_657_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_e_649_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
else
{
lean_object* v_val_669_; lean_object* v___x_671_; 
lean_dec_ref(v_e_649_);
v_val_669_ = lean_ctor_get(v_e_x3f_665_, 0);
lean_inc(v_val_669_);
lean_dec_ref(v_e_x3f_665_);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 0, v_val_669_);
v___x_671_ = v___x_657_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_val_669_);
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
}
}
else
{
lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_681_; 
lean_dec_ref(v_e_649_);
lean_dec_ref(v_post_648_);
lean_dec_ref(v_pre_647_);
v_a_674_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_681_ == 0)
{
v___x_676_ = v___x_654_;
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_dec(v___x_654_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_682_, lean_object* v_post_683_, lean_object* v_e_684_, lean_object* v_a_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_682_, v_post_683_, v_e_684_, v_a_685_, v___y_686_, v___y_687_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec(v_a_685_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_690_, lean_object* v_post_691_, lean_object* v_sz_692_, lean_object* v_i_693_, lean_object* v_bs_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_){
_start:
{
size_t v_sz_boxed_699_; size_t v_i_boxed_700_; lean_object* v_res_701_; 
v_sz_boxed_699_ = lean_unbox_usize(v_sz_692_);
lean_dec(v_sz_692_);
v_i_boxed_700_ = lean_unbox_usize(v_i_693_);
lean_dec(v_i_693_);
v_res_701_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1(v_pre_690_, v_post_691_, v_sz_boxed_699_, v_i_boxed_700_, v_bs_694_, v___y_695_, v___y_696_, v___y_697_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec(v___y_695_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_702_, lean_object* v_post_703_, lean_object* v_x_704_, lean_object* v_x_705_, lean_object* v_x_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4(v_pre_702_, v_post_703_, v_x_704_, v_x_705_, v_x_706_, v___y_707_, v___y_708_, v___y_709_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec(v___y_707_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___boxed(lean_object* v_pre_712_, lean_object* v_post_713_, lean_object* v_e_714_, lean_object* v_a_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_712_, v_post_713_, v_e_714_, v_a_715_, v___y_716_, v___y_717_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v_a_715_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(lean_object* v_00_u03b1_720_, lean_object* v_x_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_725_ = lean_apply_1(v_x_721_, lean_box(0));
v___x_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_726_, 0, v___x_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0___boxed(lean_object* v_00_u03b1_727_, lean_object* v_x_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(v_00_u03b1_727_, v_x_728_, v___y_729_, v___y_730_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
return v_res_732_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0(void){
_start:
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_733_ = lean_box(0);
v___x_734_ = lean_unsigned_to_nat(16u);
v___x_735_ = lean_mk_array(v___x_734_, v___x_733_);
return v___x_735_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1(void){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_736_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0);
v___x_737_ = lean_unsigned_to_nat(0u);
v___x_738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_738_, 0, v___x_737_);
lean_ctor_set(v___x_738_, 1, v___x_736_);
return v___x_738_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2(void){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_739_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1, &l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1);
v___x_740_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_740_, 0, lean_box(0));
lean_closure_set(v___x_740_, 1, lean_box(0));
lean_closure_set(v___x_740_, 2, v___x_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0(lean_object* v_input_741_, lean_object* v_pre_742_, lean_object* v_post_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v_a_749_; lean_object* v___x_750_; 
v___x_747_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2);
v___x_748_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(lean_box(0), v___x_747_, v___y_744_, v___y_745_);
v_a_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v_a_749_);
lean_dec_ref(v___x_748_);
v___x_750_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_742_, v_post_743_, v_input_741_, v_a_749_, v___y_744_, v___y_745_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v_a_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_760_; 
v_a_751_ = lean_ctor_get(v___x_750_, 0);
lean_inc(v_a_751_);
lean_dec_ref(v___x_750_);
v___x_752_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_752_, 0, lean_box(0));
lean_closure_set(v___x_752_, 1, lean_box(0));
lean_closure_set(v___x_752_, 2, v_a_749_);
v___x_753_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(lean_box(0), v___x_752_, v___y_744_, v___y_745_);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_760_ == 0)
{
lean_object* v_unused_761_; 
v_unused_761_ = lean_ctor_get(v___x_753_, 0);
lean_dec(v_unused_761_);
v___x_755_ = v___x_753_;
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
else
{
lean_dec(v___x_753_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_758_; 
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 0, v_a_751_);
v___x_758_ = v___x_755_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_a_751_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
else
{
lean_dec(v_a_749_);
return v___x_750_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___boxed(lean_object* v_input_762_, lean_object* v_pre_763_, lean_object* v_post_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0(v_input_762_, v_pre_763_, v_post_764_, v___y_765_, v___y_766_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam(lean_object* v_type_771_, lean_object* v_a_772_, lean_object* v_a_773_){
_start:
{
lean_object* v___f_775_; lean_object* v___f_776_; lean_object* v___x_777_; 
v___f_775_ = ((lean_object*)(l_Lean_Meta_elimOptParam___closed__0));
v___f_776_ = ((lean_object*)(l_Lean_Meta_elimOptParam___closed__1));
v___x_777_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0(v_type_771_, v___f_775_, v___f_776_, v_a_772_, v_a_773_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam___boxed(lean_object* v_type_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Lean_Meta_elimOptParam(v_type_778_, v_a_779_, v_a_780_);
lean_dec(v_a_780_);
lean_dec_ref(v_a_779_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_783_, lean_object* v_m_784_, lean_object* v_a_785_){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(v_m_784_, v_a_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_787_, lean_object* v_m_788_, lean_object* v_a_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(v_00_u03b2_787_, v_m_788_, v_a_789_);
lean_dec_ref(v_a_789_);
lean_dec_ref(v_m_788_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_791_, lean_object* v_ref_792_, lean_object* v___y_793_, lean_object* v___y_794_){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_792_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_797_, lean_object* v_ref_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_797_, v_ref_798_, v___y_799_, v___y_800_);
lean_dec(v___y_800_);
lean_dec_ref(v___y_799_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8(lean_object* v_00_u03b1_803_, lean_object* v___y_804_, lean_object* v___y_805_){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg();
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___boxed(lean_object* v_00_u03b1_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_808_, v___y_809_, v___y_810_);
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_813_, lean_object* v_x_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
lean_object* v___x_819_; 
v___x_819_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(v_x_814_, v___y_815_, v___y_816_, v___y_817_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_820_, lean_object* v_x_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5(v_00_u03b1_820_, v_x_821_, v___y_822_, v___y_823_, v___y_824_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
lean_dec(v___y_822_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_827_, lean_object* v_m_828_, lean_object* v_a_829_, lean_object* v_b_830_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6___redArg(v_m_828_, v_a_829_, v_b_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_832_, lean_object* v_a_833_, lean_object* v_x_834_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(v_a_833_, v_x_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_836_, lean_object* v_a_837_, lean_object* v_x_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_836_, v_a_837_, v_x_838_);
lean_dec(v_x_838_);
lean_dec_ref(v_a_837_);
return v_res_839_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_840_, lean_object* v_a_841_, lean_object* v_x_842_){
_start:
{
uint8_t v___x_843_; 
v___x_843_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___redArg(v_a_841_, v_x_842_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___boxed(lean_object* v_00_u03b2_844_, lean_object* v_a_845_, lean_object* v_x_846_){
_start:
{
uint8_t v_res_847_; lean_object* v_r_848_; 
v_res_847_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_844_, v_a_845_, v_x_846_);
lean_dec(v_x_846_);
lean_dec_ref(v_a_845_);
v_r_848_ = lean_box(v_res_847_);
return v_r_848_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_849_, lean_object* v_data_850_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11___redArg(v_data_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__12(lean_object* v_00_u03b2_852_, lean_object* v_a_853_, lean_object* v_b_854_, lean_object* v_x_855_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__12___redArg(v_a_853_, v_b_854_, v_x_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12(lean_object* v_00_u03b2_857_, lean_object* v_i_858_, lean_object* v_source_859_, lean_object* v_target_860_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v_i_858_, v_source_859_, v_target_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_862_, lean_object* v_x_863_, lean_object* v_x_864_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_x_863_, v_x_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0(uint8_t v_skipIfPropOrEq_866_, lean_object* v_as_867_, size_t v_sz_868_, size_t v_i_869_, lean_object* v_b_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
lean_object* v_a_877_; uint8_t v___x_881_; 
v___x_881_ = lean_usize_dec_lt(v_i_869_, v_sz_868_);
if (v___x_881_ == 0)
{
lean_object* v___x_882_; 
v___x_882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_882_, 0, v_b_870_);
return v___x_882_;
}
else
{
lean_object* v_snd_883_; lean_object* v_fst_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_962_; 
v_snd_883_ = lean_ctor_get(v_b_870_, 1);
v_fst_884_ = lean_ctor_get(v_b_870_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v_b_870_);
if (v_isSharedCheck_962_ == 0)
{
v___x_886_ = v_b_870_;
v_isShared_887_ = v_isSharedCheck_962_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_snd_883_);
lean_inc(v_fst_884_);
lean_dec(v_b_870_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_962_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v_array_888_; lean_object* v_start_889_; lean_object* v_stop_890_; uint8_t v___x_891_; 
v_array_888_ = lean_ctor_get(v_snd_883_, 0);
v_start_889_ = lean_ctor_get(v_snd_883_, 1);
v_stop_890_ = lean_ctor_get(v_snd_883_, 2);
v___x_891_ = lean_nat_dec_lt(v_start_889_, v_stop_890_);
if (v___x_891_ == 0)
{
lean_object* v___x_893_; 
if (v_isShared_887_ == 0)
{
v___x_893_ = v___x_886_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_fst_884_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v_snd_883_);
v___x_893_ = v_reuseFailAlloc_895_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
lean_object* v___x_894_; 
v___x_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_894_, 0, v___x_893_);
return v___x_894_;
}
}
else
{
lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_958_; 
lean_inc(v_stop_890_);
lean_inc(v_start_889_);
lean_inc_ref(v_array_888_);
v_isSharedCheck_958_ = !lean_is_exclusive(v_snd_883_);
if (v_isSharedCheck_958_ == 0)
{
lean_object* v_unused_959_; lean_object* v_unused_960_; lean_object* v_unused_961_; 
v_unused_959_ = lean_ctor_get(v_snd_883_, 2);
lean_dec(v_unused_959_);
v_unused_960_ = lean_ctor_get(v_snd_883_, 1);
lean_dec(v_unused_960_);
v_unused_961_ = lean_ctor_get(v_snd_883_, 0);
lean_dec(v_unused_961_);
v___x_897_ = v_snd_883_;
v_isShared_898_ = v_isSharedCheck_958_;
goto v_resetjp_896_;
}
else
{
lean_dec(v_snd_883_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_958_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v_a_899_; lean_object* v___x_900_; 
v_a_899_ = lean_array_uget_borrowed(v_as_867_, v_i_869_);
lean_inc(v___y_874_);
lean_inc_ref(v___y_873_);
lean_inc(v___y_872_);
lean_inc_ref(v___y_871_);
lean_inc(v_a_899_);
v___x_900_ = lean_infer_type(v_a_899_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
if (lean_obj_tag(v___x_900_) == 0)
{
lean_object* v_a_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_906_; 
v_a_901_ = lean_ctor_get(v___x_900_, 0);
lean_inc(v_a_901_);
lean_dec_ref(v___x_900_);
v___x_902_ = lean_array_fget(v_array_888_, v_start_889_);
v___x_903_ = lean_unsigned_to_nat(1u);
v___x_904_ = lean_nat_add(v_start_889_, v___x_903_);
lean_dec(v_start_889_);
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 1, v___x_904_);
v___x_906_ = v___x_897_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_array_888_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v___x_904_);
lean_ctor_set(v_reuseFailAlloc_949_, 2, v_stop_890_);
v___x_906_ = v_reuseFailAlloc_949_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
if (v_skipIfPropOrEq_866_ == 0)
{
lean_object* v___x_907_; 
lean_dec(v_a_901_);
lean_inc(v_a_899_);
v___x_907_ = l_Lean_Meta_mkEqHEq(v_a_899_, v___x_902_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
if (lean_obj_tag(v___x_907_) == 0)
{
lean_object* v_a_908_; lean_object* v___x_909_; lean_object* v___x_911_; 
v_a_908_ = lean_ctor_get(v___x_907_, 0);
lean_inc(v_a_908_);
lean_dec_ref(v___x_907_);
v___x_909_ = lean_array_push(v_fst_884_, v_a_908_);
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 1, v___x_906_);
lean_ctor_set(v___x_886_, 0, v___x_909_);
v___x_911_ = v___x_886_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v___x_909_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v___x_906_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
v_a_877_ = v___x_911_;
goto v___jp_876_;
}
}
else
{
lean_object* v_a_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_920_; 
lean_dec_ref(v___x_906_);
lean_del_object(v___x_886_);
lean_dec(v_fst_884_);
v_a_913_ = lean_ctor_get(v___x_907_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_920_ == 0)
{
v___x_915_ = v___x_907_;
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_a_913_);
lean_dec(v___x_907_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_918_; 
if (v_isShared_916_ == 0)
{
v___x_918_ = v___x_915_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_a_913_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
else
{
lean_object* v___x_921_; 
v___x_921_ = l_Lean_Meta_isProp(v_a_901_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_object* v_a_922_; uint8_t v___x_927_; 
v_a_922_ = lean_ctor_get(v___x_921_, 0);
lean_inc(v_a_922_);
lean_dec_ref(v___x_921_);
v___x_927_ = lean_unbox(v_a_922_);
lean_dec(v_a_922_);
if (v___x_927_ == 0)
{
uint8_t v___x_928_; 
v___x_928_ = lean_expr_eqv(v_a_899_, v___x_902_);
if (v___x_928_ == 0)
{
lean_object* v___x_929_; 
lean_del_object(v___x_886_);
lean_inc(v_a_899_);
v___x_929_ = l_Lean_Meta_mkEqHEq(v_a_899_, v___x_902_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
if (lean_obj_tag(v___x_929_) == 0)
{
lean_object* v_a_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v_a_930_ = lean_ctor_get(v___x_929_, 0);
lean_inc(v_a_930_);
lean_dec_ref(v___x_929_);
v___x_931_ = lean_array_push(v_fst_884_, v_a_930_);
v___x_932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_931_);
lean_ctor_set(v___x_932_, 1, v___x_906_);
v_a_877_ = v___x_932_;
goto v___jp_876_;
}
else
{
lean_object* v_a_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_940_; 
lean_dec_ref(v___x_906_);
lean_dec(v_fst_884_);
v_a_933_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_940_ == 0)
{
v___x_935_ = v___x_929_;
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_a_933_);
lean_dec(v___x_929_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_938_; 
if (v_isShared_936_ == 0)
{
v___x_938_ = v___x_935_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_a_933_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
}
else
{
lean_dec(v___x_902_);
goto v___jp_923_;
}
}
else
{
lean_dec(v___x_902_);
goto v___jp_923_;
}
v___jp_923_:
{
lean_object* v___x_925_; 
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 1, v___x_906_);
v___x_925_ = v___x_886_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_fst_884_);
lean_ctor_set(v_reuseFailAlloc_926_, 1, v___x_906_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
v_a_877_ = v___x_925_;
goto v___jp_876_;
}
}
}
else
{
lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_948_; 
lean_dec_ref(v___x_906_);
lean_dec(v___x_902_);
lean_del_object(v___x_886_);
lean_dec(v_fst_884_);
v_a_941_ = lean_ctor_get(v___x_921_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_948_ == 0)
{
v___x_943_ = v___x_921_;
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v___x_921_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_946_; 
if (v_isShared_944_ == 0)
{
v___x_946_ = v___x_943_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_a_941_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
}
}
else
{
lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_957_; 
lean_del_object(v___x_897_);
lean_dec(v_stop_890_);
lean_dec(v_start_889_);
lean_dec_ref(v_array_888_);
lean_del_object(v___x_886_);
lean_dec(v_fst_884_);
v_a_950_ = lean_ctor_get(v___x_900_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_957_ == 0)
{
v___x_952_ = v___x_900_;
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v___x_900_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_955_; 
if (v_isShared_953_ == 0)
{
v___x_955_ = v___x_952_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_a_950_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
}
}
}
}
v___jp_876_:
{
size_t v___x_878_; size_t v___x_879_; 
v___x_878_ = ((size_t)1ULL);
v___x_879_ = lean_usize_add(v_i_869_, v___x_878_);
v_i_869_ = v___x_879_;
v_b_870_ = v_a_877_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0___boxed(lean_object* v_skipIfPropOrEq_963_, lean_object* v_as_964_, lean_object* v_sz_965_, lean_object* v_i_966_, lean_object* v_b_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
uint8_t v_skipIfPropOrEq_boxed_973_; size_t v_sz_boxed_974_; size_t v_i_boxed_975_; lean_object* v_res_976_; 
v_skipIfPropOrEq_boxed_973_ = lean_unbox(v_skipIfPropOrEq_963_);
v_sz_boxed_974_ = lean_unbox_usize(v_sz_965_);
lean_dec(v_sz_965_);
v_i_boxed_975_ = lean_unbox_usize(v_i_966_);
lean_dec(v_i_966_);
v_res_976_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0(v_skipIfPropOrEq_boxed_973_, v_as_964_, v_sz_boxed_974_, v_i_boxed_975_, v_b_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec_ref(v_as_964_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(lean_object* v_args1_979_, lean_object* v_args2_980_, uint8_t v_skipIfPropOrEq_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_){
_start:
{
lean_object* v___x_987_; lean_object* v_eqs_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; size_t v_sz_992_; size_t v___x_993_; lean_object* v___x_994_; 
v___x_987_ = lean_unsigned_to_nat(0u);
v_eqs_988_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_989_ = lean_array_get_size(v_args2_980_);
v___x_990_ = l_Array_toSubarray___redArg(v_args2_980_, v___x_987_, v___x_989_);
v___x_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_991_, 0, v_eqs_988_);
lean_ctor_set(v___x_991_, 1, v___x_990_);
v_sz_992_ = lean_array_size(v_args1_979_);
v___x_993_ = ((size_t)0ULL);
v___x_994_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0(v_skipIfPropOrEq_981_, v_args1_979_, v_sz_992_, v___x_993_, v___x_991_, v_a_982_, v_a_983_, v_a_984_, v_a_985_);
if (lean_obj_tag(v___x_994_) == 0)
{
lean_object* v_a_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1003_; 
v_a_995_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_997_ = v___x_994_;
v_isShared_998_ = v_isSharedCheck_1003_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_a_995_);
lean_dec(v___x_994_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1003_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v_fst_999_; lean_object* v___x_1001_; 
v_fst_999_ = lean_ctor_get(v_a_995_, 0);
lean_inc(v_fst_999_);
lean_dec(v_a_995_);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 0, v_fst_999_);
v___x_1001_ = v___x_997_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_fst_999_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
else
{
lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1011_; 
v_a_1004_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1006_ = v___x_994_;
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_994_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1009_; 
if (v_isShared_1007_ == 0)
{
v___x_1009_ = v___x_1006_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_a_1004_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___boxed(lean_object* v_args1_1012_, lean_object* v_args2_1013_, lean_object* v_skipIfPropOrEq_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_){
_start:
{
uint8_t v_skipIfPropOrEq_boxed_1020_; lean_object* v_res_1021_; 
v_skipIfPropOrEq_boxed_1020_ = lean_unbox(v_skipIfPropOrEq_1014_);
v_res_1021_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v_args1_1012_, v_args2_1013_, v_skipIfPropOrEq_boxed_1020_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
lean_dec(v_a_1018_);
lean_dec_ref(v_a_1017_);
lean_dec(v_a_1016_);
lean_dec_ref(v_a_1015_);
lean_dec_ref(v_args1_1012_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0(lean_object* v_k_1022_, lean_object* v_b_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v___x_1029_; 
lean_inc(v___y_1027_);
lean_inc_ref(v___y_1026_);
lean_inc(v___y_1025_);
lean_inc_ref(v___y_1024_);
v___x_1029_ = lean_apply_6(v_k_1022_, v_b_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, lean_box(0));
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0___boxed(lean_object* v_k_1030_, lean_object* v_b_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0(v_k_1030_, v_b_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(lean_object* v_name_1038_, uint8_t v_bi_1039_, lean_object* v_type_1040_, lean_object* v_k_1041_, uint8_t v_kind_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
lean_object* v___f_1048_; lean_object* v___x_1049_; 
v___f_1048_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1048_, 0, v_k_1041_);
v___x_1049_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1038_, v_bi_1039_, v_type_1040_, v___f_1048_, v_kind_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_);
if (lean_obj_tag(v___x_1049_) == 0)
{
lean_object* v_a_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1057_; 
v_a_1050_ = lean_ctor_get(v___x_1049_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1052_ = v___x_1049_;
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_dec(v___x_1049_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1055_; 
if (v_isShared_1053_ == 0)
{
v___x_1055_ = v___x_1052_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_a_1050_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
else
{
lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1065_; 
v_a_1058_ = lean_ctor_get(v___x_1049_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1060_ = v___x_1049_;
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v___x_1049_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1063_; 
if (v_isShared_1061_ == 0)
{
v___x_1063_ = v___x_1060_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_a_1058_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___boxed(lean_object* v_name_1066_, lean_object* v_bi_1067_, lean_object* v_type_1068_, lean_object* v_k_1069_, lean_object* v_kind_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
uint8_t v_bi_boxed_1076_; uint8_t v_kind_boxed_1077_; lean_object* v_res_1078_; 
v_bi_boxed_1076_ = lean_unbox(v_bi_1067_);
v_kind_boxed_1077_ = lean_unbox(v_kind_1070_);
v_res_1078_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_name_1066_, v_bi_boxed_1076_, v_type_1068_, v_k_1069_, v_kind_boxed_1077_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0(lean_object* v_00_u03b1_1079_, lean_object* v_name_1080_, uint8_t v_bi_1081_, lean_object* v_type_1082_, lean_object* v_k_1083_, uint8_t v_kind_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_){
_start:
{
lean_object* v___x_1090_; 
v___x_1090_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_name_1080_, v_bi_1081_, v_type_1082_, v_k_1083_, v_kind_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___boxed(lean_object* v_00_u03b1_1091_, lean_object* v_name_1092_, lean_object* v_bi_1093_, lean_object* v_type_1094_, lean_object* v_k_1095_, lean_object* v_kind_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
uint8_t v_bi_boxed_1102_; uint8_t v_kind_boxed_1103_; lean_object* v_res_1104_; 
v_bi_boxed_1102_ = lean_unbox(v_bi_1093_);
v_kind_boxed_1103_ = lean_unbox(v_kind_1096_);
v_res_1104_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0(v_00_u03b1_1091_, v_name_1092_, v_bi_boxed_1102_, v_type_1094_, v_k_1095_, v_kind_boxed_1103_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(lean_object* v_msgData_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v___x_1111_; lean_object* v_env_1112_; lean_object* v___x_1113_; lean_object* v_mctx_1114_; lean_object* v_lctx_1115_; lean_object* v_options_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1111_ = lean_st_ref_get(v___y_1109_);
v_env_1112_ = lean_ctor_get(v___x_1111_, 0);
lean_inc_ref(v_env_1112_);
lean_dec(v___x_1111_);
v___x_1113_ = lean_st_ref_get(v___y_1107_);
v_mctx_1114_ = lean_ctor_get(v___x_1113_, 0);
lean_inc_ref(v_mctx_1114_);
lean_dec(v___x_1113_);
v_lctx_1115_ = lean_ctor_get(v___y_1106_, 2);
v_options_1116_ = lean_ctor_get(v___y_1108_, 2);
lean_inc_ref(v_options_1116_);
lean_inc_ref(v_lctx_1115_);
v___x_1117_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1117_, 0, v_env_1112_);
lean_ctor_set(v___x_1117_, 1, v_mctx_1114_);
lean_ctor_set(v___x_1117_, 2, v_lctx_1115_);
lean_ctor_set(v___x_1117_, 3, v_options_1116_);
v___x_1118_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1117_);
lean_ctor_set(v___x_1118_, 1, v_msgData_1105_);
v___x_1119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1118_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1___boxed(lean_object* v_msgData_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v_res_1126_; 
v_res_1126_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msgData_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(lean_object* v_msg_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_){
_start:
{
lean_object* v_ref_1133_; lean_object* v___x_1134_; lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1143_; 
v_ref_1133_ = lean_ctor_get(v___y_1130_, 5);
v___x_1134_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msg_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_);
v_a_1135_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1137_ = v___x_1134_;
v_isShared_1138_ = v_isSharedCheck_1143_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1134_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1143_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1139_; lean_object* v___x_1141_; 
lean_inc(v_ref_1133_);
v___x_1139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1139_, 0, v_ref_1133_);
lean_ctor_set(v___x_1139_, 1, v_a_1135_);
if (v_isShared_1138_ == 0)
{
lean_ctor_set_tag(v___x_1137_, 1);
lean_ctor_set(v___x_1137_, 0, v___x_1139_);
v___x_1141_ = v___x_1137_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v___x_1139_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg___boxed(lean_object* v_msg_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v_msg_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0___boxed(lean_object* v_i_1151_, lean_object* v_body_1152_, lean_object* v_args2_1153_, lean_object* v_args2New_1154_, lean_object* v_ctorVal_1155_, lean_object* v_useEq_1156_, lean_object* v_args1_1157_, lean_object* v_resultType_1158_, lean_object* v_k_1159_, lean_object* v_arg2_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
uint8_t v_useEq_boxed_1166_; lean_object* v_res_1167_; 
v_useEq_boxed_1166_ = lean_unbox(v_useEq_1156_);
v_res_1167_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0(v_i_1151_, v_body_1152_, v_args2_1153_, v_args2New_1154_, v_ctorVal_1155_, v_useEq_boxed_1166_, v_args1_1157_, v_resultType_1158_, v_k_1159_, v_arg2_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec_ref(v_body_1152_);
lean_dec(v_i_1151_);
return v_res_1167_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1(void){
_start:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1169_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__0));
v___x_1170_ = l_Lean_stringToMessageData(v___x_1169_);
return v___x_1170_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3(void){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1172_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__2));
v___x_1173_ = l_Lean_stringToMessageData(v___x_1172_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(lean_object* v_ctorVal_1174_, uint8_t v_useEq_1175_, lean_object* v_args1_1176_, lean_object* v_resultType_1177_, lean_object* v_k_1178_, lean_object* v_i_1179_, lean_object* v_type_1180_, lean_object* v_args2_1181_, lean_object* v_args2New_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_){
_start:
{
lean_object* v___x_1188_; uint8_t v___x_1189_; 
v___x_1188_ = lean_array_get_size(v_args1_1176_);
v___x_1189_ = lean_nat_dec_lt(v_i_1179_, v___x_1188_);
if (v___x_1189_ == 0)
{
lean_object* v___x_1190_; 
lean_dec_ref(v_type_1180_);
lean_dec(v_i_1179_);
lean_dec_ref(v_resultType_1177_);
lean_dec_ref(v_args1_1176_);
lean_dec_ref(v_ctorVal_1174_);
lean_inc(v_a_1186_);
lean_inc_ref(v_a_1185_);
lean_inc(v_a_1184_);
lean_inc_ref(v_a_1183_);
v___x_1190_ = lean_apply_7(v_k_1178_, v_args2_1181_, v_args2New_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, lean_box(0));
return v___x_1190_;
}
else
{
lean_object* v___x_1191_; 
lean_inc(v_a_1186_);
lean_inc_ref(v_a_1185_);
lean_inc(v_a_1184_);
lean_inc_ref(v_a_1183_);
v___x_1191_ = lean_whnf(v_type_1180_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v_a_1192_; 
v_a_1192_ = lean_ctor_get(v___x_1191_, 0);
lean_inc(v_a_1192_);
lean_dec_ref(v___x_1191_);
if (lean_obj_tag(v_a_1192_) == 7)
{
lean_object* v_binderName_1193_; lean_object* v_binderType_1194_; lean_object* v_body_1195_; lean_object* v_lctx_1196_; lean_object* v___x_1197_; uint8_t v___x_1198_; 
v_binderName_1193_ = lean_ctor_get(v_a_1192_, 0);
lean_inc(v_binderName_1193_);
v_binderType_1194_ = lean_ctor_get(v_a_1192_, 1);
lean_inc_ref(v_binderType_1194_);
v_body_1195_ = lean_ctor_get(v_a_1192_, 2);
lean_inc_ref(v_body_1195_);
lean_dec_ref(v_a_1192_);
v_lctx_1196_ = lean_ctor_get(v_a_1183_, 2);
v___x_1197_ = lean_array_fget_borrowed(v_args1_1176_, v_i_1179_);
lean_inc(v___x_1197_);
lean_inc_ref(v_lctx_1196_);
v___x_1198_ = l_Lean_Meta_occursOrInType(v_lctx_1196_, v___x_1197_, v_resultType_1177_);
if (v___x_1198_ == 0)
{
lean_object* v___x_1199_; lean_object* v___f_1200_; uint8_t v___y_1202_; 
v___x_1199_ = lean_box(v_useEq_1175_);
v___f_1200_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0___boxed), 15, 9);
lean_closure_set(v___f_1200_, 0, v_i_1179_);
lean_closure_set(v___f_1200_, 1, v_body_1195_);
lean_closure_set(v___f_1200_, 2, v_args2_1181_);
lean_closure_set(v___f_1200_, 3, v_args2New_1182_);
lean_closure_set(v___f_1200_, 4, v_ctorVal_1174_);
lean_closure_set(v___f_1200_, 5, v___x_1199_);
lean_closure_set(v___f_1200_, 6, v_args1_1176_);
lean_closure_set(v___f_1200_, 7, v_resultType_1177_);
lean_closure_set(v___f_1200_, 8, v_k_1178_);
if (v_useEq_1175_ == 0)
{
uint8_t v___x_1205_; 
v___x_1205_ = 1;
v___y_1202_ = v___x_1205_;
goto v___jp_1201_;
}
else
{
uint8_t v___x_1206_; 
v___x_1206_ = 0;
v___y_1202_ = v___x_1206_;
goto v___jp_1201_;
}
v___jp_1201_:
{
uint8_t v___x_1203_; lean_object* v___x_1204_; 
v___x_1203_ = 0;
v___x_1204_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_binderName_1193_, v___y_1202_, v_binderType_1194_, v___f_1200_, v___x_1203_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_);
return v___x_1204_;
}
}
else
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
lean_dec_ref(v_binderType_1194_);
lean_dec(v_binderName_1193_);
v___x_1207_ = lean_unsigned_to_nat(1u);
v___x_1208_ = lean_nat_add(v_i_1179_, v___x_1207_);
lean_dec(v_i_1179_);
v___x_1209_ = lean_expr_instantiate1(v_body_1195_, v___x_1197_);
lean_dec_ref(v_body_1195_);
lean_inc(v___x_1197_);
v___x_1210_ = lean_array_push(v_args2_1181_, v___x_1197_);
v_i_1179_ = v___x_1208_;
v_type_1180_ = v___x_1209_;
v_args2_1181_ = v___x_1210_;
goto _start;
}
}
else
{
lean_object* v_toConstantVal_1212_; lean_object* v_name_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
lean_dec(v_a_1192_);
lean_dec_ref(v_args2New_1182_);
lean_dec_ref(v_args2_1181_);
lean_dec(v_i_1179_);
lean_dec_ref(v_k_1178_);
lean_dec_ref(v_resultType_1177_);
lean_dec_ref(v_args1_1176_);
v_toConstantVal_1212_ = lean_ctor_get(v_ctorVal_1174_, 0);
lean_inc_ref(v_toConstantVal_1212_);
lean_dec_ref(v_ctorVal_1174_);
v_name_1213_ = lean_ctor_get(v_toConstantVal_1212_, 0);
lean_inc(v_name_1213_);
lean_dec_ref(v_toConstantVal_1212_);
v___x_1214_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1);
v___x_1215_ = l_Lean_MessageData_ofName(v_name_1213_);
v___x_1216_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1214_);
lean_ctor_set(v___x_1216_, 1, v___x_1215_);
v___x_1217_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_1218_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1216_);
lean_ctor_set(v___x_1218_, 1, v___x_1217_);
v___x_1219_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_1218_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_);
return v___x_1219_;
}
}
else
{
lean_object* v_a_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1227_; 
lean_dec_ref(v_args2New_1182_);
lean_dec_ref(v_args2_1181_);
lean_dec(v_i_1179_);
lean_dec_ref(v_k_1178_);
lean_dec_ref(v_resultType_1177_);
lean_dec_ref(v_args1_1176_);
lean_dec_ref(v_ctorVal_1174_);
v_a_1220_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1222_ = v___x_1191_;
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_a_1220_);
lean_dec(v___x_1191_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1225_; 
if (v_isShared_1223_ == 0)
{
v___x_1225_ = v___x_1222_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_a_1220_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0(lean_object* v_i_1228_, lean_object* v_body_1229_, lean_object* v_args2_1230_, lean_object* v_args2New_1231_, lean_object* v_ctorVal_1232_, uint8_t v_useEq_1233_, lean_object* v_args1_1234_, lean_object* v_resultType_1235_, lean_object* v_k_1236_, lean_object* v_arg2_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1243_ = lean_unsigned_to_nat(1u);
v___x_1244_ = lean_nat_add(v_i_1228_, v___x_1243_);
v___x_1245_ = lean_expr_instantiate1(v_body_1229_, v_arg2_1237_);
lean_inc_ref(v_arg2_1237_);
v___x_1246_ = lean_array_push(v_args2_1230_, v_arg2_1237_);
v___x_1247_ = lean_array_push(v_args2New_1231_, v_arg2_1237_);
v___x_1248_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(v_ctorVal_1232_, v_useEq_1233_, v_args1_1234_, v_resultType_1235_, v_k_1236_, v___x_1244_, v___x_1245_, v___x_1246_, v___x_1247_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___boxed(lean_object* v_ctorVal_1249_, lean_object* v_useEq_1250_, lean_object* v_args1_1251_, lean_object* v_resultType_1252_, lean_object* v_k_1253_, lean_object* v_i_1254_, lean_object* v_type_1255_, lean_object* v_args2_1256_, lean_object* v_args2New_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_){
_start:
{
uint8_t v_useEq_boxed_1263_; lean_object* v_res_1264_; 
v_useEq_boxed_1263_ = lean_unbox(v_useEq_1250_);
v_res_1264_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(v_ctorVal_1249_, v_useEq_boxed_1263_, v_args1_1251_, v_resultType_1252_, v_k_1253_, v_i_1254_, v_type_1255_, v_args2_1256_, v_args2New_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
lean_dec(v_a_1261_);
lean_dec_ref(v_a_1260_);
lean_dec(v_a_1259_);
lean_dec_ref(v_a_1258_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1(lean_object* v_00_u03b1_1265_, lean_object* v_msg_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
lean_object* v___x_1272_; 
v___x_1272_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v_msg_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___boxed(lean_object* v_00_u03b1_1273_, lean_object* v_msg_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1(v_00_u03b1_1273_, v_msg_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_match__1_splitter___redArg(lean_object* v_____x_1281_, lean_object* v_h__1_1282_, lean_object* v_h__2_1283_){
_start:
{
if (lean_obj_tag(v_____x_1281_) == 7)
{
lean_object* v_binderName_1284_; lean_object* v_binderType_1285_; lean_object* v_body_1286_; uint8_t v_binderInfo_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
lean_dec(v_h__2_1283_);
v_binderName_1284_ = lean_ctor_get(v_____x_1281_, 0);
lean_inc(v_binderName_1284_);
v_binderType_1285_ = lean_ctor_get(v_____x_1281_, 1);
lean_inc_ref(v_binderType_1285_);
v_body_1286_ = lean_ctor_get(v_____x_1281_, 2);
lean_inc_ref(v_body_1286_);
v_binderInfo_1287_ = lean_ctor_get_uint8(v_____x_1281_, sizeof(void*)*3 + 8);
lean_dec_ref(v_____x_1281_);
v___x_1288_ = lean_box(v_binderInfo_1287_);
v___x_1289_ = lean_apply_4(v_h__1_1282_, v_binderName_1284_, v_binderType_1285_, v_body_1286_, v___x_1288_);
return v___x_1289_;
}
else
{
lean_object* v___x_1290_; 
lean_dec(v_h__1_1282_);
v___x_1290_ = lean_apply_2(v_h__2_1283_, v_____x_1281_, lean_box(0));
return v___x_1290_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_match__1_splitter(lean_object* v_motive_1291_, lean_object* v_____x_1292_, lean_object* v_h__1_1293_, lean_object* v_h__2_1294_){
_start:
{
if (lean_obj_tag(v_____x_1292_) == 7)
{
lean_object* v_binderName_1295_; lean_object* v_binderType_1296_; lean_object* v_body_1297_; uint8_t v_binderInfo_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
lean_dec(v_h__2_1294_);
v_binderName_1295_ = lean_ctor_get(v_____x_1292_, 0);
lean_inc(v_binderName_1295_);
v_binderType_1296_ = lean_ctor_get(v_____x_1292_, 1);
lean_inc_ref(v_binderType_1296_);
v_body_1297_ = lean_ctor_get(v_____x_1292_, 2);
lean_inc_ref(v_body_1297_);
v_binderInfo_1298_ = lean_ctor_get_uint8(v_____x_1292_, sizeof(void*)*3 + 8);
lean_dec_ref(v_____x_1292_);
v___x_1299_ = lean_box(v_binderInfo_1298_);
v___x_1300_ = lean_apply_4(v_h__1_1293_, v_binderName_1295_, v_binderType_1296_, v_body_1297_, v___x_1299_);
return v___x_1300_;
}
else
{
lean_object* v___x_1301_; 
lean_dec(v_h__1_1293_);
v___x_1301_ = lean_apply_2(v_h__2_1294_, v_____x_1292_, lean_box(0));
return v___x_1301_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0(lean_object* v_k_1302_, lean_object* v_b_1303_, lean_object* v_c_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
lean_object* v___x_1310_; 
lean_inc(v___y_1308_);
lean_inc_ref(v___y_1307_);
lean_inc(v___y_1306_);
lean_inc_ref(v___y_1305_);
v___x_1310_ = lean_apply_7(v_k_1302_, v_b_1303_, v_c_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, lean_box(0));
return v___x_1310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed(lean_object* v_k_1311_, lean_object* v_b_1312_, lean_object* v_c_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0(v_k_1311_, v_b_1312_, v_c_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(lean_object* v_type_1320_, lean_object* v_k_1321_, uint8_t v_cleanupAnnotations_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v___f_1328_; uint8_t v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___f_1328_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1328_, 0, v_k_1321_);
v___x_1329_ = 0;
v___x_1330_ = lean_box(0);
v___x_1331_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_1329_, v___x_1330_, v_type_1320_, v___f_1328_, v_cleanupAnnotations_1322_, v___x_1329_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_);
if (lean_obj_tag(v___x_1331_) == 0)
{
lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1339_; 
v_a_1332_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1334_ = v___x_1331_;
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v___x_1331_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1339_;
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
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_a_1332_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
else
{
lean_object* v_a_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1347_; 
v_a_1340_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1342_ = v___x_1331_;
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_a_1340_);
lean_dec(v___x_1331_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1347_;
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
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_a_1340_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___boxed(lean_object* v_type_1348_, lean_object* v_k_1349_, lean_object* v_cleanupAnnotations_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1356_; lean_object* v_res_1357_; 
v_cleanupAnnotations_boxed_1356_ = lean_unbox(v_cleanupAnnotations_1350_);
v_res_1357_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_type_1348_, v_k_1349_, v_cleanupAnnotations_boxed_1356_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
lean_dec(v___y_1352_);
lean_dec_ref(v___y_1351_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2(lean_object* v_00_u03b1_1358_, lean_object* v_type_1359_, lean_object* v_k_1360_, uint8_t v_cleanupAnnotations_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
_start:
{
lean_object* v___x_1367_; 
v___x_1367_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_type_1359_, v_k_1360_, v_cleanupAnnotations_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_);
return v___x_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___boxed(lean_object* v_00_u03b1_1368_, lean_object* v_type_1369_, lean_object* v_k_1370_, lean_object* v_cleanupAnnotations_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1377_; lean_object* v_res_1378_; 
v_cleanupAnnotations_boxed_1377_ = lean_unbox(v_cleanupAnnotations_1371_);
v_res_1378_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2(v_00_u03b1_1368_, v_type_1369_, v_k_1370_, v_cleanupAnnotations_boxed_1377_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
lean_dec(v___y_1373_);
lean_dec_ref(v___y_1372_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(lean_object* v_type_1379_, lean_object* v_maxFVars_x3f_1380_, lean_object* v_k_1381_, uint8_t v_cleanupAnnotations_1382_, uint8_t v_whnfType_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_){
_start:
{
lean_object* v___f_1389_; lean_object* v___x_1390_; 
v___f_1389_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1389_, 0, v_k_1381_);
v___x_1390_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_1379_, v_maxFVars_x3f_1380_, v___f_1389_, v_cleanupAnnotations_1382_, v_whnfType_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_);
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_object* v_a_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1398_; 
v_a_1391_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1393_ = v___x_1390_;
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_a_1391_);
lean_dec(v___x_1390_);
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
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1406_; 
v_a_1399_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1401_ = v___x_1390_;
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_a_1399_);
lean_dec(v___x_1390_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1404_; 
if (v_isShared_1402_ == 0)
{
v___x_1404_ = v___x_1401_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_a_1399_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg___boxed(lean_object* v_type_1407_, lean_object* v_maxFVars_x3f_1408_, lean_object* v_k_1409_, lean_object* v_cleanupAnnotations_1410_, lean_object* v_whnfType_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1417_; uint8_t v_whnfType_boxed_1418_; lean_object* v_res_1419_; 
v_cleanupAnnotations_boxed_1417_ = lean_unbox(v_cleanupAnnotations_1410_);
v_whnfType_boxed_1418_ = lean_unbox(v_whnfType_1411_);
v_res_1419_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(v_type_1407_, v_maxFVars_x3f_1408_, v_k_1409_, v_cleanupAnnotations_boxed_1417_, v_whnfType_boxed_1418_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3(lean_object* v_00_u03b1_1420_, lean_object* v_type_1421_, lean_object* v_maxFVars_x3f_1422_, lean_object* v_k_1423_, uint8_t v_cleanupAnnotations_1424_, uint8_t v_whnfType_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v___x_1431_; 
v___x_1431_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(v_type_1421_, v_maxFVars_x3f_1422_, v_k_1423_, v_cleanupAnnotations_1424_, v_whnfType_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___boxed(lean_object* v_00_u03b1_1432_, lean_object* v_type_1433_, lean_object* v_maxFVars_x3f_1434_, lean_object* v_k_1435_, lean_object* v_cleanupAnnotations_1436_, lean_object* v_whnfType_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1443_; uint8_t v_whnfType_boxed_1444_; lean_object* v_res_1445_; 
v_cleanupAnnotations_boxed_1443_ = lean_unbox(v_cleanupAnnotations_1436_);
v_whnfType_boxed_1444_ = lean_unbox(v_whnfType_1437_);
v_res_1445_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3(v_00_u03b1_1432_, v_type_1433_, v_maxFVars_x3f_1434_, v_k_1435_, v_cleanupAnnotations_boxed_1443_, v_whnfType_boxed_1444_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0(lean_object* v_name_1446_, lean_object* v_us_1447_, lean_object* v_params_1448_, lean_object* v_args1_1449_, uint8_t v_useEq_1450_, lean_object* v_args2_1451_, lean_object* v_args2New_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1458_ = l_Lean_mkConst(v_name_1446_, v_us_1447_);
v___x_1459_ = l_Lean_mkAppN(v___x_1458_, v_params_1448_);
lean_inc_ref(v___x_1459_);
v___x_1460_ = l_Lean_mkAppN(v___x_1459_, v_args1_1449_);
v___x_1461_ = l_Lean_mkAppN(v___x_1459_, v_args2_1451_);
v___x_1462_ = l_Lean_Meta_mkEq(v___x_1460_, v___x_1461_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_object* v_a_1463_; uint8_t v___x_1464_; lean_object* v_result_1466_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___x_1511_; 
v_a_1463_ = lean_ctor_get(v___x_1462_, 0);
lean_inc(v_a_1463_);
lean_dec_ref(v___x_1462_);
v___x_1464_ = 1;
v___x_1511_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v_args1_1449_, v_args2_1451_, v___x_1464_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
if (lean_obj_tag(v___x_1511_) == 0)
{
lean_object* v_a_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1543_; 
v_a_1512_ = lean_ctor_get(v___x_1511_, 0);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1514_ = v___x_1511_;
v_isShared_1515_ = v_isSharedCheck_1543_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_a_1512_);
lean_dec(v___x_1511_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1543_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1516_; 
v___x_1516_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f(v_a_1512_);
if (lean_obj_tag(v___x_1516_) == 1)
{
lean_del_object(v___x_1514_);
if (v_useEq_1450_ == 0)
{
lean_object* v_val_1517_; lean_object* v___x_1518_; 
v_val_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_val_1517_);
lean_dec_ref(v___x_1516_);
v___x_1518_ = l_Lean_mkArrow(v_a_1463_, v_val_1517_, v___y_1455_, v___y_1456_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_object* v_a_1519_; 
v_a_1519_ = lean_ctor_get(v___x_1518_, 0);
lean_inc(v_a_1519_);
lean_dec_ref(v___x_1518_);
v_result_1466_ = v_a_1519_;
v___y_1467_ = v___y_1453_;
v___y_1468_ = v___y_1454_;
v___y_1469_ = v___y_1455_;
v___y_1470_ = v___y_1456_;
goto v___jp_1465_;
}
else
{
lean_object* v_a_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1527_; 
v_a_1520_ = lean_ctor_get(v___x_1518_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1522_ = v___x_1518_;
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_a_1520_);
lean_dec(v___x_1518_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1525_; 
if (v_isShared_1523_ == 0)
{
v___x_1525_ = v___x_1522_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_a_1520_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
}
}
else
{
lean_object* v_val_1528_; lean_object* v___x_1529_; 
v_val_1528_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_val_1528_);
lean_dec_ref(v___x_1516_);
v___x_1529_ = l_Lean_Meta_mkEq(v_a_1463_, v_val_1528_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v_a_1530_; 
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_a_1530_);
lean_dec_ref(v___x_1529_);
v_result_1466_ = v_a_1530_;
v___y_1467_ = v___y_1453_;
v___y_1468_ = v___y_1454_;
v___y_1469_ = v___y_1455_;
v___y_1470_ = v___y_1456_;
goto v___jp_1465_;
}
else
{
lean_object* v_a_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1538_; 
v_a_1531_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1533_ = v___x_1529_;
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_a_1531_);
lean_dec(v___x_1529_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1536_; 
if (v_isShared_1534_ == 0)
{
v___x_1536_ = v___x_1533_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_a_1531_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
}
}
else
{
lean_object* v___x_1539_; lean_object* v___x_1541_; 
lean_dec(v___x_1516_);
lean_dec(v_a_1463_);
v___x_1539_ = lean_box(0);
if (v_isShared_1515_ == 0)
{
lean_ctor_set(v___x_1514_, 0, v___x_1539_);
v___x_1541_ = v___x_1514_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v___x_1539_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
}
}
else
{
lean_object* v_a_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1551_; 
lean_dec(v_a_1463_);
v_a_1544_ = lean_ctor_get(v___x_1511_, 0);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1546_ = v___x_1511_;
v_isShared_1547_ = v_isSharedCheck_1551_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_a_1544_);
lean_dec(v___x_1511_);
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
v_reuseFailAlloc_1550_ = lean_alloc_ctor(1, 1, 0);
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
v___jp_1465_:
{
uint8_t v___x_1471_; uint8_t v___x_1472_; lean_object* v___x_1473_; 
v___x_1471_ = 0;
v___x_1472_ = 1;
v___x_1473_ = l_Lean_Meta_mkForallFVars(v_args2New_1452_, v_result_1466_, v___x_1471_, v___x_1464_, v___x_1464_, v___x_1472_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v_a_1474_; lean_object* v___x_1475_; 
v_a_1474_ = lean_ctor_get(v___x_1473_, 0);
lean_inc(v_a_1474_);
lean_dec_ref(v___x_1473_);
v___x_1475_ = l_Lean_Meta_mkForallFVars(v_args1_1449_, v_a_1474_, v___x_1471_, v___x_1464_, v___x_1464_, v___x_1472_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; lean_object* v___x_1477_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
lean_inc(v_a_1476_);
lean_dec_ref(v___x_1475_);
v___x_1477_ = l_Lean_Meta_mkForallFVars(v_params_1448_, v_a_1476_, v___x_1471_, v___x_1464_, v___x_1464_, v___x_1472_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1486_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1480_ = v___x_1477_;
v_isShared_1481_ = v_isSharedCheck_1486_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1477_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1486_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1482_; lean_object* v___x_1484_; 
v___x_1482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1482_, 0, v_a_1478_);
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 0, v___x_1482_);
v___x_1484_ = v___x_1480_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1482_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
else
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1494_; 
v_a_1487_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1489_ = v___x_1477_;
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1477_);
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
lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1502_; 
v_a_1495_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1497_ = v___x_1475_;
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v___x_1475_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1500_; 
if (v_isShared_1498_ == 0)
{
v___x_1500_ = v___x_1497_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_a_1495_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
}
else
{
lean_object* v_a_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1510_; 
v_a_1503_ = lean_ctor_get(v___x_1473_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1505_ = v___x_1473_;
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_a_1503_);
lean_dec(v___x_1473_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1508_; 
if (v_isShared_1506_ == 0)
{
v___x_1508_ = v___x_1505_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_a_1503_);
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
}
else
{
lean_object* v_a_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1559_; 
lean_dec_ref(v_args2_1451_);
v_a_1552_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1554_ = v___x_1462_;
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_a_1552_);
lean_dec(v___x_1462_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0___boxed(lean_object* v_name_1560_, lean_object* v_us_1561_, lean_object* v_params_1562_, lean_object* v_args1_1563_, lean_object* v_useEq_1564_, lean_object* v_args2_1565_, lean_object* v_args2New_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
uint8_t v_useEq_boxed_1572_; lean_object* v_res_1573_; 
v_useEq_boxed_1572_ = lean_unbox(v_useEq_1564_);
v_res_1573_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0(v_name_1560_, v_us_1561_, v_params_1562_, v_args1_1563_, v_useEq_boxed_1572_, v_args2_1565_, v_args2New_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec_ref(v_args2New_1566_);
lean_dec_ref(v_args1_1563_);
lean_dec_ref(v_params_1562_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1(size_t v_sz_1574_, size_t v_i_1575_, lean_object* v_bs_1576_){
_start:
{
uint8_t v___x_1577_; 
v___x_1577_ = lean_usize_dec_lt(v_i_1575_, v_sz_1574_);
if (v___x_1577_ == 0)
{
return v_bs_1576_;
}
else
{
lean_object* v_v_1578_; lean_object* v___x_1579_; lean_object* v_bs_x27_1580_; lean_object* v___x_1581_; uint8_t v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; size_t v___x_1585_; size_t v___x_1586_; lean_object* v___x_1587_; 
v_v_1578_ = lean_array_uget(v_bs_1576_, v_i_1575_);
v___x_1579_ = lean_unsigned_to_nat(0u);
v_bs_x27_1580_ = lean_array_uset(v_bs_1576_, v_i_1575_, v___x_1579_);
v___x_1581_ = l_Lean_Expr_fvarId_x21(v_v_1578_);
lean_dec(v_v_1578_);
v___x_1582_ = 1;
v___x_1583_ = lean_box(v___x_1582_);
v___x_1584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1581_);
lean_ctor_set(v___x_1584_, 1, v___x_1583_);
v___x_1585_ = ((size_t)1ULL);
v___x_1586_ = lean_usize_add(v_i_1575_, v___x_1585_);
v___x_1587_ = lean_array_uset(v_bs_x27_1580_, v_i_1575_, v___x_1584_);
v_i_1575_ = v___x_1586_;
v_bs_1576_ = v___x_1587_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1___boxed(lean_object* v_sz_1589_, lean_object* v_i_1590_, lean_object* v_bs_1591_){
_start:
{
size_t v_sz_boxed_1592_; size_t v_i_boxed_1593_; lean_object* v_res_1594_; 
v_sz_boxed_1592_ = lean_unbox_usize(v_sz_1589_);
lean_dec(v_sz_1589_);
v_i_boxed_1593_ = lean_unbox_usize(v_i_1590_);
lean_dec(v_i_1590_);
v_res_1594_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1(v_sz_boxed_1592_, v_i_boxed_1593_, v_bs_1591_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(lean_object* v_bs_1595_, lean_object* v_k_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_){
_start:
{
lean_object* v___x_1602_; 
v___x_1602_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_box(0), v_bs_1595_, v_k_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_);
if (lean_obj_tag(v___x_1602_) == 0)
{
lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1610_; 
v_a_1603_ = lean_ctor_get(v___x_1602_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1602_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1605_ = v___x_1602_;
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1602_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1608_; 
if (v_isShared_1606_ == 0)
{
v___x_1608_ = v___x_1605_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_a_1603_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
else
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1618_; 
v_a_1611_ = lean_ctor_get(v___x_1602_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1602_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1613_ = v___x_1602_;
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1602_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1616_; 
if (v_isShared_1614_ == 0)
{
v___x_1616_ = v___x_1613_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_a_1611_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_bs_1619_, lean_object* v_k_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(v_bs_1619_, v_k_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec_ref(v_bs_1619_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(lean_object* v_bs_1627_, lean_object* v_k_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
size_t v_sz_1634_; size_t v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
v_sz_1634_ = lean_array_size(v_bs_1627_);
v___x_1635_ = ((size_t)0ULL);
v___x_1636_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1(v_sz_1634_, v___x_1635_, v_bs_1627_);
v___x_1637_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(v___x_1636_, v_k_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
lean_dec_ref(v___x_1636_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg___boxed(lean_object* v_bs_1638_, lean_object* v_k_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_){
_start:
{
lean_object* v_res_1645_; 
v_res_1645_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v_bs_1638_, v_k_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
return v_res_1645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1(lean_object* v_name_1646_, lean_object* v_us_1647_, lean_object* v_params_1648_, uint8_t v_useEq_1649_, lean_object* v_ctorVal_1650_, lean_object* v_type_1651_, lean_object* v_args1_1652_, lean_object* v_resultType_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_){
_start:
{
lean_object* v___x_1659_; lean_object* v___f_1660_; 
v___x_1659_ = lean_box(v_useEq_1649_);
lean_inc_ref(v_args1_1652_);
lean_inc_ref(v_params_1648_);
v___f_1660_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1660_, 0, v_name_1646_);
lean_closure_set(v___f_1660_, 1, v_us_1647_);
lean_closure_set(v___f_1660_, 2, v_params_1648_);
lean_closure_set(v___f_1660_, 3, v_args1_1652_);
lean_closure_set(v___f_1660_, 4, v___x_1659_);
if (v_useEq_1649_ == 0)
{
lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1661_ = l_Array_append___redArg(v_params_1648_, v_args1_1652_);
v___x_1662_ = lean_unsigned_to_nat(0u);
v___x_1663_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_1664_ = lean_box(v_useEq_1649_);
v___x_1665_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___boxed), 14, 9);
lean_closure_set(v___x_1665_, 0, v_ctorVal_1650_);
lean_closure_set(v___x_1665_, 1, v___x_1664_);
lean_closure_set(v___x_1665_, 2, v_args1_1652_);
lean_closure_set(v___x_1665_, 3, v_resultType_1653_);
lean_closure_set(v___x_1665_, 4, v___f_1660_);
lean_closure_set(v___x_1665_, 5, v___x_1662_);
lean_closure_set(v___x_1665_, 6, v_type_1651_);
lean_closure_set(v___x_1665_, 7, v___x_1663_);
lean_closure_set(v___x_1665_, 8, v___x_1663_);
v___x_1666_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v___x_1661_, v___x_1665_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_);
return v___x_1666_;
}
else
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
lean_dec_ref(v_params_1648_);
v___x_1667_ = lean_unsigned_to_nat(0u);
v___x_1668_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_1669_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(v_ctorVal_1650_, v_useEq_1649_, v_args1_1652_, v_resultType_1653_, v___f_1660_, v___x_1667_, v_type_1651_, v___x_1668_, v___x_1668_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_);
return v___x_1669_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1___boxed(lean_object* v_name_1670_, lean_object* v_us_1671_, lean_object* v_params_1672_, lean_object* v_useEq_1673_, lean_object* v_ctorVal_1674_, lean_object* v_type_1675_, lean_object* v_args1_1676_, lean_object* v_resultType_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
uint8_t v_useEq_boxed_1683_; lean_object* v_res_1684_; 
v_useEq_boxed_1683_ = lean_unbox(v_useEq_1673_);
v_res_1684_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1(v_name_1670_, v_us_1671_, v_params_1672_, v_useEq_boxed_1683_, v_ctorVal_1674_, v_type_1675_, v_args1_1676_, v_resultType_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2(lean_object* v_name_1685_, lean_object* v_us_1686_, uint8_t v_useEq_1687_, lean_object* v_ctorVal_1688_, lean_object* v_params_1689_, lean_object* v_type_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v___x_1696_; lean_object* v___f_1697_; uint8_t v___x_1698_; lean_object* v___x_1699_; 
v___x_1696_ = lean_box(v_useEq_1687_);
lean_inc_ref(v_type_1690_);
v___f_1697_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1___boxed), 13, 6);
lean_closure_set(v___f_1697_, 0, v_name_1685_);
lean_closure_set(v___f_1697_, 1, v_us_1686_);
lean_closure_set(v___f_1697_, 2, v_params_1689_);
lean_closure_set(v___f_1697_, 3, v___x_1696_);
lean_closure_set(v___f_1697_, 4, v_ctorVal_1688_);
lean_closure_set(v___f_1697_, 5, v_type_1690_);
v___x_1698_ = 0;
v___x_1699_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_type_1690_, v___f_1697_, v___x_1698_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2___boxed(lean_object* v_name_1700_, lean_object* v_us_1701_, lean_object* v_useEq_1702_, lean_object* v_ctorVal_1703_, lean_object* v_params_1704_, lean_object* v_type_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_){
_start:
{
uint8_t v_useEq_boxed_1711_; lean_object* v_res_1712_; 
v_useEq_boxed_1711_ = lean_unbox(v_useEq_1702_);
v_res_1712_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2(v_name_1700_, v_us_1701_, v_useEq_boxed_1711_, v_ctorVal_1703_, v_params_1704_, v_type_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1708_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(lean_object* v_a_1713_, lean_object* v_a_1714_){
_start:
{
if (lean_obj_tag(v_a_1713_) == 0)
{
lean_object* v___x_1715_; 
v___x_1715_ = l_List_reverse___redArg(v_a_1714_);
return v___x_1715_;
}
else
{
lean_object* v_head_1716_; lean_object* v_tail_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1726_; 
v_head_1716_ = lean_ctor_get(v_a_1713_, 0);
v_tail_1717_ = lean_ctor_get(v_a_1713_, 1);
v_isSharedCheck_1726_ = !lean_is_exclusive(v_a_1713_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1719_ = v_a_1713_;
v_isShared_1720_ = v_isSharedCheck_1726_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_tail_1717_);
lean_inc(v_head_1716_);
lean_dec(v_a_1713_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1726_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1721_; lean_object* v___x_1723_; 
v___x_1721_ = l_Lean_mkLevelParam(v_head_1716_);
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 1, v_a_1714_);
lean_ctor_set(v___x_1719_, 0, v___x_1721_);
v___x_1723_ = v___x_1719_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v___x_1721_);
lean_ctor_set(v_reuseFailAlloc_1725_, 1, v_a_1714_);
v___x_1723_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
v_a_1713_ = v_tail_1717_;
v_a_1714_ = v___x_1723_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(lean_object* v_ctorVal_1727_, uint8_t v_useEq_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_){
_start:
{
lean_object* v_toConstantVal_1734_; lean_object* v_numParams_1735_; lean_object* v_name_1736_; lean_object* v_levelParams_1737_; lean_object* v_type_1738_; lean_object* v___x_1739_; 
v_toConstantVal_1734_ = lean_ctor_get(v_ctorVal_1727_, 0);
v_numParams_1735_ = lean_ctor_get(v_ctorVal_1727_, 3);
lean_inc(v_numParams_1735_);
v_name_1736_ = lean_ctor_get(v_toConstantVal_1734_, 0);
lean_inc(v_name_1736_);
v_levelParams_1737_ = lean_ctor_get(v_toConstantVal_1734_, 1);
v_type_1738_ = lean_ctor_get(v_toConstantVal_1734_, 2);
lean_inc_ref(v_type_1738_);
v___x_1739_ = l_Lean_Meta_elimOptParam(v_type_1738_, v_a_1731_, v_a_1732_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_object* v_a_1740_; lean_object* v___x_1741_; lean_object* v_us_1742_; lean_object* v___x_1743_; lean_object* v___f_1744_; lean_object* v___x_1745_; uint8_t v___x_1746_; lean_object* v___x_1747_; 
v_a_1740_ = lean_ctor_get(v___x_1739_, 0);
lean_inc(v_a_1740_);
lean_dec_ref(v___x_1739_);
v___x_1741_ = lean_box(0);
lean_inc(v_levelParams_1737_);
v_us_1742_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(v_levelParams_1737_, v___x_1741_);
v___x_1743_ = lean_box(v_useEq_1728_);
v___f_1744_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2___boxed), 11, 4);
lean_closure_set(v___f_1744_, 0, v_name_1736_);
lean_closure_set(v___f_1744_, 1, v_us_1742_);
lean_closure_set(v___f_1744_, 2, v___x_1743_);
lean_closure_set(v___f_1744_, 3, v_ctorVal_1727_);
v___x_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1745_, 0, v_numParams_1735_);
v___x_1746_ = 0;
v___x_1747_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(v_a_1740_, v___x_1745_, v___f_1744_, v___x_1746_, v___x_1746_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_);
return v___x_1747_;
}
else
{
lean_object* v_a_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1755_; 
lean_dec(v_name_1736_);
lean_dec(v_numParams_1735_);
lean_dec_ref(v_ctorVal_1727_);
v_a_1748_ = lean_ctor_get(v___x_1739_, 0);
v_isSharedCheck_1755_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1750_ = v___x_1739_;
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_a_1748_);
lean_dec(v___x_1739_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1753_; 
if (v_isShared_1751_ == 0)
{
v___x_1753_ = v___x_1750_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_a_1748_);
v___x_1753_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
return v___x_1753_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___boxed(lean_object* v_ctorVal_1756_, lean_object* v_useEq_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_){
_start:
{
uint8_t v_useEq_boxed_1763_; lean_object* v_res_1764_; 
v_useEq_boxed_1763_ = lean_unbox(v_useEq_1757_);
v_res_1764_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(v_ctorVal_1756_, v_useEq_boxed_1763_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_);
lean_dec(v_a_1761_);
lean_dec_ref(v_a_1760_);
lean_dec(v_a_1759_);
lean_dec_ref(v_a_1758_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2(lean_object* v_00_u03b1_1765_, lean_object* v_bs_1766_, lean_object* v_k_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_){
_start:
{
lean_object* v___x_1773_; 
v___x_1773_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(v_bs_1766_, v_k_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
return v___x_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1774_, lean_object* v_bs_1775_, lean_object* v_k_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_){
_start:
{
lean_object* v_res_1782_; 
v_res_1782_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2(v_00_u03b1_1774_, v_bs_1775_, v_k_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_);
lean_dec(v___y_1780_);
lean_dec_ref(v___y_1779_);
lean_dec(v___y_1778_);
lean_dec_ref(v___y_1777_);
lean_dec_ref(v_bs_1775_);
return v_res_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1(lean_object* v_00_u03b1_1783_, lean_object* v_bs_1784_, lean_object* v_k_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
lean_object* v___x_1791_; 
v___x_1791_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v_bs_1784_, v_k_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_);
return v___x_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___boxed(lean_object* v_00_u03b1_1792_, lean_object* v_bs_1793_, lean_object* v_k_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_){
_start:
{
lean_object* v_res_1800_; 
v_res_1800_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1(v_00_u03b1_1792_, v_bs_1793_, v_k_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_);
lean_dec(v___y_1798_);
lean_dec_ref(v___y_1797_);
lean_dec(v___y_1796_);
lean_dec_ref(v___y_1795_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(lean_object* v_ctorVal_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_){
_start:
{
uint8_t v___x_1807_; lean_object* v___x_1808_; 
v___x_1807_ = 0;
v___x_1808_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(v_ctorVal_1801_, v___x_1807_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_);
return v___x_1808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f___boxed(lean_object* v_ctorVal_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_){
_start:
{
lean_object* v_res_1815_; 
v_res_1815_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
lean_dec(v_a_1813_);
lean_dec_ref(v_a_1812_);
lean_dec(v_a_1811_);
lean_dec_ref(v_a_1810_);
return v_res_1815_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1(void){
_start:
{
lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1817_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__0));
v___x_1818_ = l_Lean_stringToMessageData(v___x_1817_);
return v___x_1818_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3(void){
_start:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1820_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__2));
v___x_1821_ = l_Lean_stringToMessageData(v___x_1820_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(lean_object* v_ctorName_1822_){
_start:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; 
v___x_1823_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1);
v___x_1824_ = l_Lean_MessageData_ofName(v_ctorName_1822_);
v___x_1825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1823_);
lean_ctor_set(v___x_1825_, 1, v___x_1824_);
v___x_1826_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3);
v___x_1827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1825_);
lean_ctor_set(v___x_1827_, 1, v___x_1826_);
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(lean_object* v_ctorName_1828_, lean_object* v_mvarId_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_){
_start:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1835_ = l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(v_ctorName_1828_);
v___x_1836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1836_, 0, v_mvarId_1829_);
v___x_1837_ = l_Lean_indentD(v___x_1836_);
v___x_1838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1835_);
lean_ctor_set(v___x_1838_, 1, v___x_1837_);
v___x_1839_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_1838_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_);
return v___x_1839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg___boxed(lean_object* v_ctorName_1840_, lean_object* v_mvarId_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_){
_start:
{
lean_object* v_res_1847_; 
v_res_1847_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(v_ctorName_1840_, v_mvarId_1841_, v_a_1842_, v_a_1843_, v_a_1844_, v_a_1845_);
lean_dec(v_a_1845_);
lean_dec_ref(v_a_1844_);
lean_dec(v_a_1843_);
lean_dec_ref(v_a_1842_);
return v_res_1847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure(lean_object* v_00_u03b1_1848_, lean_object* v_ctorName_1849_, lean_object* v_mvarId_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_){
_start:
{
lean_object* v___x_1856_; 
v___x_1856_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(v_ctorName_1849_, v_mvarId_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___boxed(lean_object* v_00_u03b1_1857_, lean_object* v_ctorName_1858_, lean_object* v_mvarId_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_){
_start:
{
lean_object* v_res_1865_; 
v_res_1865_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure(v_00_u03b1_1857_, v_ctorName_1858_, v_mvarId_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_);
lean_dec(v_a_1863_);
lean_dec_ref(v_a_1862_);
lean_dec(v_a_1861_);
lean_dec_ref(v_a_1860_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0(lean_object* v_ctorName_1866_, lean_object* v_as_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_){
_start:
{
if (lean_obj_tag(v_as_1867_) == 0)
{
lean_object* v___x_1873_; lean_object* v___x_1874_; 
lean_dec(v_ctorName_1866_);
v___x_1873_ = lean_box(0);
v___x_1874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1873_);
return v___x_1874_;
}
else
{
lean_object* v_head_1875_; lean_object* v_tail_1876_; lean_object* v___x_1877_; 
v_head_1875_ = lean_ctor_get(v_as_1867_, 0);
lean_inc_n(v_head_1875_, 2);
v_tail_1876_ = lean_ctor_get(v_as_1867_, 1);
lean_inc(v_tail_1876_);
lean_dec_ref(v_as_1867_);
v___x_1877_ = l_Lean_MVarId_assumptionCore(v_head_1875_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_);
if (lean_obj_tag(v___x_1877_) == 0)
{
lean_object* v_a_1878_; uint8_t v___x_1879_; 
v_a_1878_ = lean_ctor_get(v___x_1877_, 0);
lean_inc(v_a_1878_);
lean_dec_ref(v___x_1877_);
v___x_1879_ = lean_unbox(v_a_1878_);
lean_dec(v_a_1878_);
if (v___x_1879_ == 0)
{
lean_object* v___x_1880_; 
lean_dec(v_tail_1876_);
v___x_1880_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(v_ctorName_1866_, v_head_1875_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_);
return v___x_1880_;
}
else
{
lean_dec(v_head_1875_);
v_as_1867_ = v_tail_1876_;
goto _start;
}
}
else
{
lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1889_; 
lean_dec(v_tail_1876_);
lean_dec(v_head_1875_);
lean_dec(v_ctorName_1866_);
v_a_1882_ = lean_ctor_get(v___x_1877_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1877_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1884_ = v___x_1877_;
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1877_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1887_; 
if (v_isShared_1885_ == 0)
{
v___x_1887_ = v___x_1884_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_a_1882_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0___boxed(lean_object* v_ctorName_1890_, lean_object* v_as_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_){
_start:
{
lean_object* v_res_1897_; 
v_res_1897_ = l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0(v_ctorName_1890_, v_as_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(lean_object* v_mvarId_1898_, lean_object* v_ctorName_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_){
_start:
{
lean_object* v___x_1905_; 
v___x_1905_ = l_Lean_MVarId_splitAndCore(v_mvarId_1898_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_object* v_a_1906_; lean_object* v___x_1907_; 
v_a_1906_ = lean_ctor_get(v___x_1905_, 0);
lean_inc(v_a_1906_);
lean_dec_ref(v___x_1905_);
v___x_1907_ = l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0(v_ctorName_1899_, v_a_1906_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_);
return v___x_1907_;
}
else
{
lean_object* v_a_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1915_; 
lean_dec(v_ctorName_1899_);
v_a_1908_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1910_ = v___x_1905_;
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_a_1908_);
lean_dec(v___x_1905_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1913_; 
if (v_isShared_1911_ == 0)
{
v___x_1913_ = v___x_1910_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_a_1908_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption___boxed(lean_object* v_mvarId_1916_, lean_object* v_ctorName_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_){
_start:
{
lean_object* v_res_1923_; 
v_res_1923_ = l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(v_mvarId_1916_, v_ctorName_1917_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_);
lean_dec(v_a_1921_);
lean_dec_ref(v_a_1920_);
lean_dec(v_a_1919_);
lean_dec_ref(v_a_1918_);
return v_res_1923_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0(lean_object* v_msg_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
lean_object* v___f_1931_; lean_object* v___x_1016__overap_1932_; lean_object* v___x_1933_; 
v___f_1931_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0___closed__0));
v___x_1016__overap_1932_ = lean_panic_fn_borrowed(v___f_1931_, v_msg_1925_);
lean_inc(v___y_1929_);
lean_inc_ref(v___y_1928_);
lean_inc(v___y_1927_);
lean_inc_ref(v___y_1926_);
v___x_1933_ = lean_apply_5(v___x_1016__overap_1932_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, lean_box(0));
return v___x_1933_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0___boxed(lean_object* v_msg_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_){
_start:
{
lean_object* v_res_1940_; 
v_res_1940_ = l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0(v_msg_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1937_);
lean_dec(v___y_1936_);
lean_dec_ref(v___y_1935_);
return v_res_1940_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1941_; double v___x_1942_; 
v___x_1941_ = lean_unsigned_to_nat(0u);
v___x_1942_ = lean_float_of_nat(v___x_1941_);
return v___x_1942_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(lean_object* v_cls_1946_, lean_object* v_msg_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_){
_start:
{
lean_object* v_ref_1953_; lean_object* v___x_1954_; lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_2000_; 
v_ref_1953_ = lean_ctor_get(v___y_1950_, 5);
v___x_1954_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msg_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
v_a_1955_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1957_ = v___x_1954_;
v_isShared_1958_ = v_isSharedCheck_2000_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1954_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_2000_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1959_; lean_object* v_traceState_1960_; lean_object* v_env_1961_; lean_object* v_nextMacroScope_1962_; lean_object* v_ngen_1963_; lean_object* v_auxDeclNGen_1964_; lean_object* v_cache_1965_; lean_object* v_messages_1966_; lean_object* v_infoState_1967_; lean_object* v_snapshotTasks_1968_; lean_object* v_newDecls_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1999_; 
v___x_1959_ = lean_st_ref_take(v___y_1951_);
v_traceState_1960_ = lean_ctor_get(v___x_1959_, 4);
v_env_1961_ = lean_ctor_get(v___x_1959_, 0);
v_nextMacroScope_1962_ = lean_ctor_get(v___x_1959_, 1);
v_ngen_1963_ = lean_ctor_get(v___x_1959_, 2);
v_auxDeclNGen_1964_ = lean_ctor_get(v___x_1959_, 3);
v_cache_1965_ = lean_ctor_get(v___x_1959_, 5);
v_messages_1966_ = lean_ctor_get(v___x_1959_, 6);
v_infoState_1967_ = lean_ctor_get(v___x_1959_, 7);
v_snapshotTasks_1968_ = lean_ctor_get(v___x_1959_, 8);
v_newDecls_1969_ = lean_ctor_get(v___x_1959_, 9);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1959_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1971_ = v___x_1959_;
v_isShared_1972_ = v_isSharedCheck_1999_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_newDecls_1969_);
lean_inc(v_snapshotTasks_1968_);
lean_inc(v_infoState_1967_);
lean_inc(v_messages_1966_);
lean_inc(v_cache_1965_);
lean_inc(v_traceState_1960_);
lean_inc(v_auxDeclNGen_1964_);
lean_inc(v_ngen_1963_);
lean_inc(v_nextMacroScope_1962_);
lean_inc(v_env_1961_);
lean_dec(v___x_1959_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1999_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
uint64_t v_tid_1973_; lean_object* v_traces_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1998_; 
v_tid_1973_ = lean_ctor_get_uint64(v_traceState_1960_, sizeof(void*)*1);
v_traces_1974_ = lean_ctor_get(v_traceState_1960_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v_traceState_1960_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1976_ = v_traceState_1960_;
v_isShared_1977_ = v_isSharedCheck_1998_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_traces_1974_);
lean_dec(v_traceState_1960_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1998_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1978_; double v___x_1979_; uint8_t v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1988_; 
v___x_1978_ = lean_box(0);
v___x_1979_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0);
v___x_1980_ = 0;
v___x_1981_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_1982_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1982_, 0, v_cls_1946_);
lean_ctor_set(v___x_1982_, 1, v___x_1978_);
lean_ctor_set(v___x_1982_, 2, v___x_1981_);
lean_ctor_set_float(v___x_1982_, sizeof(void*)*3, v___x_1979_);
lean_ctor_set_float(v___x_1982_, sizeof(void*)*3 + 8, v___x_1979_);
lean_ctor_set_uint8(v___x_1982_, sizeof(void*)*3 + 16, v___x_1980_);
v___x_1983_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__2));
v___x_1984_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1982_);
lean_ctor_set(v___x_1984_, 1, v_a_1955_);
lean_ctor_set(v___x_1984_, 2, v___x_1983_);
lean_inc(v_ref_1953_);
v___x_1985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1985_, 0, v_ref_1953_);
lean_ctor_set(v___x_1985_, 1, v___x_1984_);
v___x_1986_ = l_Lean_PersistentArray_push___redArg(v_traces_1974_, v___x_1985_);
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 0, v___x_1986_);
v___x_1988_ = v___x_1976_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v___x_1986_);
lean_ctor_set_uint64(v_reuseFailAlloc_1997_, sizeof(void*)*1, v_tid_1973_);
v___x_1988_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
lean_object* v___x_1990_; 
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 4, v___x_1988_);
v___x_1990_ = v___x_1971_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_env_1961_);
lean_ctor_set(v_reuseFailAlloc_1996_, 1, v_nextMacroScope_1962_);
lean_ctor_set(v_reuseFailAlloc_1996_, 2, v_ngen_1963_);
lean_ctor_set(v_reuseFailAlloc_1996_, 3, v_auxDeclNGen_1964_);
lean_ctor_set(v_reuseFailAlloc_1996_, 4, v___x_1988_);
lean_ctor_set(v_reuseFailAlloc_1996_, 5, v_cache_1965_);
lean_ctor_set(v_reuseFailAlloc_1996_, 6, v_messages_1966_);
lean_ctor_set(v_reuseFailAlloc_1996_, 7, v_infoState_1967_);
lean_ctor_set(v_reuseFailAlloc_1996_, 8, v_snapshotTasks_1968_);
lean_ctor_set(v_reuseFailAlloc_1996_, 9, v_newDecls_1969_);
v___x_1990_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1994_; 
v___x_1991_ = lean_st_ref_set(v___y_1951_, v___x_1990_);
v___x_1992_ = lean_box(0);
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 0, v___x_1992_);
v___x_1994_ = v___x_1957_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v___x_1992_);
v___x_1994_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
return v___x_1994_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___boxed(lean_object* v_cls_2001_, lean_object* v_msg_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_){
_start:
{
lean_object* v_res_2008_; 
v_res_2008_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2001_, v_msg_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_);
lean_dec(v___y_2006_);
lean_dec_ref(v___y_2005_);
lean_dec(v___y_2004_);
lean_dec_ref(v___y_2003_);
return v_res_2008_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3(void){
_start:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; 
v___x_2012_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__2));
v___x_2013_ = lean_unsigned_to_nat(30u);
v___x_2014_ = lean_unsigned_to_nat(96u);
v___x_2015_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__1));
v___x_2016_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__0));
v___x_2017_ = l_mkPanicMessageWithDecl(v___x_2016_, v___x_2015_, v___x_2014_, v___x_2013_, v___x_2012_);
return v___x_2017_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9(void){
_start:
{
lean_object* v_cls_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; 
v_cls_2026_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_2027_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__8));
v___x_2028_ = l_Lean_Name_append(v___x_2027_, v_cls_2026_);
return v___x_2028_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11(void){
_start:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2030_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__10));
v___x_2031_ = l_Lean_stringToMessageData(v___x_2030_);
return v___x_2031_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13(void){
_start:
{
lean_object* v___x_2033_; lean_object* v___x_2034_; 
v___x_2033_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__12));
v___x_2034_ = l_Lean_stringToMessageData(v___x_2033_);
return v___x_2034_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15(void){
_start:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2036_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__14));
v___x_2037_ = l_Lean_stringToMessageData(v___x_2036_);
return v___x_2037_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(lean_object* v_ctorName_2038_, lean_object* v_mvarId_2039_, lean_object* v_h_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_){
_start:
{
lean_object* v___y_2047_; lean_object* v___y_2048_; lean_object* v___y_2049_; lean_object* v___y_2050_; lean_object* v_options_2066_; uint8_t v_hasTrace_2067_; 
v_options_2066_ = lean_ctor_get(v_a_2043_, 2);
v_hasTrace_2067_ = lean_ctor_get_uint8(v_options_2066_, sizeof(void*)*1);
if (v_hasTrace_2067_ == 0)
{
v___y_2047_ = v_a_2041_;
v___y_2048_ = v_a_2042_;
v___y_2049_ = v_a_2043_;
v___y_2050_ = v_a_2044_;
goto v___jp_2046_;
}
else
{
lean_object* v_inheritedTraceOptions_2068_; lean_object* v_cls_2069_; lean_object* v___x_2070_; uint8_t v___x_2071_; 
v_inheritedTraceOptions_2068_ = lean_ctor_get(v_a_2043_, 13);
v_cls_2069_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_2070_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_2071_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2068_, v_options_2066_, v___x_2070_);
if (v___x_2071_ == 0)
{
v___y_2047_ = v_a_2041_;
v___y_2048_ = v_a_2042_;
v___y_2049_ = v_a_2043_;
v___y_2050_ = v_a_2044_;
goto v___jp_2046_;
}
else
{
lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2072_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11);
lean_inc(v_ctorName_2038_);
v___x_2073_ = l_Lean_MessageData_ofName(v_ctorName_2038_);
v___x_2074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2074_, 0, v___x_2072_);
lean_ctor_set(v___x_2074_, 1, v___x_2073_);
v___x_2075_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13);
v___x_2076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2074_);
lean_ctor_set(v___x_2076_, 1, v___x_2075_);
lean_inc(v_h_2040_);
v___x_2077_ = l_Lean_mkFVar(v_h_2040_);
v___x_2078_ = l_Lean_MessageData_ofExpr(v___x_2077_);
v___x_2079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2076_);
lean_ctor_set(v___x_2079_, 1, v___x_2078_);
v___x_2080_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15);
v___x_2081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2079_);
lean_ctor_set(v___x_2081_, 1, v___x_2080_);
lean_inc(v_mvarId_2039_);
v___x_2082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2082_, 0, v_mvarId_2039_);
v___x_2083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2081_);
lean_ctor_set(v___x_2083_, 1, v___x_2082_);
v___x_2084_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2069_, v___x_2083_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_);
if (lean_obj_tag(v___x_2084_) == 0)
{
lean_dec_ref(v___x_2084_);
v___y_2047_ = v_a_2041_;
v___y_2048_ = v_a_2042_;
v___y_2049_ = v_a_2043_;
v___y_2050_ = v_a_2044_;
goto v___jp_2046_;
}
else
{
lean_dec(v_h_2040_);
lean_dec(v_mvarId_2039_);
lean_dec(v_ctorName_2038_);
return v___x_2084_;
}
}
}
v___jp_2046_:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2051_ = lean_box(0);
v___x_2052_ = l_Lean_Meta_injection(v_mvarId_2039_, v_h_2040_, v___x_2051_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_);
if (lean_obj_tag(v___x_2052_) == 0)
{
lean_object* v_a_2053_; 
v_a_2053_ = lean_ctor_get(v___x_2052_, 0);
lean_inc(v_a_2053_);
lean_dec_ref(v___x_2052_);
if (lean_obj_tag(v_a_2053_) == 0)
{
lean_object* v___x_2054_; lean_object* v___x_2055_; 
lean_dec(v_ctorName_2038_);
v___x_2054_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3);
v___x_2055_ = l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0(v___x_2054_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_);
return v___x_2055_;
}
else
{
lean_object* v_mvarId_2056_; lean_object* v___x_2057_; 
v_mvarId_2056_ = lean_ctor_get(v_a_2053_, 0);
lean_inc(v_mvarId_2056_);
lean_dec_ref(v_a_2053_);
v___x_2057_ = l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(v_mvarId_2056_, v_ctorName_2038_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_);
return v___x_2057_;
}
}
else
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2065_; 
lean_dec(v_ctorName_2038_);
v_a_2058_ = lean_ctor_get(v___x_2052_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2052_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2060_ = v___x_2052_;
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_2052_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___boxed(lean_object* v_ctorName_2085_, lean_object* v_mvarId_2086_, lean_object* v_h_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_){
_start:
{
lean_object* v_res_2093_; 
v_res_2093_ = l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(v_ctorName_2085_, v_mvarId_2086_, v_h_2087_, v_a_2088_, v_a_2089_, v_a_2090_, v_a_2091_);
lean_dec(v_a_2091_);
lean_dec_ref(v_a_2090_);
lean_dec(v_a_2089_);
lean_dec_ref(v_a_2088_);
return v_res_2093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(lean_object* v_type_2094_, lean_object* v_k_2095_, uint8_t v_cleanupAnnotations_2096_, uint8_t v_whnfType_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_){
_start:
{
lean_object* v___f_2103_; lean_object* v___x_2104_; 
v___f_2103_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2103_, 0, v_k_2095_);
v___x_2104_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_2094_, v___f_2103_, v_cleanupAnnotations_2096_, v_whnfType_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_);
if (lean_obj_tag(v___x_2104_) == 0)
{
lean_object* v_a_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2112_; 
v_a_2105_ = lean_ctor_get(v___x_2104_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2104_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2107_ = v___x_2104_;
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_a_2105_);
lean_dec(v___x_2104_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2110_; 
if (v_isShared_2108_ == 0)
{
v___x_2110_ = v___x_2107_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_a_2105_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
else
{
lean_object* v_a_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2120_; 
v_a_2113_ = lean_ctor_get(v___x_2104_, 0);
v_isSharedCheck_2120_ = !lean_is_exclusive(v___x_2104_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2115_ = v___x_2104_;
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_a_2113_);
lean_dec(v___x_2104_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2118_; 
if (v_isShared_2116_ == 0)
{
v___x_2118_ = v___x_2115_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v_a_2113_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
return v___x_2118_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg___boxed(lean_object* v_type_2121_, lean_object* v_k_2122_, lean_object* v_cleanupAnnotations_2123_, lean_object* v_whnfType_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2130_; uint8_t v_whnfType_boxed_2131_; lean_object* v_res_2132_; 
v_cleanupAnnotations_boxed_2130_ = lean_unbox(v_cleanupAnnotations_2123_);
v_whnfType_boxed_2131_ = lean_unbox(v_whnfType_2124_);
v_res_2132_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_type_2121_, v_k_2122_, v_cleanupAnnotations_boxed_2130_, v_whnfType_boxed_2131_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
return v_res_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0(lean_object* v_00_u03b1_2133_, lean_object* v_type_2134_, lean_object* v_k_2135_, uint8_t v_cleanupAnnotations_2136_, uint8_t v_whnfType_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_){
_start:
{
lean_object* v___x_2143_; 
v___x_2143_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_type_2134_, v_k_2135_, v_cleanupAnnotations_2136_, v_whnfType_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_);
return v___x_2143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___boxed(lean_object* v_00_u03b1_2144_, lean_object* v_type_2145_, lean_object* v_k_2146_, lean_object* v_cleanupAnnotations_2147_, lean_object* v_whnfType_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2154_; uint8_t v_whnfType_boxed_2155_; lean_object* v_res_2156_; 
v_cleanupAnnotations_boxed_2154_ = lean_unbox(v_cleanupAnnotations_2147_);
v_whnfType_boxed_2155_ = lean_unbox(v_whnfType_2148_);
v_res_2156_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0(v_00_u03b1_2144_, v_type_2145_, v_k_2146_, v_cleanupAnnotations_boxed_2154_, v_whnfType_boxed_2155_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
lean_dec(v___y_2152_);
lean_dec_ref(v___y_2151_);
lean_dec(v___y_2150_);
lean_dec_ref(v___y_2149_);
return v_res_2156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0(lean_object* v___x_2157_, lean_object* v_ctorName_2158_, lean_object* v_xs_2159_, lean_object* v_type_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_){
_start:
{
lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2166_ = lean_box(0);
v___x_2167_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_2160_, v___x_2166_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
if (lean_obj_tag(v___x_2167_) == 0)
{
lean_object* v_a_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
v_a_2168_ = lean_ctor_get(v___x_2167_, 0);
lean_inc(v_a_2168_);
lean_dec_ref(v___x_2167_);
v___x_2169_ = l_Lean_Expr_mvarId_x21(v_a_2168_);
v___x_2170_ = lean_array_get_size(v_xs_2159_);
v___x_2171_ = lean_unsigned_to_nat(1u);
v___x_2172_ = lean_nat_sub(v___x_2170_, v___x_2171_);
v___x_2173_ = lean_array_get_borrowed(v___x_2157_, v_xs_2159_, v___x_2172_);
lean_dec(v___x_2172_);
v___x_2174_ = l_Lean_Expr_fvarId_x21(v___x_2173_);
v___x_2175_ = l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(v_ctorName_2158_, v___x_2169_, v___x_2174_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
if (lean_obj_tag(v___x_2175_) == 0)
{
uint8_t v___x_2176_; uint8_t v___x_2177_; uint8_t v___x_2178_; lean_object* v___x_2179_; 
lean_dec_ref(v___x_2175_);
v___x_2176_ = 0;
v___x_2177_ = 1;
v___x_2178_ = 1;
v___x_2179_ = l_Lean_Meta_mkLambdaFVars(v_xs_2159_, v_a_2168_, v___x_2176_, v___x_2177_, v___x_2176_, v___x_2177_, v___x_2178_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
return v___x_2179_;
}
else
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2187_; 
lean_dec(v_a_2168_);
v_a_2180_ = lean_ctor_get(v___x_2175_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2182_ = v___x_2175_;
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2175_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2185_; 
if (v_isShared_2183_ == 0)
{
v___x_2185_ = v___x_2182_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2180_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
}
else
{
lean_dec(v_ctorName_2158_);
return v___x_2167_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0___boxed(lean_object* v___x_2188_, lean_object* v_ctorName_2189_, lean_object* v_xs_2190_, lean_object* v_type_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_){
_start:
{
lean_object* v_res_2197_; 
v_res_2197_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0(v___x_2188_, v_ctorName_2189_, v_xs_2190_, v_type_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_);
lean_dec(v___y_2195_);
lean_dec_ref(v___y_2194_);
lean_dec(v___y_2193_);
lean_dec_ref(v___y_2192_);
lean_dec_ref(v_xs_2190_);
lean_dec_ref(v___x_2188_);
return v_res_2197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(lean_object* v_ctorName_2198_, lean_object* v_targetType_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_){
_start:
{
lean_object* v___x_2205_; lean_object* v___f_2206_; uint8_t v___x_2207_; lean_object* v___x_2208_; 
v___x_2205_ = l_Lean_instInhabitedExpr;
v___f_2206_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2206_, 0, v___x_2205_);
lean_closure_set(v___f_2206_, 1, v_ctorName_2198_);
v___x_2207_ = 0;
v___x_2208_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_targetType_2199_, v___f_2206_, v___x_2207_, v___x_2207_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_);
return v___x_2208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___boxed(lean_object* v_ctorName_2209_, lean_object* v_targetType_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_){
_start:
{
lean_object* v_res_2216_; 
v_res_2216_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_ctorName_2209_, v_targetType_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_);
lean_dec(v_a_2214_);
lean_dec_ref(v_a_2213_);
lean_dec(v_a_2212_);
lean_dec_ref(v_a_2211_);
return v_res_2216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheoremNameFor(lean_object* v_ctorName_2220_){
_start:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2221_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheoremNameFor___closed__1));
v___x_2222_ = l_Lean_Name_append(v_ctorName_2220_, v___x_2221_);
return v___x_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(lean_object* v_e_2223_, lean_object* v___y_2224_){
_start:
{
uint8_t v___x_2226_; 
v___x_2226_ = l_Lean_Expr_hasMVar(v_e_2223_);
if (v___x_2226_ == 0)
{
lean_object* v___x_2227_; 
v___x_2227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2227_, 0, v_e_2223_);
return v___x_2227_;
}
else
{
lean_object* v___x_2228_; lean_object* v_mctx_2229_; lean_object* v___x_2230_; lean_object* v_fst_2231_; lean_object* v_snd_2232_; lean_object* v___x_2233_; lean_object* v_cache_2234_; lean_object* v_zetaDeltaFVarIds_2235_; lean_object* v_postponed_2236_; lean_object* v_diag_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2246_; 
v___x_2228_ = lean_st_ref_get(v___y_2224_);
v_mctx_2229_ = lean_ctor_get(v___x_2228_, 0);
lean_inc_ref(v_mctx_2229_);
lean_dec(v___x_2228_);
v___x_2230_ = l_Lean_instantiateMVarsCore(v_mctx_2229_, v_e_2223_);
v_fst_2231_ = lean_ctor_get(v___x_2230_, 0);
lean_inc(v_fst_2231_);
v_snd_2232_ = lean_ctor_get(v___x_2230_, 1);
lean_inc(v_snd_2232_);
lean_dec_ref(v___x_2230_);
v___x_2233_ = lean_st_ref_take(v___y_2224_);
v_cache_2234_ = lean_ctor_get(v___x_2233_, 1);
v_zetaDeltaFVarIds_2235_ = lean_ctor_get(v___x_2233_, 2);
v_postponed_2236_ = lean_ctor_get(v___x_2233_, 3);
v_diag_2237_ = lean_ctor_get(v___x_2233_, 4);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2233_);
if (v_isSharedCheck_2246_ == 0)
{
lean_object* v_unused_2247_; 
v_unused_2247_ = lean_ctor_get(v___x_2233_, 0);
lean_dec(v_unused_2247_);
v___x_2239_ = v___x_2233_;
v_isShared_2240_ = v_isSharedCheck_2246_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_diag_2237_);
lean_inc(v_postponed_2236_);
lean_inc(v_zetaDeltaFVarIds_2235_);
lean_inc(v_cache_2234_);
lean_dec(v___x_2233_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2246_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2242_; 
if (v_isShared_2240_ == 0)
{
lean_ctor_set(v___x_2239_, 0, v_snd_2232_);
v___x_2242_ = v___x_2239_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_snd_2232_);
lean_ctor_set(v_reuseFailAlloc_2245_, 1, v_cache_2234_);
lean_ctor_set(v_reuseFailAlloc_2245_, 2, v_zetaDeltaFVarIds_2235_);
lean_ctor_set(v_reuseFailAlloc_2245_, 3, v_postponed_2236_);
lean_ctor_set(v_reuseFailAlloc_2245_, 4, v_diag_2237_);
v___x_2242_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2243_ = lean_st_ref_set(v___y_2224_, v___x_2242_);
v___x_2244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2244_, 0, v_fst_2231_);
return v___x_2244_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg___boxed(lean_object* v_e_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_){
_start:
{
lean_object* v_res_2251_; 
v_res_2251_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_e_2248_, v___y_2249_);
lean_dec(v___y_2249_);
return v_res_2251_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0(lean_object* v_e_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_){
_start:
{
lean_object* v___x_2258_; 
v___x_2258_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_e_2252_, v___y_2254_);
return v___x_2258_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___boxed(lean_object* v_e_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_){
_start:
{
lean_object* v_res_2265_; 
v_res_2265_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0(v_e_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
return v_res_2265_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; 
v___x_2266_ = lean_unsigned_to_nat(32u);
v___x_2267_ = lean_mk_empty_array_with_capacity(v___x_2266_);
v___x_2268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2267_);
return v___x_2268_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2269_ = ((size_t)5ULL);
v___x_2270_ = lean_unsigned_to_nat(0u);
v___x_2271_ = lean_unsigned_to_nat(32u);
v___x_2272_ = lean_mk_empty_array_with_capacity(v___x_2271_);
v___x_2273_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0);
v___x_2274_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2274_, 0, v___x_2273_);
lean_ctor_set(v___x_2274_, 1, v___x_2272_);
lean_ctor_set(v___x_2274_, 2, v___x_2270_);
lean_ctor_set(v___x_2274_, 3, v___x_2270_);
lean_ctor_set_usize(v___x_2274_, 4, v___x_2269_);
return v___x_2274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(lean_object* v___y_2275_){
_start:
{
lean_object* v___x_2277_; lean_object* v_traceState_2278_; lean_object* v_traces_2279_; lean_object* v___x_2280_; lean_object* v_traceState_2281_; lean_object* v_env_2282_; lean_object* v_nextMacroScope_2283_; lean_object* v_ngen_2284_; lean_object* v_auxDeclNGen_2285_; lean_object* v_cache_2286_; lean_object* v_messages_2287_; lean_object* v_infoState_2288_; lean_object* v_snapshotTasks_2289_; lean_object* v_newDecls_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2309_; 
v___x_2277_ = lean_st_ref_get(v___y_2275_);
v_traceState_2278_ = lean_ctor_get(v___x_2277_, 4);
lean_inc_ref(v_traceState_2278_);
lean_dec(v___x_2277_);
v_traces_2279_ = lean_ctor_get(v_traceState_2278_, 0);
lean_inc_ref(v_traces_2279_);
lean_dec_ref(v_traceState_2278_);
v___x_2280_ = lean_st_ref_take(v___y_2275_);
v_traceState_2281_ = lean_ctor_get(v___x_2280_, 4);
v_env_2282_ = lean_ctor_get(v___x_2280_, 0);
v_nextMacroScope_2283_ = lean_ctor_get(v___x_2280_, 1);
v_ngen_2284_ = lean_ctor_get(v___x_2280_, 2);
v_auxDeclNGen_2285_ = lean_ctor_get(v___x_2280_, 3);
v_cache_2286_ = lean_ctor_get(v___x_2280_, 5);
v_messages_2287_ = lean_ctor_get(v___x_2280_, 6);
v_infoState_2288_ = lean_ctor_get(v___x_2280_, 7);
v_snapshotTasks_2289_ = lean_ctor_get(v___x_2280_, 8);
v_newDecls_2290_ = lean_ctor_get(v___x_2280_, 9);
v_isSharedCheck_2309_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2292_ = v___x_2280_;
v_isShared_2293_ = v_isSharedCheck_2309_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_newDecls_2290_);
lean_inc(v_snapshotTasks_2289_);
lean_inc(v_infoState_2288_);
lean_inc(v_messages_2287_);
lean_inc(v_cache_2286_);
lean_inc(v_traceState_2281_);
lean_inc(v_auxDeclNGen_2285_);
lean_inc(v_ngen_2284_);
lean_inc(v_nextMacroScope_2283_);
lean_inc(v_env_2282_);
lean_dec(v___x_2280_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2309_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
uint64_t v_tid_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2307_; 
v_tid_2294_ = lean_ctor_get_uint64(v_traceState_2281_, sizeof(void*)*1);
v_isSharedCheck_2307_ = !lean_is_exclusive(v_traceState_2281_);
if (v_isSharedCheck_2307_ == 0)
{
lean_object* v_unused_2308_; 
v_unused_2308_ = lean_ctor_get(v_traceState_2281_, 0);
lean_dec(v_unused_2308_);
v___x_2296_ = v_traceState_2281_;
v_isShared_2297_ = v_isSharedCheck_2307_;
goto v_resetjp_2295_;
}
else
{
lean_dec(v_traceState_2281_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2307_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2298_; lean_object* v___x_2300_; 
v___x_2298_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1);
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 0, v___x_2298_);
v___x_2300_ = v___x_2296_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v___x_2298_);
lean_ctor_set_uint64(v_reuseFailAlloc_2306_, sizeof(void*)*1, v_tid_2294_);
v___x_2300_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
lean_object* v___x_2302_; 
if (v_isShared_2293_ == 0)
{
lean_ctor_set(v___x_2292_, 4, v___x_2300_);
v___x_2302_ = v___x_2292_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v_env_2282_);
lean_ctor_set(v_reuseFailAlloc_2305_, 1, v_nextMacroScope_2283_);
lean_ctor_set(v_reuseFailAlloc_2305_, 2, v_ngen_2284_);
lean_ctor_set(v_reuseFailAlloc_2305_, 3, v_auxDeclNGen_2285_);
lean_ctor_set(v_reuseFailAlloc_2305_, 4, v___x_2300_);
lean_ctor_set(v_reuseFailAlloc_2305_, 5, v_cache_2286_);
lean_ctor_set(v_reuseFailAlloc_2305_, 6, v_messages_2287_);
lean_ctor_set(v_reuseFailAlloc_2305_, 7, v_infoState_2288_);
lean_ctor_set(v_reuseFailAlloc_2305_, 8, v_snapshotTasks_2289_);
lean_ctor_set(v_reuseFailAlloc_2305_, 9, v_newDecls_2290_);
v___x_2302_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2303_ = lean_st_ref_set(v___y_2275_, v___x_2302_);
v___x_2304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2304_, 0, v_traces_2279_);
return v___x_2304_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___boxed(lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
lean_object* v_res_2312_; 
v_res_2312_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v___y_2310_);
lean_dec(v___y_2310_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1(lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_){
_start:
{
lean_object* v___x_2318_; 
v___x_2318_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v___y_2316_);
return v___x_2318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___boxed(lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_){
_start:
{
lean_object* v_res_2324_; 
v_res_2324_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1(v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
lean_dec(v___y_2320_);
lean_dec_ref(v___y_2319_);
return v_res_2324_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(lean_object* v_opts_2325_, lean_object* v_opt_2326_){
_start:
{
lean_object* v_name_2327_; lean_object* v_defValue_2328_; lean_object* v_map_2329_; lean_object* v___x_2330_; 
v_name_2327_ = lean_ctor_get(v_opt_2326_, 0);
v_defValue_2328_ = lean_ctor_get(v_opt_2326_, 1);
v_map_2329_ = lean_ctor_get(v_opts_2325_, 0);
v___x_2330_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2329_, v_name_2327_);
if (lean_obj_tag(v___x_2330_) == 0)
{
uint8_t v___x_2331_; 
v___x_2331_ = lean_unbox(v_defValue_2328_);
return v___x_2331_;
}
else
{
lean_object* v_val_2332_; 
v_val_2332_ = lean_ctor_get(v___x_2330_, 0);
lean_inc(v_val_2332_);
lean_dec_ref(v___x_2330_);
if (lean_obj_tag(v_val_2332_) == 1)
{
uint8_t v_v_2333_; 
v_v_2333_ = lean_ctor_get_uint8(v_val_2332_, 0);
lean_dec_ref(v_val_2332_);
return v_v_2333_;
}
else
{
uint8_t v___x_2334_; 
lean_dec(v_val_2332_);
v___x_2334_ = lean_unbox(v_defValue_2328_);
return v___x_2334_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2___boxed(lean_object* v_opts_2335_, lean_object* v_opt_2336_){
_start:
{
uint8_t v_res_2337_; lean_object* v_r_2338_; 
v_res_2337_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_opts_2335_, v_opt_2336_);
lean_dec_ref(v_opt_2336_);
lean_dec_ref(v_opts_2335_);
v_r_2338_ = lean_box(v_res_2337_);
return v_r_2338_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; 
v___x_2340_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__0));
v___x_2341_ = l_Lean_stringToMessageData(v___x_2340_);
return v___x_2341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0(lean_object* v_name_2342_, lean_object* v_x_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_){
_start:
{
lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; 
v___x_2349_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1);
v___x_2350_ = l_Lean_MessageData_ofName(v_name_2342_);
v___x_2351_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2351_, 0, v___x_2349_);
lean_ctor_set(v___x_2351_, 1, v___x_2350_);
v___x_2352_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_2353_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2353_, 0, v___x_2351_);
lean_ctor_set(v___x_2353_, 1, v___x_2352_);
v___x_2354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2354_, 0, v___x_2353_);
return v___x_2354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed(lean_object* v_name_2355_, lean_object* v_x_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_){
_start:
{
lean_object* v_res_2362_; 
v_res_2362_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0(v_name_2355_, v_x_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_);
lean_dec(v___y_2360_);
lean_dec_ref(v___y_2359_);
lean_dec(v___y_2358_);
lean_dec_ref(v___y_2357_);
lean_dec_ref(v_x_2356_);
return v_res_2362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(lean_object* v_name_2363_, lean_object* v_val_2364_, lean_object* v_name_2365_, lean_object* v_levelParams_2366_, uint8_t v___x_2367_, lean_object* v_____r_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_){
_start:
{
lean_object* v___x_2374_; 
lean_inc_ref(v_val_2364_);
v___x_2374_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2363_, v_val_2364_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_);
if (lean_obj_tag(v___x_2374_) == 0)
{
lean_object* v_a_2375_; lean_object* v___x_2376_; lean_object* v_a_2377_; lean_object* v___x_2378_; lean_object* v_a_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2391_; 
v_a_2375_ = lean_ctor_get(v___x_2374_, 0);
lean_inc(v_a_2375_);
lean_dec_ref(v___x_2374_);
v___x_2376_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2364_, v___y_2370_);
v_a_2377_ = lean_ctor_get(v___x_2376_, 0);
lean_inc(v_a_2377_);
lean_dec_ref(v___x_2376_);
v___x_2378_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2375_, v___y_2370_);
v_a_2379_ = lean_ctor_get(v___x_2378_, 0);
v_isSharedCheck_2391_ = !lean_is_exclusive(v___x_2378_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2381_ = v___x_2378_;
v_isShared_2382_ = v_isSharedCheck_2391_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_a_2379_);
lean_dec(v___x_2378_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2391_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2388_; 
lean_inc(v_name_2365_);
v___x_2383_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2383_, 0, v_name_2365_);
lean_ctor_set(v___x_2383_, 1, v_levelParams_2366_);
lean_ctor_set(v___x_2383_, 2, v_a_2377_);
v___x_2384_ = lean_box(0);
v___x_2385_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2385_, 0, v_name_2365_);
lean_ctor_set(v___x_2385_, 1, v___x_2384_);
v___x_2386_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2383_);
lean_ctor_set(v___x_2386_, 1, v_a_2379_);
lean_ctor_set(v___x_2386_, 2, v___x_2385_);
if (v_isShared_2382_ == 0)
{
lean_ctor_set_tag(v___x_2381_, 2);
lean_ctor_set(v___x_2381_, 0, v___x_2386_);
v___x_2388_ = v___x_2381_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v___x_2386_);
v___x_2388_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
lean_object* v___x_2389_; 
v___x_2389_ = l_Lean_addDecl(v___x_2388_, v___x_2367_, v___y_2371_, v___y_2372_);
return v___x_2389_;
}
}
}
else
{
lean_object* v_a_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2399_; 
lean_dec(v_levelParams_2366_);
lean_dec(v_name_2365_);
lean_dec_ref(v_val_2364_);
v_a_2392_ = lean_ctor_get(v___x_2374_, 0);
v_isSharedCheck_2399_ = !lean_is_exclusive(v___x_2374_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2394_ = v___x_2374_;
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_a_2392_);
lean_dec(v___x_2374_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v___x_2397_; 
if (v_isShared_2395_ == 0)
{
v___x_2397_ = v___x_2394_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_a_2392_);
v___x_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
return v___x_2397_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1___boxed(lean_object* v_name_2400_, lean_object* v_val_2401_, lean_object* v_name_2402_, lean_object* v_levelParams_2403_, lean_object* v___x_2404_, lean_object* v_____r_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_){
_start:
{
uint8_t v___x_12976__boxed_2411_; lean_object* v_res_2412_; 
v___x_12976__boxed_2411_ = lean_unbox(v___x_2404_);
v_res_2412_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(v_name_2400_, v_val_2401_, v_name_2402_, v_levelParams_2403_, v___x_12976__boxed_2411_, v_____r_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_);
lean_dec(v___y_2409_);
lean_dec_ref(v___y_2408_);
lean_dec(v___y_2407_);
lean_dec_ref(v___y_2406_);
return v_res_2412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(lean_object* v_name_2413_, lean_object* v_val_2414_, lean_object* v_name_2415_, lean_object* v_levelParams_2416_, lean_object* v_____r_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_){
_start:
{
lean_object* v___x_2423_; 
lean_inc_ref(v_val_2414_);
v___x_2423_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2413_, v_val_2414_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
if (lean_obj_tag(v___x_2423_) == 0)
{
lean_object* v_a_2424_; lean_object* v___x_2425_; lean_object* v_a_2426_; lean_object* v___x_2427_; lean_object* v_a_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2441_; 
v_a_2424_ = lean_ctor_get(v___x_2423_, 0);
lean_inc(v_a_2424_);
lean_dec_ref(v___x_2423_);
v___x_2425_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2414_, v___y_2419_);
v_a_2426_ = lean_ctor_get(v___x_2425_, 0);
lean_inc(v_a_2426_);
lean_dec_ref(v___x_2425_);
v___x_2427_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2424_, v___y_2419_);
v_a_2428_ = lean_ctor_get(v___x_2427_, 0);
v_isSharedCheck_2441_ = !lean_is_exclusive(v___x_2427_);
if (v_isSharedCheck_2441_ == 0)
{
v___x_2430_ = v___x_2427_;
v_isShared_2431_ = v_isSharedCheck_2441_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_a_2428_);
lean_dec(v___x_2427_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2441_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2437_; 
lean_inc(v_name_2415_);
v___x_2432_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2432_, 0, v_name_2415_);
lean_ctor_set(v___x_2432_, 1, v_levelParams_2416_);
lean_ctor_set(v___x_2432_, 2, v_a_2426_);
v___x_2433_ = lean_box(0);
v___x_2434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2434_, 0, v_name_2415_);
lean_ctor_set(v___x_2434_, 1, v___x_2433_);
v___x_2435_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2435_, 0, v___x_2432_);
lean_ctor_set(v___x_2435_, 1, v_a_2428_);
lean_ctor_set(v___x_2435_, 2, v___x_2434_);
if (v_isShared_2431_ == 0)
{
lean_ctor_set_tag(v___x_2430_, 2);
lean_ctor_set(v___x_2430_, 0, v___x_2435_);
v___x_2437_ = v___x_2430_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v___x_2435_);
v___x_2437_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
uint8_t v___x_2438_; lean_object* v___x_2439_; 
v___x_2438_ = 0;
v___x_2439_ = l_Lean_addDecl(v___x_2437_, v___x_2438_, v___y_2420_, v___y_2421_);
return v___x_2439_;
}
}
}
else
{
lean_object* v_a_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2449_; 
lean_dec(v_levelParams_2416_);
lean_dec(v_name_2415_);
lean_dec_ref(v_val_2414_);
v_a_2442_ = lean_ctor_get(v___x_2423_, 0);
v_isSharedCheck_2449_ = !lean_is_exclusive(v___x_2423_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2444_ = v___x_2423_;
v_isShared_2445_ = v_isSharedCheck_2449_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_a_2442_);
lean_dec(v___x_2423_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2___boxed(lean_object* v_name_2450_, lean_object* v_val_2451_, lean_object* v_name_2452_, lean_object* v_levelParams_2453_, lean_object* v_____r_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_){
_start:
{
lean_object* v_res_2460_; 
v_res_2460_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(v_name_2450_, v_val_2451_, v_name_2452_, v_levelParams_2453_, v_____r_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
lean_dec(v___y_2458_);
lean_dec_ref(v___y_2457_);
lean_dec(v___y_2456_);
lean_dec_ref(v___y_2455_);
return v_res_2460_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(lean_object* v_e_2461_){
_start:
{
if (lean_obj_tag(v_e_2461_) == 0)
{
uint8_t v___x_2462_; 
v___x_2462_ = 2;
return v___x_2462_;
}
else
{
uint8_t v___x_2463_; 
v___x_2463_ = 0;
return v___x_2463_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3___boxed(lean_object* v_e_2464_){
_start:
{
uint8_t v_res_2465_; lean_object* v_r_2466_; 
v_res_2465_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(v_e_2464_);
lean_dec_ref(v_e_2464_);
v_r_2466_ = lean_box(v_res_2465_);
return v_r_2466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(lean_object* v_opts_2467_, lean_object* v_opt_2468_){
_start:
{
lean_object* v_name_2469_; lean_object* v_defValue_2470_; lean_object* v_map_2471_; lean_object* v___x_2472_; 
v_name_2469_ = lean_ctor_get(v_opt_2468_, 0);
v_defValue_2470_ = lean_ctor_get(v_opt_2468_, 1);
v_map_2471_ = lean_ctor_get(v_opts_2467_, 0);
v___x_2472_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2471_, v_name_2469_);
if (lean_obj_tag(v___x_2472_) == 0)
{
lean_inc(v_defValue_2470_);
return v_defValue_2470_;
}
else
{
lean_object* v_val_2473_; 
v_val_2473_ = lean_ctor_get(v___x_2472_, 0);
lean_inc(v_val_2473_);
lean_dec_ref(v___x_2472_);
if (lean_obj_tag(v_val_2473_) == 3)
{
lean_object* v_v_2474_; 
v_v_2474_ = lean_ctor_get(v_val_2473_, 0);
lean_inc(v_v_2474_);
lean_dec_ref(v_val_2473_);
return v_v_2474_;
}
else
{
lean_dec(v_val_2473_);
lean_inc(v_defValue_2470_);
return v_defValue_2470_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6___boxed(lean_object* v_opts_2475_, lean_object* v_opt_2476_){
_start:
{
lean_object* v_res_2477_; 
v_res_2477_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(v_opts_2475_, v_opt_2476_);
lean_dec_ref(v_opt_2476_);
lean_dec_ref(v_opts_2475_);
return v_res_2477_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___redArg(lean_object* v_x_2478_){
_start:
{
if (lean_obj_tag(v_x_2478_) == 0)
{
lean_object* v_a_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2487_; 
v_a_2480_ = lean_ctor_get(v_x_2478_, 0);
v_isSharedCheck_2487_ = !lean_is_exclusive(v_x_2478_);
if (v_isSharedCheck_2487_ == 0)
{
v___x_2482_ = v_x_2478_;
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_a_2480_);
lean_dec(v_x_2478_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2485_; 
if (v_isShared_2483_ == 0)
{
lean_ctor_set_tag(v___x_2482_, 1);
v___x_2485_ = v___x_2482_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v_a_2480_);
v___x_2485_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
return v___x_2485_;
}
}
}
else
{
lean_object* v_a_2488_; lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2495_; 
v_a_2488_ = lean_ctor_get(v_x_2478_, 0);
v_isSharedCheck_2495_ = !lean_is_exclusive(v_x_2478_);
if (v_isSharedCheck_2495_ == 0)
{
v___x_2490_ = v_x_2478_;
v_isShared_2491_ = v_isSharedCheck_2495_;
goto v_resetjp_2489_;
}
else
{
lean_inc(v_a_2488_);
lean_dec(v_x_2478_);
v___x_2490_ = lean_box(0);
v_isShared_2491_ = v_isSharedCheck_2495_;
goto v_resetjp_2489_;
}
v_resetjp_2489_:
{
lean_object* v___x_2493_; 
if (v_isShared_2491_ == 0)
{
lean_ctor_set_tag(v___x_2490_, 0);
v___x_2493_ = v___x_2490_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v_a_2488_);
v___x_2493_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
return v___x_2493_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___redArg___boxed(lean_object* v_x_2496_, lean_object* v___y_2497_){
_start:
{
lean_object* v_res_2498_; 
v_res_2498_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___redArg(v_x_2496_);
return v_res_2498_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4_spec__5(size_t v_sz_2499_, size_t v_i_2500_, lean_object* v_bs_2501_){
_start:
{
uint8_t v___x_2502_; 
v___x_2502_ = lean_usize_dec_lt(v_i_2500_, v_sz_2499_);
if (v___x_2502_ == 0)
{
return v_bs_2501_;
}
else
{
lean_object* v_v_2503_; lean_object* v_msg_2504_; lean_object* v___x_2505_; lean_object* v_bs_x27_2506_; size_t v___x_2507_; size_t v___x_2508_; lean_object* v___x_2509_; 
v_v_2503_ = lean_array_uget_borrowed(v_bs_2501_, v_i_2500_);
v_msg_2504_ = lean_ctor_get(v_v_2503_, 1);
lean_inc_ref(v_msg_2504_);
v___x_2505_ = lean_unsigned_to_nat(0u);
v_bs_x27_2506_ = lean_array_uset(v_bs_2501_, v_i_2500_, v___x_2505_);
v___x_2507_ = ((size_t)1ULL);
v___x_2508_ = lean_usize_add(v_i_2500_, v___x_2507_);
v___x_2509_ = lean_array_uset(v_bs_x27_2506_, v_i_2500_, v_msg_2504_);
v_i_2500_ = v___x_2508_;
v_bs_2501_ = v___x_2509_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4_spec__5___boxed(lean_object* v_sz_2511_, lean_object* v_i_2512_, lean_object* v_bs_2513_){
_start:
{
size_t v_sz_boxed_2514_; size_t v_i_boxed_2515_; lean_object* v_res_2516_; 
v_sz_boxed_2514_ = lean_unbox_usize(v_sz_2511_);
lean_dec(v_sz_2511_);
v_i_boxed_2515_ = lean_unbox_usize(v_i_2512_);
lean_dec(v_i_2512_);
v_res_2516_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4_spec__5(v_sz_boxed_2514_, v_i_boxed_2515_, v_bs_2513_);
return v_res_2516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4(lean_object* v_oldTraces_2517_, lean_object* v_data_2518_, lean_object* v_ref_2519_, lean_object* v_msg_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_){
_start:
{
lean_object* v_fileName_2526_; lean_object* v_fileMap_2527_; lean_object* v_options_2528_; lean_object* v_currRecDepth_2529_; lean_object* v_maxRecDepth_2530_; lean_object* v_ref_2531_; lean_object* v_currNamespace_2532_; lean_object* v_openDecls_2533_; lean_object* v_initHeartbeats_2534_; lean_object* v_maxHeartbeats_2535_; lean_object* v_quotContext_2536_; lean_object* v_currMacroScope_2537_; uint8_t v_diag_2538_; lean_object* v_cancelTk_x3f_2539_; uint8_t v_suppressElabErrors_2540_; lean_object* v_inheritedTraceOptions_2541_; lean_object* v___x_2542_; lean_object* v_traceState_2543_; lean_object* v_traces_2544_; lean_object* v_ref_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; size_t v_sz_2548_; size_t v___x_2549_; lean_object* v___x_2550_; lean_object* v_msg_2551_; lean_object* v___x_2552_; lean_object* v_a_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2591_; 
v_fileName_2526_ = lean_ctor_get(v___y_2523_, 0);
v_fileMap_2527_ = lean_ctor_get(v___y_2523_, 1);
v_options_2528_ = lean_ctor_get(v___y_2523_, 2);
v_currRecDepth_2529_ = lean_ctor_get(v___y_2523_, 3);
v_maxRecDepth_2530_ = lean_ctor_get(v___y_2523_, 4);
v_ref_2531_ = lean_ctor_get(v___y_2523_, 5);
v_currNamespace_2532_ = lean_ctor_get(v___y_2523_, 6);
v_openDecls_2533_ = lean_ctor_get(v___y_2523_, 7);
v_initHeartbeats_2534_ = lean_ctor_get(v___y_2523_, 8);
v_maxHeartbeats_2535_ = lean_ctor_get(v___y_2523_, 9);
v_quotContext_2536_ = lean_ctor_get(v___y_2523_, 10);
v_currMacroScope_2537_ = lean_ctor_get(v___y_2523_, 11);
v_diag_2538_ = lean_ctor_get_uint8(v___y_2523_, sizeof(void*)*14);
v_cancelTk_x3f_2539_ = lean_ctor_get(v___y_2523_, 12);
v_suppressElabErrors_2540_ = lean_ctor_get_uint8(v___y_2523_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2541_ = lean_ctor_get(v___y_2523_, 13);
v___x_2542_ = lean_st_ref_get(v___y_2524_);
v_traceState_2543_ = lean_ctor_get(v___x_2542_, 4);
lean_inc_ref(v_traceState_2543_);
lean_dec(v___x_2542_);
v_traces_2544_ = lean_ctor_get(v_traceState_2543_, 0);
lean_inc_ref(v_traces_2544_);
lean_dec_ref(v_traceState_2543_);
v_ref_2545_ = l_Lean_replaceRef(v_ref_2519_, v_ref_2531_);
lean_inc_ref(v_inheritedTraceOptions_2541_);
lean_inc(v_cancelTk_x3f_2539_);
lean_inc(v_currMacroScope_2537_);
lean_inc(v_quotContext_2536_);
lean_inc(v_maxHeartbeats_2535_);
lean_inc(v_initHeartbeats_2534_);
lean_inc(v_openDecls_2533_);
lean_inc(v_currNamespace_2532_);
lean_inc(v_maxRecDepth_2530_);
lean_inc(v_currRecDepth_2529_);
lean_inc_ref(v_options_2528_);
lean_inc_ref(v_fileMap_2527_);
lean_inc_ref(v_fileName_2526_);
v___x_2546_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2546_, 0, v_fileName_2526_);
lean_ctor_set(v___x_2546_, 1, v_fileMap_2527_);
lean_ctor_set(v___x_2546_, 2, v_options_2528_);
lean_ctor_set(v___x_2546_, 3, v_currRecDepth_2529_);
lean_ctor_set(v___x_2546_, 4, v_maxRecDepth_2530_);
lean_ctor_set(v___x_2546_, 5, v_ref_2545_);
lean_ctor_set(v___x_2546_, 6, v_currNamespace_2532_);
lean_ctor_set(v___x_2546_, 7, v_openDecls_2533_);
lean_ctor_set(v___x_2546_, 8, v_initHeartbeats_2534_);
lean_ctor_set(v___x_2546_, 9, v_maxHeartbeats_2535_);
lean_ctor_set(v___x_2546_, 10, v_quotContext_2536_);
lean_ctor_set(v___x_2546_, 11, v_currMacroScope_2537_);
lean_ctor_set(v___x_2546_, 12, v_cancelTk_x3f_2539_);
lean_ctor_set(v___x_2546_, 13, v_inheritedTraceOptions_2541_);
lean_ctor_set_uint8(v___x_2546_, sizeof(void*)*14, v_diag_2538_);
lean_ctor_set_uint8(v___x_2546_, sizeof(void*)*14 + 1, v_suppressElabErrors_2540_);
v___x_2547_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2544_);
lean_dec_ref(v_traces_2544_);
v_sz_2548_ = lean_array_size(v___x_2547_);
v___x_2549_ = ((size_t)0ULL);
v___x_2550_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4_spec__5(v_sz_2548_, v___x_2549_, v___x_2547_);
v_msg_2551_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2551_, 0, v_data_2518_);
lean_ctor_set(v_msg_2551_, 1, v_msg_2520_);
lean_ctor_set(v_msg_2551_, 2, v___x_2550_);
v___x_2552_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msg_2551_, v___y_2521_, v___y_2522_, v___x_2546_, v___y_2524_);
lean_dec_ref(v___x_2546_);
v_a_2553_ = lean_ctor_get(v___x_2552_, 0);
v_isSharedCheck_2591_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2555_ = v___x_2552_;
v_isShared_2556_ = v_isSharedCheck_2591_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_a_2553_);
lean_dec(v___x_2552_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2591_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2557_; lean_object* v_traceState_2558_; lean_object* v_env_2559_; lean_object* v_nextMacroScope_2560_; lean_object* v_ngen_2561_; lean_object* v_auxDeclNGen_2562_; lean_object* v_cache_2563_; lean_object* v_messages_2564_; lean_object* v_infoState_2565_; lean_object* v_snapshotTasks_2566_; lean_object* v_newDecls_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2590_; 
v___x_2557_ = lean_st_ref_take(v___y_2524_);
v_traceState_2558_ = lean_ctor_get(v___x_2557_, 4);
v_env_2559_ = lean_ctor_get(v___x_2557_, 0);
v_nextMacroScope_2560_ = lean_ctor_get(v___x_2557_, 1);
v_ngen_2561_ = lean_ctor_get(v___x_2557_, 2);
v_auxDeclNGen_2562_ = lean_ctor_get(v___x_2557_, 3);
v_cache_2563_ = lean_ctor_get(v___x_2557_, 5);
v_messages_2564_ = lean_ctor_get(v___x_2557_, 6);
v_infoState_2565_ = lean_ctor_get(v___x_2557_, 7);
v_snapshotTasks_2566_ = lean_ctor_get(v___x_2557_, 8);
v_newDecls_2567_ = lean_ctor_get(v___x_2557_, 9);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2569_ = v___x_2557_;
v_isShared_2570_ = v_isSharedCheck_2590_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_newDecls_2567_);
lean_inc(v_snapshotTasks_2566_);
lean_inc(v_infoState_2565_);
lean_inc(v_messages_2564_);
lean_inc(v_cache_2563_);
lean_inc(v_traceState_2558_);
lean_inc(v_auxDeclNGen_2562_);
lean_inc(v_ngen_2561_);
lean_inc(v_nextMacroScope_2560_);
lean_inc(v_env_2559_);
lean_dec(v___x_2557_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2590_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
uint64_t v_tid_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2588_; 
v_tid_2571_ = lean_ctor_get_uint64(v_traceState_2558_, sizeof(void*)*1);
v_isSharedCheck_2588_ = !lean_is_exclusive(v_traceState_2558_);
if (v_isSharedCheck_2588_ == 0)
{
lean_object* v_unused_2589_; 
v_unused_2589_ = lean_ctor_get(v_traceState_2558_, 0);
lean_dec(v_unused_2589_);
v___x_2573_ = v_traceState_2558_;
v_isShared_2574_ = v_isSharedCheck_2588_;
goto v_resetjp_2572_;
}
else
{
lean_dec(v_traceState_2558_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2588_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2578_; 
v___x_2575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2575_, 0, v_ref_2519_);
lean_ctor_set(v___x_2575_, 1, v_a_2553_);
v___x_2576_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2517_, v___x_2575_);
if (v_isShared_2574_ == 0)
{
lean_ctor_set(v___x_2573_, 0, v___x_2576_);
v___x_2578_ = v___x_2573_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v___x_2576_);
lean_ctor_set_uint64(v_reuseFailAlloc_2587_, sizeof(void*)*1, v_tid_2571_);
v___x_2578_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
lean_object* v___x_2580_; 
if (v_isShared_2570_ == 0)
{
lean_ctor_set(v___x_2569_, 4, v___x_2578_);
v___x_2580_ = v___x_2569_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_env_2559_);
lean_ctor_set(v_reuseFailAlloc_2586_, 1, v_nextMacroScope_2560_);
lean_ctor_set(v_reuseFailAlloc_2586_, 2, v_ngen_2561_);
lean_ctor_set(v_reuseFailAlloc_2586_, 3, v_auxDeclNGen_2562_);
lean_ctor_set(v_reuseFailAlloc_2586_, 4, v___x_2578_);
lean_ctor_set(v_reuseFailAlloc_2586_, 5, v_cache_2563_);
lean_ctor_set(v_reuseFailAlloc_2586_, 6, v_messages_2564_);
lean_ctor_set(v_reuseFailAlloc_2586_, 7, v_infoState_2565_);
lean_ctor_set(v_reuseFailAlloc_2586_, 8, v_snapshotTasks_2566_);
lean_ctor_set(v_reuseFailAlloc_2586_, 9, v_newDecls_2567_);
v___x_2580_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2584_; 
v___x_2581_ = lean_st_ref_set(v___y_2524_, v___x_2580_);
v___x_2582_ = lean_box(0);
if (v_isShared_2556_ == 0)
{
lean_ctor_set(v___x_2555_, 0, v___x_2582_);
v___x_2584_ = v___x_2555_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v___x_2582_);
v___x_2584_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
return v___x_2584_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___boxed(lean_object* v_oldTraces_2592_, lean_object* v_data_2593_, lean_object* v_ref_2594_, lean_object* v_msg_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_){
_start:
{
lean_object* v_res_2601_; 
v_res_2601_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4(v_oldTraces_2592_, v_data_2593_, v_ref_2594_, v_msg_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
lean_dec(v___y_2599_);
lean_dec_ref(v___y_2598_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
return v_res_2601_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2603_; lean_object* v___x_2604_; 
v___x_2603_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__0));
v___x_2604_ = l_Lean_stringToMessageData(v___x_2603_);
return v___x_2604_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__3(void){
_start:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; 
v___x_2606_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2));
v___x_2607_ = l_Lean_stringToMessageData(v___x_2606_);
return v___x_2607_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__4(void){
_start:
{
lean_object* v___x_2608_; double v___x_2609_; 
v___x_2608_ = lean_unsigned_to_nat(1000u);
v___x_2609_ = lean_float_of_nat(v___x_2608_);
return v___x_2609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(lean_object* v_cls_2610_, uint8_t v_collapsed_2611_, lean_object* v_tag_2612_, lean_object* v_opts_2613_, uint8_t v_clsEnabled_2614_, lean_object* v_oldTraces_2615_, lean_object* v_msg_2616_, lean_object* v_resStartStop_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_){
_start:
{
lean_object* v_fst_2623_; lean_object* v_snd_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2715_; 
v_fst_2623_ = lean_ctor_get(v_resStartStop_2617_, 0);
v_snd_2624_ = lean_ctor_get(v_resStartStop_2617_, 1);
v_isSharedCheck_2715_ = !lean_is_exclusive(v_resStartStop_2617_);
if (v_isSharedCheck_2715_ == 0)
{
v___x_2626_ = v_resStartStop_2617_;
v_isShared_2627_ = v_isSharedCheck_2715_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_snd_2624_);
lean_inc(v_fst_2623_);
lean_dec(v_resStartStop_2617_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2715_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___y_2629_; lean_object* v___y_2630_; lean_object* v_data_2631_; lean_object* v_fst_2634_; lean_object* v_snd_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2714_; 
v_fst_2634_ = lean_ctor_get(v_snd_2624_, 0);
v_snd_2635_ = lean_ctor_get(v_snd_2624_, 1);
v_isSharedCheck_2714_ = !lean_is_exclusive(v_snd_2624_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2637_ = v_snd_2624_;
v_isShared_2638_ = v_isSharedCheck_2714_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_snd_2635_);
lean_inc(v_fst_2634_);
lean_dec(v_snd_2624_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2714_;
goto v_resetjp_2636_;
}
v___jp_2628_:
{
lean_object* v___x_2632_; 
lean_inc(v___y_2630_);
v___x_2632_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4(v_oldTraces_2615_, v_data_2631_, v___y_2630_, v___y_2629_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
if (lean_obj_tag(v___x_2632_) == 0)
{
lean_object* v___x_2633_; 
lean_dec_ref(v___x_2632_);
v___x_2633_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___redArg(v_fst_2623_);
return v___x_2633_;
}
else
{
lean_dec(v_fst_2623_);
return v___x_2632_;
}
}
v_resetjp_2636_:
{
lean_object* v___x_2639_; uint8_t v___x_2640_; lean_object* v___y_2642_; lean_object* v_a_2643_; uint8_t v___y_2667_; double v___y_2699_; 
v___x_2639_ = l_Lean_trace_profiler;
v___x_2640_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_opts_2613_, v___x_2639_);
if (v___x_2640_ == 0)
{
v___y_2667_ = v___x_2640_;
goto v___jp_2666_;
}
else
{
lean_object* v___x_2704_; uint8_t v___x_2705_; 
v___x_2704_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2705_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_opts_2613_, v___x_2704_);
if (v___x_2705_ == 0)
{
lean_object* v___x_2706_; lean_object* v___x_2707_; double v___x_2708_; double v___x_2709_; double v___x_2710_; 
v___x_2706_ = l_Lean_trace_profiler_threshold;
v___x_2707_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(v_opts_2613_, v___x_2706_);
v___x_2708_ = lean_float_of_nat(v___x_2707_);
v___x_2709_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__4);
v___x_2710_ = lean_float_div(v___x_2708_, v___x_2709_);
v___y_2699_ = v___x_2710_;
goto v___jp_2698_;
}
else
{
lean_object* v___x_2711_; lean_object* v___x_2712_; double v___x_2713_; 
v___x_2711_ = l_Lean_trace_profiler_threshold;
v___x_2712_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(v_opts_2613_, v___x_2711_);
v___x_2713_ = lean_float_of_nat(v___x_2712_);
v___y_2699_ = v___x_2713_;
goto v___jp_2698_;
}
}
v___jp_2641_:
{
uint8_t v_result_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2649_; 
v_result_2644_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(v_fst_2623_);
v___x_2645_ = l_Lean_TraceResult_toEmoji(v_result_2644_);
v___x_2646_ = l_Lean_stringToMessageData(v___x_2645_);
v___x_2647_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1);
if (v_isShared_2638_ == 0)
{
lean_ctor_set_tag(v___x_2637_, 7);
lean_ctor_set(v___x_2637_, 1, v___x_2647_);
lean_ctor_set(v___x_2637_, 0, v___x_2646_);
v___x_2649_ = v___x_2637_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v___x_2646_);
lean_ctor_set(v_reuseFailAlloc_2660_, 1, v___x_2647_);
v___x_2649_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
lean_object* v_m_2651_; 
if (v_isShared_2627_ == 0)
{
lean_ctor_set_tag(v___x_2626_, 7);
lean_ctor_set(v___x_2626_, 1, v_a_2643_);
lean_ctor_set(v___x_2626_, 0, v___x_2649_);
v_m_2651_ = v___x_2626_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v___x_2649_);
lean_ctor_set(v_reuseFailAlloc_2659_, 1, v_a_2643_);
v_m_2651_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
lean_object* v___x_2652_; lean_object* v___x_2653_; double v___x_2654_; lean_object* v_data_2655_; 
v___x_2652_ = lean_box(v_result_2644_);
v___x_2653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2653_, 0, v___x_2652_);
v___x_2654_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0);
lean_inc_ref(v_tag_2612_);
lean_inc_ref(v___x_2653_);
lean_inc(v_cls_2610_);
v_data_2655_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2655_, 0, v_cls_2610_);
lean_ctor_set(v_data_2655_, 1, v___x_2653_);
lean_ctor_set(v_data_2655_, 2, v_tag_2612_);
lean_ctor_set_float(v_data_2655_, sizeof(void*)*3, v___x_2654_);
lean_ctor_set_float(v_data_2655_, sizeof(void*)*3 + 8, v___x_2654_);
lean_ctor_set_uint8(v_data_2655_, sizeof(void*)*3 + 16, v_collapsed_2611_);
if (v___x_2640_ == 0)
{
lean_dec_ref(v___x_2653_);
lean_dec(v_snd_2635_);
lean_dec(v_fst_2634_);
lean_dec_ref(v_tag_2612_);
lean_dec(v_cls_2610_);
v___y_2629_ = v_m_2651_;
v___y_2630_ = v___y_2642_;
v_data_2631_ = v_data_2655_;
goto v___jp_2628_;
}
else
{
lean_object* v_data_2656_; double v___x_2657_; double v___x_2658_; 
lean_dec_ref(v_data_2655_);
v_data_2656_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2656_, 0, v_cls_2610_);
lean_ctor_set(v_data_2656_, 1, v___x_2653_);
lean_ctor_set(v_data_2656_, 2, v_tag_2612_);
v___x_2657_ = lean_unbox_float(v_fst_2634_);
lean_dec(v_fst_2634_);
lean_ctor_set_float(v_data_2656_, sizeof(void*)*3, v___x_2657_);
v___x_2658_ = lean_unbox_float(v_snd_2635_);
lean_dec(v_snd_2635_);
lean_ctor_set_float(v_data_2656_, sizeof(void*)*3 + 8, v___x_2658_);
lean_ctor_set_uint8(v_data_2656_, sizeof(void*)*3 + 16, v_collapsed_2611_);
v___y_2629_ = v_m_2651_;
v___y_2630_ = v___y_2642_;
v_data_2631_ = v_data_2656_;
goto v___jp_2628_;
}
}
}
}
v___jp_2661_:
{
lean_object* v_ref_2662_; lean_object* v___x_2663_; 
v_ref_2662_ = lean_ctor_get(v___y_2620_, 5);
lean_inc(v___y_2621_);
lean_inc_ref(v___y_2620_);
lean_inc(v___y_2619_);
lean_inc_ref(v___y_2618_);
lean_inc(v_fst_2623_);
v___x_2663_ = lean_apply_6(v_msg_2616_, v_fst_2623_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_, lean_box(0));
if (lean_obj_tag(v___x_2663_) == 0)
{
lean_object* v_a_2664_; 
v_a_2664_ = lean_ctor_get(v___x_2663_, 0);
lean_inc(v_a_2664_);
lean_dec_ref(v___x_2663_);
v___y_2642_ = v_ref_2662_;
v_a_2643_ = v_a_2664_;
goto v___jp_2641_;
}
else
{
lean_object* v___x_2665_; 
lean_dec_ref(v___x_2663_);
v___x_2665_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__3);
v___y_2642_ = v_ref_2662_;
v_a_2643_ = v___x_2665_;
goto v___jp_2641_;
}
}
v___jp_2666_:
{
if (v_clsEnabled_2614_ == 0)
{
if (v___y_2667_ == 0)
{
lean_object* v___x_2668_; lean_object* v_traceState_2669_; lean_object* v_env_2670_; lean_object* v_nextMacroScope_2671_; lean_object* v_ngen_2672_; lean_object* v_auxDeclNGen_2673_; lean_object* v_cache_2674_; lean_object* v_messages_2675_; lean_object* v_infoState_2676_; lean_object* v_snapshotTasks_2677_; lean_object* v_newDecls_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2697_; 
lean_del_object(v___x_2637_);
lean_dec(v_snd_2635_);
lean_dec(v_fst_2634_);
lean_del_object(v___x_2626_);
lean_dec_ref(v_msg_2616_);
lean_dec_ref(v_tag_2612_);
lean_dec(v_cls_2610_);
v___x_2668_ = lean_st_ref_take(v___y_2621_);
v_traceState_2669_ = lean_ctor_get(v___x_2668_, 4);
v_env_2670_ = lean_ctor_get(v___x_2668_, 0);
v_nextMacroScope_2671_ = lean_ctor_get(v___x_2668_, 1);
v_ngen_2672_ = lean_ctor_get(v___x_2668_, 2);
v_auxDeclNGen_2673_ = lean_ctor_get(v___x_2668_, 3);
v_cache_2674_ = lean_ctor_get(v___x_2668_, 5);
v_messages_2675_ = lean_ctor_get(v___x_2668_, 6);
v_infoState_2676_ = lean_ctor_get(v___x_2668_, 7);
v_snapshotTasks_2677_ = lean_ctor_get(v___x_2668_, 8);
v_newDecls_2678_ = lean_ctor_get(v___x_2668_, 9);
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2668_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2680_ = v___x_2668_;
v_isShared_2681_ = v_isSharedCheck_2697_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_newDecls_2678_);
lean_inc(v_snapshotTasks_2677_);
lean_inc(v_infoState_2676_);
lean_inc(v_messages_2675_);
lean_inc(v_cache_2674_);
lean_inc(v_traceState_2669_);
lean_inc(v_auxDeclNGen_2673_);
lean_inc(v_ngen_2672_);
lean_inc(v_nextMacroScope_2671_);
lean_inc(v_env_2670_);
lean_dec(v___x_2668_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2697_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
uint64_t v_tid_2682_; lean_object* v_traces_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2696_; 
v_tid_2682_ = lean_ctor_get_uint64(v_traceState_2669_, sizeof(void*)*1);
v_traces_2683_ = lean_ctor_get(v_traceState_2669_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v_traceState_2669_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2685_ = v_traceState_2669_;
v_isShared_2686_ = v_isSharedCheck_2696_;
goto v_resetjp_2684_;
}
else
{
lean_inc(v_traces_2683_);
lean_dec(v_traceState_2669_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2696_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
lean_object* v___x_2687_; lean_object* v___x_2689_; 
v___x_2687_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2615_, v_traces_2683_);
lean_dec_ref(v_traces_2683_);
if (v_isShared_2686_ == 0)
{
lean_ctor_set(v___x_2685_, 0, v___x_2687_);
v___x_2689_ = v___x_2685_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v___x_2687_);
lean_ctor_set_uint64(v_reuseFailAlloc_2695_, sizeof(void*)*1, v_tid_2682_);
v___x_2689_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
lean_object* v___x_2691_; 
if (v_isShared_2681_ == 0)
{
lean_ctor_set(v___x_2680_, 4, v___x_2689_);
v___x_2691_ = v___x_2680_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_env_2670_);
lean_ctor_set(v_reuseFailAlloc_2694_, 1, v_nextMacroScope_2671_);
lean_ctor_set(v_reuseFailAlloc_2694_, 2, v_ngen_2672_);
lean_ctor_set(v_reuseFailAlloc_2694_, 3, v_auxDeclNGen_2673_);
lean_ctor_set(v_reuseFailAlloc_2694_, 4, v___x_2689_);
lean_ctor_set(v_reuseFailAlloc_2694_, 5, v_cache_2674_);
lean_ctor_set(v_reuseFailAlloc_2694_, 6, v_messages_2675_);
lean_ctor_set(v_reuseFailAlloc_2694_, 7, v_infoState_2676_);
lean_ctor_set(v_reuseFailAlloc_2694_, 8, v_snapshotTasks_2677_);
lean_ctor_set(v_reuseFailAlloc_2694_, 9, v_newDecls_2678_);
v___x_2691_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
lean_object* v___x_2692_; lean_object* v___x_2693_; 
v___x_2692_ = lean_st_ref_set(v___y_2621_, v___x_2691_);
v___x_2693_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___redArg(v_fst_2623_);
return v___x_2693_;
}
}
}
}
}
else
{
goto v___jp_2661_;
}
}
else
{
goto v___jp_2661_;
}
}
v___jp_2698_:
{
double v___x_2700_; double v___x_2701_; double v___x_2702_; uint8_t v___x_2703_; 
v___x_2700_ = lean_unbox_float(v_snd_2635_);
v___x_2701_ = lean_unbox_float(v_fst_2634_);
v___x_2702_ = lean_float_sub(v___x_2700_, v___x_2701_);
v___x_2703_ = lean_float_decLt(v___y_2699_, v___x_2702_);
v___y_2667_ = v___x_2703_;
goto v___jp_2666_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___boxed(lean_object* v_cls_2716_, lean_object* v_collapsed_2717_, lean_object* v_tag_2718_, lean_object* v_opts_2719_, lean_object* v_clsEnabled_2720_, lean_object* v_oldTraces_2721_, lean_object* v_msg_2722_, lean_object* v_resStartStop_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_){
_start:
{
uint8_t v_collapsed_boxed_2729_; uint8_t v_clsEnabled_boxed_2730_; lean_object* v_res_2731_; 
v_collapsed_boxed_2729_ = lean_unbox(v_collapsed_2717_);
v_clsEnabled_boxed_2730_ = lean_unbox(v_clsEnabled_2720_);
v_res_2731_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_2716_, v_collapsed_boxed_2729_, v_tag_2718_, v_opts_2719_, v_clsEnabled_boxed_2730_, v_oldTraces_2721_, v_msg_2722_, v_resStartStop_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec_ref(v_opts_2719_);
return v_res_2731_;
}
}
static double _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0(void){
_start:
{
lean_object* v___x_2732_; double v___x_2733_; 
v___x_2732_ = lean_unsigned_to_nat(1000000000u);
v___x_2733_ = lean_float_of_nat(v___x_2732_);
return v___x_2733_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2(void){
_start:
{
lean_object* v___x_2735_; lean_object* v___x_2736_; 
v___x_2735_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1));
v___x_2736_ = l_Lean_stringToMessageData(v___x_2735_);
return v___x_2736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(lean_object* v_ctorVal_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_){
_start:
{
lean_object* v_toConstantVal_2743_; lean_object* v_options_2744_; lean_object* v_name_2745_; lean_object* v_levelParams_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2957_; 
v_toConstantVal_2743_ = lean_ctor_get(v_ctorVal_2737_, 0);
lean_inc_ref(v_toConstantVal_2743_);
v_options_2744_ = lean_ctor_get(v_a_2740_, 2);
v_name_2745_ = lean_ctor_get(v_toConstantVal_2743_, 0);
v_levelParams_2746_ = lean_ctor_get(v_toConstantVal_2743_, 1);
v_isSharedCheck_2957_ = !lean_is_exclusive(v_toConstantVal_2743_);
if (v_isSharedCheck_2957_ == 0)
{
lean_object* v_unused_2958_; 
v_unused_2958_ = lean_ctor_get(v_toConstantVal_2743_, 2);
lean_dec(v_unused_2958_);
v___x_2748_ = v_toConstantVal_2743_;
v_isShared_2749_ = v_isSharedCheck_2957_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_levelParams_2746_);
lean_inc(v_name_2745_);
lean_dec(v_toConstantVal_2743_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2957_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v_inheritedTraceOptions_2750_; uint8_t v_hasTrace_2751_; lean_object* v_name_2752_; 
v_inheritedTraceOptions_2750_ = lean_ctor_get(v_a_2740_, 13);
v_hasTrace_2751_ = lean_ctor_get_uint8(v_options_2744_, sizeof(void*)*1);
lean_inc(v_name_2745_);
v_name_2752_ = l_Lean_Meta_mkInjectiveTheoremNameFor(v_name_2745_);
if (v_hasTrace_2751_ == 0)
{
lean_object* v___x_2753_; 
v___x_2753_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_);
if (lean_obj_tag(v___x_2753_) == 0)
{
lean_object* v_a_2754_; lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2791_; 
v_a_2754_ = lean_ctor_get(v___x_2753_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___x_2753_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2756_ = v___x_2753_;
v_isShared_2757_ = v_isSharedCheck_2791_;
goto v_resetjp_2755_;
}
else
{
lean_inc(v_a_2754_);
lean_dec(v___x_2753_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2791_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
if (lean_obj_tag(v_a_2754_) == 1)
{
lean_object* v_val_2758_; lean_object* v___x_2759_; 
lean_del_object(v___x_2756_);
v_val_2758_ = lean_ctor_get(v_a_2754_, 0);
lean_inc_n(v_val_2758_, 2);
lean_dec_ref(v_a_2754_);
v___x_2759_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2745_, v_val_2758_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_);
if (lean_obj_tag(v___x_2759_) == 0)
{
lean_object* v_a_2760_; lean_object* v___x_2761_; lean_object* v_a_2762_; lean_object* v___x_2763_; lean_object* v_a_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2778_; 
v_a_2760_ = lean_ctor_get(v___x_2759_, 0);
lean_inc(v_a_2760_);
lean_dec_ref(v___x_2759_);
v___x_2761_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2758_, v_a_2739_);
v_a_2762_ = lean_ctor_get(v___x_2761_, 0);
lean_inc(v_a_2762_);
lean_dec_ref(v___x_2761_);
v___x_2763_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2760_, v_a_2739_);
v_a_2764_ = lean_ctor_get(v___x_2763_, 0);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2766_ = v___x_2763_;
v_isShared_2767_ = v_isSharedCheck_2778_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_a_2764_);
lean_dec(v___x_2763_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2778_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v___x_2769_; 
lean_inc(v_name_2752_);
if (v_isShared_2749_ == 0)
{
lean_ctor_set(v___x_2748_, 2, v_a_2762_);
lean_ctor_set(v___x_2748_, 0, v_name_2752_);
v___x_2769_ = v___x_2748_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_name_2752_);
lean_ctor_set(v_reuseFailAlloc_2777_, 1, v_levelParams_2746_);
lean_ctor_set(v_reuseFailAlloc_2777_, 2, v_a_2762_);
v___x_2769_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2774_; 
v___x_2770_ = lean_box(0);
v___x_2771_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2771_, 0, v_name_2752_);
lean_ctor_set(v___x_2771_, 1, v___x_2770_);
v___x_2772_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2772_, 0, v___x_2769_);
lean_ctor_set(v___x_2772_, 1, v_a_2764_);
lean_ctor_set(v___x_2772_, 2, v___x_2771_);
if (v_isShared_2767_ == 0)
{
lean_ctor_set_tag(v___x_2766_, 2);
lean_ctor_set(v___x_2766_, 0, v___x_2772_);
v___x_2774_ = v___x_2766_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v___x_2772_);
v___x_2774_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
lean_object* v___x_2775_; 
v___x_2775_ = l_Lean_addDecl(v___x_2774_, v_hasTrace_2751_, v_a_2740_, v_a_2741_);
return v___x_2775_;
}
}
}
}
else
{
lean_object* v_a_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2786_; 
lean_dec(v_val_2758_);
lean_dec(v_name_2752_);
lean_del_object(v___x_2748_);
lean_dec(v_levelParams_2746_);
v_a_2779_ = lean_ctor_get(v___x_2759_, 0);
v_isSharedCheck_2786_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2786_ == 0)
{
v___x_2781_ = v___x_2759_;
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_a_2779_);
lean_dec(v___x_2759_);
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
else
{
lean_object* v___x_2787_; lean_object* v___x_2789_; 
lean_dec(v_a_2754_);
lean_dec(v_name_2752_);
lean_del_object(v___x_2748_);
lean_dec(v_levelParams_2746_);
lean_dec(v_name_2745_);
v___x_2787_ = lean_box(0);
if (v_isShared_2757_ == 0)
{
lean_ctor_set(v___x_2756_, 0, v___x_2787_);
v___x_2789_ = v___x_2756_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v___x_2787_);
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
lean_dec(v_name_2752_);
lean_del_object(v___x_2748_);
lean_dec(v_levelParams_2746_);
lean_dec(v_name_2745_);
v_a_2792_ = lean_ctor_get(v___x_2753_, 0);
v_isSharedCheck_2799_ = !lean_is_exclusive(v___x_2753_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2794_ = v___x_2753_;
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_a_2792_);
lean_dec(v___x_2753_);
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
lean_object* v___f_2800_; lean_object* v_cls_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; uint8_t v___x_2804_; lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v_a_2808_; lean_object* v___y_2818_; lean_object* v___y_2819_; lean_object* v_a_2820_; lean_object* v___y_2823_; lean_object* v___y_2824_; lean_object* v_a_2825_; lean_object* v___y_2828_; lean_object* v___y_2829_; lean_object* v___y_2830_; lean_object* v___y_2834_; lean_object* v___y_2835_; lean_object* v_a_2836_; lean_object* v___y_2849_; lean_object* v___y_2850_; lean_object* v_a_2851_; lean_object* v___y_2854_; lean_object* v___y_2855_; lean_object* v_a_2856_; lean_object* v___y_2859_; lean_object* v___y_2860_; lean_object* v___y_2861_; 
lean_inc(v_name_2752_);
v___f_2800_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2800_, 0, v_name_2752_);
v_cls_2801_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_2802_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_2803_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_2804_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2750_, v_options_2744_, v___x_2803_);
if (v___x_2804_ == 0)
{
lean_object* v___x_2899_; uint8_t v___x_2900_; 
v___x_2899_ = l_Lean_trace_profiler;
v___x_2900_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_2744_, v___x_2899_);
if (v___x_2900_ == 0)
{
lean_object* v___x_2901_; 
lean_dec_ref(v___f_2800_);
v___x_2901_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_);
if (lean_obj_tag(v___x_2901_) == 0)
{
lean_object* v_a_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2948_; 
v_a_2902_ = lean_ctor_get(v___x_2901_, 0);
v_isSharedCheck_2948_ = !lean_is_exclusive(v___x_2901_);
if (v_isSharedCheck_2948_ == 0)
{
v___x_2904_ = v___x_2901_;
v_isShared_2905_ = v_isSharedCheck_2948_;
goto v_resetjp_2903_;
}
else
{
lean_inc(v_a_2902_);
lean_dec(v___x_2901_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_2948_;
goto v_resetjp_2903_;
}
v_resetjp_2903_:
{
if (lean_obj_tag(v_a_2902_) == 1)
{
lean_object* v_val_2906_; lean_object* v___y_2908_; lean_object* v___y_2909_; lean_object* v___y_2910_; lean_object* v___y_2911_; 
lean_del_object(v___x_2904_);
v_val_2906_ = lean_ctor_get(v_a_2902_, 0);
lean_inc(v_val_2906_);
lean_dec_ref(v_a_2902_);
if (v___x_2804_ == 0)
{
v___y_2908_ = v_a_2738_;
v___y_2909_ = v_a_2739_;
v___y_2910_ = v_a_2740_;
v___y_2911_ = v_a_2741_;
goto v___jp_2907_;
}
else
{
lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; 
v___x_2940_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
lean_inc(v_val_2906_);
v___x_2941_ = l_Lean_MessageData_ofExpr(v_val_2906_);
v___x_2942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2940_);
lean_ctor_set(v___x_2942_, 1, v___x_2941_);
v___x_2943_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2801_, v___x_2942_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_);
if (lean_obj_tag(v___x_2943_) == 0)
{
lean_dec_ref(v___x_2943_);
v___y_2908_ = v_a_2738_;
v___y_2909_ = v_a_2739_;
v___y_2910_ = v_a_2740_;
v___y_2911_ = v_a_2741_;
goto v___jp_2907_;
}
else
{
lean_dec(v_val_2906_);
lean_dec(v_name_2752_);
lean_del_object(v___x_2748_);
lean_dec(v_levelParams_2746_);
lean_dec(v_name_2745_);
return v___x_2943_;
}
}
v___jp_2907_:
{
lean_object* v___x_2912_; 
lean_inc(v_val_2906_);
v___x_2912_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2745_, v_val_2906_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_);
if (lean_obj_tag(v___x_2912_) == 0)
{
lean_object* v_a_2913_; lean_object* v___x_2914_; lean_object* v_a_2915_; lean_object* v___x_2916_; lean_object* v_a_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2931_; 
v_a_2913_ = lean_ctor_get(v___x_2912_, 0);
lean_inc(v_a_2913_);
lean_dec_ref(v___x_2912_);
v___x_2914_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2906_, v___y_2909_);
v_a_2915_ = lean_ctor_get(v___x_2914_, 0);
lean_inc(v_a_2915_);
lean_dec_ref(v___x_2914_);
v___x_2916_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2913_, v___y_2909_);
v_a_2917_ = lean_ctor_get(v___x_2916_, 0);
v_isSharedCheck_2931_ = !lean_is_exclusive(v___x_2916_);
if (v_isSharedCheck_2931_ == 0)
{
v___x_2919_ = v___x_2916_;
v_isShared_2920_ = v_isSharedCheck_2931_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_a_2917_);
lean_dec(v___x_2916_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2931_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v___x_2922_; 
lean_inc(v_name_2752_);
if (v_isShared_2749_ == 0)
{
lean_ctor_set(v___x_2748_, 2, v_a_2915_);
lean_ctor_set(v___x_2748_, 0, v_name_2752_);
v___x_2922_ = v___x_2748_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v_name_2752_);
lean_ctor_set(v_reuseFailAlloc_2930_, 1, v_levelParams_2746_);
lean_ctor_set(v_reuseFailAlloc_2930_, 2, v_a_2915_);
v___x_2922_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2927_; 
v___x_2923_ = lean_box(0);
v___x_2924_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2924_, 0, v_name_2752_);
lean_ctor_set(v___x_2924_, 1, v___x_2923_);
v___x_2925_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2925_, 0, v___x_2922_);
lean_ctor_set(v___x_2925_, 1, v_a_2917_);
lean_ctor_set(v___x_2925_, 2, v___x_2924_);
if (v_isShared_2920_ == 0)
{
lean_ctor_set_tag(v___x_2919_, 2);
lean_ctor_set(v___x_2919_, 0, v___x_2925_);
v___x_2927_ = v___x_2919_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v___x_2925_);
v___x_2927_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
lean_object* v___x_2928_; 
v___x_2928_ = l_Lean_addDecl(v___x_2927_, v___x_2900_, v___y_2910_, v___y_2911_);
return v___x_2928_;
}
}
}
}
else
{
lean_object* v_a_2932_; lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_2939_; 
lean_dec(v_val_2906_);
lean_dec(v_name_2752_);
lean_del_object(v___x_2748_);
lean_dec(v_levelParams_2746_);
v_a_2932_ = lean_ctor_get(v___x_2912_, 0);
v_isSharedCheck_2939_ = !lean_is_exclusive(v___x_2912_);
if (v_isSharedCheck_2939_ == 0)
{
v___x_2934_ = v___x_2912_;
v_isShared_2935_ = v_isSharedCheck_2939_;
goto v_resetjp_2933_;
}
else
{
lean_inc(v_a_2932_);
lean_dec(v___x_2912_);
v___x_2934_ = lean_box(0);
v_isShared_2935_ = v_isSharedCheck_2939_;
goto v_resetjp_2933_;
}
v_resetjp_2933_:
{
lean_object* v___x_2937_; 
if (v_isShared_2935_ == 0)
{
v___x_2937_ = v___x_2934_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v_a_2932_);
v___x_2937_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
return v___x_2937_;
}
}
}
}
}
else
{
lean_object* v___x_2944_; lean_object* v___x_2946_; 
lean_dec(v_a_2902_);
lean_dec(v_name_2752_);
lean_del_object(v___x_2748_);
lean_dec(v_levelParams_2746_);
lean_dec(v_name_2745_);
v___x_2944_ = lean_box(0);
if (v_isShared_2905_ == 0)
{
lean_ctor_set(v___x_2904_, 0, v___x_2944_);
v___x_2946_ = v___x_2904_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v___x_2944_);
v___x_2946_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
return v___x_2946_;
}
}
}
}
else
{
lean_object* v_a_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2956_; 
lean_dec(v_name_2752_);
lean_del_object(v___x_2748_);
lean_dec(v_levelParams_2746_);
lean_dec(v_name_2745_);
v_a_2949_ = lean_ctor_get(v___x_2901_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v___x_2901_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2951_ = v___x_2901_;
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_a_2949_);
lean_dec(v___x_2901_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2954_; 
if (v_isShared_2952_ == 0)
{
v___x_2954_ = v___x_2951_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_a_2949_);
v___x_2954_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
return v___x_2954_;
}
}
}
}
else
{
lean_del_object(v___x_2748_);
goto v___jp_2864_;
}
}
else
{
lean_del_object(v___x_2748_);
goto v___jp_2864_;
}
v___jp_2805_:
{
lean_object* v___x_2809_; double v___x_2810_; double v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; 
v___x_2809_ = lean_io_get_num_heartbeats();
v___x_2810_ = lean_float_of_nat(v___y_2807_);
v___x_2811_ = lean_float_of_nat(v___x_2809_);
v___x_2812_ = lean_box_float(v___x_2810_);
v___x_2813_ = lean_box_float(v___x_2811_);
v___x_2814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2814_, 0, v___x_2812_);
lean_ctor_set(v___x_2814_, 1, v___x_2813_);
v___x_2815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2815_, 0, v_a_2808_);
lean_ctor_set(v___x_2815_, 1, v___x_2814_);
v___x_2816_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_2801_, v_hasTrace_2751_, v___x_2802_, v_options_2744_, v___x_2804_, v___y_2806_, v___f_2800_, v___x_2815_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_);
return v___x_2816_;
}
v___jp_2817_:
{
lean_object* v___x_2821_; 
v___x_2821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2821_, 0, v_a_2820_);
v___y_2806_ = v___y_2818_;
v___y_2807_ = v___y_2819_;
v_a_2808_ = v___x_2821_;
goto v___jp_2805_;
}
v___jp_2822_:
{
lean_object* v___x_2826_; 
v___x_2826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2826_, 0, v_a_2825_);
v___y_2806_ = v___y_2823_;
v___y_2807_ = v___y_2824_;
v_a_2808_ = v___x_2826_;
goto v___jp_2805_;
}
v___jp_2827_:
{
if (lean_obj_tag(v___y_2830_) == 0)
{
lean_object* v_a_2831_; 
v_a_2831_ = lean_ctor_get(v___y_2830_, 0);
lean_inc(v_a_2831_);
lean_dec_ref(v___y_2830_);
v___y_2823_ = v___y_2828_;
v___y_2824_ = v___y_2829_;
v_a_2825_ = v_a_2831_;
goto v___jp_2822_;
}
else
{
lean_object* v_a_2832_; 
v_a_2832_ = lean_ctor_get(v___y_2830_, 0);
lean_inc(v_a_2832_);
lean_dec_ref(v___y_2830_);
v___y_2818_ = v___y_2828_;
v___y_2819_ = v___y_2829_;
v_a_2820_ = v_a_2832_;
goto v___jp_2817_;
}
}
v___jp_2833_:
{
lean_object* v___x_2837_; double v___x_2838_; double v___x_2839_; double v___x_2840_; double v___x_2841_; double v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; 
v___x_2837_ = lean_io_mono_nanos_now();
v___x_2838_ = lean_float_of_nat(v___y_2835_);
v___x_2839_ = lean_float_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0);
v___x_2840_ = lean_float_div(v___x_2838_, v___x_2839_);
v___x_2841_ = lean_float_of_nat(v___x_2837_);
v___x_2842_ = lean_float_div(v___x_2841_, v___x_2839_);
v___x_2843_ = lean_box_float(v___x_2840_);
v___x_2844_ = lean_box_float(v___x_2842_);
v___x_2845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2845_, 0, v___x_2843_);
lean_ctor_set(v___x_2845_, 1, v___x_2844_);
v___x_2846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2846_, 0, v_a_2836_);
lean_ctor_set(v___x_2846_, 1, v___x_2845_);
v___x_2847_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_2801_, v_hasTrace_2751_, v___x_2802_, v_options_2744_, v___x_2804_, v___y_2834_, v___f_2800_, v___x_2846_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_);
return v___x_2847_;
}
v___jp_2848_:
{
lean_object* v___x_2852_; 
v___x_2852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2852_, 0, v_a_2851_);
v___y_2834_ = v___y_2850_;
v___y_2835_ = v___y_2849_;
v_a_2836_ = v___x_2852_;
goto v___jp_2833_;
}
v___jp_2853_:
{
lean_object* v___x_2857_; 
v___x_2857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2857_, 0, v_a_2856_);
v___y_2834_ = v___y_2855_;
v___y_2835_ = v___y_2854_;
v_a_2836_ = v___x_2857_;
goto v___jp_2833_;
}
v___jp_2858_:
{
if (lean_obj_tag(v___y_2861_) == 0)
{
lean_object* v_a_2862_; 
v_a_2862_ = lean_ctor_get(v___y_2861_, 0);
lean_inc(v_a_2862_);
lean_dec_ref(v___y_2861_);
v___y_2849_ = v___y_2860_;
v___y_2850_ = v___y_2859_;
v_a_2851_ = v_a_2862_;
goto v___jp_2848_;
}
else
{
lean_object* v_a_2863_; 
v_a_2863_ = lean_ctor_get(v___y_2861_, 0);
lean_inc(v_a_2863_);
lean_dec_ref(v___y_2861_);
v___y_2854_ = v___y_2860_;
v___y_2855_ = v___y_2859_;
v_a_2856_ = v_a_2863_;
goto v___jp_2853_;
}
}
v___jp_2864_:
{
lean_object* v___x_2865_; lean_object* v_a_2866_; lean_object* v___x_2867_; uint8_t v___x_2868_; 
v___x_2865_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v_a_2741_);
v_a_2866_ = lean_ctor_get(v___x_2865_, 0);
lean_inc(v_a_2866_);
lean_dec_ref(v___x_2865_);
v___x_2867_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2868_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_2744_, v___x_2867_);
if (v___x_2868_ == 0)
{
lean_object* v___x_2869_; lean_object* v___x_2870_; 
v___x_2869_ = lean_io_mono_nanos_now();
v___x_2870_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_);
if (lean_obj_tag(v___x_2870_) == 0)
{
lean_object* v_a_2871_; 
v_a_2871_ = lean_ctor_get(v___x_2870_, 0);
lean_inc(v_a_2871_);
lean_dec_ref(v___x_2870_);
if (lean_obj_tag(v_a_2871_) == 1)
{
if (v___x_2804_ == 0)
{
lean_object* v_val_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; 
v_val_2872_ = lean_ctor_get(v_a_2871_, 0);
lean_inc(v_val_2872_);
lean_dec_ref(v_a_2871_);
v___x_2873_ = lean_box(0);
v___x_2874_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(v_name_2745_, v_val_2872_, v_name_2752_, v_levelParams_2746_, v___x_2868_, v___x_2873_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_);
v___y_2859_ = v_a_2866_;
v___y_2860_ = v___x_2869_;
v___y_2861_ = v___x_2874_;
goto v___jp_2858_;
}
else
{
lean_object* v_val_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; 
v_val_2875_ = lean_ctor_get(v_a_2871_, 0);
lean_inc_n(v_val_2875_, 2);
lean_dec_ref(v_a_2871_);
v___x_2876_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_2877_ = l_Lean_MessageData_ofExpr(v_val_2875_);
v___x_2878_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2878_, 0, v___x_2876_);
lean_ctor_set(v___x_2878_, 1, v___x_2877_);
v___x_2879_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2801_, v___x_2878_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_);
if (lean_obj_tag(v___x_2879_) == 0)
{
lean_object* v_a_2880_; lean_object* v___x_2881_; 
v_a_2880_ = lean_ctor_get(v___x_2879_, 0);
lean_inc(v_a_2880_);
lean_dec_ref(v___x_2879_);
v___x_2881_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(v_name_2745_, v_val_2875_, v_name_2752_, v_levelParams_2746_, v___x_2868_, v_a_2880_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_);
v___y_2859_ = v_a_2866_;
v___y_2860_ = v___x_2869_;
v___y_2861_ = v___x_2881_;
goto v___jp_2858_;
}
else
{
lean_dec(v_val_2875_);
lean_dec(v_name_2752_);
lean_dec(v_levelParams_2746_);
lean_dec(v_name_2745_);
v___y_2859_ = v_a_2866_;
v___y_2860_ = v___x_2869_;
v___y_2861_ = v___x_2879_;
goto v___jp_2858_;
}
}
}
else
{
lean_object* v___x_2882_; 
lean_dec(v_a_2871_);
lean_dec(v_name_2752_);
lean_dec(v_levelParams_2746_);
lean_dec(v_name_2745_);
v___x_2882_ = lean_box(0);
v___y_2849_ = v___x_2869_;
v___y_2850_ = v_a_2866_;
v_a_2851_ = v___x_2882_;
goto v___jp_2848_;
}
}
else
{
lean_object* v_a_2883_; 
lean_dec(v_name_2752_);
lean_dec(v_levelParams_2746_);
lean_dec(v_name_2745_);
v_a_2883_ = lean_ctor_get(v___x_2870_, 0);
lean_inc(v_a_2883_);
lean_dec_ref(v___x_2870_);
v___y_2854_ = v___x_2869_;
v___y_2855_ = v_a_2866_;
v_a_2856_ = v_a_2883_;
goto v___jp_2853_;
}
}
else
{
lean_object* v___x_2884_; lean_object* v___x_2885_; 
v___x_2884_ = lean_io_get_num_heartbeats();
v___x_2885_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_);
if (lean_obj_tag(v___x_2885_) == 0)
{
lean_object* v_a_2886_; 
v_a_2886_ = lean_ctor_get(v___x_2885_, 0);
lean_inc(v_a_2886_);
lean_dec_ref(v___x_2885_);
if (lean_obj_tag(v_a_2886_) == 1)
{
if (v___x_2804_ == 0)
{
lean_object* v_val_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; 
v_val_2887_ = lean_ctor_get(v_a_2886_, 0);
lean_inc(v_val_2887_);
lean_dec_ref(v_a_2886_);
v___x_2888_ = lean_box(0);
v___x_2889_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(v_name_2745_, v_val_2887_, v_name_2752_, v_levelParams_2746_, v___x_2888_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_);
v___y_2828_ = v_a_2866_;
v___y_2829_ = v___x_2884_;
v___y_2830_ = v___x_2889_;
goto v___jp_2827_;
}
else
{
lean_object* v_val_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; 
v_val_2890_ = lean_ctor_get(v_a_2886_, 0);
lean_inc_n(v_val_2890_, 2);
lean_dec_ref(v_a_2886_);
v___x_2891_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_2892_ = l_Lean_MessageData_ofExpr(v_val_2890_);
v___x_2893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2893_, 0, v___x_2891_);
lean_ctor_set(v___x_2893_, 1, v___x_2892_);
v___x_2894_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2801_, v___x_2893_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_);
if (lean_obj_tag(v___x_2894_) == 0)
{
lean_object* v_a_2895_; lean_object* v___x_2896_; 
v_a_2895_ = lean_ctor_get(v___x_2894_, 0);
lean_inc(v_a_2895_);
lean_dec_ref(v___x_2894_);
v___x_2896_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(v_name_2745_, v_val_2890_, v_name_2752_, v_levelParams_2746_, v_a_2895_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_);
v___y_2828_ = v_a_2866_;
v___y_2829_ = v___x_2884_;
v___y_2830_ = v___x_2896_;
goto v___jp_2827_;
}
else
{
lean_dec(v_val_2890_);
lean_dec(v_name_2752_);
lean_dec(v_levelParams_2746_);
lean_dec(v_name_2745_);
v___y_2828_ = v_a_2866_;
v___y_2829_ = v___x_2884_;
v___y_2830_ = v___x_2894_;
goto v___jp_2827_;
}
}
}
else
{
lean_object* v___x_2897_; 
lean_dec(v_a_2886_);
lean_dec(v_name_2752_);
lean_dec(v_levelParams_2746_);
lean_dec(v_name_2745_);
v___x_2897_ = lean_box(0);
v___y_2823_ = v_a_2866_;
v___y_2824_ = v___x_2884_;
v_a_2825_ = v___x_2897_;
goto v___jp_2822_;
}
}
else
{
lean_object* v_a_2898_; 
lean_dec(v_name_2752_);
lean_dec(v_levelParams_2746_);
lean_dec(v_name_2745_);
v_a_2898_ = lean_ctor_get(v___x_2885_, 0);
lean_inc(v_a_2898_);
lean_dec_ref(v___x_2885_);
v___y_2818_ = v_a_2866_;
v___y_2819_ = v___x_2884_;
v_a_2820_ = v_a_2898_;
goto v___jp_2817_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___boxed(lean_object* v_ctorVal_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_){
_start:
{
lean_object* v_res_2965_; 
v_res_2965_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(v_ctorVal_2959_, v_a_2960_, v_a_2961_, v_a_2962_, v_a_2963_);
lean_dec(v_a_2963_);
lean_dec_ref(v_a_2962_);
lean_dec(v_a_2961_);
lean_dec_ref(v_a_2960_);
return v_res_2965_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5(lean_object* v_00_u03b1_2966_, lean_object* v_x_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_){
_start:
{
lean_object* v___x_2973_; 
v___x_2973_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___redArg(v_x_2967_);
return v___x_2973_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2974_, lean_object* v_x_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_){
_start:
{
lean_object* v_res_2981_; 
v_res_2981_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5(v_00_u03b1_2974_, v_x_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_);
lean_dec(v___y_2979_);
lean_dec_ref(v___y_2978_);
lean_dec(v___y_2977_);
lean_dec_ref(v___y_2976_);
return v_res_2981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveEqTheoremNameFor(lean_object* v_ctorName_2985_){
_start:
{
lean_object* v___x_2986_; lean_object* v___x_2987_; 
v___x_2986_ = ((lean_object*)(l_Lean_Meta_mkInjectiveEqTheoremNameFor___closed__1));
v___x_2987_ = l_Lean_Name_append(v_ctorName_2985_, v___x_2986_);
return v___x_2987_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(lean_object* v_ctorVal_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_){
_start:
{
uint8_t v___x_2994_; lean_object* v___x_2995_; 
v___x_2994_ = 1;
v___x_2995_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(v_ctorVal_2988_, v___x_2994_, v_a_2989_, v_a_2990_, v_a_2991_, v_a_2992_);
return v___x_2995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f___boxed(lean_object* v_ctorVal_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_){
_start:
{
lean_object* v_res_3002_; 
v_res_3002_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_2996_, v_a_2997_, v_a_2998_, v_a_2999_, v_a_3000_);
lean_dec(v_a_3000_);
lean_dec_ref(v_a_2999_);
lean_dec(v_a_2998_);
lean_dec_ref(v_a_2997_);
return v_res_3002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(lean_object* v_e_3003_, lean_object* v_t_3004_, lean_object* v_acc_3005_, lean_object* v_a_3006_){
_start:
{
lean_object* v___x_3008_; 
v___x_3008_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_t_3004_, v_a_3006_);
if (lean_obj_tag(v___x_3008_) == 0)
{
lean_object* v_a_3009_; lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3032_; 
v_a_3009_ = lean_ctor_get(v___x_3008_, 0);
v_isSharedCheck_3032_ = !lean_is_exclusive(v___x_3008_);
if (v_isSharedCheck_3032_ == 0)
{
v___x_3011_ = v___x_3008_;
v_isShared_3012_ = v_isSharedCheck_3032_;
goto v_resetjp_3010_;
}
else
{
lean_inc(v_a_3009_);
lean_dec(v___x_3008_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3032_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
lean_object* v___x_3018_; uint8_t v___x_3019_; 
v___x_3018_ = l_Lean_Expr_cleanupAnnotations(v_a_3009_);
v___x_3019_ = l_Lean_Expr_isApp(v___x_3018_);
if (v___x_3019_ == 0)
{
lean_dec_ref(v___x_3018_);
goto v___jp_3013_;
}
else
{
lean_object* v_arg_3020_; lean_object* v___x_3021_; uint8_t v___x_3022_; 
v_arg_3020_ = lean_ctor_get(v___x_3018_, 1);
lean_inc_ref(v_arg_3020_);
v___x_3021_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3018_);
v___x_3022_ = l_Lean_Expr_isApp(v___x_3021_);
if (v___x_3022_ == 0)
{
lean_dec_ref(v___x_3021_);
lean_dec_ref(v_arg_3020_);
goto v___jp_3013_;
}
else
{
lean_object* v_arg_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; uint8_t v___x_3026_; 
v_arg_3023_ = lean_ctor_get(v___x_3021_, 1);
lean_inc_ref(v_arg_3023_);
v___x_3024_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3021_);
v___x_3025_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__1));
v___x_3026_ = l_Lean_Expr_isConstOf(v___x_3024_, v___x_3025_);
lean_dec_ref(v___x_3024_);
if (v___x_3026_ == 0)
{
lean_dec_ref(v_arg_3023_);
lean_dec_ref(v_arg_3020_);
goto v___jp_3013_;
}
else
{
lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; 
lean_del_object(v___x_3011_);
v___x_3027_ = lean_unsigned_to_nat(0u);
v___x_3028_ = l_Lean_mkProj(v___x_3025_, v___x_3027_, v_e_3003_);
lean_inc_ref(v___x_3028_);
v___x_3029_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v___x_3028_, v_arg_3023_, v_acc_3005_, v_a_3006_);
if (lean_obj_tag(v___x_3029_) == 0)
{
lean_object* v_a_3030_; 
v_a_3030_ = lean_ctor_get(v___x_3029_, 0);
lean_inc(v_a_3030_);
lean_dec_ref(v___x_3029_);
v_e_3003_ = v___x_3028_;
v_t_3004_ = v_arg_3020_;
v_acc_3005_ = v_a_3030_;
goto _start;
}
else
{
lean_dec_ref(v___x_3028_);
lean_dec_ref(v_arg_3020_);
return v___x_3029_;
}
}
}
}
v___jp_3013_:
{
lean_object* v___x_3014_; lean_object* v___x_3016_; 
v___x_3014_ = lean_array_push(v_acc_3005_, v_e_3003_);
if (v_isShared_3012_ == 0)
{
lean_ctor_set(v___x_3011_, 0, v___x_3014_);
v___x_3016_ = v___x_3011_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v___x_3014_);
v___x_3016_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
return v___x_3016_;
}
}
}
}
else
{
lean_object* v_a_3033_; lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3040_; 
lean_dec_ref(v_acc_3005_);
lean_dec_ref(v_e_3003_);
v_a_3033_ = lean_ctor_get(v___x_3008_, 0);
v_isSharedCheck_3040_ = !lean_is_exclusive(v___x_3008_);
if (v_isSharedCheck_3040_ == 0)
{
v___x_3035_ = v___x_3008_;
v_isShared_3036_ = v_isSharedCheck_3040_;
goto v_resetjp_3034_;
}
else
{
lean_inc(v_a_3033_);
lean_dec(v___x_3008_);
v___x_3035_ = lean_box(0);
v_isShared_3036_ = v_isSharedCheck_3040_;
goto v_resetjp_3034_;
}
v_resetjp_3034_:
{
lean_object* v___x_3038_; 
if (v_isShared_3036_ == 0)
{
v___x_3038_ = v___x_3035_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3039_; 
v_reuseFailAlloc_3039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3039_, 0, v_a_3033_);
v___x_3038_ = v_reuseFailAlloc_3039_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
return v___x_3038_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg___boxed(lean_object* v_e_3041_, lean_object* v_t_3042_, lean_object* v_acc_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_){
_start:
{
lean_object* v_res_3046_; 
v_res_3046_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v_e_3041_, v_t_3042_, v_acc_3043_, v_a_3044_);
lean_dec(v_a_3044_);
return v_res_3046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go(lean_object* v_e_3047_, lean_object* v_t_3048_, lean_object* v_acc_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_){
_start:
{
lean_object* v___x_3055_; 
v___x_3055_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v_e_3047_, v_t_3048_, v_acc_3049_, v_a_3051_);
return v___x_3055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___boxed(lean_object* v_e_3056_, lean_object* v_t_3057_, lean_object* v_acc_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_){
_start:
{
lean_object* v_res_3064_; 
v_res_3064_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go(v_e_3056_, v_t_3057_, v_acc_3058_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_);
lean_dec(v_a_3062_);
lean_dec_ref(v_a_3061_);
lean_dec(v_a_3060_);
lean_dec_ref(v_a_3059_);
return v_res_3064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections(lean_object* v_e_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_){
_start:
{
lean_object* v___x_3071_; 
lean_inc(v_a_3069_);
lean_inc_ref(v_a_3068_);
lean_inc(v_a_3067_);
lean_inc_ref(v_a_3066_);
lean_inc_ref(v_e_3065_);
v___x_3071_ = lean_infer_type(v_e_3065_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
if (lean_obj_tag(v___x_3071_) == 0)
{
lean_object* v_a_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; 
v_a_3072_ = lean_ctor_get(v___x_3071_, 0);
lean_inc(v_a_3072_);
lean_dec_ref(v___x_3071_);
v___x_3073_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_3074_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v_e_3065_, v_a_3072_, v___x_3073_, v_a_3067_);
return v___x_3074_;
}
else
{
lean_object* v_a_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3082_; 
lean_dec_ref(v_e_3065_);
v_a_3075_ = lean_ctor_get(v___x_3071_, 0);
v_isSharedCheck_3082_ = !lean_is_exclusive(v___x_3071_);
if (v_isSharedCheck_3082_ == 0)
{
v___x_3077_ = v___x_3071_;
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_a_3075_);
lean_dec(v___x_3071_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
lean_object* v___x_3080_; 
if (v_isShared_3078_ == 0)
{
v___x_3080_ = v___x_3077_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v_a_3075_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections___boxed(lean_object* v_e_3083_, lean_object* v_a_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_){
_start:
{
lean_object* v_res_3089_; 
v_res_3089_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections(v_e_3083_, v_a_3084_, v_a_3085_, v_a_3086_, v_a_3087_);
lean_dec(v_a_3087_);
lean_dec_ref(v_a_3086_);
lean_dec(v_a_3085_);
lean_dec_ref(v_a_3084_);
return v_res_3089_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_x_3090_, lean_object* v_x_3091_, lean_object* v_x_3092_, lean_object* v_x_3093_){
_start:
{
lean_object* v_ks_3094_; lean_object* v_vs_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3119_; 
v_ks_3094_ = lean_ctor_get(v_x_3090_, 0);
v_vs_3095_ = lean_ctor_get(v_x_3090_, 1);
v_isSharedCheck_3119_ = !lean_is_exclusive(v_x_3090_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3097_ = v_x_3090_;
v_isShared_3098_ = v_isSharedCheck_3119_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_vs_3095_);
lean_inc(v_ks_3094_);
lean_dec(v_x_3090_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3119_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v___x_3099_; uint8_t v___x_3100_; 
v___x_3099_ = lean_array_get_size(v_ks_3094_);
v___x_3100_ = lean_nat_dec_lt(v_x_3091_, v___x_3099_);
if (v___x_3100_ == 0)
{
lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3104_; 
lean_dec(v_x_3091_);
v___x_3101_ = lean_array_push(v_ks_3094_, v_x_3092_);
v___x_3102_ = lean_array_push(v_vs_3095_, v_x_3093_);
if (v_isShared_3098_ == 0)
{
lean_ctor_set(v___x_3097_, 1, v___x_3102_);
lean_ctor_set(v___x_3097_, 0, v___x_3101_);
v___x_3104_ = v___x_3097_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v___x_3101_);
lean_ctor_set(v_reuseFailAlloc_3105_, 1, v___x_3102_);
v___x_3104_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
return v___x_3104_;
}
}
else
{
lean_object* v_k_x27_3106_; uint8_t v___x_3107_; 
v_k_x27_3106_ = lean_array_fget_borrowed(v_ks_3094_, v_x_3091_);
v___x_3107_ = l_Lean_instBEqMVarId_beq(v_x_3092_, v_k_x27_3106_);
if (v___x_3107_ == 0)
{
lean_object* v___x_3109_; 
if (v_isShared_3098_ == 0)
{
v___x_3109_ = v___x_3097_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v_ks_3094_);
lean_ctor_set(v_reuseFailAlloc_3113_, 1, v_vs_3095_);
v___x_3109_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
lean_object* v___x_3110_; lean_object* v___x_3111_; 
v___x_3110_ = lean_unsigned_to_nat(1u);
v___x_3111_ = lean_nat_add(v_x_3091_, v___x_3110_);
lean_dec(v_x_3091_);
v_x_3090_ = v___x_3109_;
v_x_3091_ = v___x_3111_;
goto _start;
}
}
else
{
lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3117_; 
v___x_3114_ = lean_array_fset(v_ks_3094_, v_x_3091_, v_x_3092_);
v___x_3115_ = lean_array_fset(v_vs_3095_, v_x_3091_, v_x_3093_);
lean_dec(v_x_3091_);
if (v_isShared_3098_ == 0)
{
lean_ctor_set(v___x_3097_, 1, v___x_3115_);
lean_ctor_set(v___x_3097_, 0, v___x_3114_);
v___x_3117_ = v___x_3097_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v___x_3114_);
lean_ctor_set(v_reuseFailAlloc_3118_, 1, v___x_3115_);
v___x_3117_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
return v___x_3117_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_n_3120_, lean_object* v_k_3121_, lean_object* v_v_3122_){
_start:
{
lean_object* v___x_3123_; lean_object* v___x_3124_; 
v___x_3123_ = lean_unsigned_to_nat(0u);
v___x_3124_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_n_3120_, v___x_3123_, v_k_3121_, v_v_3122_);
return v___x_3124_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_3125_; size_t v___x_3126_; size_t v___x_3127_; 
v___x_3125_ = ((size_t)5ULL);
v___x_3126_ = ((size_t)1ULL);
v___x_3127_ = lean_usize_shift_left(v___x_3126_, v___x_3125_);
return v___x_3127_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_3128_; size_t v___x_3129_; size_t v___x_3130_; 
v___x_3128_ = ((size_t)1ULL);
v___x_3129_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_3130_ = lean_usize_sub(v___x_3129_, v___x_3128_);
return v___x_3130_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_3131_; 
v___x_3131_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_3131_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(lean_object* v_x_3132_, size_t v_x_3133_, size_t v_x_3134_, lean_object* v_x_3135_, lean_object* v_x_3136_){
_start:
{
if (lean_obj_tag(v_x_3132_) == 0)
{
lean_object* v_es_3137_; size_t v___x_3138_; size_t v___x_3139_; size_t v___x_3140_; size_t v___x_3141_; lean_object* v_j_3142_; lean_object* v___x_3143_; uint8_t v___x_3144_; 
v_es_3137_ = lean_ctor_get(v_x_3132_, 0);
v___x_3138_ = ((size_t)5ULL);
v___x_3139_ = ((size_t)1ULL);
v___x_3140_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_3141_ = lean_usize_land(v_x_3133_, v___x_3140_);
v_j_3142_ = lean_usize_to_nat(v___x_3141_);
v___x_3143_ = lean_array_get_size(v_es_3137_);
v___x_3144_ = lean_nat_dec_lt(v_j_3142_, v___x_3143_);
if (v___x_3144_ == 0)
{
lean_dec(v_j_3142_);
lean_dec(v_x_3136_);
lean_dec(v_x_3135_);
return v_x_3132_;
}
else
{
lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3181_; 
lean_inc_ref(v_es_3137_);
v_isSharedCheck_3181_ = !lean_is_exclusive(v_x_3132_);
if (v_isSharedCheck_3181_ == 0)
{
lean_object* v_unused_3182_; 
v_unused_3182_ = lean_ctor_get(v_x_3132_, 0);
lean_dec(v_unused_3182_);
v___x_3146_ = v_x_3132_;
v_isShared_3147_ = v_isSharedCheck_3181_;
goto v_resetjp_3145_;
}
else
{
lean_dec(v_x_3132_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3181_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v_v_3148_; lean_object* v___x_3149_; lean_object* v_xs_x27_3150_; lean_object* v___y_3152_; 
v_v_3148_ = lean_array_fget(v_es_3137_, v_j_3142_);
v___x_3149_ = lean_box(0);
v_xs_x27_3150_ = lean_array_fset(v_es_3137_, v_j_3142_, v___x_3149_);
switch(lean_obj_tag(v_v_3148_))
{
case 0:
{
lean_object* v_key_3157_; lean_object* v_val_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3168_; 
v_key_3157_ = lean_ctor_get(v_v_3148_, 0);
v_val_3158_ = lean_ctor_get(v_v_3148_, 1);
v_isSharedCheck_3168_ = !lean_is_exclusive(v_v_3148_);
if (v_isSharedCheck_3168_ == 0)
{
v___x_3160_ = v_v_3148_;
v_isShared_3161_ = v_isSharedCheck_3168_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_val_3158_);
lean_inc(v_key_3157_);
lean_dec(v_v_3148_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3168_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
uint8_t v___x_3162_; 
v___x_3162_ = l_Lean_instBEqMVarId_beq(v_x_3135_, v_key_3157_);
if (v___x_3162_ == 0)
{
lean_object* v___x_3163_; lean_object* v___x_3164_; 
lean_del_object(v___x_3160_);
v___x_3163_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3157_, v_val_3158_, v_x_3135_, v_x_3136_);
v___x_3164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3164_, 0, v___x_3163_);
v___y_3152_ = v___x_3164_;
goto v___jp_3151_;
}
else
{
lean_object* v___x_3166_; 
lean_dec(v_val_3158_);
lean_dec(v_key_3157_);
if (v_isShared_3161_ == 0)
{
lean_ctor_set(v___x_3160_, 1, v_x_3136_);
lean_ctor_set(v___x_3160_, 0, v_x_3135_);
v___x_3166_ = v___x_3160_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3167_; 
v_reuseFailAlloc_3167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3167_, 0, v_x_3135_);
lean_ctor_set(v_reuseFailAlloc_3167_, 1, v_x_3136_);
v___x_3166_ = v_reuseFailAlloc_3167_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
v___y_3152_ = v___x_3166_;
goto v___jp_3151_;
}
}
}
}
case 1:
{
lean_object* v_node_3169_; lean_object* v___x_3171_; uint8_t v_isShared_3172_; uint8_t v_isSharedCheck_3179_; 
v_node_3169_ = lean_ctor_get(v_v_3148_, 0);
v_isSharedCheck_3179_ = !lean_is_exclusive(v_v_3148_);
if (v_isSharedCheck_3179_ == 0)
{
v___x_3171_ = v_v_3148_;
v_isShared_3172_ = v_isSharedCheck_3179_;
goto v_resetjp_3170_;
}
else
{
lean_inc(v_node_3169_);
lean_dec(v_v_3148_);
v___x_3171_ = lean_box(0);
v_isShared_3172_ = v_isSharedCheck_3179_;
goto v_resetjp_3170_;
}
v_resetjp_3170_:
{
size_t v___x_3173_; size_t v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3177_; 
v___x_3173_ = lean_usize_shift_right(v_x_3133_, v___x_3138_);
v___x_3174_ = lean_usize_add(v_x_3134_, v___x_3139_);
v___x_3175_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_node_3169_, v___x_3173_, v___x_3174_, v_x_3135_, v_x_3136_);
if (v_isShared_3172_ == 0)
{
lean_ctor_set(v___x_3171_, 0, v___x_3175_);
v___x_3177_ = v___x_3171_;
goto v_reusejp_3176_;
}
else
{
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v___x_3175_);
v___x_3177_ = v_reuseFailAlloc_3178_;
goto v_reusejp_3176_;
}
v_reusejp_3176_:
{
v___y_3152_ = v___x_3177_;
goto v___jp_3151_;
}
}
}
default: 
{
lean_object* v___x_3180_; 
v___x_3180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3180_, 0, v_x_3135_);
lean_ctor_set(v___x_3180_, 1, v_x_3136_);
v___y_3152_ = v___x_3180_;
goto v___jp_3151_;
}
}
v___jp_3151_:
{
lean_object* v___x_3153_; lean_object* v___x_3155_; 
v___x_3153_ = lean_array_fset(v_xs_x27_3150_, v_j_3142_, v___y_3152_);
lean_dec(v_j_3142_);
if (v_isShared_3147_ == 0)
{
lean_ctor_set(v___x_3146_, 0, v___x_3153_);
v___x_3155_ = v___x_3146_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v___x_3153_);
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
else
{
lean_object* v_ks_3183_; lean_object* v_vs_3184_; lean_object* v___x_3186_; uint8_t v_isShared_3187_; uint8_t v_isSharedCheck_3204_; 
v_ks_3183_ = lean_ctor_get(v_x_3132_, 0);
v_vs_3184_ = lean_ctor_get(v_x_3132_, 1);
v_isSharedCheck_3204_ = !lean_is_exclusive(v_x_3132_);
if (v_isSharedCheck_3204_ == 0)
{
v___x_3186_ = v_x_3132_;
v_isShared_3187_ = v_isSharedCheck_3204_;
goto v_resetjp_3185_;
}
else
{
lean_inc(v_vs_3184_);
lean_inc(v_ks_3183_);
lean_dec(v_x_3132_);
v___x_3186_ = lean_box(0);
v_isShared_3187_ = v_isSharedCheck_3204_;
goto v_resetjp_3185_;
}
v_resetjp_3185_:
{
lean_object* v___x_3189_; 
if (v_isShared_3187_ == 0)
{
v___x_3189_ = v___x_3186_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v_ks_3183_);
lean_ctor_set(v_reuseFailAlloc_3203_, 1, v_vs_3184_);
v___x_3189_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
lean_object* v_newNode_3190_; uint8_t v___y_3192_; size_t v___x_3198_; uint8_t v___x_3199_; 
v_newNode_3190_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(v___x_3189_, v_x_3135_, v_x_3136_);
v___x_3198_ = ((size_t)7ULL);
v___x_3199_ = lean_usize_dec_le(v___x_3198_, v_x_3134_);
if (v___x_3199_ == 0)
{
lean_object* v___x_3200_; lean_object* v___x_3201_; uint8_t v___x_3202_; 
v___x_3200_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3190_);
v___x_3201_ = lean_unsigned_to_nat(4u);
v___x_3202_ = lean_nat_dec_lt(v___x_3200_, v___x_3201_);
lean_dec(v___x_3200_);
v___y_3192_ = v___x_3202_;
goto v___jp_3191_;
}
else
{
v___y_3192_ = v___x_3199_;
goto v___jp_3191_;
}
v___jp_3191_:
{
if (v___y_3192_ == 0)
{
lean_object* v_ks_3193_; lean_object* v_vs_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; 
v_ks_3193_ = lean_ctor_get(v_newNode_3190_, 0);
lean_inc_ref(v_ks_3193_);
v_vs_3194_ = lean_ctor_get(v_newNode_3190_, 1);
lean_inc_ref(v_vs_3194_);
lean_dec_ref(v_newNode_3190_);
v___x_3195_ = lean_unsigned_to_nat(0u);
v___x_3196_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__2);
v___x_3197_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(v_x_3134_, v_ks_3193_, v_vs_3194_, v___x_3195_, v___x_3196_);
lean_dec_ref(v_vs_3194_);
lean_dec_ref(v_ks_3193_);
return v___x_3197_;
}
else
{
return v_newNode_3190_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(size_t v_depth_3205_, lean_object* v_keys_3206_, lean_object* v_vals_3207_, lean_object* v_i_3208_, lean_object* v_entries_3209_){
_start:
{
lean_object* v___x_3210_; uint8_t v___x_3211_; 
v___x_3210_ = lean_array_get_size(v_keys_3206_);
v___x_3211_ = lean_nat_dec_lt(v_i_3208_, v___x_3210_);
if (v___x_3211_ == 0)
{
lean_dec(v_i_3208_);
return v_entries_3209_;
}
else
{
lean_object* v_k_3212_; lean_object* v_v_3213_; uint64_t v___x_3214_; size_t v_h_3215_; size_t v___x_3216_; lean_object* v___x_3217_; size_t v___x_3218_; size_t v___x_3219_; size_t v___x_3220_; size_t v_h_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; 
v_k_3212_ = lean_array_fget_borrowed(v_keys_3206_, v_i_3208_);
v_v_3213_ = lean_array_fget_borrowed(v_vals_3207_, v_i_3208_);
v___x_3214_ = l_Lean_instHashableMVarId_hash(v_k_3212_);
v_h_3215_ = lean_uint64_to_usize(v___x_3214_);
v___x_3216_ = ((size_t)5ULL);
v___x_3217_ = lean_unsigned_to_nat(1u);
v___x_3218_ = ((size_t)1ULL);
v___x_3219_ = lean_usize_sub(v_depth_3205_, v___x_3218_);
v___x_3220_ = lean_usize_mul(v___x_3216_, v___x_3219_);
v_h_3221_ = lean_usize_shift_right(v_h_3215_, v___x_3220_);
v___x_3222_ = lean_nat_add(v_i_3208_, v___x_3217_);
lean_dec(v_i_3208_);
lean_inc(v_v_3213_);
lean_inc(v_k_3212_);
v___x_3223_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_entries_3209_, v_h_3221_, v_depth_3205_, v_k_3212_, v_v_3213_);
v_i_3208_ = v___x_3222_;
v_entries_3209_ = v___x_3223_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_depth_3225_, lean_object* v_keys_3226_, lean_object* v_vals_3227_, lean_object* v_i_3228_, lean_object* v_entries_3229_){
_start:
{
size_t v_depth_boxed_3230_; lean_object* v_res_3231_; 
v_depth_boxed_3230_ = lean_unbox_usize(v_depth_3225_);
lean_dec(v_depth_3225_);
v_res_3231_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_boxed_3230_, v_keys_3226_, v_vals_3227_, v_i_3228_, v_entries_3229_);
lean_dec_ref(v_vals_3227_);
lean_dec_ref(v_keys_3226_);
return v_res_3231_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_3232_, lean_object* v_x_3233_, lean_object* v_x_3234_, lean_object* v_x_3235_, lean_object* v_x_3236_){
_start:
{
size_t v_x_5659__boxed_3237_; size_t v_x_5660__boxed_3238_; lean_object* v_res_3239_; 
v_x_5659__boxed_3237_ = lean_unbox_usize(v_x_3233_);
lean_dec(v_x_3233_);
v_x_5660__boxed_3238_ = lean_unbox_usize(v_x_3234_);
lean_dec(v_x_3234_);
v_res_3239_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_x_3232_, v_x_5659__boxed_3237_, v_x_5660__boxed_3238_, v_x_3235_, v_x_3236_);
return v_res_3239_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(lean_object* v_x_3240_, lean_object* v_x_3241_, lean_object* v_x_3242_){
_start:
{
uint64_t v___x_3243_; size_t v___x_3244_; size_t v___x_3245_; lean_object* v___x_3246_; 
v___x_3243_ = l_Lean_instHashableMVarId_hash(v_x_3241_);
v___x_3244_ = lean_uint64_to_usize(v___x_3243_);
v___x_3245_ = ((size_t)1ULL);
v___x_3246_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_x_3240_, v___x_3244_, v___x_3245_, v_x_3241_, v_x_3242_);
return v___x_3246_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(lean_object* v_mvarId_3247_, lean_object* v_val_3248_, lean_object* v___y_3249_){
_start:
{
lean_object* v___x_3251_; lean_object* v_mctx_3252_; lean_object* v_cache_3253_; lean_object* v_zetaDeltaFVarIds_3254_; lean_object* v_postponed_3255_; lean_object* v_diag_3256_; lean_object* v___x_3258_; uint8_t v_isShared_3259_; uint8_t v_isSharedCheck_3284_; 
v___x_3251_ = lean_st_ref_take(v___y_3249_);
v_mctx_3252_ = lean_ctor_get(v___x_3251_, 0);
v_cache_3253_ = lean_ctor_get(v___x_3251_, 1);
v_zetaDeltaFVarIds_3254_ = lean_ctor_get(v___x_3251_, 2);
v_postponed_3255_ = lean_ctor_get(v___x_3251_, 3);
v_diag_3256_ = lean_ctor_get(v___x_3251_, 4);
v_isSharedCheck_3284_ = !lean_is_exclusive(v___x_3251_);
if (v_isSharedCheck_3284_ == 0)
{
v___x_3258_ = v___x_3251_;
v_isShared_3259_ = v_isSharedCheck_3284_;
goto v_resetjp_3257_;
}
else
{
lean_inc(v_diag_3256_);
lean_inc(v_postponed_3255_);
lean_inc(v_zetaDeltaFVarIds_3254_);
lean_inc(v_cache_3253_);
lean_inc(v_mctx_3252_);
lean_dec(v___x_3251_);
v___x_3258_ = lean_box(0);
v_isShared_3259_ = v_isSharedCheck_3284_;
goto v_resetjp_3257_;
}
v_resetjp_3257_:
{
lean_object* v_depth_3260_; lean_object* v_levelAssignDepth_3261_; lean_object* v_lmvarCounter_3262_; lean_object* v_mvarCounter_3263_; lean_object* v_lDecls_3264_; lean_object* v_decls_3265_; lean_object* v_userNames_3266_; lean_object* v_lAssignment_3267_; lean_object* v_eAssignment_3268_; lean_object* v_dAssignment_3269_; lean_object* v___x_3271_; uint8_t v_isShared_3272_; uint8_t v_isSharedCheck_3283_; 
v_depth_3260_ = lean_ctor_get(v_mctx_3252_, 0);
v_levelAssignDepth_3261_ = lean_ctor_get(v_mctx_3252_, 1);
v_lmvarCounter_3262_ = lean_ctor_get(v_mctx_3252_, 2);
v_mvarCounter_3263_ = lean_ctor_get(v_mctx_3252_, 3);
v_lDecls_3264_ = lean_ctor_get(v_mctx_3252_, 4);
v_decls_3265_ = lean_ctor_get(v_mctx_3252_, 5);
v_userNames_3266_ = lean_ctor_get(v_mctx_3252_, 6);
v_lAssignment_3267_ = lean_ctor_get(v_mctx_3252_, 7);
v_eAssignment_3268_ = lean_ctor_get(v_mctx_3252_, 8);
v_dAssignment_3269_ = lean_ctor_get(v_mctx_3252_, 9);
v_isSharedCheck_3283_ = !lean_is_exclusive(v_mctx_3252_);
if (v_isSharedCheck_3283_ == 0)
{
v___x_3271_ = v_mctx_3252_;
v_isShared_3272_ = v_isSharedCheck_3283_;
goto v_resetjp_3270_;
}
else
{
lean_inc(v_dAssignment_3269_);
lean_inc(v_eAssignment_3268_);
lean_inc(v_lAssignment_3267_);
lean_inc(v_userNames_3266_);
lean_inc(v_decls_3265_);
lean_inc(v_lDecls_3264_);
lean_inc(v_mvarCounter_3263_);
lean_inc(v_lmvarCounter_3262_);
lean_inc(v_levelAssignDepth_3261_);
lean_inc(v_depth_3260_);
lean_dec(v_mctx_3252_);
v___x_3271_ = lean_box(0);
v_isShared_3272_ = v_isSharedCheck_3283_;
goto v_resetjp_3270_;
}
v_resetjp_3270_:
{
lean_object* v___x_3273_; lean_object* v___x_3275_; 
v___x_3273_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(v_eAssignment_3268_, v_mvarId_3247_, v_val_3248_);
if (v_isShared_3272_ == 0)
{
lean_ctor_set(v___x_3271_, 8, v___x_3273_);
v___x_3275_ = v___x_3271_;
goto v_reusejp_3274_;
}
else
{
lean_object* v_reuseFailAlloc_3282_; 
v_reuseFailAlloc_3282_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3282_, 0, v_depth_3260_);
lean_ctor_set(v_reuseFailAlloc_3282_, 1, v_levelAssignDepth_3261_);
lean_ctor_set(v_reuseFailAlloc_3282_, 2, v_lmvarCounter_3262_);
lean_ctor_set(v_reuseFailAlloc_3282_, 3, v_mvarCounter_3263_);
lean_ctor_set(v_reuseFailAlloc_3282_, 4, v_lDecls_3264_);
lean_ctor_set(v_reuseFailAlloc_3282_, 5, v_decls_3265_);
lean_ctor_set(v_reuseFailAlloc_3282_, 6, v_userNames_3266_);
lean_ctor_set(v_reuseFailAlloc_3282_, 7, v_lAssignment_3267_);
lean_ctor_set(v_reuseFailAlloc_3282_, 8, v___x_3273_);
lean_ctor_set(v_reuseFailAlloc_3282_, 9, v_dAssignment_3269_);
v___x_3275_ = v_reuseFailAlloc_3282_;
goto v_reusejp_3274_;
}
v_reusejp_3274_:
{
lean_object* v___x_3277_; 
if (v_isShared_3259_ == 0)
{
lean_ctor_set(v___x_3258_, 0, v___x_3275_);
v___x_3277_ = v___x_3258_;
goto v_reusejp_3276_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v___x_3275_);
lean_ctor_set(v_reuseFailAlloc_3281_, 1, v_cache_3253_);
lean_ctor_set(v_reuseFailAlloc_3281_, 2, v_zetaDeltaFVarIds_3254_);
lean_ctor_set(v_reuseFailAlloc_3281_, 3, v_postponed_3255_);
lean_ctor_set(v_reuseFailAlloc_3281_, 4, v_diag_3256_);
v___x_3277_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3276_;
}
v_reusejp_3276_:
{
lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; 
v___x_3278_ = lean_st_ref_set(v___y_3249_, v___x_3277_);
v___x_3279_ = lean_box(0);
v___x_3280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3280_, 0, v___x_3279_);
return v___x_3280_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg___boxed(lean_object* v_mvarId_3285_, lean_object* v_val_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_){
_start:
{
lean_object* v_res_3289_; 
v_res_3289_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(v_mvarId_3285_, v_val_3286_, v___y_3287_);
lean_dec(v___y_3287_);
return v_res_3289_;
}
}
static lean_object* _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3291_; lean_object* v___x_3292_; 
v___x_3291_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___closed__0));
v___x_3292_ = l_Lean_stringToMessageData(v___x_3291_);
return v___x_3292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(lean_object* v___f_3293_, lean_object* v_a_3294_, lean_object* v_x_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_){
_start:
{
lean_object* v___x_3301_; lean_object* v___x_3302_; 
v___x_3301_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___closed__1, &l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___closed__1_once, _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___closed__1);
v___x_3302_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_3301_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_);
if (lean_obj_tag(v___x_3302_) == 0)
{
lean_object* v_a_3303_; lean_object* v___x_3304_; 
v_a_3303_ = lean_ctor_get(v___x_3302_, 0);
lean_inc(v_a_3303_);
lean_dec_ref(v___x_3302_);
lean_inc(v___y_3299_);
lean_inc_ref(v___y_3298_);
lean_inc(v___y_3297_);
lean_inc_ref(v___y_3296_);
v___x_3304_ = lean_apply_7(v___f_3293_, v_a_3303_, v_a_3294_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_, lean_box(0));
return v___x_3304_;
}
else
{
lean_object* v_a_3305_; lean_object* v___x_3307_; uint8_t v_isShared_3308_; uint8_t v_isSharedCheck_3312_; 
lean_dec(v_a_3294_);
lean_dec_ref(v___f_3293_);
v_a_3305_ = lean_ctor_get(v___x_3302_, 0);
v_isSharedCheck_3312_ = !lean_is_exclusive(v___x_3302_);
if (v_isSharedCheck_3312_ == 0)
{
v___x_3307_ = v___x_3302_;
v_isShared_3308_ = v_isSharedCheck_3312_;
goto v_resetjp_3306_;
}
else
{
lean_inc(v_a_3305_);
lean_dec(v___x_3302_);
v___x_3307_ = lean_box(0);
v_isShared_3308_ = v_isSharedCheck_3312_;
goto v_resetjp_3306_;
}
v_resetjp_3306_:
{
lean_object* v___x_3310_; 
if (v_isShared_3308_ == 0)
{
v___x_3310_ = v___x_3307_;
goto v_reusejp_3309_;
}
else
{
lean_object* v_reuseFailAlloc_3311_; 
v_reuseFailAlloc_3311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3311_, 0, v_a_3305_);
v___x_3310_ = v_reuseFailAlloc_3311_;
goto v_reusejp_3309_;
}
v_reusejp_3309_:
{
return v___x_3310_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___boxed(lean_object* v___f_3313_, lean_object* v_a_3314_, lean_object* v_x_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_){
_start:
{
lean_object* v_res_3321_; 
v_res_3321_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(v___f_3313_, v_a_3314_, v_x_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_);
lean_dec(v___y_3319_);
lean_dec_ref(v___y_3318_);
lean_dec(v___y_3317_);
lean_dec_ref(v___y_3316_);
lean_dec(v_x_3315_);
return v_res_3321_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0(uint8_t v___x_3322_, lean_object* v_____r_3323_, lean_object* v_mvarId_u2082_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_){
_start:
{
lean_object* v___x_3330_; 
v___x_3330_ = l_Lean_Meta_introSubstEq(v_mvarId_u2082_3324_, v___x_3322_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_);
if (lean_obj_tag(v___x_3330_) == 0)
{
lean_object* v_a_3331_; lean_object* v___x_3333_; uint8_t v_isShared_3334_; uint8_t v_isSharedCheck_3340_; 
v_a_3331_ = lean_ctor_get(v___x_3330_, 0);
v_isSharedCheck_3340_ = !lean_is_exclusive(v___x_3330_);
if (v_isSharedCheck_3340_ == 0)
{
v___x_3333_ = v___x_3330_;
v_isShared_3334_ = v_isSharedCheck_3340_;
goto v_resetjp_3332_;
}
else
{
lean_inc(v_a_3331_);
lean_dec(v___x_3330_);
v___x_3333_ = lean_box(0);
v_isShared_3334_ = v_isSharedCheck_3340_;
goto v_resetjp_3332_;
}
v_resetjp_3332_:
{
lean_object* v_snd_3335_; lean_object* v___x_3336_; lean_object* v___x_3338_; 
v_snd_3335_ = lean_ctor_get(v_a_3331_, 1);
lean_inc(v_snd_3335_);
lean_dec(v_a_3331_);
v___x_3336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3336_, 0, v_snd_3335_);
if (v_isShared_3334_ == 0)
{
lean_ctor_set(v___x_3333_, 0, v___x_3336_);
v___x_3338_ = v___x_3333_;
goto v_reusejp_3337_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v___x_3336_);
v___x_3338_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3337_;
}
v_reusejp_3337_:
{
return v___x_3338_;
}
}
}
else
{
lean_object* v_a_3341_; lean_object* v___x_3343_; uint8_t v_isShared_3344_; uint8_t v_isSharedCheck_3348_; 
v_a_3341_ = lean_ctor_get(v___x_3330_, 0);
v_isSharedCheck_3348_ = !lean_is_exclusive(v___x_3330_);
if (v_isSharedCheck_3348_ == 0)
{
v___x_3343_ = v___x_3330_;
v_isShared_3344_ = v_isSharedCheck_3348_;
goto v_resetjp_3342_;
}
else
{
lean_inc(v_a_3341_);
lean_dec(v___x_3330_);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0___boxed(lean_object* v___x_3349_, lean_object* v_____r_3350_, lean_object* v_mvarId_u2082_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_){
_start:
{
uint8_t v___x_5932__boxed_3357_; lean_object* v_res_3358_; 
v___x_5932__boxed_3357_ = lean_unbox(v___x_3349_);
v_res_3358_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0(v___x_5932__boxed_3357_, v_____r_3350_, v_mvarId_u2082_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_);
lean_dec(v___y_3355_);
lean_dec_ref(v___y_3354_);
lean_dec(v___y_3353_);
lean_dec_ref(v___y_3352_);
return v_res_3358_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(lean_object* v___f_3359_, lean_object* v_a_3360_, lean_object* v_x_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_){
_start:
{
lean_object* v___x_3367_; lean_object* v___x_3368_; 
v___x_3367_ = lean_box(0);
lean_inc(v___y_3365_);
lean_inc_ref(v___y_3364_);
lean_inc(v___y_3363_);
lean_inc_ref(v___y_3362_);
v___x_3368_ = lean_apply_7(v___f_3359_, v___x_3367_, v_a_3360_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_, lean_box(0));
return v___x_3368_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1___boxed(lean_object* v___f_3369_, lean_object* v_a_3370_, lean_object* v_x_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_){
_start:
{
lean_object* v_res_3377_; 
v_res_3377_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(v___f_3369_, v_a_3370_, v_x_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
lean_dec(v___y_3375_);
lean_dec_ref(v___y_3374_);
lean_dec(v___y_3373_);
lean_dec_ref(v___y_3372_);
return v_res_3377_;
}
}
static lean_object* _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; 
v___x_3383_ = lean_box(0);
v___x_3384_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__2));
v___x_3385_ = l_Lean_mkConst(v___x_3384_, v___x_3383_);
return v___x_3385_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg(lean_object* v_a_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_){
_start:
{
lean_object* v___y_3393_; lean_object* v___x_3413_; 
lean_inc(v_a_3386_);
v___x_3413_ = l_Lean_MVarId_getType(v_a_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_);
if (lean_obj_tag(v___x_3413_) == 0)
{
lean_object* v_a_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3473_; 
v_a_3414_ = lean_ctor_get(v___x_3413_, 0);
v_isSharedCheck_3473_ = !lean_is_exclusive(v___x_3413_);
if (v_isSharedCheck_3473_ == 0)
{
v___x_3416_ = v___x_3413_;
v_isShared_3417_ = v_isSharedCheck_3473_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_a_3414_);
lean_dec(v___x_3413_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3473_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
if (lean_obj_tag(v_a_3414_) == 7)
{
lean_object* v_binderType_3418_; lean_object* v_body_3419_; uint8_t v___x_3420_; 
v_binderType_3418_ = lean_ctor_get(v_a_3414_, 1);
lean_inc_ref(v_binderType_3418_);
v_body_3419_ = lean_ctor_get(v_a_3414_, 2);
lean_inc_ref(v_body_3419_);
lean_dec_ref(v_a_3414_);
v___x_3420_ = l_Lean_Expr_hasLooseBVars(v_body_3419_);
if (v___x_3420_ == 0)
{
lean_object* v___x_3421_; 
lean_del_object(v___x_3416_);
v___x_3421_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_3418_, v___y_3388_);
if (lean_obj_tag(v___x_3421_) == 0)
{
lean_object* v_a_3422_; lean_object* v___x_3423_; lean_object* v___f_3424_; lean_object* v___x_3425_; uint8_t v___x_3426_; 
v_a_3422_ = lean_ctor_get(v___x_3421_, 0);
lean_inc(v_a_3422_);
lean_dec_ref(v___x_3421_);
v___x_3423_ = lean_box(v___x_3420_);
v___f_3424_ = lean_alloc_closure((void*)(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3424_, 0, v___x_3423_);
v___x_3425_ = l_Lean_Expr_cleanupAnnotations(v_a_3422_);
v___x_3426_ = l_Lean_Expr_isApp(v___x_3425_);
if (v___x_3426_ == 0)
{
lean_object* v___x_3427_; lean_object* v___x_3428_; 
lean_dec_ref(v___x_3425_);
lean_dec_ref(v_body_3419_);
v___x_3427_ = lean_box(0);
v___x_3428_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(v___f_3424_, v_a_3386_, v___x_3427_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_);
v___y_3393_ = v___x_3428_;
goto v___jp_3392_;
}
else
{
lean_object* v_arg_3429_; lean_object* v___x_3430_; uint8_t v___x_3431_; 
v_arg_3429_ = lean_ctor_get(v___x_3425_, 1);
lean_inc_ref(v_arg_3429_);
v___x_3430_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3425_);
v___x_3431_ = l_Lean_Expr_isApp(v___x_3430_);
if (v___x_3431_ == 0)
{
lean_object* v___x_3432_; lean_object* v___x_3433_; 
lean_dec_ref(v___x_3430_);
lean_dec_ref(v_arg_3429_);
lean_dec_ref(v_body_3419_);
v___x_3432_ = lean_box(0);
v___x_3433_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(v___f_3424_, v_a_3386_, v___x_3432_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_);
v___y_3393_ = v___x_3433_;
goto v___jp_3392_;
}
else
{
lean_object* v_arg_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; uint8_t v___x_3437_; 
v_arg_3434_ = lean_ctor_get(v___x_3430_, 1);
lean_inc_ref(v_arg_3434_);
v___x_3435_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3430_);
v___x_3436_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__1));
v___x_3437_ = l_Lean_Expr_isConstOf(v___x_3435_, v___x_3436_);
lean_dec_ref(v___x_3435_);
if (v___x_3437_ == 0)
{
lean_object* v___x_3438_; lean_object* v___x_3439_; 
lean_dec_ref(v_arg_3434_);
lean_dec_ref(v_arg_3429_);
lean_dec_ref(v_body_3419_);
v___x_3438_ = lean_box(0);
v___x_3439_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(v___f_3424_, v_a_3386_, v___x_3438_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_);
v___y_3393_ = v___x_3439_;
goto v___jp_3392_;
}
else
{
lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; 
v___x_3440_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__3, &l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__3_once, _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__3);
v___x_3441_ = l_Lean_mkApp3(v___x_3440_, v_arg_3434_, v_arg_3429_, v_body_3419_);
v___x_3442_ = lean_unsigned_to_nat(1u);
lean_inc(v_a_3386_);
v___x_3443_ = l_Lean_MVarId_applyN(v_a_3386_, v___x_3441_, v___x_3442_, v___x_3437_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_);
if (lean_obj_tag(v___x_3443_) == 0)
{
lean_object* v_a_3444_; 
v_a_3444_ = lean_ctor_get(v___x_3443_, 0);
lean_inc(v_a_3444_);
lean_dec_ref(v___x_3443_);
if (lean_obj_tag(v_a_3444_) == 1)
{
lean_object* v_tail_3445_; 
v_tail_3445_ = lean_ctor_get(v_a_3444_, 1);
if (lean_obj_tag(v_tail_3445_) == 0)
{
lean_object* v_head_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; 
lean_dec_ref(v___f_3424_);
lean_dec(v_a_3386_);
v_head_3446_ = lean_ctor_get(v_a_3444_, 0);
lean_inc(v_head_3446_);
lean_dec_ref(v_a_3444_);
v___x_3447_ = lean_box(0);
v___x_3448_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0(v___x_3420_, v___x_3447_, v_head_3446_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_);
v___y_3393_ = v___x_3448_;
goto v___jp_3392_;
}
else
{
lean_object* v___x_3449_; 
v___x_3449_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(v___f_3424_, v_a_3386_, v_a_3444_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_);
lean_dec_ref(v_a_3444_);
v___y_3393_ = v___x_3449_;
goto v___jp_3392_;
}
}
else
{
lean_object* v___x_3450_; 
v___x_3450_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(v___f_3424_, v_a_3386_, v_a_3444_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_);
lean_dec(v_a_3444_);
v___y_3393_ = v___x_3450_;
goto v___jp_3392_;
}
}
else
{
lean_object* v_a_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3458_; 
lean_dec_ref(v___f_3424_);
lean_dec(v_a_3386_);
v_a_3451_ = lean_ctor_get(v___x_3443_, 0);
v_isSharedCheck_3458_ = !lean_is_exclusive(v___x_3443_);
if (v_isSharedCheck_3458_ == 0)
{
v___x_3453_ = v___x_3443_;
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_a_3451_);
lean_dec(v___x_3443_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
lean_object* v___x_3456_; 
if (v_isShared_3454_ == 0)
{
v___x_3456_ = v___x_3453_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v_a_3451_);
v___x_3456_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
return v___x_3456_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3466_; 
lean_dec_ref(v_body_3419_);
lean_dec(v_a_3386_);
v_a_3459_ = lean_ctor_get(v___x_3421_, 0);
v_isSharedCheck_3466_ = !lean_is_exclusive(v___x_3421_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3461_ = v___x_3421_;
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_a_3459_);
lean_dec(v___x_3421_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
lean_object* v___x_3464_; 
if (v_isShared_3462_ == 0)
{
v___x_3464_ = v___x_3461_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v_a_3459_);
v___x_3464_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
return v___x_3464_;
}
}
}
}
else
{
lean_object* v___x_3468_; 
lean_dec_ref(v_body_3419_);
lean_dec_ref(v_binderType_3418_);
if (v_isShared_3417_ == 0)
{
lean_ctor_set(v___x_3416_, 0, v_a_3386_);
v___x_3468_ = v___x_3416_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_a_3386_);
v___x_3468_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
return v___x_3468_;
}
}
}
else
{
lean_object* v___x_3471_; 
lean_dec(v_a_3414_);
if (v_isShared_3417_ == 0)
{
lean_ctor_set(v___x_3416_, 0, v_a_3386_);
v___x_3471_ = v___x_3416_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v_a_3386_);
v___x_3471_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
return v___x_3471_;
}
}
}
}
else
{
lean_object* v_a_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3481_; 
lean_dec(v_a_3386_);
v_a_3474_ = lean_ctor_get(v___x_3413_, 0);
v_isSharedCheck_3481_ = !lean_is_exclusive(v___x_3413_);
if (v_isSharedCheck_3481_ == 0)
{
v___x_3476_ = v___x_3413_;
v_isShared_3477_ = v_isSharedCheck_3481_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_a_3474_);
lean_dec(v___x_3413_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3481_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
lean_object* v___x_3479_; 
if (v_isShared_3477_ == 0)
{
v___x_3479_ = v___x_3476_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v_a_3474_);
v___x_3479_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
return v___x_3479_;
}
}
}
v___jp_3392_:
{
if (lean_obj_tag(v___y_3393_) == 0)
{
lean_object* v_a_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3404_; 
v_a_3394_ = lean_ctor_get(v___y_3393_, 0);
v_isSharedCheck_3404_ = !lean_is_exclusive(v___y_3393_);
if (v_isSharedCheck_3404_ == 0)
{
v___x_3396_ = v___y_3393_;
v_isShared_3397_ = v_isSharedCheck_3404_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_a_3394_);
lean_dec(v___y_3393_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3404_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
if (lean_obj_tag(v_a_3394_) == 0)
{
lean_object* v_a_3398_; lean_object* v___x_3400_; 
v_a_3398_ = lean_ctor_get(v_a_3394_, 0);
lean_inc(v_a_3398_);
lean_dec_ref(v_a_3394_);
if (v_isShared_3397_ == 0)
{
lean_ctor_set(v___x_3396_, 0, v_a_3398_);
v___x_3400_ = v___x_3396_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v_a_3398_);
v___x_3400_ = v_reuseFailAlloc_3401_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
return v___x_3400_;
}
}
else
{
lean_object* v_a_3402_; 
lean_del_object(v___x_3396_);
v_a_3402_ = lean_ctor_get(v_a_3394_, 0);
lean_inc(v_a_3402_);
lean_dec_ref(v_a_3394_);
v_a_3386_ = v_a_3402_;
goto _start;
}
}
}
else
{
lean_object* v_a_3405_; lean_object* v___x_3407_; uint8_t v_isShared_3408_; uint8_t v_isSharedCheck_3412_; 
v_a_3405_ = lean_ctor_get(v___y_3393_, 0);
v_isSharedCheck_3412_ = !lean_is_exclusive(v___y_3393_);
if (v_isSharedCheck_3412_ == 0)
{
v___x_3407_ = v___y_3393_;
v_isShared_3408_ = v_isSharedCheck_3412_;
goto v_resetjp_3406_;
}
else
{
lean_inc(v_a_3405_);
lean_dec(v___y_3393_);
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
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___boxed(lean_object* v_a_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_){
_start:
{
lean_object* v_res_3488_; 
v_res_3488_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg(v_a_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_);
lean_dec(v___y_3486_);
lean_dec_ref(v___y_3485_);
lean_dec(v___y_3484_);
lean_dec_ref(v___y_3483_);
return v_res_3488_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; 
v___x_3494_ = lean_box(0);
v___x_3495_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__2));
v___x_3496_ = l_Lean_mkConst(v___x_3495_, v___x_3494_);
return v___x_3496_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6(void){
_start:
{
lean_object* v___x_3502_; lean_object* v___x_3503_; 
v___x_3502_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__5));
v___x_3503_ = l_Lean_stringToMessageData(v___x_3502_);
return v___x_3503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0(lean_object* v_ctorVal_3504_, lean_object* v_xs_3505_, lean_object* v_type_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_){
_start:
{
lean_object* v___x_3512_; lean_object* v___x_3513_; 
v___x_3512_ = lean_box(0);
v___x_3513_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_3506_, v___x_3512_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_);
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_object* v_a_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; uint8_t v___x_3518_; uint8_t v___x_3519_; lean_object* v___y_3521_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; 
v_a_3514_ = lean_ctor_get(v___x_3513_, 0);
lean_inc(v_a_3514_);
lean_dec_ref(v___x_3513_);
v___x_3515_ = l_Lean_Expr_mvarId_x21(v_a_3514_);
v___x_3516_ = lean_box(0);
v___x_3517_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3);
v___x_3518_ = 1;
v___x_3519_ = 0;
v___x_3532_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__4));
v___x_3533_ = lean_box(0);
v___x_3534_ = l_Lean_MVarId_apply(v___x_3515_, v___x_3517_, v___x_3532_, v___x_3533_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_);
if (lean_obj_tag(v___x_3534_) == 0)
{
lean_object* v_a_3535_; lean_object* v___y_3537_; lean_object* v___y_3538_; lean_object* v___y_3539_; lean_object* v___y_3540_; 
v_a_3535_ = lean_ctor_get(v___x_3534_, 0);
lean_inc(v_a_3535_);
lean_dec_ref(v___x_3534_);
if (lean_obj_tag(v_a_3535_) == 1)
{
lean_object* v_tail_3549_; 
v_tail_3549_ = lean_ctor_get(v_a_3535_, 1);
lean_inc(v_tail_3549_);
if (lean_obj_tag(v_tail_3549_) == 1)
{
lean_object* v_tail_3550_; 
v_tail_3550_ = lean_ctor_get(v_tail_3549_, 1);
if (lean_obj_tag(v_tail_3550_) == 0)
{
lean_object* v_toConstantVal_3551_; lean_object* v_head_3552_; lean_object* v_head_3553_; lean_object* v_name_3554_; lean_object* v_levelParams_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; 
v_toConstantVal_3551_ = lean_ctor_get(v_ctorVal_3504_, 0);
lean_inc_ref(v_toConstantVal_3551_);
lean_dec_ref(v_ctorVal_3504_);
v_head_3552_ = lean_ctor_get(v_a_3535_, 0);
lean_inc(v_head_3552_);
lean_dec_ref(v_a_3535_);
v_head_3553_ = lean_ctor_get(v_tail_3549_, 0);
lean_inc(v_head_3553_);
lean_dec_ref(v_tail_3549_);
v_name_3554_ = lean_ctor_get(v_toConstantVal_3551_, 0);
lean_inc_n(v_name_3554_, 2);
v_levelParams_3555_ = lean_ctor_get(v_toConstantVal_3551_, 1);
lean_inc(v_levelParams_3555_);
lean_dec_ref(v_toConstantVal_3551_);
v___x_3556_ = l_Lean_Meta_mkInjectiveTheoremNameFor(v_name_3554_);
v___x_3557_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(v_levelParams_3555_, v___x_3516_);
v___x_3558_ = l_Lean_mkConst(v___x_3556_, v___x_3557_);
v___x_3559_ = l_Lean_mkAppN(v___x_3558_, v_xs_3505_);
v___x_3560_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(v_head_3552_, v___x_3559_, v___y_3508_);
lean_dec_ref(v___x_3560_);
v___x_3561_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg(v_head_3553_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_);
if (lean_obj_tag(v___x_3561_) == 0)
{
lean_object* v_a_3562_; lean_object* v___x_3563_; 
v_a_3562_ = lean_ctor_get(v___x_3561_, 0);
lean_inc(v_a_3562_);
lean_dec_ref(v___x_3561_);
v___x_3563_ = l_Lean_MVarId_refl(v_a_3562_, v___x_3518_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_);
if (lean_obj_tag(v___x_3563_) == 0)
{
lean_dec(v_name_3554_);
v___y_3521_ = v___x_3563_;
goto v___jp_3520_;
}
else
{
lean_object* v_a_3564_; uint8_t v___y_3566_; uint8_t v___x_3569_; 
v_a_3564_ = lean_ctor_get(v___x_3563_, 0);
lean_inc(v_a_3564_);
v___x_3569_ = l_Lean_Exception_isInterrupt(v_a_3564_);
if (v___x_3569_ == 0)
{
uint8_t v___x_3570_; 
v___x_3570_ = l_Lean_Exception_isRuntime(v_a_3564_);
v___y_3566_ = v___x_3570_;
goto v___jp_3565_;
}
else
{
lean_dec(v_a_3564_);
v___y_3566_ = v___x_3569_;
goto v___jp_3565_;
}
v___jp_3565_:
{
if (v___y_3566_ == 0)
{
lean_object* v___x_3567_; lean_object* v___x_3568_; 
lean_dec_ref(v___x_3563_);
v___x_3567_ = l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(v_name_3554_);
v___x_3568_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_3567_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_);
v___y_3521_ = v___x_3568_;
goto v___jp_3520_;
}
else
{
lean_dec(v_name_3554_);
v___y_3521_ = v___x_3563_;
goto v___jp_3520_;
}
}
}
}
else
{
lean_object* v_a_3571_; lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3578_; 
lean_dec(v_name_3554_);
lean_dec(v_a_3514_);
v_a_3571_ = lean_ctor_get(v___x_3561_, 0);
v_isSharedCheck_3578_ = !lean_is_exclusive(v___x_3561_);
if (v_isSharedCheck_3578_ == 0)
{
v___x_3573_ = v___x_3561_;
v_isShared_3574_ = v_isSharedCheck_3578_;
goto v_resetjp_3572_;
}
else
{
lean_inc(v_a_3571_);
lean_dec(v___x_3561_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3578_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
lean_object* v___x_3576_; 
if (v_isShared_3574_ == 0)
{
v___x_3576_ = v___x_3573_;
goto v_reusejp_3575_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v_a_3571_);
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
lean_dec_ref(v_tail_3549_);
lean_dec_ref(v_a_3535_);
lean_dec(v_a_3514_);
v___y_3537_ = v___y_3507_;
v___y_3538_ = v___y_3508_;
v___y_3539_ = v___y_3509_;
v___y_3540_ = v___y_3510_;
goto v___jp_3536_;
}
}
else
{
lean_dec_ref(v_a_3535_);
lean_dec(v_tail_3549_);
lean_dec(v_a_3514_);
v___y_3537_ = v___y_3507_;
v___y_3538_ = v___y_3508_;
v___y_3539_ = v___y_3509_;
v___y_3540_ = v___y_3510_;
goto v___jp_3536_;
}
}
else
{
lean_dec(v_a_3535_);
lean_dec(v_a_3514_);
v___y_3537_ = v___y_3507_;
v___y_3538_ = v___y_3508_;
v___y_3539_ = v___y_3509_;
v___y_3540_ = v___y_3510_;
goto v___jp_3536_;
}
v___jp_3536_:
{
lean_object* v_toConstantVal_3541_; lean_object* v_name_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; 
v_toConstantVal_3541_ = lean_ctor_get(v_ctorVal_3504_, 0);
lean_inc_ref(v_toConstantVal_3541_);
lean_dec_ref(v_ctorVal_3504_);
v_name_3542_ = lean_ctor_get(v_toConstantVal_3541_, 0);
lean_inc(v_name_3542_);
lean_dec_ref(v_toConstantVal_3541_);
v___x_3543_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6);
v___x_3544_ = l_Lean_MessageData_ofName(v_name_3542_);
v___x_3545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3545_, 0, v___x_3543_);
lean_ctor_set(v___x_3545_, 1, v___x_3544_);
v___x_3546_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_3547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3547_, 0, v___x_3545_);
lean_ctor_set(v___x_3547_, 1, v___x_3546_);
v___x_3548_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_3547_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_);
return v___x_3548_;
}
}
else
{
lean_object* v_a_3579_; lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3586_; 
lean_dec(v_a_3514_);
lean_dec_ref(v_ctorVal_3504_);
v_a_3579_ = lean_ctor_get(v___x_3534_, 0);
v_isSharedCheck_3586_ = !lean_is_exclusive(v___x_3534_);
if (v_isSharedCheck_3586_ == 0)
{
v___x_3581_ = v___x_3534_;
v_isShared_3582_ = v_isSharedCheck_3586_;
goto v_resetjp_3580_;
}
else
{
lean_inc(v_a_3579_);
lean_dec(v___x_3534_);
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
v___jp_3520_:
{
if (lean_obj_tag(v___y_3521_) == 0)
{
uint8_t v___x_3522_; lean_object* v___x_3523_; 
lean_dec_ref(v___y_3521_);
v___x_3522_ = 1;
v___x_3523_ = l_Lean_Meta_mkLambdaFVars(v_xs_3505_, v_a_3514_, v___x_3519_, v___x_3518_, v___x_3519_, v___x_3518_, v___x_3522_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_);
return v___x_3523_;
}
else
{
lean_object* v_a_3524_; lean_object* v___x_3526_; uint8_t v_isShared_3527_; uint8_t v_isSharedCheck_3531_; 
lean_dec(v_a_3514_);
v_a_3524_ = lean_ctor_get(v___y_3521_, 0);
v_isSharedCheck_3531_ = !lean_is_exclusive(v___y_3521_);
if (v_isSharedCheck_3531_ == 0)
{
v___x_3526_ = v___y_3521_;
v_isShared_3527_ = v_isSharedCheck_3531_;
goto v_resetjp_3525_;
}
else
{
lean_inc(v_a_3524_);
lean_dec(v___y_3521_);
v___x_3526_ = lean_box(0);
v_isShared_3527_ = v_isSharedCheck_3531_;
goto v_resetjp_3525_;
}
v_resetjp_3525_:
{
lean_object* v___x_3529_; 
if (v_isShared_3527_ == 0)
{
v___x_3529_ = v___x_3526_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3530_; 
v_reuseFailAlloc_3530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3530_, 0, v_a_3524_);
v___x_3529_ = v_reuseFailAlloc_3530_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
return v___x_3529_;
}
}
}
}
}
else
{
lean_dec_ref(v_ctorVal_3504_);
return v___x_3513_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___boxed(lean_object* v_ctorVal_3587_, lean_object* v_xs_3588_, lean_object* v_type_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_){
_start:
{
lean_object* v_res_3595_; 
v_res_3595_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0(v_ctorVal_3587_, v_xs_3588_, v_type_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_);
lean_dec(v___y_3593_);
lean_dec_ref(v___y_3592_);
lean_dec(v___y_3591_);
lean_dec_ref(v___y_3590_);
lean_dec_ref(v_xs_3588_);
return v_res_3595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(lean_object* v_ctorVal_3596_, lean_object* v_targetType_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_){
_start:
{
lean_object* v___f_3603_; uint8_t v___x_3604_; lean_object* v___x_3605_; 
v___f_3603_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3603_, 0, v_ctorVal_3596_);
v___x_3604_ = 0;
v___x_3605_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_targetType_3597_, v___f_3603_, v___x_3604_, v___x_3604_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_);
return v___x_3605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___boxed(lean_object* v_ctorVal_3606_, lean_object* v_targetType_3607_, lean_object* v_a_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_){
_start:
{
lean_object* v_res_3613_; 
v_res_3613_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3606_, v_targetType_3607_, v_a_3608_, v_a_3609_, v_a_3610_, v_a_3611_);
lean_dec(v_a_3611_);
lean_dec_ref(v_a_3610_);
lean_dec(v_a_3609_);
lean_dec_ref(v_a_3608_);
return v_res_3613_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0(lean_object* v_mvarId_3614_, lean_object* v_val_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_){
_start:
{
lean_object* v___x_3621_; 
v___x_3621_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(v_mvarId_3614_, v_val_3615_, v___y_3617_);
return v___x_3621_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___boxed(lean_object* v_mvarId_3622_, lean_object* v_val_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_){
_start:
{
lean_object* v_res_3629_; 
v_res_3629_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0(v_mvarId_3622_, v_val_3623_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_);
lean_dec(v___y_3627_);
lean_dec_ref(v___y_3626_);
lean_dec(v___y_3625_);
lean_dec_ref(v___y_3624_);
return v_res_3629_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1(lean_object* v_inst_3630_, lean_object* v_a_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_){
_start:
{
lean_object* v___x_3637_; 
v___x_3637_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg(v_a_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_);
return v___x_3637_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___boxed(lean_object* v_inst_3638_, lean_object* v_a_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_){
_start:
{
lean_object* v_res_3645_; 
v_res_3645_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1(v_inst_3638_, v_a_3639_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_);
lean_dec(v___y_3643_);
lean_dec_ref(v___y_3642_);
lean_dec(v___y_3641_);
lean_dec_ref(v___y_3640_);
return v_res_3645_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0(lean_object* v_00_u03b2_3646_, lean_object* v_x_3647_, lean_object* v_x_3648_, lean_object* v_x_3649_){
_start:
{
lean_object* v___x_3650_; 
v___x_3650_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(v_x_3647_, v_x_3648_, v_x_3649_);
return v___x_3650_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3651_, lean_object* v_x_3652_, size_t v_x_3653_, size_t v_x_3654_, lean_object* v_x_3655_, lean_object* v_x_3656_){
_start:
{
lean_object* v___x_3657_; 
v___x_3657_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_x_3652_, v_x_3653_, v_x_3654_, v_x_3655_, v_x_3656_);
return v___x_3657_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3658_, lean_object* v_x_3659_, lean_object* v_x_3660_, lean_object* v_x_3661_, lean_object* v_x_3662_, lean_object* v_x_3663_){
_start:
{
size_t v_x_6508__boxed_3664_; size_t v_x_6509__boxed_3665_; lean_object* v_res_3666_; 
v_x_6508__boxed_3664_ = lean_unbox_usize(v_x_3660_);
lean_dec(v_x_3660_);
v_x_6509__boxed_3665_ = lean_unbox_usize(v_x_3661_);
lean_dec(v_x_3661_);
v_res_3666_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1(v_00_u03b2_3658_, v_x_3659_, v_x_6508__boxed_3664_, v_x_6509__boxed_3665_, v_x_3662_, v_x_3663_);
return v_res_3666_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_3667_, lean_object* v_n_3668_, lean_object* v_k_3669_, lean_object* v_v_3670_){
_start:
{
lean_object* v___x_3671_; 
v___x_3671_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(v_n_3668_, v_k_3669_, v_v_3670_);
return v___x_3671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_3672_, size_t v_depth_3673_, lean_object* v_keys_3674_, lean_object* v_vals_3675_, lean_object* v_heq_3676_, lean_object* v_i_3677_, lean_object* v_entries_3678_){
_start:
{
lean_object* v___x_3679_; 
v___x_3679_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_3673_, v_keys_3674_, v_vals_3675_, v_i_3677_, v_entries_3678_);
return v___x_3679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_3680_, lean_object* v_depth_3681_, lean_object* v_keys_3682_, lean_object* v_vals_3683_, lean_object* v_heq_3684_, lean_object* v_i_3685_, lean_object* v_entries_3686_){
_start:
{
size_t v_depth_boxed_3687_; lean_object* v_res_3688_; 
v_depth_boxed_3687_ = lean_unbox_usize(v_depth_3681_);
lean_dec(v_depth_3681_);
v_res_3688_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_3680_, v_depth_boxed_3687_, v_keys_3682_, v_vals_3683_, v_heq_3684_, v_i_3685_, v_entries_3686_);
lean_dec_ref(v_vals_3683_);
lean_dec_ref(v_keys_3682_);
return v_res_3688_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_3689_, lean_object* v_x_3690_, lean_object* v_x_3691_, lean_object* v_x_3692_, lean_object* v_x_3693_){
_start:
{
lean_object* v___x_3694_; 
v___x_3694_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_x_3690_, v_x_3691_, v_x_3692_, v_x_3693_);
return v___x_3694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(lean_object* v_ctorVal_3695_, lean_object* v_val_3696_, lean_object* v_name_3697_, lean_object* v_levelParams_3698_, uint8_t v___x_3699_, uint8_t v_hasTrace_3700_, lean_object* v_____r_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_){
_start:
{
lean_object* v___x_3707_; 
lean_inc_ref(v_val_3696_);
v___x_3707_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3695_, v_val_3696_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_);
if (lean_obj_tag(v___x_3707_) == 0)
{
lean_object* v_a_3708_; lean_object* v___x_3709_; lean_object* v_a_3710_; lean_object* v___x_3711_; lean_object* v_a_3712_; lean_object* v___x_3714_; uint8_t v_isShared_3715_; uint8_t v_isSharedCheck_3728_; 
v_a_3708_ = lean_ctor_get(v___x_3707_, 0);
lean_inc(v_a_3708_);
lean_dec_ref(v___x_3707_);
v___x_3709_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3696_, v___y_3703_);
v_a_3710_ = lean_ctor_get(v___x_3709_, 0);
lean_inc(v_a_3710_);
lean_dec_ref(v___x_3709_);
v___x_3711_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3708_, v___y_3703_);
v_a_3712_ = lean_ctor_get(v___x_3711_, 0);
v_isSharedCheck_3728_ = !lean_is_exclusive(v___x_3711_);
if (v_isSharedCheck_3728_ == 0)
{
v___x_3714_ = v___x_3711_;
v_isShared_3715_ = v_isSharedCheck_3728_;
goto v_resetjp_3713_;
}
else
{
lean_inc(v_a_3712_);
lean_dec(v___x_3711_);
v___x_3714_ = lean_box(0);
v_isShared_3715_ = v_isSharedCheck_3728_;
goto v_resetjp_3713_;
}
v_resetjp_3713_:
{
lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3721_; 
lean_inc_n(v_name_3697_, 2);
v___x_3716_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3716_, 0, v_name_3697_);
lean_ctor_set(v___x_3716_, 1, v_levelParams_3698_);
lean_ctor_set(v___x_3716_, 2, v_a_3710_);
v___x_3717_ = lean_box(0);
v___x_3718_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3718_, 0, v_name_3697_);
lean_ctor_set(v___x_3718_, 1, v___x_3717_);
v___x_3719_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3719_, 0, v___x_3716_);
lean_ctor_set(v___x_3719_, 1, v_a_3712_);
lean_ctor_set(v___x_3719_, 2, v___x_3718_);
if (v_isShared_3715_ == 0)
{
lean_ctor_set_tag(v___x_3714_, 2);
lean_ctor_set(v___x_3714_, 0, v___x_3719_);
v___x_3721_ = v___x_3714_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v___x_3719_);
v___x_3721_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
lean_object* v___x_3722_; 
v___x_3722_ = l_Lean_addDecl(v___x_3721_, v___x_3699_, v___y_3704_, v___y_3705_);
if (lean_obj_tag(v___x_3722_) == 0)
{
lean_object* v___x_3723_; uint8_t v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; 
lean_dec_ref(v___x_3722_);
v___x_3723_ = l_Lean_Meta_simpExtension;
v___x_3724_ = 0;
v___x_3725_ = lean_unsigned_to_nat(1000u);
v___x_3726_ = l_Lean_Meta_addSimpTheorem(v___x_3723_, v_name_3697_, v_hasTrace_3700_, v___x_3699_, v___x_3724_, v___x_3725_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_);
return v___x_3726_;
}
else
{
lean_dec(v_name_3697_);
return v___x_3722_;
}
}
}
}
else
{
lean_object* v_a_3729_; lean_object* v___x_3731_; uint8_t v_isShared_3732_; uint8_t v_isSharedCheck_3736_; 
lean_dec(v_levelParams_3698_);
lean_dec(v_name_3697_);
lean_dec_ref(v_val_3696_);
v_a_3729_ = lean_ctor_get(v___x_3707_, 0);
v_isSharedCheck_3736_ = !lean_is_exclusive(v___x_3707_);
if (v_isSharedCheck_3736_ == 0)
{
v___x_3731_ = v___x_3707_;
v_isShared_3732_ = v_isSharedCheck_3736_;
goto v_resetjp_3730_;
}
else
{
lean_inc(v_a_3729_);
lean_dec(v___x_3707_);
v___x_3731_ = lean_box(0);
v_isShared_3732_ = v_isSharedCheck_3736_;
goto v_resetjp_3730_;
}
v_resetjp_3730_:
{
lean_object* v___x_3734_; 
if (v_isShared_3732_ == 0)
{
v___x_3734_ = v___x_3731_;
goto v_reusejp_3733_;
}
else
{
lean_object* v_reuseFailAlloc_3735_; 
v_reuseFailAlloc_3735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3735_, 0, v_a_3729_);
v___x_3734_ = v_reuseFailAlloc_3735_;
goto v_reusejp_3733_;
}
v_reusejp_3733_:
{
return v___x_3734_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1___boxed(lean_object* v_ctorVal_3737_, lean_object* v_val_3738_, lean_object* v_name_3739_, lean_object* v_levelParams_3740_, lean_object* v___x_3741_, lean_object* v_hasTrace_3742_, lean_object* v_____r_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_){
_start:
{
uint8_t v___x_9099__boxed_3749_; uint8_t v_hasTrace_boxed_3750_; lean_object* v_res_3751_; 
v___x_9099__boxed_3749_ = lean_unbox(v___x_3741_);
v_hasTrace_boxed_3750_ = lean_unbox(v_hasTrace_3742_);
v_res_3751_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(v_ctorVal_3737_, v_val_3738_, v_name_3739_, v_levelParams_3740_, v___x_9099__boxed_3749_, v_hasTrace_boxed_3750_, v_____r_3743_, v___y_3744_, v___y_3745_, v___y_3746_, v___y_3747_);
lean_dec(v___y_3747_);
lean_dec_ref(v___y_3746_);
lean_dec(v___y_3745_);
lean_dec_ref(v___y_3744_);
return v_res_3751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(lean_object* v_ctorVal_3752_, lean_object* v_val_3753_, lean_object* v_name_3754_, lean_object* v_levelParams_3755_, uint8_t v___x_3756_, lean_object* v_____r_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_){
_start:
{
lean_object* v___x_3763_; 
lean_inc_ref(v_val_3753_);
v___x_3763_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3752_, v_val_3753_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_);
if (lean_obj_tag(v___x_3763_) == 0)
{
lean_object* v_a_3764_; lean_object* v___x_3765_; lean_object* v_a_3766_; lean_object* v___x_3767_; lean_object* v_a_3768_; lean_object* v___x_3770_; uint8_t v_isShared_3771_; uint8_t v_isSharedCheck_3785_; 
v_a_3764_ = lean_ctor_get(v___x_3763_, 0);
lean_inc(v_a_3764_);
lean_dec_ref(v___x_3763_);
v___x_3765_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3753_, v___y_3759_);
v_a_3766_ = lean_ctor_get(v___x_3765_, 0);
lean_inc(v_a_3766_);
lean_dec_ref(v___x_3765_);
v___x_3767_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3764_, v___y_3759_);
v_a_3768_ = lean_ctor_get(v___x_3767_, 0);
v_isSharedCheck_3785_ = !lean_is_exclusive(v___x_3767_);
if (v_isSharedCheck_3785_ == 0)
{
v___x_3770_ = v___x_3767_;
v_isShared_3771_ = v_isSharedCheck_3785_;
goto v_resetjp_3769_;
}
else
{
lean_inc(v_a_3768_);
lean_dec(v___x_3767_);
v___x_3770_ = lean_box(0);
v_isShared_3771_ = v_isSharedCheck_3785_;
goto v_resetjp_3769_;
}
v_resetjp_3769_:
{
lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3777_; 
lean_inc_n(v_name_3754_, 2);
v___x_3772_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3772_, 0, v_name_3754_);
lean_ctor_set(v___x_3772_, 1, v_levelParams_3755_);
lean_ctor_set(v___x_3772_, 2, v_a_3766_);
v___x_3773_ = lean_box(0);
v___x_3774_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3774_, 0, v_name_3754_);
lean_ctor_set(v___x_3774_, 1, v___x_3773_);
v___x_3775_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3775_, 0, v___x_3772_);
lean_ctor_set(v___x_3775_, 1, v_a_3768_);
lean_ctor_set(v___x_3775_, 2, v___x_3774_);
if (v_isShared_3771_ == 0)
{
lean_ctor_set_tag(v___x_3770_, 2);
lean_ctor_set(v___x_3770_, 0, v___x_3775_);
v___x_3777_ = v___x_3770_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3784_; 
v_reuseFailAlloc_3784_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3784_, 0, v___x_3775_);
v___x_3777_ = v_reuseFailAlloc_3784_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
uint8_t v___x_3778_; lean_object* v___x_3779_; 
v___x_3778_ = 0;
v___x_3779_ = l_Lean_addDecl(v___x_3777_, v___x_3778_, v___y_3760_, v___y_3761_);
if (lean_obj_tag(v___x_3779_) == 0)
{
lean_object* v___x_3780_; uint8_t v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; 
lean_dec_ref(v___x_3779_);
v___x_3780_ = l_Lean_Meta_simpExtension;
v___x_3781_ = 0;
v___x_3782_ = lean_unsigned_to_nat(1000u);
v___x_3783_ = l_Lean_Meta_addSimpTheorem(v___x_3780_, v_name_3754_, v___x_3756_, v___x_3778_, v___x_3781_, v___x_3782_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_);
return v___x_3783_;
}
else
{
lean_dec(v_name_3754_);
return v___x_3779_;
}
}
}
}
else
{
lean_object* v_a_3786_; lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_3793_; 
lean_dec(v_levelParams_3755_);
lean_dec(v_name_3754_);
lean_dec_ref(v_val_3753_);
v_a_3786_ = lean_ctor_get(v___x_3763_, 0);
v_isSharedCheck_3793_ = !lean_is_exclusive(v___x_3763_);
if (v_isSharedCheck_3793_ == 0)
{
v___x_3788_ = v___x_3763_;
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
else
{
lean_inc(v_a_3786_);
lean_dec(v___x_3763_);
v___x_3788_ = lean_box(0);
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
v_resetjp_3787_:
{
lean_object* v___x_3791_; 
if (v_isShared_3789_ == 0)
{
v___x_3791_ = v___x_3788_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v_a_3786_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0___boxed(lean_object* v_ctorVal_3794_, lean_object* v_val_3795_, lean_object* v_name_3796_, lean_object* v_levelParams_3797_, lean_object* v___x_3798_, lean_object* v_____r_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_){
_start:
{
uint8_t v___x_9187__boxed_3805_; lean_object* v_res_3806_; 
v___x_9187__boxed_3805_ = lean_unbox(v___x_3798_);
v_res_3806_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(v_ctorVal_3794_, v_val_3795_, v_name_3796_, v_levelParams_3797_, v___x_9187__boxed_3805_, v_____r_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_);
lean_dec(v___y_3803_);
lean_dec_ref(v___y_3802_);
lean_dec(v___y_3801_);
lean_dec_ref(v___y_3800_);
return v_res_3806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(lean_object* v_ctorVal_3807_, lean_object* v_a_3808_, lean_object* v_a_3809_, lean_object* v_a_3810_, lean_object* v_a_3811_){
_start:
{
lean_object* v_toConstantVal_3813_; lean_object* v_options_3814_; lean_object* v_name_3815_; lean_object* v_levelParams_3816_; lean_object* v___x_3818_; uint8_t v_isShared_3819_; uint8_t v_isSharedCheck_4036_; 
v_toConstantVal_3813_ = lean_ctor_get(v_ctorVal_3807_, 0);
lean_inc_ref(v_toConstantVal_3813_);
v_options_3814_ = lean_ctor_get(v_a_3810_, 2);
v_name_3815_ = lean_ctor_get(v_toConstantVal_3813_, 0);
v_levelParams_3816_ = lean_ctor_get(v_toConstantVal_3813_, 1);
v_isSharedCheck_4036_ = !lean_is_exclusive(v_toConstantVal_3813_);
if (v_isSharedCheck_4036_ == 0)
{
lean_object* v_unused_4037_; 
v_unused_4037_ = lean_ctor_get(v_toConstantVal_3813_, 2);
lean_dec(v_unused_4037_);
v___x_3818_ = v_toConstantVal_3813_;
v_isShared_3819_ = v_isSharedCheck_4036_;
goto v_resetjp_3817_;
}
else
{
lean_inc(v_levelParams_3816_);
lean_inc(v_name_3815_);
lean_dec(v_toConstantVal_3813_);
v___x_3818_ = lean_box(0);
v_isShared_3819_ = v_isSharedCheck_4036_;
goto v_resetjp_3817_;
}
v_resetjp_3817_:
{
lean_object* v_inheritedTraceOptions_3820_; uint8_t v_hasTrace_3821_; lean_object* v_name_3822_; 
v_inheritedTraceOptions_3820_ = lean_ctor_get(v_a_3810_, 13);
v_hasTrace_3821_ = lean_ctor_get_uint8(v_options_3814_, sizeof(void*)*1);
v_name_3822_ = l_Lean_Meta_mkInjectiveEqTheoremNameFor(v_name_3815_);
if (v_hasTrace_3821_ == 0)
{
lean_object* v___x_3823_; 
lean_inc_ref(v_ctorVal_3807_);
v___x_3823_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3807_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_);
if (lean_obj_tag(v___x_3823_) == 0)
{
lean_object* v_a_3824_; lean_object* v___x_3826_; uint8_t v_isShared_3827_; uint8_t v_isSharedCheck_3866_; 
v_a_3824_ = lean_ctor_get(v___x_3823_, 0);
v_isSharedCheck_3866_ = !lean_is_exclusive(v___x_3823_);
if (v_isSharedCheck_3866_ == 0)
{
v___x_3826_ = v___x_3823_;
v_isShared_3827_ = v_isSharedCheck_3866_;
goto v_resetjp_3825_;
}
else
{
lean_inc(v_a_3824_);
lean_dec(v___x_3823_);
v___x_3826_ = lean_box(0);
v_isShared_3827_ = v_isSharedCheck_3866_;
goto v_resetjp_3825_;
}
v_resetjp_3825_:
{
if (lean_obj_tag(v_a_3824_) == 1)
{
lean_object* v_val_3828_; lean_object* v___x_3829_; 
lean_del_object(v___x_3826_);
v_val_3828_ = lean_ctor_get(v_a_3824_, 0);
lean_inc_n(v_val_3828_, 2);
lean_dec_ref(v_a_3824_);
v___x_3829_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3807_, v_val_3828_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_);
if (lean_obj_tag(v___x_3829_) == 0)
{
lean_object* v_a_3830_; lean_object* v___x_3831_; lean_object* v_a_3832_; lean_object* v___x_3833_; lean_object* v_a_3834_; lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3853_; 
v_a_3830_ = lean_ctor_get(v___x_3829_, 0);
lean_inc(v_a_3830_);
lean_dec_ref(v___x_3829_);
v___x_3831_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3828_, v_a_3809_);
v_a_3832_ = lean_ctor_get(v___x_3831_, 0);
lean_inc(v_a_3832_);
lean_dec_ref(v___x_3831_);
v___x_3833_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3830_, v_a_3809_);
v_a_3834_ = lean_ctor_get(v___x_3833_, 0);
v_isSharedCheck_3853_ = !lean_is_exclusive(v___x_3833_);
if (v_isSharedCheck_3853_ == 0)
{
v___x_3836_ = v___x_3833_;
v_isShared_3837_ = v_isSharedCheck_3853_;
goto v_resetjp_3835_;
}
else
{
lean_inc(v_a_3834_);
lean_dec(v___x_3833_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3853_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
lean_object* v___x_3839_; 
lean_inc(v_name_3822_);
if (v_isShared_3819_ == 0)
{
lean_ctor_set(v___x_3818_, 2, v_a_3832_);
lean_ctor_set(v___x_3818_, 0, v_name_3822_);
v___x_3839_ = v___x_3818_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3852_; 
v_reuseFailAlloc_3852_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3852_, 0, v_name_3822_);
lean_ctor_set(v_reuseFailAlloc_3852_, 1, v_levelParams_3816_);
lean_ctor_set(v_reuseFailAlloc_3852_, 2, v_a_3832_);
v___x_3839_ = v_reuseFailAlloc_3852_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3844_; 
v___x_3840_ = lean_box(0);
lean_inc(v_name_3822_);
v___x_3841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3841_, 0, v_name_3822_);
lean_ctor_set(v___x_3841_, 1, v___x_3840_);
v___x_3842_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3842_, 0, v___x_3839_);
lean_ctor_set(v___x_3842_, 1, v_a_3834_);
lean_ctor_set(v___x_3842_, 2, v___x_3841_);
if (v_isShared_3837_ == 0)
{
lean_ctor_set_tag(v___x_3836_, 2);
lean_ctor_set(v___x_3836_, 0, v___x_3842_);
v___x_3844_ = v___x_3836_;
goto v_reusejp_3843_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v___x_3842_);
v___x_3844_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3843_;
}
v_reusejp_3843_:
{
lean_object* v___x_3845_; 
v___x_3845_ = l_Lean_addDecl(v___x_3844_, v_hasTrace_3821_, v_a_3810_, v_a_3811_);
if (lean_obj_tag(v___x_3845_) == 0)
{
lean_object* v___x_3846_; uint8_t v___x_3847_; uint8_t v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; 
lean_dec_ref(v___x_3845_);
v___x_3846_ = l_Lean_Meta_simpExtension;
v___x_3847_ = 1;
v___x_3848_ = 0;
v___x_3849_ = lean_unsigned_to_nat(1000u);
v___x_3850_ = l_Lean_Meta_addSimpTheorem(v___x_3846_, v_name_3822_, v___x_3847_, v_hasTrace_3821_, v___x_3848_, v___x_3849_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_);
return v___x_3850_;
}
else
{
lean_dec(v_name_3822_);
return v___x_3845_;
}
}
}
}
}
else
{
lean_object* v_a_3854_; lean_object* v___x_3856_; uint8_t v_isShared_3857_; uint8_t v_isSharedCheck_3861_; 
lean_dec(v_val_3828_);
lean_dec(v_name_3822_);
lean_del_object(v___x_3818_);
lean_dec(v_levelParams_3816_);
v_a_3854_ = lean_ctor_get(v___x_3829_, 0);
v_isSharedCheck_3861_ = !lean_is_exclusive(v___x_3829_);
if (v_isSharedCheck_3861_ == 0)
{
v___x_3856_ = v___x_3829_;
v_isShared_3857_ = v_isSharedCheck_3861_;
goto v_resetjp_3855_;
}
else
{
lean_inc(v_a_3854_);
lean_dec(v___x_3829_);
v___x_3856_ = lean_box(0);
v_isShared_3857_ = v_isSharedCheck_3861_;
goto v_resetjp_3855_;
}
v_resetjp_3855_:
{
lean_object* v___x_3859_; 
if (v_isShared_3857_ == 0)
{
v___x_3859_ = v___x_3856_;
goto v_reusejp_3858_;
}
else
{
lean_object* v_reuseFailAlloc_3860_; 
v_reuseFailAlloc_3860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3860_, 0, v_a_3854_);
v___x_3859_ = v_reuseFailAlloc_3860_;
goto v_reusejp_3858_;
}
v_reusejp_3858_:
{
return v___x_3859_;
}
}
}
}
else
{
lean_object* v___x_3862_; lean_object* v___x_3864_; 
lean_dec(v_a_3824_);
lean_dec(v_name_3822_);
lean_del_object(v___x_3818_);
lean_dec(v_levelParams_3816_);
lean_dec_ref(v_ctorVal_3807_);
v___x_3862_ = lean_box(0);
if (v_isShared_3827_ == 0)
{
lean_ctor_set(v___x_3826_, 0, v___x_3862_);
v___x_3864_ = v___x_3826_;
goto v_reusejp_3863_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v___x_3862_);
v___x_3864_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3863_;
}
v_reusejp_3863_:
{
return v___x_3864_;
}
}
}
}
else
{
lean_object* v_a_3867_; lean_object* v___x_3869_; uint8_t v_isShared_3870_; uint8_t v_isSharedCheck_3874_; 
lean_dec(v_name_3822_);
lean_del_object(v___x_3818_);
lean_dec(v_levelParams_3816_);
lean_dec_ref(v_ctorVal_3807_);
v_a_3867_ = lean_ctor_get(v___x_3823_, 0);
v_isSharedCheck_3874_ = !lean_is_exclusive(v___x_3823_);
if (v_isSharedCheck_3874_ == 0)
{
v___x_3869_ = v___x_3823_;
v_isShared_3870_ = v_isSharedCheck_3874_;
goto v_resetjp_3868_;
}
else
{
lean_inc(v_a_3867_);
lean_dec(v___x_3823_);
v___x_3869_ = lean_box(0);
v_isShared_3870_ = v_isSharedCheck_3874_;
goto v_resetjp_3868_;
}
v_resetjp_3868_:
{
lean_object* v___x_3872_; 
if (v_isShared_3870_ == 0)
{
v___x_3872_ = v___x_3869_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3873_; 
v_reuseFailAlloc_3873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3873_, 0, v_a_3867_);
v___x_3872_ = v_reuseFailAlloc_3873_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
return v___x_3872_;
}
}
}
}
else
{
lean_object* v___f_3875_; lean_object* v_cls_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; uint8_t v___x_3879_; lean_object* v___y_3881_; lean_object* v___y_3882_; lean_object* v_a_3883_; lean_object* v___y_3893_; lean_object* v___y_3894_; lean_object* v_a_3895_; lean_object* v___y_3898_; lean_object* v___y_3899_; lean_object* v_a_3900_; lean_object* v___y_3903_; lean_object* v___y_3904_; lean_object* v___y_3905_; lean_object* v___y_3909_; lean_object* v___y_3910_; lean_object* v_a_3911_; lean_object* v___y_3924_; lean_object* v___y_3925_; lean_object* v_a_3926_; lean_object* v___y_3929_; lean_object* v___y_3930_; lean_object* v_a_3931_; lean_object* v___y_3934_; lean_object* v___y_3935_; lean_object* v___y_3936_; 
lean_inc(v_name_3822_);
v___f_3875_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3875_, 0, v_name_3822_);
v_cls_3876_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_3877_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_3878_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_3879_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3820_, v_options_3814_, v___x_3878_);
if (v___x_3879_ == 0)
{
lean_object* v___x_3974_; uint8_t v___x_3975_; 
v___x_3974_ = l_Lean_trace_profiler;
v___x_3975_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_3814_, v___x_3974_);
if (v___x_3975_ == 0)
{
lean_object* v___x_3976_; 
lean_dec_ref(v___f_3875_);
lean_inc_ref(v_ctorVal_3807_);
v___x_3976_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3807_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_);
if (lean_obj_tag(v___x_3976_) == 0)
{
lean_object* v_a_3977_; lean_object* v___x_3979_; uint8_t v_isShared_3980_; uint8_t v_isSharedCheck_4027_; 
v_a_3977_ = lean_ctor_get(v___x_3976_, 0);
v_isSharedCheck_4027_ = !lean_is_exclusive(v___x_3976_);
if (v_isSharedCheck_4027_ == 0)
{
v___x_3979_ = v___x_3976_;
v_isShared_3980_ = v_isSharedCheck_4027_;
goto v_resetjp_3978_;
}
else
{
lean_inc(v_a_3977_);
lean_dec(v___x_3976_);
v___x_3979_ = lean_box(0);
v_isShared_3980_ = v_isSharedCheck_4027_;
goto v_resetjp_3978_;
}
v_resetjp_3978_:
{
if (lean_obj_tag(v_a_3977_) == 1)
{
lean_object* v_val_3981_; lean_object* v___y_3983_; lean_object* v___y_3984_; lean_object* v___y_3985_; lean_object* v___y_3986_; 
lean_del_object(v___x_3979_);
v_val_3981_ = lean_ctor_get(v_a_3977_, 0);
lean_inc(v_val_3981_);
lean_dec_ref(v_a_3977_);
if (v___x_3879_ == 0)
{
v___y_3983_ = v_a_3808_;
v___y_3984_ = v_a_3809_;
v___y_3985_ = v_a_3810_;
v___y_3986_ = v_a_3811_;
goto v___jp_3982_;
}
else
{
lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; 
v___x_4019_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
lean_inc(v_val_3981_);
v___x_4020_ = l_Lean_MessageData_ofExpr(v_val_3981_);
v___x_4021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4021_, 0, v___x_4019_);
lean_ctor_set(v___x_4021_, 1, v___x_4020_);
v___x_4022_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_3876_, v___x_4021_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_);
if (lean_obj_tag(v___x_4022_) == 0)
{
lean_dec_ref(v___x_4022_);
v___y_3983_ = v_a_3808_;
v___y_3984_ = v_a_3809_;
v___y_3985_ = v_a_3810_;
v___y_3986_ = v_a_3811_;
goto v___jp_3982_;
}
else
{
lean_dec(v_val_3981_);
lean_dec(v_name_3822_);
lean_del_object(v___x_3818_);
lean_dec(v_levelParams_3816_);
lean_dec_ref(v_ctorVal_3807_);
return v___x_4022_;
}
}
v___jp_3982_:
{
lean_object* v___x_3987_; 
lean_inc(v_val_3981_);
v___x_3987_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3807_, v_val_3981_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_);
if (lean_obj_tag(v___x_3987_) == 0)
{
lean_object* v_a_3988_; lean_object* v___x_3989_; lean_object* v_a_3990_; lean_object* v___x_3991_; lean_object* v_a_3992_; lean_object* v___x_3994_; uint8_t v_isShared_3995_; uint8_t v_isSharedCheck_4010_; 
v_a_3988_ = lean_ctor_get(v___x_3987_, 0);
lean_inc(v_a_3988_);
lean_dec_ref(v___x_3987_);
v___x_3989_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3981_, v___y_3984_);
v_a_3990_ = lean_ctor_get(v___x_3989_, 0);
lean_inc(v_a_3990_);
lean_dec_ref(v___x_3989_);
v___x_3991_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3988_, v___y_3984_);
v_a_3992_ = lean_ctor_get(v___x_3991_, 0);
v_isSharedCheck_4010_ = !lean_is_exclusive(v___x_3991_);
if (v_isSharedCheck_4010_ == 0)
{
v___x_3994_ = v___x_3991_;
v_isShared_3995_ = v_isSharedCheck_4010_;
goto v_resetjp_3993_;
}
else
{
lean_inc(v_a_3992_);
lean_dec(v___x_3991_);
v___x_3994_ = lean_box(0);
v_isShared_3995_ = v_isSharedCheck_4010_;
goto v_resetjp_3993_;
}
v_resetjp_3993_:
{
lean_object* v___x_3997_; 
lean_inc(v_name_3822_);
if (v_isShared_3819_ == 0)
{
lean_ctor_set(v___x_3818_, 2, v_a_3990_);
lean_ctor_set(v___x_3818_, 0, v_name_3822_);
v___x_3997_ = v___x_3818_;
goto v_reusejp_3996_;
}
else
{
lean_object* v_reuseFailAlloc_4009_; 
v_reuseFailAlloc_4009_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4009_, 0, v_name_3822_);
lean_ctor_set(v_reuseFailAlloc_4009_, 1, v_levelParams_3816_);
lean_ctor_set(v_reuseFailAlloc_4009_, 2, v_a_3990_);
v___x_3997_ = v_reuseFailAlloc_4009_;
goto v_reusejp_3996_;
}
v_reusejp_3996_:
{
lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4002_; 
v___x_3998_ = lean_box(0);
lean_inc(v_name_3822_);
v___x_3999_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3999_, 0, v_name_3822_);
lean_ctor_set(v___x_3999_, 1, v___x_3998_);
v___x_4000_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4000_, 0, v___x_3997_);
lean_ctor_set(v___x_4000_, 1, v_a_3992_);
lean_ctor_set(v___x_4000_, 2, v___x_3999_);
if (v_isShared_3995_ == 0)
{
lean_ctor_set_tag(v___x_3994_, 2);
lean_ctor_set(v___x_3994_, 0, v___x_4000_);
v___x_4002_ = v___x_3994_;
goto v_reusejp_4001_;
}
else
{
lean_object* v_reuseFailAlloc_4008_; 
v_reuseFailAlloc_4008_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4008_, 0, v___x_4000_);
v___x_4002_ = v_reuseFailAlloc_4008_;
goto v_reusejp_4001_;
}
v_reusejp_4001_:
{
lean_object* v___x_4003_; 
v___x_4003_ = l_Lean_addDecl(v___x_4002_, v___x_3975_, v___y_3985_, v___y_3986_);
if (lean_obj_tag(v___x_4003_) == 0)
{
lean_object* v___x_4004_; uint8_t v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; 
lean_dec_ref(v___x_4003_);
v___x_4004_ = l_Lean_Meta_simpExtension;
v___x_4005_ = 0;
v___x_4006_ = lean_unsigned_to_nat(1000u);
v___x_4007_ = l_Lean_Meta_addSimpTheorem(v___x_4004_, v_name_3822_, v_hasTrace_3821_, v___x_3975_, v___x_4005_, v___x_4006_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_);
return v___x_4007_;
}
else
{
lean_dec(v_name_3822_);
return v___x_4003_;
}
}
}
}
}
else
{
lean_object* v_a_4011_; lean_object* v___x_4013_; uint8_t v_isShared_4014_; uint8_t v_isSharedCheck_4018_; 
lean_dec(v_val_3981_);
lean_dec(v_name_3822_);
lean_del_object(v___x_3818_);
lean_dec(v_levelParams_3816_);
v_a_4011_ = lean_ctor_get(v___x_3987_, 0);
v_isSharedCheck_4018_ = !lean_is_exclusive(v___x_3987_);
if (v_isSharedCheck_4018_ == 0)
{
v___x_4013_ = v___x_3987_;
v_isShared_4014_ = v_isSharedCheck_4018_;
goto v_resetjp_4012_;
}
else
{
lean_inc(v_a_4011_);
lean_dec(v___x_3987_);
v___x_4013_ = lean_box(0);
v_isShared_4014_ = v_isSharedCheck_4018_;
goto v_resetjp_4012_;
}
v_resetjp_4012_:
{
lean_object* v___x_4016_; 
if (v_isShared_4014_ == 0)
{
v___x_4016_ = v___x_4013_;
goto v_reusejp_4015_;
}
else
{
lean_object* v_reuseFailAlloc_4017_; 
v_reuseFailAlloc_4017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4017_, 0, v_a_4011_);
v___x_4016_ = v_reuseFailAlloc_4017_;
goto v_reusejp_4015_;
}
v_reusejp_4015_:
{
return v___x_4016_;
}
}
}
}
}
else
{
lean_object* v___x_4023_; lean_object* v___x_4025_; 
lean_dec(v_a_3977_);
lean_dec(v_name_3822_);
lean_del_object(v___x_3818_);
lean_dec(v_levelParams_3816_);
lean_dec_ref(v_ctorVal_3807_);
v___x_4023_ = lean_box(0);
if (v_isShared_3980_ == 0)
{
lean_ctor_set(v___x_3979_, 0, v___x_4023_);
v___x_4025_ = v___x_3979_;
goto v_reusejp_4024_;
}
else
{
lean_object* v_reuseFailAlloc_4026_; 
v_reuseFailAlloc_4026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4026_, 0, v___x_4023_);
v___x_4025_ = v_reuseFailAlloc_4026_;
goto v_reusejp_4024_;
}
v_reusejp_4024_:
{
return v___x_4025_;
}
}
}
}
else
{
lean_object* v_a_4028_; lean_object* v___x_4030_; uint8_t v_isShared_4031_; uint8_t v_isSharedCheck_4035_; 
lean_dec(v_name_3822_);
lean_del_object(v___x_3818_);
lean_dec(v_levelParams_3816_);
lean_dec_ref(v_ctorVal_3807_);
v_a_4028_ = lean_ctor_get(v___x_3976_, 0);
v_isSharedCheck_4035_ = !lean_is_exclusive(v___x_3976_);
if (v_isSharedCheck_4035_ == 0)
{
v___x_4030_ = v___x_3976_;
v_isShared_4031_ = v_isSharedCheck_4035_;
goto v_resetjp_4029_;
}
else
{
lean_inc(v_a_4028_);
lean_dec(v___x_3976_);
v___x_4030_ = lean_box(0);
v_isShared_4031_ = v_isSharedCheck_4035_;
goto v_resetjp_4029_;
}
v_resetjp_4029_:
{
lean_object* v___x_4033_; 
if (v_isShared_4031_ == 0)
{
v___x_4033_ = v___x_4030_;
goto v_reusejp_4032_;
}
else
{
lean_object* v_reuseFailAlloc_4034_; 
v_reuseFailAlloc_4034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4034_, 0, v_a_4028_);
v___x_4033_ = v_reuseFailAlloc_4034_;
goto v_reusejp_4032_;
}
v_reusejp_4032_:
{
return v___x_4033_;
}
}
}
}
else
{
lean_del_object(v___x_3818_);
goto v___jp_3939_;
}
}
else
{
lean_del_object(v___x_3818_);
goto v___jp_3939_;
}
v___jp_3880_:
{
lean_object* v___x_3884_; double v___x_3885_; double v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; 
v___x_3884_ = lean_io_get_num_heartbeats();
v___x_3885_ = lean_float_of_nat(v___y_3881_);
v___x_3886_ = lean_float_of_nat(v___x_3884_);
v___x_3887_ = lean_box_float(v___x_3885_);
v___x_3888_ = lean_box_float(v___x_3886_);
v___x_3889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3889_, 0, v___x_3887_);
lean_ctor_set(v___x_3889_, 1, v___x_3888_);
v___x_3890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3890_, 0, v_a_3883_);
lean_ctor_set(v___x_3890_, 1, v___x_3889_);
v___x_3891_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_3876_, v_hasTrace_3821_, v___x_3877_, v_options_3814_, v___x_3879_, v___y_3882_, v___f_3875_, v___x_3890_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_);
return v___x_3891_;
}
v___jp_3892_:
{
lean_object* v___x_3896_; 
v___x_3896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3896_, 0, v_a_3895_);
v___y_3881_ = v___y_3893_;
v___y_3882_ = v___y_3894_;
v_a_3883_ = v___x_3896_;
goto v___jp_3880_;
}
v___jp_3897_:
{
lean_object* v___x_3901_; 
v___x_3901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3901_, 0, v_a_3900_);
v___y_3881_ = v___y_3898_;
v___y_3882_ = v___y_3899_;
v_a_3883_ = v___x_3901_;
goto v___jp_3880_;
}
v___jp_3902_:
{
if (lean_obj_tag(v___y_3905_) == 0)
{
lean_object* v_a_3906_; 
v_a_3906_ = lean_ctor_get(v___y_3905_, 0);
lean_inc(v_a_3906_);
lean_dec_ref(v___y_3905_);
v___y_3898_ = v___y_3903_;
v___y_3899_ = v___y_3904_;
v_a_3900_ = v_a_3906_;
goto v___jp_3897_;
}
else
{
lean_object* v_a_3907_; 
v_a_3907_ = lean_ctor_get(v___y_3905_, 0);
lean_inc(v_a_3907_);
lean_dec_ref(v___y_3905_);
v___y_3893_ = v___y_3903_;
v___y_3894_ = v___y_3904_;
v_a_3895_ = v_a_3907_;
goto v___jp_3892_;
}
}
v___jp_3908_:
{
lean_object* v___x_3912_; double v___x_3913_; double v___x_3914_; double v___x_3915_; double v___x_3916_; double v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; 
v___x_3912_ = lean_io_mono_nanos_now();
v___x_3913_ = lean_float_of_nat(v___y_3909_);
v___x_3914_ = lean_float_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0);
v___x_3915_ = lean_float_div(v___x_3913_, v___x_3914_);
v___x_3916_ = lean_float_of_nat(v___x_3912_);
v___x_3917_ = lean_float_div(v___x_3916_, v___x_3914_);
v___x_3918_ = lean_box_float(v___x_3915_);
v___x_3919_ = lean_box_float(v___x_3917_);
v___x_3920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3920_, 0, v___x_3918_);
lean_ctor_set(v___x_3920_, 1, v___x_3919_);
v___x_3921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3921_, 0, v_a_3911_);
lean_ctor_set(v___x_3921_, 1, v___x_3920_);
v___x_3922_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_3876_, v_hasTrace_3821_, v___x_3877_, v_options_3814_, v___x_3879_, v___y_3910_, v___f_3875_, v___x_3921_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_);
return v___x_3922_;
}
v___jp_3923_:
{
lean_object* v___x_3927_; 
v___x_3927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3927_, 0, v_a_3926_);
v___y_3909_ = v___y_3924_;
v___y_3910_ = v___y_3925_;
v_a_3911_ = v___x_3927_;
goto v___jp_3908_;
}
v___jp_3928_:
{
lean_object* v___x_3932_; 
v___x_3932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3932_, 0, v_a_3931_);
v___y_3909_ = v___y_3929_;
v___y_3910_ = v___y_3930_;
v_a_3911_ = v___x_3932_;
goto v___jp_3908_;
}
v___jp_3933_:
{
if (lean_obj_tag(v___y_3936_) == 0)
{
lean_object* v_a_3937_; 
v_a_3937_ = lean_ctor_get(v___y_3936_, 0);
lean_inc(v_a_3937_);
lean_dec_ref(v___y_3936_);
v___y_3924_ = v___y_3934_;
v___y_3925_ = v___y_3935_;
v_a_3926_ = v_a_3937_;
goto v___jp_3923_;
}
else
{
lean_object* v_a_3938_; 
v_a_3938_ = lean_ctor_get(v___y_3936_, 0);
lean_inc(v_a_3938_);
lean_dec_ref(v___y_3936_);
v___y_3929_ = v___y_3934_;
v___y_3930_ = v___y_3935_;
v_a_3931_ = v_a_3938_;
goto v___jp_3928_;
}
}
v___jp_3939_:
{
lean_object* v___x_3940_; lean_object* v_a_3941_; lean_object* v___x_3942_; uint8_t v___x_3943_; 
v___x_3940_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v_a_3811_);
v_a_3941_ = lean_ctor_get(v___x_3940_, 0);
lean_inc(v_a_3941_);
lean_dec_ref(v___x_3940_);
v___x_3942_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3943_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_3814_, v___x_3942_);
if (v___x_3943_ == 0)
{
lean_object* v___x_3944_; lean_object* v___x_3945_; 
v___x_3944_ = lean_io_mono_nanos_now();
lean_inc_ref(v_ctorVal_3807_);
v___x_3945_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3807_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_);
if (lean_obj_tag(v___x_3945_) == 0)
{
lean_object* v_a_3946_; 
v_a_3946_ = lean_ctor_get(v___x_3945_, 0);
lean_inc(v_a_3946_);
lean_dec_ref(v___x_3945_);
if (lean_obj_tag(v_a_3946_) == 1)
{
if (v___x_3879_ == 0)
{
lean_object* v_val_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; 
v_val_3947_ = lean_ctor_get(v_a_3946_, 0);
lean_inc(v_val_3947_);
lean_dec_ref(v_a_3946_);
v___x_3948_ = lean_box(0);
v___x_3949_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(v_ctorVal_3807_, v_val_3947_, v_name_3822_, v_levelParams_3816_, v___x_3943_, v_hasTrace_3821_, v___x_3948_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_);
v___y_3934_ = v___x_3944_;
v___y_3935_ = v_a_3941_;
v___y_3936_ = v___x_3949_;
goto v___jp_3933_;
}
else
{
lean_object* v_val_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; 
v_val_3950_ = lean_ctor_get(v_a_3946_, 0);
lean_inc_n(v_val_3950_, 2);
lean_dec_ref(v_a_3946_);
v___x_3951_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_3952_ = l_Lean_MessageData_ofExpr(v_val_3950_);
v___x_3953_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3953_, 0, v___x_3951_);
lean_ctor_set(v___x_3953_, 1, v___x_3952_);
v___x_3954_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_3876_, v___x_3953_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_);
if (lean_obj_tag(v___x_3954_) == 0)
{
lean_object* v_a_3955_; lean_object* v___x_3956_; 
v_a_3955_ = lean_ctor_get(v___x_3954_, 0);
lean_inc(v_a_3955_);
lean_dec_ref(v___x_3954_);
v___x_3956_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(v_ctorVal_3807_, v_val_3950_, v_name_3822_, v_levelParams_3816_, v___x_3943_, v_hasTrace_3821_, v_a_3955_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_);
v___y_3934_ = v___x_3944_;
v___y_3935_ = v_a_3941_;
v___y_3936_ = v___x_3956_;
goto v___jp_3933_;
}
else
{
lean_dec(v_val_3950_);
lean_dec(v_name_3822_);
lean_dec(v_levelParams_3816_);
lean_dec_ref(v_ctorVal_3807_);
v___y_3934_ = v___x_3944_;
v___y_3935_ = v_a_3941_;
v___y_3936_ = v___x_3954_;
goto v___jp_3933_;
}
}
}
else
{
lean_object* v___x_3957_; 
lean_dec(v_a_3946_);
lean_dec(v_name_3822_);
lean_dec(v_levelParams_3816_);
lean_dec_ref(v_ctorVal_3807_);
v___x_3957_ = lean_box(0);
v___y_3924_ = v___x_3944_;
v___y_3925_ = v_a_3941_;
v_a_3926_ = v___x_3957_;
goto v___jp_3923_;
}
}
else
{
lean_object* v_a_3958_; 
lean_dec(v_name_3822_);
lean_dec(v_levelParams_3816_);
lean_dec_ref(v_ctorVal_3807_);
v_a_3958_ = lean_ctor_get(v___x_3945_, 0);
lean_inc(v_a_3958_);
lean_dec_ref(v___x_3945_);
v___y_3929_ = v___x_3944_;
v___y_3930_ = v_a_3941_;
v_a_3931_ = v_a_3958_;
goto v___jp_3928_;
}
}
else
{
lean_object* v___x_3959_; lean_object* v___x_3960_; 
v___x_3959_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_ctorVal_3807_);
v___x_3960_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3807_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_);
if (lean_obj_tag(v___x_3960_) == 0)
{
lean_object* v_a_3961_; 
v_a_3961_ = lean_ctor_get(v___x_3960_, 0);
lean_inc(v_a_3961_);
lean_dec_ref(v___x_3960_);
if (lean_obj_tag(v_a_3961_) == 1)
{
if (v___x_3879_ == 0)
{
lean_object* v_val_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; 
v_val_3962_ = lean_ctor_get(v_a_3961_, 0);
lean_inc(v_val_3962_);
lean_dec_ref(v_a_3961_);
v___x_3963_ = lean_box(0);
v___x_3964_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(v_ctorVal_3807_, v_val_3962_, v_name_3822_, v_levelParams_3816_, v___x_3943_, v___x_3963_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_);
v___y_3903_ = v___x_3959_;
v___y_3904_ = v_a_3941_;
v___y_3905_ = v___x_3964_;
goto v___jp_3902_;
}
else
{
lean_object* v_val_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; 
v_val_3965_ = lean_ctor_get(v_a_3961_, 0);
lean_inc_n(v_val_3965_, 2);
lean_dec_ref(v_a_3961_);
v___x_3966_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_3967_ = l_Lean_MessageData_ofExpr(v_val_3965_);
v___x_3968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3968_, 0, v___x_3966_);
lean_ctor_set(v___x_3968_, 1, v___x_3967_);
v___x_3969_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_3876_, v___x_3968_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_);
if (lean_obj_tag(v___x_3969_) == 0)
{
lean_object* v_a_3970_; lean_object* v___x_3971_; 
v_a_3970_ = lean_ctor_get(v___x_3969_, 0);
lean_inc(v_a_3970_);
lean_dec_ref(v___x_3969_);
v___x_3971_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(v_ctorVal_3807_, v_val_3965_, v_name_3822_, v_levelParams_3816_, v___x_3943_, v_a_3970_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_);
v___y_3903_ = v___x_3959_;
v___y_3904_ = v_a_3941_;
v___y_3905_ = v___x_3971_;
goto v___jp_3902_;
}
else
{
lean_dec(v_val_3965_);
lean_dec(v_name_3822_);
lean_dec(v_levelParams_3816_);
lean_dec_ref(v_ctorVal_3807_);
v___y_3903_ = v___x_3959_;
v___y_3904_ = v_a_3941_;
v___y_3905_ = v___x_3969_;
goto v___jp_3902_;
}
}
}
else
{
lean_object* v___x_3972_; 
lean_dec(v_a_3961_);
lean_dec(v_name_3822_);
lean_dec(v_levelParams_3816_);
lean_dec_ref(v_ctorVal_3807_);
v___x_3972_ = lean_box(0);
v___y_3898_ = v___x_3959_;
v___y_3899_ = v_a_3941_;
v_a_3900_ = v___x_3972_;
goto v___jp_3897_;
}
}
else
{
lean_object* v_a_3973_; 
lean_dec(v_name_3822_);
lean_dec(v_levelParams_3816_);
lean_dec_ref(v_ctorVal_3807_);
v_a_3973_ = lean_ctor_get(v___x_3960_, 0);
lean_inc(v_a_3973_);
lean_dec_ref(v___x_3960_);
v___y_3893_ = v___x_3959_;
v___y_3894_ = v_a_3941_;
v_a_3895_ = v_a_3973_;
goto v___jp_3892_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___boxed(lean_object* v_ctorVal_4038_, lean_object* v_a_4039_, lean_object* v_a_4040_, lean_object* v_a_4041_, lean_object* v_a_4042_, lean_object* v_a_4043_){
_start:
{
lean_object* v_res_4044_; 
v_res_4044_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(v_ctorVal_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_);
lean_dec(v_a_4042_);
lean_dec_ref(v_a_4041_);
lean_dec(v_a_4040_);
lean_dec_ref(v_a_4039_);
return v_res_4044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(lean_object* v_name_4045_, lean_object* v_decl_4046_, lean_object* v_ref_4047_){
_start:
{
lean_object* v_defValue_4049_; lean_object* v_descr_4050_; lean_object* v_deprecation_x3f_4051_; lean_object* v___x_4052_; uint8_t v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; 
v_defValue_4049_ = lean_ctor_get(v_decl_4046_, 0);
v_descr_4050_ = lean_ctor_get(v_decl_4046_, 1);
v_deprecation_x3f_4051_ = lean_ctor_get(v_decl_4046_, 2);
v___x_4052_ = lean_alloc_ctor(1, 0, 1);
v___x_4053_ = lean_unbox(v_defValue_4049_);
lean_ctor_set_uint8(v___x_4052_, 0, v___x_4053_);
lean_inc(v_deprecation_x3f_4051_);
lean_inc_ref(v_descr_4050_);
lean_inc_n(v_name_4045_, 2);
v___x_4054_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4054_, 0, v_name_4045_);
lean_ctor_set(v___x_4054_, 1, v_ref_4047_);
lean_ctor_set(v___x_4054_, 2, v___x_4052_);
lean_ctor_set(v___x_4054_, 3, v_descr_4050_);
lean_ctor_set(v___x_4054_, 4, v_deprecation_x3f_4051_);
v___x_4055_ = lean_register_option(v_name_4045_, v___x_4054_);
if (lean_obj_tag(v___x_4055_) == 0)
{
lean_object* v___x_4057_; uint8_t v_isShared_4058_; uint8_t v_isSharedCheck_4063_; 
v_isSharedCheck_4063_ = !lean_is_exclusive(v___x_4055_);
if (v_isSharedCheck_4063_ == 0)
{
lean_object* v_unused_4064_; 
v_unused_4064_ = lean_ctor_get(v___x_4055_, 0);
lean_dec(v_unused_4064_);
v___x_4057_ = v___x_4055_;
v_isShared_4058_ = v_isSharedCheck_4063_;
goto v_resetjp_4056_;
}
else
{
lean_dec(v___x_4055_);
v___x_4057_ = lean_box(0);
v_isShared_4058_ = v_isSharedCheck_4063_;
goto v_resetjp_4056_;
}
v_resetjp_4056_:
{
lean_object* v___x_4059_; lean_object* v___x_4061_; 
lean_inc(v_defValue_4049_);
v___x_4059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4059_, 0, v_name_4045_);
lean_ctor_set(v___x_4059_, 1, v_defValue_4049_);
if (v_isShared_4058_ == 0)
{
lean_ctor_set(v___x_4057_, 0, v___x_4059_);
v___x_4061_ = v___x_4057_;
goto v_reusejp_4060_;
}
else
{
lean_object* v_reuseFailAlloc_4062_; 
v_reuseFailAlloc_4062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4062_, 0, v___x_4059_);
v___x_4061_ = v_reuseFailAlloc_4062_;
goto v_reusejp_4060_;
}
v_reusejp_4060_:
{
return v___x_4061_;
}
}
}
else
{
lean_object* v_a_4065_; lean_object* v___x_4067_; uint8_t v_isShared_4068_; uint8_t v_isSharedCheck_4072_; 
lean_dec(v_name_4045_);
v_a_4065_ = lean_ctor_get(v___x_4055_, 0);
v_isSharedCheck_4072_ = !lean_is_exclusive(v___x_4055_);
if (v_isSharedCheck_4072_ == 0)
{
v___x_4067_ = v___x_4055_;
v_isShared_4068_ = v_isSharedCheck_4072_;
goto v_resetjp_4066_;
}
else
{
lean_inc(v_a_4065_);
lean_dec(v___x_4055_);
v___x_4067_ = lean_box(0);
v_isShared_4068_ = v_isSharedCheck_4072_;
goto v_resetjp_4066_;
}
v_resetjp_4066_:
{
lean_object* v___x_4070_; 
if (v_isShared_4068_ == 0)
{
v___x_4070_ = v___x_4067_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v_a_4065_);
v___x_4070_ = v_reuseFailAlloc_4071_;
goto v_reusejp_4069_;
}
v_reusejp_4069_:
{
return v___x_4070_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_4073_, lean_object* v_decl_4074_, lean_object* v_ref_4075_, lean_object* v_a_4076_){
_start:
{
lean_object* v_res_4077_; 
v_res_4077_ = l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(v_name_4073_, v_decl_4074_, v_ref_4075_);
lean_dec_ref(v_decl_4074_);
return v_res_4077_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; 
v___x_4092_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_));
v___x_4093_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_));
v___x_4094_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_));
v___x_4095_ = l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(v___x_4092_, v___x_4093_, v___x_4094_);
return v___x_4095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4____boxed(lean_object* v_a_4096_){
_start:
{
lean_object* v_res_4097_; 
v_res_4097_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_();
return v_res_4097_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(lean_object* v___y_4098_, uint8_t v_isExporting_4099_, lean_object* v___x_4100_, lean_object* v___y_4101_, lean_object* v___x_4102_, lean_object* v_a_x3f_4103_){
_start:
{
lean_object* v___x_4105_; lean_object* v_env_4106_; lean_object* v_nextMacroScope_4107_; lean_object* v_ngen_4108_; lean_object* v_auxDeclNGen_4109_; lean_object* v_traceState_4110_; lean_object* v_messages_4111_; lean_object* v_infoState_4112_; lean_object* v_snapshotTasks_4113_; lean_object* v_newDecls_4114_; lean_object* v___x_4116_; uint8_t v_isShared_4117_; uint8_t v_isSharedCheck_4139_; 
v___x_4105_ = lean_st_ref_take(v___y_4098_);
v_env_4106_ = lean_ctor_get(v___x_4105_, 0);
v_nextMacroScope_4107_ = lean_ctor_get(v___x_4105_, 1);
v_ngen_4108_ = lean_ctor_get(v___x_4105_, 2);
v_auxDeclNGen_4109_ = lean_ctor_get(v___x_4105_, 3);
v_traceState_4110_ = lean_ctor_get(v___x_4105_, 4);
v_messages_4111_ = lean_ctor_get(v___x_4105_, 6);
v_infoState_4112_ = lean_ctor_get(v___x_4105_, 7);
v_snapshotTasks_4113_ = lean_ctor_get(v___x_4105_, 8);
v_newDecls_4114_ = lean_ctor_get(v___x_4105_, 9);
v_isSharedCheck_4139_ = !lean_is_exclusive(v___x_4105_);
if (v_isSharedCheck_4139_ == 0)
{
lean_object* v_unused_4140_; 
v_unused_4140_ = lean_ctor_get(v___x_4105_, 5);
lean_dec(v_unused_4140_);
v___x_4116_ = v___x_4105_;
v_isShared_4117_ = v_isSharedCheck_4139_;
goto v_resetjp_4115_;
}
else
{
lean_inc(v_newDecls_4114_);
lean_inc(v_snapshotTasks_4113_);
lean_inc(v_infoState_4112_);
lean_inc(v_messages_4111_);
lean_inc(v_traceState_4110_);
lean_inc(v_auxDeclNGen_4109_);
lean_inc(v_ngen_4108_);
lean_inc(v_nextMacroScope_4107_);
lean_inc(v_env_4106_);
lean_dec(v___x_4105_);
v___x_4116_ = lean_box(0);
v_isShared_4117_ = v_isSharedCheck_4139_;
goto v_resetjp_4115_;
}
v_resetjp_4115_:
{
lean_object* v___x_4118_; lean_object* v___x_4120_; 
v___x_4118_ = l_Lean_Environment_setExporting(v_env_4106_, v_isExporting_4099_);
if (v_isShared_4117_ == 0)
{
lean_ctor_set(v___x_4116_, 5, v___x_4100_);
lean_ctor_set(v___x_4116_, 0, v___x_4118_);
v___x_4120_ = v___x_4116_;
goto v_reusejp_4119_;
}
else
{
lean_object* v_reuseFailAlloc_4138_; 
v_reuseFailAlloc_4138_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4138_, 0, v___x_4118_);
lean_ctor_set(v_reuseFailAlloc_4138_, 1, v_nextMacroScope_4107_);
lean_ctor_set(v_reuseFailAlloc_4138_, 2, v_ngen_4108_);
lean_ctor_set(v_reuseFailAlloc_4138_, 3, v_auxDeclNGen_4109_);
lean_ctor_set(v_reuseFailAlloc_4138_, 4, v_traceState_4110_);
lean_ctor_set(v_reuseFailAlloc_4138_, 5, v___x_4100_);
lean_ctor_set(v_reuseFailAlloc_4138_, 6, v_messages_4111_);
lean_ctor_set(v_reuseFailAlloc_4138_, 7, v_infoState_4112_);
lean_ctor_set(v_reuseFailAlloc_4138_, 8, v_snapshotTasks_4113_);
lean_ctor_set(v_reuseFailAlloc_4138_, 9, v_newDecls_4114_);
v___x_4120_ = v_reuseFailAlloc_4138_;
goto v_reusejp_4119_;
}
v_reusejp_4119_:
{
lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v_mctx_4123_; lean_object* v_zetaDeltaFVarIds_4124_; lean_object* v_postponed_4125_; lean_object* v_diag_4126_; lean_object* v___x_4128_; uint8_t v_isShared_4129_; uint8_t v_isSharedCheck_4136_; 
v___x_4121_ = lean_st_ref_set(v___y_4098_, v___x_4120_);
v___x_4122_ = lean_st_ref_take(v___y_4101_);
v_mctx_4123_ = lean_ctor_get(v___x_4122_, 0);
v_zetaDeltaFVarIds_4124_ = lean_ctor_get(v___x_4122_, 2);
v_postponed_4125_ = lean_ctor_get(v___x_4122_, 3);
v_diag_4126_ = lean_ctor_get(v___x_4122_, 4);
v_isSharedCheck_4136_ = !lean_is_exclusive(v___x_4122_);
if (v_isSharedCheck_4136_ == 0)
{
lean_object* v_unused_4137_; 
v_unused_4137_ = lean_ctor_get(v___x_4122_, 1);
lean_dec(v_unused_4137_);
v___x_4128_ = v___x_4122_;
v_isShared_4129_ = v_isSharedCheck_4136_;
goto v_resetjp_4127_;
}
else
{
lean_inc(v_diag_4126_);
lean_inc(v_postponed_4125_);
lean_inc(v_zetaDeltaFVarIds_4124_);
lean_inc(v_mctx_4123_);
lean_dec(v___x_4122_);
v___x_4128_ = lean_box(0);
v_isShared_4129_ = v_isSharedCheck_4136_;
goto v_resetjp_4127_;
}
v_resetjp_4127_:
{
lean_object* v___x_4131_; 
if (v_isShared_4129_ == 0)
{
lean_ctor_set(v___x_4128_, 1, v___x_4102_);
v___x_4131_ = v___x_4128_;
goto v_reusejp_4130_;
}
else
{
lean_object* v_reuseFailAlloc_4135_; 
v_reuseFailAlloc_4135_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4135_, 0, v_mctx_4123_);
lean_ctor_set(v_reuseFailAlloc_4135_, 1, v___x_4102_);
lean_ctor_set(v_reuseFailAlloc_4135_, 2, v_zetaDeltaFVarIds_4124_);
lean_ctor_set(v_reuseFailAlloc_4135_, 3, v_postponed_4125_);
lean_ctor_set(v_reuseFailAlloc_4135_, 4, v_diag_4126_);
v___x_4131_ = v_reuseFailAlloc_4135_;
goto v_reusejp_4130_;
}
v_reusejp_4130_:
{
lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; 
v___x_4132_ = lean_st_ref_set(v___y_4101_, v___x_4131_);
v___x_4133_ = lean_box(0);
v___x_4134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4134_, 0, v___x_4133_);
return v___x_4134_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0___boxed(lean_object* v___y_4141_, lean_object* v_isExporting_4142_, lean_object* v___x_4143_, lean_object* v___y_4144_, lean_object* v___x_4145_, lean_object* v_a_x3f_4146_, lean_object* v___y_4147_){
_start:
{
uint8_t v_isExporting_boxed_4148_; lean_object* v_res_4149_; 
v_isExporting_boxed_4148_ = lean_unbox(v_isExporting_4142_);
v_res_4149_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(v___y_4141_, v_isExporting_boxed_4148_, v___x_4143_, v___y_4144_, v___x_4145_, v_a_x3f_4146_);
lean_dec(v_a_x3f_4146_);
lean_dec(v___y_4144_);
lean_dec(v___y_4141_);
return v_res_4149_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_4150_; 
v___x_4150_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4150_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4151_; lean_object* v___x_4152_; 
v___x_4151_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0);
v___x_4152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4152_, 0, v___x_4151_);
return v___x_4152_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_4153_; lean_object* v___x_4154_; 
v___x_4153_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1);
v___x_4154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4154_, 0, v___x_4153_);
lean_ctor_set(v___x_4154_, 1, v___x_4153_);
return v___x_4154_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_4155_; lean_object* v___x_4156_; 
v___x_4155_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1);
v___x_4156_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4156_, 0, v___x_4155_);
lean_ctor_set(v___x_4156_, 1, v___x_4155_);
lean_ctor_set(v___x_4156_, 2, v___x_4155_);
lean_ctor_set(v___x_4156_, 3, v___x_4155_);
lean_ctor_set(v___x_4156_, 4, v___x_4155_);
lean_ctor_set(v___x_4156_, 5, v___x_4155_);
return v___x_4156_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(lean_object* v_x_4157_, uint8_t v_isExporting_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_){
_start:
{
lean_object* v___x_4164_; lean_object* v_env_4165_; uint8_t v_isExporting_4166_; lean_object* v___x_4167_; lean_object* v_env_4168_; lean_object* v_nextMacroScope_4169_; lean_object* v_ngen_4170_; lean_object* v_auxDeclNGen_4171_; lean_object* v_traceState_4172_; lean_object* v_messages_4173_; lean_object* v_infoState_4174_; lean_object* v_snapshotTasks_4175_; lean_object* v_newDecls_4176_; lean_object* v___x_4178_; uint8_t v_isShared_4179_; uint8_t v_isSharedCheck_4230_; 
v___x_4164_ = lean_st_ref_get(v___y_4162_);
v_env_4165_ = lean_ctor_get(v___x_4164_, 0);
lean_inc_ref(v_env_4165_);
lean_dec(v___x_4164_);
v_isExporting_4166_ = lean_ctor_get_uint8(v_env_4165_, sizeof(void*)*8);
lean_dec_ref(v_env_4165_);
v___x_4167_ = lean_st_ref_take(v___y_4162_);
v_env_4168_ = lean_ctor_get(v___x_4167_, 0);
v_nextMacroScope_4169_ = lean_ctor_get(v___x_4167_, 1);
v_ngen_4170_ = lean_ctor_get(v___x_4167_, 2);
v_auxDeclNGen_4171_ = lean_ctor_get(v___x_4167_, 3);
v_traceState_4172_ = lean_ctor_get(v___x_4167_, 4);
v_messages_4173_ = lean_ctor_get(v___x_4167_, 6);
v_infoState_4174_ = lean_ctor_get(v___x_4167_, 7);
v_snapshotTasks_4175_ = lean_ctor_get(v___x_4167_, 8);
v_newDecls_4176_ = lean_ctor_get(v___x_4167_, 9);
v_isSharedCheck_4230_ = !lean_is_exclusive(v___x_4167_);
if (v_isSharedCheck_4230_ == 0)
{
lean_object* v_unused_4231_; 
v_unused_4231_ = lean_ctor_get(v___x_4167_, 5);
lean_dec(v_unused_4231_);
v___x_4178_ = v___x_4167_;
v_isShared_4179_ = v_isSharedCheck_4230_;
goto v_resetjp_4177_;
}
else
{
lean_inc(v_newDecls_4176_);
lean_inc(v_snapshotTasks_4175_);
lean_inc(v_infoState_4174_);
lean_inc(v_messages_4173_);
lean_inc(v_traceState_4172_);
lean_inc(v_auxDeclNGen_4171_);
lean_inc(v_ngen_4170_);
lean_inc(v_nextMacroScope_4169_);
lean_inc(v_env_4168_);
lean_dec(v___x_4167_);
v___x_4178_ = lean_box(0);
v_isShared_4179_ = v_isSharedCheck_4230_;
goto v_resetjp_4177_;
}
v_resetjp_4177_:
{
lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4183_; 
v___x_4180_ = l_Lean_Environment_setExporting(v_env_4168_, v_isExporting_4158_);
v___x_4181_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2);
if (v_isShared_4179_ == 0)
{
lean_ctor_set(v___x_4178_, 5, v___x_4181_);
lean_ctor_set(v___x_4178_, 0, v___x_4180_);
v___x_4183_ = v___x_4178_;
goto v_reusejp_4182_;
}
else
{
lean_object* v_reuseFailAlloc_4229_; 
v_reuseFailAlloc_4229_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4229_, 0, v___x_4180_);
lean_ctor_set(v_reuseFailAlloc_4229_, 1, v_nextMacroScope_4169_);
lean_ctor_set(v_reuseFailAlloc_4229_, 2, v_ngen_4170_);
lean_ctor_set(v_reuseFailAlloc_4229_, 3, v_auxDeclNGen_4171_);
lean_ctor_set(v_reuseFailAlloc_4229_, 4, v_traceState_4172_);
lean_ctor_set(v_reuseFailAlloc_4229_, 5, v___x_4181_);
lean_ctor_set(v_reuseFailAlloc_4229_, 6, v_messages_4173_);
lean_ctor_set(v_reuseFailAlloc_4229_, 7, v_infoState_4174_);
lean_ctor_set(v_reuseFailAlloc_4229_, 8, v_snapshotTasks_4175_);
lean_ctor_set(v_reuseFailAlloc_4229_, 9, v_newDecls_4176_);
v___x_4183_ = v_reuseFailAlloc_4229_;
goto v_reusejp_4182_;
}
v_reusejp_4182_:
{
lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v_mctx_4186_; lean_object* v_zetaDeltaFVarIds_4187_; lean_object* v_postponed_4188_; lean_object* v_diag_4189_; lean_object* v___x_4191_; uint8_t v_isShared_4192_; uint8_t v_isSharedCheck_4227_; 
v___x_4184_ = lean_st_ref_set(v___y_4162_, v___x_4183_);
v___x_4185_ = lean_st_ref_take(v___y_4160_);
v_mctx_4186_ = lean_ctor_get(v___x_4185_, 0);
v_zetaDeltaFVarIds_4187_ = lean_ctor_get(v___x_4185_, 2);
v_postponed_4188_ = lean_ctor_get(v___x_4185_, 3);
v_diag_4189_ = lean_ctor_get(v___x_4185_, 4);
v_isSharedCheck_4227_ = !lean_is_exclusive(v___x_4185_);
if (v_isSharedCheck_4227_ == 0)
{
lean_object* v_unused_4228_; 
v_unused_4228_ = lean_ctor_get(v___x_4185_, 1);
lean_dec(v_unused_4228_);
v___x_4191_ = v___x_4185_;
v_isShared_4192_ = v_isSharedCheck_4227_;
goto v_resetjp_4190_;
}
else
{
lean_inc(v_diag_4189_);
lean_inc(v_postponed_4188_);
lean_inc(v_zetaDeltaFVarIds_4187_);
lean_inc(v_mctx_4186_);
lean_dec(v___x_4185_);
v___x_4191_ = lean_box(0);
v_isShared_4192_ = v_isSharedCheck_4227_;
goto v_resetjp_4190_;
}
v_resetjp_4190_:
{
lean_object* v___x_4193_; lean_object* v___x_4195_; 
v___x_4193_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3);
if (v_isShared_4192_ == 0)
{
lean_ctor_set(v___x_4191_, 1, v___x_4193_);
v___x_4195_ = v___x_4191_;
goto v_reusejp_4194_;
}
else
{
lean_object* v_reuseFailAlloc_4226_; 
v_reuseFailAlloc_4226_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4226_, 0, v_mctx_4186_);
lean_ctor_set(v_reuseFailAlloc_4226_, 1, v___x_4193_);
lean_ctor_set(v_reuseFailAlloc_4226_, 2, v_zetaDeltaFVarIds_4187_);
lean_ctor_set(v_reuseFailAlloc_4226_, 3, v_postponed_4188_);
lean_ctor_set(v_reuseFailAlloc_4226_, 4, v_diag_4189_);
v___x_4195_ = v_reuseFailAlloc_4226_;
goto v_reusejp_4194_;
}
v_reusejp_4194_:
{
lean_object* v___x_4196_; lean_object* v_r_4197_; 
v___x_4196_ = lean_st_ref_set(v___y_4160_, v___x_4195_);
lean_inc(v___y_4162_);
lean_inc_ref(v___y_4161_);
lean_inc(v___y_4160_);
lean_inc_ref(v___y_4159_);
v_r_4197_ = lean_apply_5(v_x_4157_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_, lean_box(0));
if (lean_obj_tag(v_r_4197_) == 0)
{
lean_object* v_a_4198_; lean_object* v___x_4200_; uint8_t v_isShared_4201_; uint8_t v_isSharedCheck_4214_; 
v_a_4198_ = lean_ctor_get(v_r_4197_, 0);
v_isSharedCheck_4214_ = !lean_is_exclusive(v_r_4197_);
if (v_isSharedCheck_4214_ == 0)
{
v___x_4200_ = v_r_4197_;
v_isShared_4201_ = v_isSharedCheck_4214_;
goto v_resetjp_4199_;
}
else
{
lean_inc(v_a_4198_);
lean_dec(v_r_4197_);
v___x_4200_ = lean_box(0);
v_isShared_4201_ = v_isSharedCheck_4214_;
goto v_resetjp_4199_;
}
v_resetjp_4199_:
{
lean_object* v___x_4203_; 
lean_inc(v_a_4198_);
if (v_isShared_4201_ == 0)
{
lean_ctor_set_tag(v___x_4200_, 1);
v___x_4203_ = v___x_4200_;
goto v_reusejp_4202_;
}
else
{
lean_object* v_reuseFailAlloc_4213_; 
v_reuseFailAlloc_4213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4213_, 0, v_a_4198_);
v___x_4203_ = v_reuseFailAlloc_4213_;
goto v_reusejp_4202_;
}
v_reusejp_4202_:
{
lean_object* v___x_4204_; lean_object* v___x_4206_; uint8_t v_isShared_4207_; uint8_t v_isSharedCheck_4211_; 
v___x_4204_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(v___y_4162_, v_isExporting_4166_, v___x_4181_, v___y_4160_, v___x_4193_, v___x_4203_);
lean_dec_ref(v___x_4203_);
v_isSharedCheck_4211_ = !lean_is_exclusive(v___x_4204_);
if (v_isSharedCheck_4211_ == 0)
{
lean_object* v_unused_4212_; 
v_unused_4212_ = lean_ctor_get(v___x_4204_, 0);
lean_dec(v_unused_4212_);
v___x_4206_ = v___x_4204_;
v_isShared_4207_ = v_isSharedCheck_4211_;
goto v_resetjp_4205_;
}
else
{
lean_dec(v___x_4204_);
v___x_4206_ = lean_box(0);
v_isShared_4207_ = v_isSharedCheck_4211_;
goto v_resetjp_4205_;
}
v_resetjp_4205_:
{
lean_object* v___x_4209_; 
if (v_isShared_4207_ == 0)
{
lean_ctor_set(v___x_4206_, 0, v_a_4198_);
v___x_4209_ = v___x_4206_;
goto v_reusejp_4208_;
}
else
{
lean_object* v_reuseFailAlloc_4210_; 
v_reuseFailAlloc_4210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4210_, 0, v_a_4198_);
v___x_4209_ = v_reuseFailAlloc_4210_;
goto v_reusejp_4208_;
}
v_reusejp_4208_:
{
return v___x_4209_;
}
}
}
}
}
else
{
lean_object* v_a_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4219_; uint8_t v_isShared_4220_; uint8_t v_isSharedCheck_4224_; 
v_a_4215_ = lean_ctor_get(v_r_4197_, 0);
lean_inc(v_a_4215_);
lean_dec_ref(v_r_4197_);
v___x_4216_ = lean_box(0);
v___x_4217_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(v___y_4162_, v_isExporting_4166_, v___x_4181_, v___y_4160_, v___x_4193_, v___x_4216_);
v_isSharedCheck_4224_ = !lean_is_exclusive(v___x_4217_);
if (v_isSharedCheck_4224_ == 0)
{
lean_object* v_unused_4225_; 
v_unused_4225_ = lean_ctor_get(v___x_4217_, 0);
lean_dec(v_unused_4225_);
v___x_4219_ = v___x_4217_;
v_isShared_4220_ = v_isSharedCheck_4224_;
goto v_resetjp_4218_;
}
else
{
lean_dec(v___x_4217_);
v___x_4219_ = lean_box(0);
v_isShared_4220_ = v_isSharedCheck_4224_;
goto v_resetjp_4218_;
}
v_resetjp_4218_:
{
lean_object* v___x_4222_; 
if (v_isShared_4220_ == 0)
{
lean_ctor_set_tag(v___x_4219_, 1);
lean_ctor_set(v___x_4219_, 0, v_a_4215_);
v___x_4222_ = v___x_4219_;
goto v_reusejp_4221_;
}
else
{
lean_object* v_reuseFailAlloc_4223_; 
v_reuseFailAlloc_4223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4223_, 0, v_a_4215_);
v___x_4222_ = v_reuseFailAlloc_4223_;
goto v_reusejp_4221_;
}
v_reusejp_4221_:
{
return v___x_4222_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___boxed(lean_object* v_x_4232_, lean_object* v_isExporting_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_){
_start:
{
uint8_t v_isExporting_boxed_4239_; lean_object* v_res_4240_; 
v_isExporting_boxed_4239_ = lean_unbox(v_isExporting_4233_);
v_res_4240_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(v_x_4232_, v_isExporting_boxed_4239_, v___y_4234_, v___y_4235_, v___y_4236_, v___y_4237_);
lean_dec(v___y_4237_);
lean_dec_ref(v___y_4236_);
lean_dec(v___y_4235_);
lean_dec_ref(v___y_4234_);
return v_res_4240_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2(lean_object* v_00_u03b1_4241_, lean_object* v_x_4242_, uint8_t v_isExporting_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_){
_start:
{
lean_object* v___x_4249_; 
v___x_4249_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(v_x_4242_, v_isExporting_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_);
return v___x_4249_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___boxed(lean_object* v_00_u03b1_4250_, lean_object* v_x_4251_, lean_object* v_isExporting_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_){
_start:
{
uint8_t v_isExporting_boxed_4258_; lean_object* v_res_4259_; 
v_isExporting_boxed_4258_ = lean_unbox(v_isExporting_4252_);
v_res_4259_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2(v_00_u03b1_4250_, v_x_4251_, v_isExporting_boxed_4258_, v___y_4253_, v___y_4254_, v___y_4255_, v___y_4256_);
lean_dec(v___y_4256_);
lean_dec_ref(v___y_4255_);
lean_dec(v___y_4254_);
lean_dec_ref(v___y_4253_);
return v_res_4259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(lean_object* v_lctx_4260_, lean_object* v_localInsts_4261_, lean_object* v_x_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_){
_start:
{
lean_object* v___x_4268_; 
v___x_4268_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_4260_, v_localInsts_4261_, v_x_4262_, v___y_4263_, v___y_4264_, v___y_4265_, v___y_4266_);
if (lean_obj_tag(v___x_4268_) == 0)
{
lean_object* v_a_4269_; lean_object* v___x_4271_; uint8_t v_isShared_4272_; uint8_t v_isSharedCheck_4276_; 
v_a_4269_ = lean_ctor_get(v___x_4268_, 0);
v_isSharedCheck_4276_ = !lean_is_exclusive(v___x_4268_);
if (v_isSharedCheck_4276_ == 0)
{
v___x_4271_ = v___x_4268_;
v_isShared_4272_ = v_isSharedCheck_4276_;
goto v_resetjp_4270_;
}
else
{
lean_inc(v_a_4269_);
lean_dec(v___x_4268_);
v___x_4271_ = lean_box(0);
v_isShared_4272_ = v_isSharedCheck_4276_;
goto v_resetjp_4270_;
}
v_resetjp_4270_:
{
lean_object* v___x_4274_; 
if (v_isShared_4272_ == 0)
{
v___x_4274_ = v___x_4271_;
goto v_reusejp_4273_;
}
else
{
lean_object* v_reuseFailAlloc_4275_; 
v_reuseFailAlloc_4275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4275_, 0, v_a_4269_);
v___x_4274_ = v_reuseFailAlloc_4275_;
goto v_reusejp_4273_;
}
v_reusejp_4273_:
{
return v___x_4274_;
}
}
}
else
{
lean_object* v_a_4277_; lean_object* v___x_4279_; uint8_t v_isShared_4280_; uint8_t v_isSharedCheck_4284_; 
v_a_4277_ = lean_ctor_get(v___x_4268_, 0);
v_isSharedCheck_4284_ = !lean_is_exclusive(v___x_4268_);
if (v_isSharedCheck_4284_ == 0)
{
v___x_4279_ = v___x_4268_;
v_isShared_4280_ = v_isSharedCheck_4284_;
goto v_resetjp_4278_;
}
else
{
lean_inc(v_a_4277_);
lean_dec(v___x_4268_);
v___x_4279_ = lean_box(0);
v_isShared_4280_ = v_isSharedCheck_4284_;
goto v_resetjp_4278_;
}
v_resetjp_4278_:
{
lean_object* v___x_4282_; 
if (v_isShared_4280_ == 0)
{
v___x_4282_ = v___x_4279_;
goto v_reusejp_4281_;
}
else
{
lean_object* v_reuseFailAlloc_4283_; 
v_reuseFailAlloc_4283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4283_, 0, v_a_4277_);
v___x_4282_ = v_reuseFailAlloc_4283_;
goto v_reusejp_4281_;
}
v_reusejp_4281_:
{
return v___x_4282_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg___boxed(lean_object* v_lctx_4285_, lean_object* v_localInsts_4286_, lean_object* v_x_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_){
_start:
{
lean_object* v_res_4293_; 
v_res_4293_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v_lctx_4285_, v_localInsts_4286_, v_x_4287_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_);
lean_dec(v___y_4291_);
lean_dec_ref(v___y_4290_);
lean_dec(v___y_4289_);
lean_dec_ref(v___y_4288_);
return v_res_4293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4(lean_object* v_00_u03b1_4294_, lean_object* v_lctx_4295_, lean_object* v_localInsts_4296_, lean_object* v_x_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_){
_start:
{
lean_object* v___x_4303_; 
v___x_4303_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v_lctx_4295_, v_localInsts_4296_, v_x_4297_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_);
return v___x_4303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___boxed(lean_object* v_00_u03b1_4304_, lean_object* v_lctx_4305_, lean_object* v_localInsts_4306_, lean_object* v_x_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_){
_start:
{
lean_object* v_res_4313_; 
v_res_4313_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4(v_00_u03b1_4304_, v_lctx_4305_, v_localInsts_4306_, v_x_4307_, v___y_4308_, v___y_4309_, v___y_4310_, v___y_4311_);
lean_dec(v___y_4311_);
lean_dec_ref(v___y_4310_);
lean_dec(v___y_4309_);
lean_dec_ref(v___y_4308_);
return v_res_4313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__0(lean_object* v_declName_4314_, lean_object* v_x_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_){
_start:
{
lean_object* v___x_4321_; lean_object* v___x_4322_; 
v___x_4321_ = l_Lean_MessageData_ofName(v_declName_4314_);
v___x_4322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4322_, 0, v___x_4321_);
return v___x_4322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__0___boxed(lean_object* v_declName_4323_, lean_object* v_x_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_){
_start:
{
lean_object* v_res_4330_; 
v_res_4330_ = l_Lean_Meta_mkInjectiveTheorems___lam__0(v_declName_4323_, v_x_4324_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_);
lean_dec(v___y_4328_);
lean_dec_ref(v___y_4327_);
lean_dec(v___y_4326_);
lean_dec_ref(v___y_4325_);
lean_dec_ref(v_x_4324_);
return v_res_4330_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_4331_; 
v___x_4331_ = l_instMonadEIO(lean_box(0));
return v___x_4331_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(lean_object* v_msg_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_){
_start:
{
lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v_toApplicative_4344_; lean_object* v___x_4346_; uint8_t v_isShared_4347_; uint8_t v_isSharedCheck_4405_; 
v___x_4342_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0);
v___x_4343_ = l_StateRefT_x27_instMonad___redArg(v___x_4342_);
v_toApplicative_4344_ = lean_ctor_get(v___x_4343_, 0);
v_isSharedCheck_4405_ = !lean_is_exclusive(v___x_4343_);
if (v_isSharedCheck_4405_ == 0)
{
lean_object* v_unused_4406_; 
v_unused_4406_ = lean_ctor_get(v___x_4343_, 1);
lean_dec(v_unused_4406_);
v___x_4346_ = v___x_4343_;
v_isShared_4347_ = v_isSharedCheck_4405_;
goto v_resetjp_4345_;
}
else
{
lean_inc(v_toApplicative_4344_);
lean_dec(v___x_4343_);
v___x_4346_ = lean_box(0);
v_isShared_4347_ = v_isSharedCheck_4405_;
goto v_resetjp_4345_;
}
v_resetjp_4345_:
{
lean_object* v_toFunctor_4348_; lean_object* v_toSeq_4349_; lean_object* v_toSeqLeft_4350_; lean_object* v_toSeqRight_4351_; lean_object* v___x_4353_; uint8_t v_isShared_4354_; uint8_t v_isSharedCheck_4403_; 
v_toFunctor_4348_ = lean_ctor_get(v_toApplicative_4344_, 0);
v_toSeq_4349_ = lean_ctor_get(v_toApplicative_4344_, 2);
v_toSeqLeft_4350_ = lean_ctor_get(v_toApplicative_4344_, 3);
v_toSeqRight_4351_ = lean_ctor_get(v_toApplicative_4344_, 4);
v_isSharedCheck_4403_ = !lean_is_exclusive(v_toApplicative_4344_);
if (v_isSharedCheck_4403_ == 0)
{
lean_object* v_unused_4404_; 
v_unused_4404_ = lean_ctor_get(v_toApplicative_4344_, 1);
lean_dec(v_unused_4404_);
v___x_4353_ = v_toApplicative_4344_;
v_isShared_4354_ = v_isSharedCheck_4403_;
goto v_resetjp_4352_;
}
else
{
lean_inc(v_toSeqRight_4351_);
lean_inc(v_toSeqLeft_4350_);
lean_inc(v_toSeq_4349_);
lean_inc(v_toFunctor_4348_);
lean_dec(v_toApplicative_4344_);
v___x_4353_ = lean_box(0);
v_isShared_4354_ = v_isSharedCheck_4403_;
goto v_resetjp_4352_;
}
v_resetjp_4352_:
{
lean_object* v___f_4355_; lean_object* v___f_4356_; lean_object* v___f_4357_; lean_object* v___f_4358_; lean_object* v___x_4359_; lean_object* v___f_4360_; lean_object* v___f_4361_; lean_object* v___f_4362_; lean_object* v___x_4364_; 
v___f_4355_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__1));
v___f_4356_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__2));
lean_inc_ref(v_toFunctor_4348_);
v___f_4357_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4357_, 0, v_toFunctor_4348_);
v___f_4358_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4358_, 0, v_toFunctor_4348_);
v___x_4359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4359_, 0, v___f_4357_);
lean_ctor_set(v___x_4359_, 1, v___f_4358_);
v___f_4360_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4360_, 0, v_toSeqRight_4351_);
v___f_4361_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4361_, 0, v_toSeqLeft_4350_);
v___f_4362_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4362_, 0, v_toSeq_4349_);
if (v_isShared_4354_ == 0)
{
lean_ctor_set(v___x_4353_, 4, v___f_4360_);
lean_ctor_set(v___x_4353_, 3, v___f_4361_);
lean_ctor_set(v___x_4353_, 2, v___f_4362_);
lean_ctor_set(v___x_4353_, 1, v___f_4355_);
lean_ctor_set(v___x_4353_, 0, v___x_4359_);
v___x_4364_ = v___x_4353_;
goto v_reusejp_4363_;
}
else
{
lean_object* v_reuseFailAlloc_4402_; 
v_reuseFailAlloc_4402_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4402_, 0, v___x_4359_);
lean_ctor_set(v_reuseFailAlloc_4402_, 1, v___f_4355_);
lean_ctor_set(v_reuseFailAlloc_4402_, 2, v___f_4362_);
lean_ctor_set(v_reuseFailAlloc_4402_, 3, v___f_4361_);
lean_ctor_set(v_reuseFailAlloc_4402_, 4, v___f_4360_);
v___x_4364_ = v_reuseFailAlloc_4402_;
goto v_reusejp_4363_;
}
v_reusejp_4363_:
{
lean_object* v___x_4366_; 
if (v_isShared_4347_ == 0)
{
lean_ctor_set(v___x_4346_, 1, v___f_4356_);
lean_ctor_set(v___x_4346_, 0, v___x_4364_);
v___x_4366_ = v___x_4346_;
goto v_reusejp_4365_;
}
else
{
lean_object* v_reuseFailAlloc_4401_; 
v_reuseFailAlloc_4401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4401_, 0, v___x_4364_);
lean_ctor_set(v_reuseFailAlloc_4401_, 1, v___f_4356_);
v___x_4366_ = v_reuseFailAlloc_4401_;
goto v_reusejp_4365_;
}
v_reusejp_4365_:
{
lean_object* v___x_4367_; lean_object* v_toApplicative_4368_; lean_object* v___x_4370_; uint8_t v_isShared_4371_; uint8_t v_isSharedCheck_4399_; 
v___x_4367_ = l_StateRefT_x27_instMonad___redArg(v___x_4366_);
v_toApplicative_4368_ = lean_ctor_get(v___x_4367_, 0);
v_isSharedCheck_4399_ = !lean_is_exclusive(v___x_4367_);
if (v_isSharedCheck_4399_ == 0)
{
lean_object* v_unused_4400_; 
v_unused_4400_ = lean_ctor_get(v___x_4367_, 1);
lean_dec(v_unused_4400_);
v___x_4370_ = v___x_4367_;
v_isShared_4371_ = v_isSharedCheck_4399_;
goto v_resetjp_4369_;
}
else
{
lean_inc(v_toApplicative_4368_);
lean_dec(v___x_4367_);
v___x_4370_ = lean_box(0);
v_isShared_4371_ = v_isSharedCheck_4399_;
goto v_resetjp_4369_;
}
v_resetjp_4369_:
{
lean_object* v_toFunctor_4372_; lean_object* v_toSeq_4373_; lean_object* v_toSeqLeft_4374_; lean_object* v_toSeqRight_4375_; lean_object* v___x_4377_; uint8_t v_isShared_4378_; uint8_t v_isSharedCheck_4397_; 
v_toFunctor_4372_ = lean_ctor_get(v_toApplicative_4368_, 0);
v_toSeq_4373_ = lean_ctor_get(v_toApplicative_4368_, 2);
v_toSeqLeft_4374_ = lean_ctor_get(v_toApplicative_4368_, 3);
v_toSeqRight_4375_ = lean_ctor_get(v_toApplicative_4368_, 4);
v_isSharedCheck_4397_ = !lean_is_exclusive(v_toApplicative_4368_);
if (v_isSharedCheck_4397_ == 0)
{
lean_object* v_unused_4398_; 
v_unused_4398_ = lean_ctor_get(v_toApplicative_4368_, 1);
lean_dec(v_unused_4398_);
v___x_4377_ = v_toApplicative_4368_;
v_isShared_4378_ = v_isSharedCheck_4397_;
goto v_resetjp_4376_;
}
else
{
lean_inc(v_toSeqRight_4375_);
lean_inc(v_toSeqLeft_4374_);
lean_inc(v_toSeq_4373_);
lean_inc(v_toFunctor_4372_);
lean_dec(v_toApplicative_4368_);
v___x_4377_ = lean_box(0);
v_isShared_4378_ = v_isSharedCheck_4397_;
goto v_resetjp_4376_;
}
v_resetjp_4376_:
{
lean_object* v___f_4379_; lean_object* v___f_4380_; lean_object* v___f_4381_; lean_object* v___f_4382_; lean_object* v___x_4383_; lean_object* v___f_4384_; lean_object* v___f_4385_; lean_object* v___f_4386_; lean_object* v___x_4388_; 
v___f_4379_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__3));
v___f_4380_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__4));
lean_inc_ref(v_toFunctor_4372_);
v___f_4381_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4381_, 0, v_toFunctor_4372_);
v___f_4382_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4382_, 0, v_toFunctor_4372_);
v___x_4383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4383_, 0, v___f_4381_);
lean_ctor_set(v___x_4383_, 1, v___f_4382_);
v___f_4384_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4384_, 0, v_toSeqRight_4375_);
v___f_4385_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4385_, 0, v_toSeqLeft_4374_);
v___f_4386_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4386_, 0, v_toSeq_4373_);
if (v_isShared_4378_ == 0)
{
lean_ctor_set(v___x_4377_, 4, v___f_4384_);
lean_ctor_set(v___x_4377_, 3, v___f_4385_);
lean_ctor_set(v___x_4377_, 2, v___f_4386_);
lean_ctor_set(v___x_4377_, 1, v___f_4379_);
lean_ctor_set(v___x_4377_, 0, v___x_4383_);
v___x_4388_ = v___x_4377_;
goto v_reusejp_4387_;
}
else
{
lean_object* v_reuseFailAlloc_4396_; 
v_reuseFailAlloc_4396_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4396_, 0, v___x_4383_);
lean_ctor_set(v_reuseFailAlloc_4396_, 1, v___f_4379_);
lean_ctor_set(v_reuseFailAlloc_4396_, 2, v___f_4386_);
lean_ctor_set(v_reuseFailAlloc_4396_, 3, v___f_4385_);
lean_ctor_set(v_reuseFailAlloc_4396_, 4, v___f_4384_);
v___x_4388_ = v_reuseFailAlloc_4396_;
goto v_reusejp_4387_;
}
v_reusejp_4387_:
{
lean_object* v___x_4390_; 
if (v_isShared_4371_ == 0)
{
lean_ctor_set(v___x_4370_, 1, v___f_4380_);
lean_ctor_set(v___x_4370_, 0, v___x_4388_);
v___x_4390_ = v___x_4370_;
goto v_reusejp_4389_;
}
else
{
lean_object* v_reuseFailAlloc_4395_; 
v_reuseFailAlloc_4395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4395_, 0, v___x_4388_);
lean_ctor_set(v_reuseFailAlloc_4395_, 1, v___f_4380_);
v___x_4390_ = v_reuseFailAlloc_4395_;
goto v_reusejp_4389_;
}
v_reusejp_4389_:
{
lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_19137__overap_4393_; lean_object* v___x_4394_; 
v___x_4391_ = lean_box(0);
v___x_4392_ = l_instInhabitedOfMonad___redArg(v___x_4390_, v___x_4391_);
v___x_19137__overap_4393_ = lean_panic_fn_borrowed(v___x_4392_, v_msg_4336_);
lean_dec(v___x_4392_);
lean_inc(v___y_4340_);
lean_inc_ref(v___y_4339_);
lean_inc(v___y_4338_);
lean_inc_ref(v___y_4337_);
v___x_4394_ = lean_apply_5(v___x_19137__overap_4393_, v___y_4337_, v___y_4338_, v___y_4339_, v___y_4340_, lean_box(0));
return v___x_4394_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___boxed(lean_object* v_msg_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_){
_start:
{
lean_object* v_res_4413_; 
v_res_4413_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(v_msg_4407_, v___y_4408_, v___y_4409_, v___y_4410_, v___y_4411_);
lean_dec(v___y_4411_);
lean_dec_ref(v___y_4410_);
lean_dec(v___y_4409_);
lean_dec_ref(v___y_4408_);
return v_res_4413_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1(void){
_start:
{
lean_object* v___x_4415_; lean_object* v___x_4416_; 
v___x_4415_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__0));
v___x_4416_ = l_Lean_stringToMessageData(v___x_4415_);
return v___x_4416_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4(void){
_start:
{
lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; 
v___x_4419_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__2));
v___x_4420_ = lean_unsigned_to_nat(11u);
v___x_4421_ = lean_unsigned_to_nat(122u);
v___x_4422_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__3));
v___x_4423_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__2));
v___x_4424_ = l_mkPanicMessageWithDecl(v___x_4423_, v___x_4422_, v___x_4421_, v___x_4420_, v___x_4419_);
return v___x_4424_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(lean_object* v_constName_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_){
_start:
{
lean_object* v___x_4439_; lean_object* v_env_4440_; uint8_t v___x_4441_; lean_object* v___x_4442_; 
v___x_4439_ = lean_st_ref_get(v___y_4429_);
v_env_4440_ = lean_ctor_get(v___x_4439_, 0);
lean_inc_ref(v_env_4440_);
lean_dec(v___x_4439_);
v___x_4441_ = 0;
lean_inc(v_constName_4425_);
v___x_4442_ = l_Lean_Environment_findAsync_x3f(v_env_4440_, v_constName_4425_, v___x_4441_);
if (lean_obj_tag(v___x_4442_) == 1)
{
lean_object* v_val_4443_; uint8_t v_kind_4444_; 
v_val_4443_ = lean_ctor_get(v___x_4442_, 0);
lean_inc(v_val_4443_);
lean_dec_ref(v___x_4442_);
v_kind_4444_ = lean_ctor_get_uint8(v_val_4443_, sizeof(void*)*3);
if (v_kind_4444_ == 6)
{
lean_object* v___x_4445_; 
v___x_4445_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_4443_);
if (lean_obj_tag(v___x_4445_) == 6)
{
lean_object* v_val_4446_; lean_object* v___x_4448_; uint8_t v_isShared_4449_; uint8_t v_isSharedCheck_4453_; 
lean_dec(v_constName_4425_);
v_val_4446_ = lean_ctor_get(v___x_4445_, 0);
v_isSharedCheck_4453_ = !lean_is_exclusive(v___x_4445_);
if (v_isSharedCheck_4453_ == 0)
{
v___x_4448_ = v___x_4445_;
v_isShared_4449_ = v_isSharedCheck_4453_;
goto v_resetjp_4447_;
}
else
{
lean_inc(v_val_4446_);
lean_dec(v___x_4445_);
v___x_4448_ = lean_box(0);
v_isShared_4449_ = v_isSharedCheck_4453_;
goto v_resetjp_4447_;
}
v_resetjp_4447_:
{
lean_object* v___x_4451_; 
if (v_isShared_4449_ == 0)
{
lean_ctor_set_tag(v___x_4448_, 0);
v___x_4451_ = v___x_4448_;
goto v_reusejp_4450_;
}
else
{
lean_object* v_reuseFailAlloc_4452_; 
v_reuseFailAlloc_4452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4452_, 0, v_val_4446_);
v___x_4451_ = v_reuseFailAlloc_4452_;
goto v_reusejp_4450_;
}
v_reusejp_4450_:
{
return v___x_4451_;
}
}
}
else
{
lean_object* v___x_4454_; lean_object* v___x_4455_; 
lean_dec_ref(v___x_4445_);
v___x_4454_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4);
v___x_4455_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(v___x_4454_, v___y_4426_, v___y_4427_, v___y_4428_, v___y_4429_);
if (lean_obj_tag(v___x_4455_) == 0)
{
lean_object* v_a_4456_; lean_object* v___x_4458_; uint8_t v_isShared_4459_; uint8_t v_isSharedCheck_4464_; 
v_a_4456_ = lean_ctor_get(v___x_4455_, 0);
v_isSharedCheck_4464_ = !lean_is_exclusive(v___x_4455_);
if (v_isSharedCheck_4464_ == 0)
{
v___x_4458_ = v___x_4455_;
v_isShared_4459_ = v_isSharedCheck_4464_;
goto v_resetjp_4457_;
}
else
{
lean_inc(v_a_4456_);
lean_dec(v___x_4455_);
v___x_4458_ = lean_box(0);
v_isShared_4459_ = v_isSharedCheck_4464_;
goto v_resetjp_4457_;
}
v_resetjp_4457_:
{
if (lean_obj_tag(v_a_4456_) == 0)
{
lean_del_object(v___x_4458_);
goto v___jp_4431_;
}
else
{
lean_object* v_val_4460_; lean_object* v___x_4462_; 
lean_dec(v_constName_4425_);
v_val_4460_ = lean_ctor_get(v_a_4456_, 0);
lean_inc(v_val_4460_);
lean_dec_ref(v_a_4456_);
if (v_isShared_4459_ == 0)
{
lean_ctor_set(v___x_4458_, 0, v_val_4460_);
v___x_4462_ = v___x_4458_;
goto v_reusejp_4461_;
}
else
{
lean_object* v_reuseFailAlloc_4463_; 
v_reuseFailAlloc_4463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4463_, 0, v_val_4460_);
v___x_4462_ = v_reuseFailAlloc_4463_;
goto v_reusejp_4461_;
}
v_reusejp_4461_:
{
return v___x_4462_;
}
}
}
}
else
{
lean_object* v_a_4465_; lean_object* v___x_4467_; uint8_t v_isShared_4468_; uint8_t v_isSharedCheck_4472_; 
lean_dec(v_constName_4425_);
v_a_4465_ = lean_ctor_get(v___x_4455_, 0);
v_isSharedCheck_4472_ = !lean_is_exclusive(v___x_4455_);
if (v_isSharedCheck_4472_ == 0)
{
v___x_4467_ = v___x_4455_;
v_isShared_4468_ = v_isSharedCheck_4472_;
goto v_resetjp_4466_;
}
else
{
lean_inc(v_a_4465_);
lean_dec(v___x_4455_);
v___x_4467_ = lean_box(0);
v_isShared_4468_ = v_isSharedCheck_4472_;
goto v_resetjp_4466_;
}
v_resetjp_4466_:
{
lean_object* v___x_4470_; 
if (v_isShared_4468_ == 0)
{
v___x_4470_ = v___x_4467_;
goto v_reusejp_4469_;
}
else
{
lean_object* v_reuseFailAlloc_4471_; 
v_reuseFailAlloc_4471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4471_, 0, v_a_4465_);
v___x_4470_ = v_reuseFailAlloc_4471_;
goto v_reusejp_4469_;
}
v_reusejp_4469_:
{
return v___x_4470_;
}
}
}
}
}
else
{
lean_dec(v_val_4443_);
goto v___jp_4431_;
}
}
else
{
lean_dec(v___x_4442_);
goto v___jp_4431_;
}
v___jp_4431_:
{
lean_object* v___x_4432_; uint8_t v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; 
v___x_4432_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_4433_ = 0;
v___x_4434_ = l_Lean_MessageData_ofConstName(v_constName_4425_, v___x_4433_);
v___x_4435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4435_, 0, v___x_4432_);
lean_ctor_set(v___x_4435_, 1, v___x_4434_);
v___x_4436_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1);
v___x_4437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4437_, 0, v___x_4435_);
lean_ctor_set(v___x_4437_, 1, v___x_4436_);
v___x_4438_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_4437_, v___y_4426_, v___y_4427_, v___y_4428_, v___y_4429_);
return v___x_4438_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___boxed(lean_object* v_constName_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_){
_start:
{
lean_object* v_res_4479_; 
v_res_4479_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(v_constName_4473_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_);
lean_dec(v___y_4477_);
lean_dec_ref(v___y_4476_);
lean_dec(v___y_4475_);
lean_dec_ref(v___y_4474_);
return v_res_4479_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0(lean_object* v_head_4480_, lean_object* v___x_4481_, lean_object* v___x_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_){
_start:
{
lean_object* v___x_4488_; 
v___x_4488_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(v_head_4480_, v___y_4483_, v___y_4484_, v___y_4485_, v___y_4486_);
if (lean_obj_tag(v___x_4488_) == 0)
{
lean_object* v_a_4489_; lean_object* v___x_4491_; uint8_t v_isShared_4492_; uint8_t v_isSharedCheck_4500_; 
v_a_4489_ = lean_ctor_get(v___x_4488_, 0);
v_isSharedCheck_4500_ = !lean_is_exclusive(v___x_4488_);
if (v_isSharedCheck_4500_ == 0)
{
v___x_4491_ = v___x_4488_;
v_isShared_4492_ = v_isSharedCheck_4500_;
goto v_resetjp_4490_;
}
else
{
lean_inc(v_a_4489_);
lean_dec(v___x_4488_);
v___x_4491_ = lean_box(0);
v_isShared_4492_ = v_isSharedCheck_4500_;
goto v_resetjp_4490_;
}
v_resetjp_4490_:
{
lean_object* v_numFields_4493_; uint8_t v___x_4494_; 
v_numFields_4493_ = lean_ctor_get(v_a_4489_, 4);
v___x_4494_ = lean_nat_dec_lt(v___x_4481_, v_numFields_4493_);
if (v___x_4494_ == 0)
{
lean_object* v___x_4496_; 
lean_dec(v_a_4489_);
if (v_isShared_4492_ == 0)
{
lean_ctor_set(v___x_4491_, 0, v___x_4482_);
v___x_4496_ = v___x_4491_;
goto v_reusejp_4495_;
}
else
{
lean_object* v_reuseFailAlloc_4497_; 
v_reuseFailAlloc_4497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4497_, 0, v___x_4482_);
v___x_4496_ = v_reuseFailAlloc_4497_;
goto v_reusejp_4495_;
}
v_reusejp_4495_:
{
return v___x_4496_;
}
}
else
{
lean_object* v___x_4498_; 
lean_del_object(v___x_4491_);
lean_inc(v_a_4489_);
v___x_4498_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(v_a_4489_, v___y_4483_, v___y_4484_, v___y_4485_, v___y_4486_);
if (lean_obj_tag(v___x_4498_) == 0)
{
lean_object* v___x_4499_; 
lean_dec_ref(v___x_4498_);
v___x_4499_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(v_a_4489_, v___y_4483_, v___y_4484_, v___y_4485_, v___y_4486_);
return v___x_4499_;
}
else
{
lean_dec(v_a_4489_);
return v___x_4498_;
}
}
}
}
else
{
lean_object* v_a_4501_; lean_object* v___x_4503_; uint8_t v_isShared_4504_; uint8_t v_isSharedCheck_4508_; 
v_a_4501_ = lean_ctor_get(v___x_4488_, 0);
v_isSharedCheck_4508_ = !lean_is_exclusive(v___x_4488_);
if (v_isSharedCheck_4508_ == 0)
{
v___x_4503_ = v___x_4488_;
v_isShared_4504_ = v_isSharedCheck_4508_;
goto v_resetjp_4502_;
}
else
{
lean_inc(v_a_4501_);
lean_dec(v___x_4488_);
v___x_4503_ = lean_box(0);
v_isShared_4504_ = v_isSharedCheck_4508_;
goto v_resetjp_4502_;
}
v_resetjp_4502_:
{
lean_object* v___x_4506_; 
if (v_isShared_4504_ == 0)
{
v___x_4506_ = v___x_4503_;
goto v_reusejp_4505_;
}
else
{
lean_object* v_reuseFailAlloc_4507_; 
v_reuseFailAlloc_4507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4507_, 0, v_a_4501_);
v___x_4506_ = v_reuseFailAlloc_4507_;
goto v_reusejp_4505_;
}
v_reusejp_4505_:
{
return v___x_4506_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0___boxed(lean_object* v_head_4509_, lean_object* v___x_4510_, lean_object* v___x_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_){
_start:
{
lean_object* v_res_4517_; 
v_res_4517_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0(v_head_4509_, v___x_4510_, v___x_4511_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_);
lean_dec(v___y_4515_);
lean_dec_ref(v___y_4514_);
lean_dec(v___y_4513_);
lean_dec_ref(v___y_4512_);
lean_dec(v___x_4510_);
return v_res_4517_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(uint8_t v___y_4518_, uint8_t v___x_4519_, lean_object* v_as_x27_4520_, lean_object* v_b_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_){
_start:
{
if (lean_obj_tag(v_as_x27_4520_) == 0)
{
lean_object* v___x_4527_; 
v___x_4527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4527_, 0, v_b_4521_);
return v___x_4527_;
}
else
{
lean_object* v_head_4528_; lean_object* v_tail_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; lean_object* v___f_4532_; uint8_t v___y_4534_; uint8_t v___x_4537_; 
v_head_4528_ = lean_ctor_get(v_as_x27_4520_, 0);
v_tail_4529_ = lean_ctor_get(v_as_x27_4520_, 1);
v___x_4530_ = lean_unsigned_to_nat(0u);
v___x_4531_ = lean_box(0);
lean_inc(v_head_4528_);
v___f_4532_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4532_, 0, v_head_4528_);
lean_closure_set(v___f_4532_, 1, v___x_4530_);
lean_closure_set(v___f_4532_, 2, v___x_4531_);
v___x_4537_ = l_Lean_isPrivateName(v_head_4528_);
if (v___x_4537_ == 0)
{
v___y_4534_ = v___y_4518_;
goto v___jp_4533_;
}
else
{
v___y_4534_ = v___x_4519_;
goto v___jp_4533_;
}
v___jp_4533_:
{
lean_object* v___x_4535_; 
v___x_4535_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(v___f_4532_, v___y_4534_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_);
if (lean_obj_tag(v___x_4535_) == 0)
{
lean_dec_ref(v___x_4535_);
v_as_x27_4520_ = v_tail_4529_;
v_b_4521_ = v___x_4531_;
goto _start;
}
else
{
return v___x_4535_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___boxed(lean_object* v___y_4538_, lean_object* v___x_4539_, lean_object* v_as_x27_4540_, lean_object* v_b_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_){
_start:
{
uint8_t v___y_20247__boxed_4547_; uint8_t v___x_20248__boxed_4548_; lean_object* v_res_4549_; 
v___y_20247__boxed_4547_ = lean_unbox(v___y_4538_);
v___x_20248__boxed_4548_ = lean_unbox(v___x_4539_);
v_res_4549_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___y_20247__boxed_4547_, v___x_20248__boxed_4548_, v_as_x27_4540_, v_b_4541_, v___y_4542_, v___y_4543_, v___y_4544_, v___y_4545_);
lean_dec(v___y_4545_);
lean_dec_ref(v___y_4544_);
lean_dec(v___y_4543_);
lean_dec_ref(v___y_4542_);
lean_dec(v_as_x27_4540_);
return v_res_4549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__1(uint8_t v___y_4550_, uint8_t v_hasTrace_4551_, lean_object* v_ctors_4552_, lean_object* v___x_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_){
_start:
{
lean_object* v___x_4559_; 
v___x_4559_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___y_4550_, v_hasTrace_4551_, v_ctors_4552_, v___x_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_);
if (lean_obj_tag(v___x_4559_) == 0)
{
lean_object* v___x_4561_; uint8_t v_isShared_4562_; uint8_t v_isSharedCheck_4566_; 
v_isSharedCheck_4566_ = !lean_is_exclusive(v___x_4559_);
if (v_isSharedCheck_4566_ == 0)
{
lean_object* v_unused_4567_; 
v_unused_4567_ = lean_ctor_get(v___x_4559_, 0);
lean_dec(v_unused_4567_);
v___x_4561_ = v___x_4559_;
v_isShared_4562_ = v_isSharedCheck_4566_;
goto v_resetjp_4560_;
}
else
{
lean_dec(v___x_4559_);
v___x_4561_ = lean_box(0);
v_isShared_4562_ = v_isSharedCheck_4566_;
goto v_resetjp_4560_;
}
v_resetjp_4560_:
{
lean_object* v___x_4564_; 
if (v_isShared_4562_ == 0)
{
lean_ctor_set(v___x_4561_, 0, v___x_4553_);
v___x_4564_ = v___x_4561_;
goto v_reusejp_4563_;
}
else
{
lean_object* v_reuseFailAlloc_4565_; 
v_reuseFailAlloc_4565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4565_, 0, v___x_4553_);
v___x_4564_ = v_reuseFailAlloc_4565_;
goto v_reusejp_4563_;
}
v_reusejp_4563_:
{
return v___x_4564_;
}
}
}
else
{
return v___x_4559_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed(lean_object* v___y_4568_, lean_object* v_hasTrace_4569_, lean_object* v_ctors_4570_, lean_object* v___x_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_){
_start:
{
uint8_t v___y_20292__boxed_4577_; uint8_t v_hasTrace_boxed_4578_; lean_object* v_res_4579_; 
v___y_20292__boxed_4577_ = lean_unbox(v___y_4568_);
v_hasTrace_boxed_4578_ = lean_unbox(v_hasTrace_4569_);
v_res_4579_ = l_Lean_Meta_mkInjectiveTheorems___lam__1(v___y_20292__boxed_4577_, v_hasTrace_boxed_4578_, v_ctors_4570_, v___x_4571_, v___y_4572_, v___y_4573_, v___y_4574_, v___y_4575_);
lean_dec(v___y_4575_);
lean_dec_ref(v___y_4574_);
lean_dec(v___y_4573_);
lean_dec_ref(v___y_4572_);
lean_dec(v_ctors_4570_);
return v_res_4579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__2(uint8_t v_hasTrace_4580_, uint8_t v___x_4581_, lean_object* v_ctors_4582_, lean_object* v___x_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_){
_start:
{
lean_object* v___x_4589_; 
v___x_4589_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v_hasTrace_4580_, v___x_4581_, v_ctors_4582_, v___x_4583_, v___y_4584_, v___y_4585_, v___y_4586_, v___y_4587_);
if (lean_obj_tag(v___x_4589_) == 0)
{
lean_object* v___x_4591_; uint8_t v_isShared_4592_; uint8_t v_isSharedCheck_4596_; 
v_isSharedCheck_4596_ = !lean_is_exclusive(v___x_4589_);
if (v_isSharedCheck_4596_ == 0)
{
lean_object* v_unused_4597_; 
v_unused_4597_ = lean_ctor_get(v___x_4589_, 0);
lean_dec(v_unused_4597_);
v___x_4591_ = v___x_4589_;
v_isShared_4592_ = v_isSharedCheck_4596_;
goto v_resetjp_4590_;
}
else
{
lean_dec(v___x_4589_);
v___x_4591_ = lean_box(0);
v_isShared_4592_ = v_isSharedCheck_4596_;
goto v_resetjp_4590_;
}
v_resetjp_4590_:
{
lean_object* v___x_4594_; 
if (v_isShared_4592_ == 0)
{
lean_ctor_set(v___x_4591_, 0, v___x_4583_);
v___x_4594_ = v___x_4591_;
goto v_reusejp_4593_;
}
else
{
lean_object* v_reuseFailAlloc_4595_; 
v_reuseFailAlloc_4595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4595_, 0, v___x_4583_);
v___x_4594_ = v_reuseFailAlloc_4595_;
goto v_reusejp_4593_;
}
v_reusejp_4593_:
{
return v___x_4594_;
}
}
}
else
{
return v___x_4589_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__2___boxed(lean_object* v_hasTrace_4598_, lean_object* v___x_4599_, lean_object* v_ctors_4600_, lean_object* v___x_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_){
_start:
{
uint8_t v_hasTrace_boxed_4607_; uint8_t v___x_20333__boxed_4608_; lean_object* v_res_4609_; 
v_hasTrace_boxed_4607_ = lean_unbox(v_hasTrace_4598_);
v___x_20333__boxed_4608_ = lean_unbox(v___x_4599_);
v_res_4609_ = l_Lean_Meta_mkInjectiveTheorems___lam__2(v_hasTrace_boxed_4607_, v___x_20333__boxed_4608_, v_ctors_4600_, v___x_4601_, v___y_4602_, v___y_4603_, v___y_4604_, v___y_4605_);
lean_dec(v___y_4605_);
lean_dec_ref(v___y_4604_);
lean_dec(v___y_4603_);
lean_dec_ref(v___y_4602_);
lean_dec(v_ctors_4600_);
return v_res_4609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__3(uint8_t v___x_4610_, uint8_t v_isUnsafe_4611_, lean_object* v_ctors_4612_, lean_object* v___x_4613_, lean_object* v___y_4614_, lean_object* v___y_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_){
_start:
{
lean_object* v___x_4619_; 
v___x_4619_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___x_4610_, v_isUnsafe_4611_, v_ctors_4612_, v___x_4613_, v___y_4614_, v___y_4615_, v___y_4616_, v___y_4617_);
if (lean_obj_tag(v___x_4619_) == 0)
{
lean_object* v___x_4621_; uint8_t v_isShared_4622_; uint8_t v_isSharedCheck_4626_; 
v_isSharedCheck_4626_ = !lean_is_exclusive(v___x_4619_);
if (v_isSharedCheck_4626_ == 0)
{
lean_object* v_unused_4627_; 
v_unused_4627_ = lean_ctor_get(v___x_4619_, 0);
lean_dec(v_unused_4627_);
v___x_4621_ = v___x_4619_;
v_isShared_4622_ = v_isSharedCheck_4626_;
goto v_resetjp_4620_;
}
else
{
lean_dec(v___x_4619_);
v___x_4621_ = lean_box(0);
v_isShared_4622_ = v_isSharedCheck_4626_;
goto v_resetjp_4620_;
}
v_resetjp_4620_:
{
lean_object* v___x_4624_; 
if (v_isShared_4622_ == 0)
{
lean_ctor_set(v___x_4621_, 0, v___x_4613_);
v___x_4624_ = v___x_4621_;
goto v_reusejp_4623_;
}
else
{
lean_object* v_reuseFailAlloc_4625_; 
v_reuseFailAlloc_4625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4625_, 0, v___x_4613_);
v___x_4624_ = v_reuseFailAlloc_4625_;
goto v_reusejp_4623_;
}
v_reusejp_4623_:
{
return v___x_4624_;
}
}
}
else
{
return v___x_4619_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__3___boxed(lean_object* v___x_4628_, lean_object* v_isUnsafe_4629_, lean_object* v_ctors_4630_, lean_object* v___x_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_, lean_object* v___y_4634_, lean_object* v___y_4635_, lean_object* v___y_4636_){
_start:
{
uint8_t v___x_20374__boxed_4637_; uint8_t v_isUnsafe_boxed_4638_; lean_object* v_res_4639_; 
v___x_20374__boxed_4637_ = lean_unbox(v___x_4628_);
v_isUnsafe_boxed_4638_ = lean_unbox(v_isUnsafe_4629_);
v_res_4639_ = l_Lean_Meta_mkInjectiveTheorems___lam__3(v___x_20374__boxed_4637_, v_isUnsafe_boxed_4638_, v_ctors_4630_, v___x_4631_, v___y_4632_, v___y_4633_, v___y_4634_, v___y_4635_);
lean_dec(v___y_4635_);
lean_dec_ref(v___y_4634_);
lean_dec(v___y_4633_);
lean_dec_ref(v___y_4632_);
lean_dec(v_ctors_4630_);
return v_res_4639_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4641_; lean_object* v___x_4642_; 
v___x_4641_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__0));
v___x_4642_ = l_Lean_stringToMessageData(v___x_4641_);
return v___x_4642_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(lean_object* v_constName_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_){
_start:
{
lean_object* v___x_4649_; lean_object* v_env_4650_; lean_object* v___x_4651_; 
v___x_4649_ = lean_st_ref_get(v___y_4647_);
v_env_4650_ = lean_ctor_get(v___x_4649_, 0);
lean_inc_ref(v_env_4650_);
lean_dec(v___x_4649_);
lean_inc(v_constName_4643_);
v___x_4651_ = l_Lean_isInductiveCore_x3f(v_env_4650_, v_constName_4643_);
if (lean_obj_tag(v___x_4651_) == 0)
{
lean_object* v___x_4652_; uint8_t v___x_4653_; lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; 
v___x_4652_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_4653_ = 0;
v___x_4654_ = l_Lean_MessageData_ofConstName(v_constName_4643_, v___x_4653_);
v___x_4655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4655_, 0, v___x_4652_);
lean_ctor_set(v___x_4655_, 1, v___x_4654_);
v___x_4656_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1);
v___x_4657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4657_, 0, v___x_4655_);
lean_ctor_set(v___x_4657_, 1, v___x_4656_);
v___x_4658_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_4657_, v___y_4644_, v___y_4645_, v___y_4646_, v___y_4647_);
return v___x_4658_;
}
else
{
lean_object* v_val_4659_; lean_object* v___x_4661_; uint8_t v_isShared_4662_; uint8_t v_isSharedCheck_4666_; 
lean_dec(v_constName_4643_);
v_val_4659_ = lean_ctor_get(v___x_4651_, 0);
v_isSharedCheck_4666_ = !lean_is_exclusive(v___x_4651_);
if (v_isSharedCheck_4666_ == 0)
{
v___x_4661_ = v___x_4651_;
v_isShared_4662_ = v_isSharedCheck_4666_;
goto v_resetjp_4660_;
}
else
{
lean_inc(v_val_4659_);
lean_dec(v___x_4651_);
v___x_4661_ = lean_box(0);
v_isShared_4662_ = v_isSharedCheck_4666_;
goto v_resetjp_4660_;
}
v_resetjp_4660_:
{
lean_object* v___x_4664_; 
if (v_isShared_4662_ == 0)
{
lean_ctor_set_tag(v___x_4661_, 0);
v___x_4664_ = v___x_4661_;
goto v_reusejp_4663_;
}
else
{
lean_object* v_reuseFailAlloc_4665_; 
v_reuseFailAlloc_4665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4665_, 0, v_val_4659_);
v___x_4664_ = v_reuseFailAlloc_4665_;
goto v_reusejp_4663_;
}
v_reusejp_4663_:
{
return v___x_4664_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___boxed(lean_object* v_constName_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_, lean_object* v___y_4672_){
_start:
{
lean_object* v_res_4673_; 
v_res_4673_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_constName_4667_, v___y_4668_, v___y_4669_, v___y_4670_, v___y_4671_);
lean_dec(v___y_4671_);
lean_dec_ref(v___y_4670_);
lean_dec(v___y_4669_);
lean_dec_ref(v___y_4668_);
return v_res_4673_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__0(void){
_start:
{
lean_object* v___x_4674_; 
v___x_4674_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4674_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__1(void){
_start:
{
lean_object* v___x_4675_; lean_object* v___x_4676_; 
v___x_4675_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__0, &l_Lean_Meta_mkInjectiveTheorems___closed__0_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__0);
v___x_4676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4676_, 0, v___x_4675_);
return v___x_4676_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__2(void){
_start:
{
lean_object* v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; 
v___x_4677_ = lean_unsigned_to_nat(32u);
v___x_4678_ = lean_mk_empty_array_with_capacity(v___x_4677_);
v___x_4679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4679_, 0, v___x_4678_);
return v___x_4679_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__3(void){
_start:
{
size_t v___x_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; 
v___x_4680_ = ((size_t)5ULL);
v___x_4681_ = lean_unsigned_to_nat(0u);
v___x_4682_ = lean_unsigned_to_nat(32u);
v___x_4683_ = lean_mk_empty_array_with_capacity(v___x_4682_);
v___x_4684_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__2, &l_Lean_Meta_mkInjectiveTheorems___closed__2_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__2);
v___x_4685_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4685_, 0, v___x_4684_);
lean_ctor_set(v___x_4685_, 1, v___x_4683_);
lean_ctor_set(v___x_4685_, 2, v___x_4681_);
lean_ctor_set(v___x_4685_, 3, v___x_4681_);
lean_ctor_set_usize(v___x_4685_, 4, v___x_4680_);
return v___x_4685_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__4(void){
_start:
{
lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; 
v___x_4686_ = lean_box(1);
v___x_4687_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_4688_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_4689_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4689_, 0, v___x_4688_);
lean_ctor_set(v___x_4689_, 1, v___x_4687_);
lean_ctor_set(v___x_4689_, 2, v___x_4686_);
return v___x_4689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems(lean_object* v_declName_4692_, lean_object* v_a_4693_, lean_object* v_a_4694_, lean_object* v_a_4695_, lean_object* v_a_4696_){
_start:
{
lean_object* v___x_4698_; lean_object* v___x_4699_; 
v___x_4698_ = lean_st_ref_get(v_a_4696_);
lean_inc(v_declName_4692_);
v___x_4699_ = l_Lean_Meta_isInductivePredicate(v_declName_4692_, v_a_4693_, v_a_4694_, v_a_4695_, v_a_4696_);
if (lean_obj_tag(v___x_4699_) == 0)
{
lean_object* v_a_4700_; lean_object* v___x_4702_; uint8_t v_isShared_4703_; uint8_t v_isSharedCheck_4896_; 
v_a_4700_ = lean_ctor_get(v___x_4699_, 0);
v_isSharedCheck_4896_ = !lean_is_exclusive(v___x_4699_);
if (v_isSharedCheck_4896_ == 0)
{
v___x_4702_ = v___x_4699_;
v_isShared_4703_ = v_isSharedCheck_4896_;
goto v_resetjp_4701_;
}
else
{
lean_inc(v_a_4700_);
lean_dec(v___x_4699_);
v___x_4702_ = lean_box(0);
v_isShared_4703_ = v_isSharedCheck_4896_;
goto v_resetjp_4701_;
}
v_resetjp_4701_:
{
lean_object* v_env_4709_; lean_object* v___f_4710_; lean_object* v___x_4711_; uint8_t v___x_4712_; uint8_t v___y_4714_; lean_object* v___y_4715_; lean_object* v___y_4716_; lean_object* v___y_4717_; lean_object* v___y_4718_; lean_object* v___y_4719_; lean_object* v_a_4720_; lean_object* v___y_4730_; uint8_t v___y_4731_; lean_object* v___y_4732_; lean_object* v___y_4733_; lean_object* v___y_4734_; lean_object* v___y_4735_; lean_object* v_a_4736_; lean_object* v___y_4739_; uint8_t v___y_4740_; lean_object* v___y_4741_; lean_object* v___y_4742_; lean_object* v___y_4743_; lean_object* v___y_4744_; lean_object* v_a_4745_; uint8_t v___y_4748_; lean_object* v___y_4749_; lean_object* v___y_4750_; lean_object* v___y_4751_; lean_object* v___y_4752_; lean_object* v___y_4753_; lean_object* v_a_4754_; lean_object* v___y_4767_; uint8_t v___y_4768_; lean_object* v___y_4769_; lean_object* v___y_4770_; lean_object* v___y_4771_; lean_object* v___y_4772_; lean_object* v_a_4773_; lean_object* v___y_4776_; uint8_t v___y_4777_; lean_object* v___y_4778_; lean_object* v___y_4779_; lean_object* v___y_4780_; lean_object* v___y_4781_; lean_object* v_a_4782_; uint8_t v___y_4785_; lean_object* v___y_4786_; uint8_t v___y_4787_; lean_object* v___y_4788_; lean_object* v___y_4789_; uint8_t v___y_4827_; uint8_t v___x_4892_; 
v_env_4709_ = lean_ctor_get(v___x_4698_, 0);
lean_inc_ref(v_env_4709_);
lean_dec(v___x_4698_);
lean_inc(v_declName_4692_);
v___f_4710_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4710_, 0, v_declName_4692_);
v___x_4711_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__2));
v___x_4712_ = 1;
v___x_4892_ = l_Lean_Environment_contains(v_env_4709_, v___x_4711_, v___x_4712_);
if (v___x_4892_ == 0)
{
v___y_4827_ = v___x_4892_;
goto v___jp_4826_;
}
else
{
lean_object* v_options_4893_; lean_object* v___x_4894_; uint8_t v___x_4895_; 
v_options_4893_ = lean_ctor_get(v_a_4695_, 2);
v___x_4894_ = l_Lean_Meta_genInjectivity;
v___x_4895_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_4893_, v___x_4894_);
v___y_4827_ = v___x_4895_;
goto v___jp_4826_;
}
v___jp_4704_:
{
lean_object* v___x_4705_; lean_object* v___x_4707_; 
v___x_4705_ = lean_box(0);
if (v_isShared_4703_ == 0)
{
lean_ctor_set(v___x_4702_, 0, v___x_4705_);
v___x_4707_ = v___x_4702_;
goto v_reusejp_4706_;
}
else
{
lean_object* v_reuseFailAlloc_4708_; 
v_reuseFailAlloc_4708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4708_, 0, v___x_4705_);
v___x_4707_ = v_reuseFailAlloc_4708_;
goto v_reusejp_4706_;
}
v_reusejp_4706_:
{
return v___x_4707_;
}
}
v___jp_4713_:
{
lean_object* v___x_4721_; double v___x_4722_; double v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; 
v___x_4721_ = lean_io_get_num_heartbeats();
v___x_4722_ = lean_float_of_nat(v___y_4718_);
v___x_4723_ = lean_float_of_nat(v___x_4721_);
v___x_4724_ = lean_box_float(v___x_4722_);
v___x_4725_ = lean_box_float(v___x_4723_);
v___x_4726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4726_, 0, v___x_4724_);
lean_ctor_set(v___x_4726_, 1, v___x_4725_);
v___x_4727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4727_, 0, v_a_4720_);
lean_ctor_set(v___x_4727_, 1, v___x_4726_);
lean_inc_ref(v___y_4715_);
lean_inc(v___y_4717_);
v___x_4728_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v___y_4717_, v___x_4712_, v___y_4715_, v___y_4719_, v___y_4714_, v___y_4716_, v___f_4710_, v___x_4727_, v_a_4693_, v_a_4694_, v_a_4695_, v_a_4696_);
return v___x_4728_;
}
v___jp_4729_:
{
lean_object* v___x_4737_; 
v___x_4737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4737_, 0, v_a_4736_);
v___y_4714_ = v___y_4731_;
v___y_4715_ = v___y_4730_;
v___y_4716_ = v___y_4732_;
v___y_4717_ = v___y_4733_;
v___y_4718_ = v___y_4734_;
v___y_4719_ = v___y_4735_;
v_a_4720_ = v___x_4737_;
goto v___jp_4713_;
}
v___jp_4738_:
{
lean_object* v___x_4746_; 
v___x_4746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4746_, 0, v_a_4745_);
v___y_4714_ = v___y_4740_;
v___y_4715_ = v___y_4739_;
v___y_4716_ = v___y_4741_;
v___y_4717_ = v___y_4742_;
v___y_4718_ = v___y_4743_;
v___y_4719_ = v___y_4744_;
v_a_4720_ = v___x_4746_;
goto v___jp_4713_;
}
v___jp_4747_:
{
lean_object* v___x_4755_; double v___x_4756_; double v___x_4757_; double v___x_4758_; double v___x_4759_; double v___x_4760_; lean_object* v___x_4761_; lean_object* v___x_4762_; lean_object* v___x_4763_; lean_object* v___x_4764_; lean_object* v___x_4765_; 
v___x_4755_ = lean_io_mono_nanos_now();
v___x_4756_ = lean_float_of_nat(v___y_4752_);
v___x_4757_ = lean_float_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0);
v___x_4758_ = lean_float_div(v___x_4756_, v___x_4757_);
v___x_4759_ = lean_float_of_nat(v___x_4755_);
v___x_4760_ = lean_float_div(v___x_4759_, v___x_4757_);
v___x_4761_ = lean_box_float(v___x_4758_);
v___x_4762_ = lean_box_float(v___x_4760_);
v___x_4763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4763_, 0, v___x_4761_);
lean_ctor_set(v___x_4763_, 1, v___x_4762_);
v___x_4764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4764_, 0, v_a_4754_);
lean_ctor_set(v___x_4764_, 1, v___x_4763_);
lean_inc_ref(v___y_4749_);
lean_inc(v___y_4751_);
v___x_4765_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v___y_4751_, v___x_4712_, v___y_4749_, v___y_4753_, v___y_4748_, v___y_4750_, v___f_4710_, v___x_4764_, v_a_4693_, v_a_4694_, v_a_4695_, v_a_4696_);
return v___x_4765_;
}
v___jp_4766_:
{
lean_object* v___x_4774_; 
v___x_4774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4774_, 0, v_a_4773_);
v___y_4748_ = v___y_4768_;
v___y_4749_ = v___y_4767_;
v___y_4750_ = v___y_4769_;
v___y_4751_ = v___y_4770_;
v___y_4752_ = v___y_4771_;
v___y_4753_ = v___y_4772_;
v_a_4754_ = v___x_4774_;
goto v___jp_4747_;
}
v___jp_4775_:
{
lean_object* v___x_4783_; 
v___x_4783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4783_, 0, v_a_4782_);
v___y_4748_ = v___y_4777_;
v___y_4749_ = v___y_4776_;
v___y_4750_ = v___y_4778_;
v___y_4751_ = v___y_4779_;
v___y_4752_ = v___y_4780_;
v___y_4753_ = v___y_4781_;
v_a_4754_ = v___x_4783_;
goto v___jp_4747_;
}
v___jp_4784_:
{
lean_object* v___x_4790_; lean_object* v_a_4791_; lean_object* v___x_4792_; uint8_t v___x_4793_; 
v___x_4790_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v_a_4696_);
v_a_4791_ = lean_ctor_get(v___x_4790_, 0);
lean_inc(v_a_4791_);
lean_dec_ref(v___x_4790_);
v___x_4792_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4793_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v___y_4789_, v___x_4792_);
if (v___x_4793_ == 0)
{
lean_object* v___x_4794_; lean_object* v___x_4795_; 
v___x_4794_ = lean_io_mono_nanos_now();
v___x_4795_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4692_, v_a_4693_, v_a_4694_, v_a_4695_, v_a_4696_);
if (lean_obj_tag(v___x_4795_) == 0)
{
lean_object* v_a_4796_; uint8_t v_isUnsafe_4797_; 
v_a_4796_ = lean_ctor_get(v___x_4795_, 0);
lean_inc(v_a_4796_);
lean_dec_ref(v___x_4795_);
v_isUnsafe_4797_ = lean_ctor_get_uint8(v_a_4796_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4797_ == 0)
{
lean_object* v_ctors_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; lean_object* v___x_4802_; lean_object* v___x_4803_; lean_object* v___f_4804_; lean_object* v___x_4805_; 
v_ctors_4798_ = lean_ctor_get(v_a_4796_, 4);
lean_inc(v_ctors_4798_);
lean_dec(v_a_4796_);
v___x_4799_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4800_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4801_ = lean_box(0);
v___x_4802_ = lean_box(v___y_4785_);
v___x_4803_ = lean_box(v___x_4793_);
v___f_4804_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__2___boxed), 9, 4);
lean_closure_set(v___f_4804_, 0, v___x_4802_);
lean_closure_set(v___f_4804_, 1, v___x_4803_);
lean_closure_set(v___f_4804_, 2, v_ctors_4798_);
lean_closure_set(v___f_4804_, 3, v___x_4801_);
v___x_4805_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4799_, v___x_4800_, v___f_4804_, v_a_4693_, v_a_4694_, v_a_4695_, v_a_4696_);
if (lean_obj_tag(v___x_4805_) == 0)
{
lean_object* v_a_4806_; 
v_a_4806_ = lean_ctor_get(v___x_4805_, 0);
lean_inc(v_a_4806_);
lean_dec_ref(v___x_4805_);
v___y_4767_ = v___y_4786_;
v___y_4768_ = v___y_4787_;
v___y_4769_ = v_a_4791_;
v___y_4770_ = v___y_4788_;
v___y_4771_ = v___x_4794_;
v___y_4772_ = v___y_4789_;
v_a_4773_ = v_a_4806_;
goto v___jp_4766_;
}
else
{
lean_object* v_a_4807_; 
v_a_4807_ = lean_ctor_get(v___x_4805_, 0);
lean_inc(v_a_4807_);
lean_dec_ref(v___x_4805_);
v___y_4776_ = v___y_4786_;
v___y_4777_ = v___y_4787_;
v___y_4778_ = v_a_4791_;
v___y_4779_ = v___y_4788_;
v___y_4780_ = v___x_4794_;
v___y_4781_ = v___y_4789_;
v_a_4782_ = v_a_4807_;
goto v___jp_4775_;
}
}
else
{
lean_object* v___x_4808_; 
lean_dec(v_a_4796_);
v___x_4808_ = lean_box(0);
v___y_4767_ = v___y_4786_;
v___y_4768_ = v___y_4787_;
v___y_4769_ = v_a_4791_;
v___y_4770_ = v___y_4788_;
v___y_4771_ = v___x_4794_;
v___y_4772_ = v___y_4789_;
v_a_4773_ = v___x_4808_;
goto v___jp_4766_;
}
}
else
{
lean_object* v_a_4809_; 
v_a_4809_ = lean_ctor_get(v___x_4795_, 0);
lean_inc(v_a_4809_);
lean_dec_ref(v___x_4795_);
v___y_4776_ = v___y_4786_;
v___y_4777_ = v___y_4787_;
v___y_4778_ = v_a_4791_;
v___y_4779_ = v___y_4788_;
v___y_4780_ = v___x_4794_;
v___y_4781_ = v___y_4789_;
v_a_4782_ = v_a_4809_;
goto v___jp_4775_;
}
}
else
{
lean_object* v___x_4810_; lean_object* v___x_4811_; 
v___x_4810_ = lean_io_get_num_heartbeats();
v___x_4811_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4692_, v_a_4693_, v_a_4694_, v_a_4695_, v_a_4696_);
if (lean_obj_tag(v___x_4811_) == 0)
{
lean_object* v_a_4812_; uint8_t v_isUnsafe_4813_; 
v_a_4812_ = lean_ctor_get(v___x_4811_, 0);
lean_inc(v_a_4812_);
lean_dec_ref(v___x_4811_);
v_isUnsafe_4813_ = lean_ctor_get_uint8(v_a_4812_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4813_ == 0)
{
lean_object* v_ctors_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; lean_object* v___f_4820_; lean_object* v___x_4821_; 
v_ctors_4814_ = lean_ctor_get(v_a_4812_, 4);
lean_inc(v_ctors_4814_);
lean_dec(v_a_4812_);
v___x_4815_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4816_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4817_ = lean_box(0);
v___x_4818_ = lean_box(v___x_4793_);
v___x_4819_ = lean_box(v_isUnsafe_4813_);
v___f_4820_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__3___boxed), 9, 4);
lean_closure_set(v___f_4820_, 0, v___x_4818_);
lean_closure_set(v___f_4820_, 1, v___x_4819_);
lean_closure_set(v___f_4820_, 2, v_ctors_4814_);
lean_closure_set(v___f_4820_, 3, v___x_4817_);
v___x_4821_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4815_, v___x_4816_, v___f_4820_, v_a_4693_, v_a_4694_, v_a_4695_, v_a_4696_);
if (lean_obj_tag(v___x_4821_) == 0)
{
lean_object* v_a_4822_; 
v_a_4822_ = lean_ctor_get(v___x_4821_, 0);
lean_inc(v_a_4822_);
lean_dec_ref(v___x_4821_);
v___y_4730_ = v___y_4786_;
v___y_4731_ = v___y_4787_;
v___y_4732_ = v_a_4791_;
v___y_4733_ = v___y_4788_;
v___y_4734_ = v___x_4810_;
v___y_4735_ = v___y_4789_;
v_a_4736_ = v_a_4822_;
goto v___jp_4729_;
}
else
{
lean_object* v_a_4823_; 
v_a_4823_ = lean_ctor_get(v___x_4821_, 0);
lean_inc(v_a_4823_);
lean_dec_ref(v___x_4821_);
v___y_4739_ = v___y_4786_;
v___y_4740_ = v___y_4787_;
v___y_4741_ = v_a_4791_;
v___y_4742_ = v___y_4788_;
v___y_4743_ = v___x_4810_;
v___y_4744_ = v___y_4789_;
v_a_4745_ = v_a_4823_;
goto v___jp_4738_;
}
}
else
{
lean_object* v___x_4824_; 
lean_dec(v_a_4812_);
v___x_4824_ = lean_box(0);
v___y_4730_ = v___y_4786_;
v___y_4731_ = v___y_4787_;
v___y_4732_ = v_a_4791_;
v___y_4733_ = v___y_4788_;
v___y_4734_ = v___x_4810_;
v___y_4735_ = v___y_4789_;
v_a_4736_ = v___x_4824_;
goto v___jp_4729_;
}
}
else
{
lean_object* v_a_4825_; 
v_a_4825_ = lean_ctor_get(v___x_4811_, 0);
lean_inc(v_a_4825_);
lean_dec_ref(v___x_4811_);
v___y_4739_ = v___y_4786_;
v___y_4740_ = v___y_4787_;
v___y_4741_ = v_a_4791_;
v___y_4742_ = v___y_4788_;
v___y_4743_ = v___x_4810_;
v___y_4744_ = v___y_4789_;
v_a_4745_ = v_a_4825_;
goto v___jp_4738_;
}
}
}
v___jp_4826_:
{
if (v___y_4827_ == 0)
{
lean_dec_ref(v___f_4710_);
lean_dec(v_a_4700_);
lean_dec(v_declName_4692_);
goto v___jp_4704_;
}
else
{
uint8_t v___x_4828_; 
v___x_4828_ = lean_unbox(v_a_4700_);
lean_dec(v_a_4700_);
if (v___x_4828_ == 0)
{
lean_object* v_options_4829_; uint8_t v_hasTrace_4830_; 
lean_del_object(v___x_4702_);
v_options_4829_ = lean_ctor_get(v_a_4695_, 2);
v_hasTrace_4830_ = lean_ctor_get_uint8(v_options_4829_, sizeof(void*)*1);
if (v_hasTrace_4830_ == 0)
{
lean_object* v___x_4831_; 
lean_dec_ref(v___f_4710_);
v___x_4831_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4692_, v_a_4693_, v_a_4694_, v_a_4695_, v_a_4696_);
if (lean_obj_tag(v___x_4831_) == 0)
{
lean_object* v_a_4832_; lean_object* v___x_4834_; uint8_t v_isShared_4835_; uint8_t v_isSharedCheck_4849_; 
v_a_4832_ = lean_ctor_get(v___x_4831_, 0);
v_isSharedCheck_4849_ = !lean_is_exclusive(v___x_4831_);
if (v_isSharedCheck_4849_ == 0)
{
v___x_4834_ = v___x_4831_;
v_isShared_4835_ = v_isSharedCheck_4849_;
goto v_resetjp_4833_;
}
else
{
lean_inc(v_a_4832_);
lean_dec(v___x_4831_);
v___x_4834_ = lean_box(0);
v_isShared_4835_ = v_isSharedCheck_4849_;
goto v_resetjp_4833_;
}
v_resetjp_4833_:
{
uint8_t v_isUnsafe_4836_; 
v_isUnsafe_4836_ = lean_ctor_get_uint8(v_a_4832_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4836_ == 0)
{
lean_object* v_ctors_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; lean_object* v___f_4843_; lean_object* v___x_4844_; 
lean_del_object(v___x_4834_);
v_ctors_4837_ = lean_ctor_get(v_a_4832_, 4);
lean_inc(v_ctors_4837_);
lean_dec(v_a_4832_);
v___x_4838_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4839_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4840_ = lean_box(0);
v___x_4841_ = lean_box(v___y_4827_);
v___x_4842_ = lean_box(v_hasTrace_4830_);
v___f_4843_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed), 9, 4);
lean_closure_set(v___f_4843_, 0, v___x_4841_);
lean_closure_set(v___f_4843_, 1, v___x_4842_);
lean_closure_set(v___f_4843_, 2, v_ctors_4837_);
lean_closure_set(v___f_4843_, 3, v___x_4840_);
v___x_4844_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4838_, v___x_4839_, v___f_4843_, v_a_4693_, v_a_4694_, v_a_4695_, v_a_4696_);
return v___x_4844_;
}
else
{
lean_object* v___x_4845_; lean_object* v___x_4847_; 
lean_dec(v_a_4832_);
v___x_4845_ = lean_box(0);
if (v_isShared_4835_ == 0)
{
lean_ctor_set(v___x_4834_, 0, v___x_4845_);
v___x_4847_ = v___x_4834_;
goto v_reusejp_4846_;
}
else
{
lean_object* v_reuseFailAlloc_4848_; 
v_reuseFailAlloc_4848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4848_, 0, v___x_4845_);
v___x_4847_ = v_reuseFailAlloc_4848_;
goto v_reusejp_4846_;
}
v_reusejp_4846_:
{
return v___x_4847_;
}
}
}
}
else
{
lean_object* v_a_4850_; lean_object* v___x_4852_; uint8_t v_isShared_4853_; uint8_t v_isSharedCheck_4857_; 
v_a_4850_ = lean_ctor_get(v___x_4831_, 0);
v_isSharedCheck_4857_ = !lean_is_exclusive(v___x_4831_);
if (v_isSharedCheck_4857_ == 0)
{
v___x_4852_ = v___x_4831_;
v_isShared_4853_ = v_isSharedCheck_4857_;
goto v_resetjp_4851_;
}
else
{
lean_inc(v_a_4850_);
lean_dec(v___x_4831_);
v___x_4852_ = lean_box(0);
v_isShared_4853_ = v_isSharedCheck_4857_;
goto v_resetjp_4851_;
}
v_resetjp_4851_:
{
lean_object* v___x_4855_; 
if (v_isShared_4853_ == 0)
{
v___x_4855_ = v___x_4852_;
goto v_reusejp_4854_;
}
else
{
lean_object* v_reuseFailAlloc_4856_; 
v_reuseFailAlloc_4856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4856_, 0, v_a_4850_);
v___x_4855_ = v_reuseFailAlloc_4856_;
goto v_reusejp_4854_;
}
v_reusejp_4854_:
{
return v___x_4855_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_4858_; lean_object* v___x_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; uint8_t v___x_4862_; 
v_inheritedTraceOptions_4858_ = lean_ctor_get(v_a_4695_, 13);
v___x_4859_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_4860_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_4861_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_4862_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4858_, v_options_4829_, v___x_4861_);
if (v___x_4862_ == 0)
{
lean_object* v___x_4863_; uint8_t v___x_4864_; 
v___x_4863_ = l_Lean_trace_profiler;
v___x_4864_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_4829_, v___x_4863_);
if (v___x_4864_ == 0)
{
lean_object* v___x_4865_; 
lean_dec_ref(v___f_4710_);
v___x_4865_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4692_, v_a_4693_, v_a_4694_, v_a_4695_, v_a_4696_);
if (lean_obj_tag(v___x_4865_) == 0)
{
lean_object* v_a_4866_; lean_object* v___x_4868_; uint8_t v_isShared_4869_; uint8_t v_isSharedCheck_4883_; 
v_a_4866_ = lean_ctor_get(v___x_4865_, 0);
v_isSharedCheck_4883_ = !lean_is_exclusive(v___x_4865_);
if (v_isSharedCheck_4883_ == 0)
{
v___x_4868_ = v___x_4865_;
v_isShared_4869_ = v_isSharedCheck_4883_;
goto v_resetjp_4867_;
}
else
{
lean_inc(v_a_4866_);
lean_dec(v___x_4865_);
v___x_4868_ = lean_box(0);
v_isShared_4869_ = v_isSharedCheck_4883_;
goto v_resetjp_4867_;
}
v_resetjp_4867_:
{
uint8_t v_isUnsafe_4870_; 
v_isUnsafe_4870_ = lean_ctor_get_uint8(v_a_4866_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4870_ == 0)
{
lean_object* v_ctors_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; lean_object* v___x_4874_; lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v___f_4877_; lean_object* v___x_4878_; 
lean_del_object(v___x_4868_);
v_ctors_4871_ = lean_ctor_get(v_a_4866_, 4);
lean_inc(v_ctors_4871_);
lean_dec(v_a_4866_);
v___x_4872_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4873_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4874_ = lean_box(0);
v___x_4875_ = lean_box(v_hasTrace_4830_);
v___x_4876_ = lean_box(v___x_4864_);
v___f_4877_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__2___boxed), 9, 4);
lean_closure_set(v___f_4877_, 0, v___x_4875_);
lean_closure_set(v___f_4877_, 1, v___x_4876_);
lean_closure_set(v___f_4877_, 2, v_ctors_4871_);
lean_closure_set(v___f_4877_, 3, v___x_4874_);
v___x_4878_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4872_, v___x_4873_, v___f_4877_, v_a_4693_, v_a_4694_, v_a_4695_, v_a_4696_);
return v___x_4878_;
}
else
{
lean_object* v___x_4879_; lean_object* v___x_4881_; 
lean_dec(v_a_4866_);
v___x_4879_ = lean_box(0);
if (v_isShared_4869_ == 0)
{
lean_ctor_set(v___x_4868_, 0, v___x_4879_);
v___x_4881_ = v___x_4868_;
goto v_reusejp_4880_;
}
else
{
lean_object* v_reuseFailAlloc_4882_; 
v_reuseFailAlloc_4882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4882_, 0, v___x_4879_);
v___x_4881_ = v_reuseFailAlloc_4882_;
goto v_reusejp_4880_;
}
v_reusejp_4880_:
{
return v___x_4881_;
}
}
}
}
else
{
lean_object* v_a_4884_; lean_object* v___x_4886_; uint8_t v_isShared_4887_; uint8_t v_isSharedCheck_4891_; 
v_a_4884_ = lean_ctor_get(v___x_4865_, 0);
v_isSharedCheck_4891_ = !lean_is_exclusive(v___x_4865_);
if (v_isSharedCheck_4891_ == 0)
{
v___x_4886_ = v___x_4865_;
v_isShared_4887_ = v_isSharedCheck_4891_;
goto v_resetjp_4885_;
}
else
{
lean_inc(v_a_4884_);
lean_dec(v___x_4865_);
v___x_4886_ = lean_box(0);
v_isShared_4887_ = v_isSharedCheck_4891_;
goto v_resetjp_4885_;
}
v_resetjp_4885_:
{
lean_object* v___x_4889_; 
if (v_isShared_4887_ == 0)
{
v___x_4889_ = v___x_4886_;
goto v_reusejp_4888_;
}
else
{
lean_object* v_reuseFailAlloc_4890_; 
v_reuseFailAlloc_4890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4890_, 0, v_a_4884_);
v___x_4889_ = v_reuseFailAlloc_4890_;
goto v_reusejp_4888_;
}
v_reusejp_4888_:
{
return v___x_4889_;
}
}
}
}
else
{
v___y_4785_ = v_hasTrace_4830_;
v___y_4786_ = v___x_4860_;
v___y_4787_ = v___x_4862_;
v___y_4788_ = v___x_4859_;
v___y_4789_ = v_options_4829_;
goto v___jp_4784_;
}
}
else
{
v___y_4785_ = v_hasTrace_4830_;
v___y_4786_ = v___x_4860_;
v___y_4787_ = v___x_4862_;
v___y_4788_ = v___x_4859_;
v___y_4789_ = v_options_4829_;
goto v___jp_4784_;
}
}
}
else
{
lean_dec_ref(v___f_4710_);
lean_dec(v_declName_4692_);
goto v___jp_4704_;
}
}
}
}
}
else
{
lean_object* v_a_4897_; lean_object* v___x_4899_; uint8_t v_isShared_4900_; uint8_t v_isSharedCheck_4904_; 
lean_dec(v___x_4698_);
lean_dec(v_declName_4692_);
v_a_4897_ = lean_ctor_get(v___x_4699_, 0);
v_isSharedCheck_4904_ = !lean_is_exclusive(v___x_4699_);
if (v_isSharedCheck_4904_ == 0)
{
v___x_4899_ = v___x_4699_;
v_isShared_4900_ = v_isSharedCheck_4904_;
goto v_resetjp_4898_;
}
else
{
lean_inc(v_a_4897_);
lean_dec(v___x_4699_);
v___x_4899_ = lean_box(0);
v_isShared_4900_ = v_isSharedCheck_4904_;
goto v_resetjp_4898_;
}
v_resetjp_4898_:
{
lean_object* v___x_4902_; 
if (v_isShared_4900_ == 0)
{
v___x_4902_ = v___x_4899_;
goto v_reusejp_4901_;
}
else
{
lean_object* v_reuseFailAlloc_4903_; 
v_reuseFailAlloc_4903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4903_, 0, v_a_4897_);
v___x_4902_ = v_reuseFailAlloc_4903_;
goto v_reusejp_4901_;
}
v_reusejp_4901_:
{
return v___x_4902_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___boxed(lean_object* v_declName_4905_, lean_object* v_a_4906_, lean_object* v_a_4907_, lean_object* v_a_4908_, lean_object* v_a_4909_, lean_object* v_a_4910_){
_start:
{
lean_object* v_res_4911_; 
v_res_4911_ = l_Lean_Meta_mkInjectiveTheorems(v_declName_4905_, v_a_4906_, v_a_4907_, v_a_4908_, v_a_4909_);
lean_dec(v_a_4909_);
lean_dec_ref(v_a_4908_);
lean_dec(v_a_4907_);
lean_dec_ref(v_a_4906_);
return v_res_4911_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3(uint8_t v___y_4912_, uint8_t v___x_4913_, lean_object* v_as_4914_, lean_object* v_as_x27_4915_, lean_object* v_b_4916_, lean_object* v_a_4917_, lean_object* v___y_4918_, lean_object* v___y_4919_, lean_object* v___y_4920_, lean_object* v___y_4921_){
_start:
{
lean_object* v___x_4923_; 
v___x_4923_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___y_4912_, v___x_4913_, v_as_x27_4915_, v_b_4916_, v___y_4918_, v___y_4919_, v___y_4920_, v___y_4921_);
return v___x_4923_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___boxed(lean_object* v___y_4924_, lean_object* v___x_4925_, lean_object* v_as_4926_, lean_object* v_as_x27_4927_, lean_object* v_b_4928_, lean_object* v_a_4929_, lean_object* v___y_4930_, lean_object* v___y_4931_, lean_object* v___y_4932_, lean_object* v___y_4933_, lean_object* v___y_4934_){
_start:
{
uint8_t v___y_21001__boxed_4935_; uint8_t v___x_21002__boxed_4936_; lean_object* v_res_4937_; 
v___y_21001__boxed_4935_ = lean_unbox(v___y_4924_);
v___x_21002__boxed_4936_ = lean_unbox(v___x_4925_);
v_res_4937_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3(v___y_21001__boxed_4935_, v___x_21002__boxed_4936_, v_as_4926_, v_as_x27_4927_, v_b_4928_, v_a_4929_, v___y_4930_, v___y_4931_, v___y_4932_, v___y_4933_);
lean_dec(v___y_4933_);
lean_dec_ref(v___y_4932_);
lean_dec(v___y_4931_);
lean_dec_ref(v___y_4930_);
lean_dec(v_as_x27_4927_);
lean_dec(v_as_4926_);
return v_res_4937_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; 
v___x_4978_ = lean_unsigned_to_nat(4172903888u);
v___x_4979_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_));
v___x_4980_ = l_Lean_Name_num___override(v___x_4979_, v___x_4978_);
return v___x_4980_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; 
v___x_4982_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_));
v___x_4983_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4984_ = l_Lean_Name_str___override(v___x_4983_, v___x_4982_);
return v___x_4984_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; 
v___x_4986_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_));
v___x_4987_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4988_ = l_Lean_Name_str___override(v___x_4987_, v___x_4986_);
return v___x_4988_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; 
v___x_4989_ = lean_unsigned_to_nat(2u);
v___x_4990_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4991_ = l_Lean_Name_num___override(v___x_4990_, v___x_4989_);
return v___x_4991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4993_; uint8_t v___x_4994_; lean_object* v___x_4995_; lean_object* v___x_4996_; 
v___x_4993_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_4994_ = 0;
v___x_4995_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4996_ = l_Lean_registerTraceClass(v___x_4993_, v___x_4994_, v___x_4995_);
return v___x_4996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2____boxed(lean_object* v_a_4997_){
_start:
{
lean_object* v_res_4998_; 
v_res_4998_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_();
return v_res_4998_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(lean_object* v_a_4999_, lean_object* v_b_5000_){
_start:
{
lean_object* v_array_5001_; lean_object* v_start_5002_; lean_object* v_stop_5003_; lean_object* v___x_5005_; uint8_t v_isShared_5006_; uint8_t v_isSharedCheck_5016_; 
v_array_5001_ = lean_ctor_get(v_a_4999_, 0);
v_start_5002_ = lean_ctor_get(v_a_4999_, 1);
v_stop_5003_ = lean_ctor_get(v_a_4999_, 2);
v_isSharedCheck_5016_ = !lean_is_exclusive(v_a_4999_);
if (v_isSharedCheck_5016_ == 0)
{
v___x_5005_ = v_a_4999_;
v_isShared_5006_ = v_isSharedCheck_5016_;
goto v_resetjp_5004_;
}
else
{
lean_inc(v_stop_5003_);
lean_inc(v_start_5002_);
lean_inc(v_array_5001_);
lean_dec(v_a_4999_);
v___x_5005_ = lean_box(0);
v_isShared_5006_ = v_isSharedCheck_5016_;
goto v_resetjp_5004_;
}
v_resetjp_5004_:
{
uint8_t v___x_5007_; 
v___x_5007_ = lean_nat_dec_lt(v_start_5002_, v_stop_5003_);
if (v___x_5007_ == 0)
{
lean_del_object(v___x_5005_);
lean_dec(v_stop_5003_);
lean_dec(v_start_5002_);
lean_dec_ref(v_array_5001_);
return v_b_5000_;
}
else
{
lean_object* v___x_5008_; lean_object* v___x_5009_; lean_object* v___x_5011_; 
v___x_5008_ = lean_unsigned_to_nat(1u);
v___x_5009_ = lean_nat_add(v_start_5002_, v___x_5008_);
lean_inc_ref(v_array_5001_);
if (v_isShared_5006_ == 0)
{
lean_ctor_set(v___x_5005_, 1, v___x_5009_);
v___x_5011_ = v___x_5005_;
goto v_reusejp_5010_;
}
else
{
lean_object* v_reuseFailAlloc_5015_; 
v_reuseFailAlloc_5015_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5015_, 0, v_array_5001_);
lean_ctor_set(v_reuseFailAlloc_5015_, 1, v___x_5009_);
lean_ctor_set(v_reuseFailAlloc_5015_, 2, v_stop_5003_);
v___x_5011_ = v_reuseFailAlloc_5015_;
goto v_reusejp_5010_;
}
v_reusejp_5010_:
{
lean_object* v___x_5012_; lean_object* v___x_5013_; 
v___x_5012_ = lean_array_fget(v_array_5001_, v_start_5002_);
lean_dec(v_start_5002_);
lean_dec_ref(v_array_5001_);
v___x_5013_ = lean_array_push(v_b_5000_, v___x_5012_);
v_a_4999_ = v___x_5011_;
v_b_5000_ = v___x_5013_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_5017_; 
v___x_5017_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_5017_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_5018_; lean_object* v___x_5019_; 
v___x_5018_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_5019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5019_, 0, v___x_5018_);
return v___x_5019_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_5020_; lean_object* v___x_5021_; lean_object* v___x_5022_; 
v___x_5020_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_5021_ = lean_unsigned_to_nat(0u);
v___x_5022_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_5022_, 0, v___x_5021_);
lean_ctor_set(v___x_5022_, 1, v___x_5021_);
lean_ctor_set(v___x_5022_, 2, v___x_5021_);
lean_ctor_set(v___x_5022_, 3, v___x_5021_);
lean_ctor_set(v___x_5022_, 4, v___x_5020_);
lean_ctor_set(v___x_5022_, 5, v___x_5020_);
lean_ctor_set(v___x_5022_, 6, v___x_5020_);
lean_ctor_set(v___x_5022_, 7, v___x_5020_);
lean_ctor_set(v___x_5022_, 8, v___x_5020_);
lean_ctor_set(v___x_5022_, 9, v___x_5020_);
return v___x_5022_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_5023_; lean_object* v___x_5024_; lean_object* v___x_5025_; lean_object* v___x_5026_; 
v___x_5023_ = lean_box(1);
v___x_5024_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_5025_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_5026_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5026_, 0, v___x_5025_);
lean_ctor_set(v___x_5026_, 1, v___x_5024_);
lean_ctor_set(v___x_5026_, 2, v___x_5023_);
return v___x_5026_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_5028_; lean_object* v___x_5029_; 
v___x_5028_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4));
v___x_5029_ = l_Lean_stringToMessageData(v___x_5028_);
return v___x_5029_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_5031_; lean_object* v___x_5032_; 
v___x_5031_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_5032_ = l_Lean_stringToMessageData(v___x_5031_);
return v___x_5032_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_5034_; lean_object* v___x_5035_; 
v___x_5034_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_5035_ = l_Lean_stringToMessageData(v___x_5034_);
return v___x_5035_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_5037_; lean_object* v___x_5038_; 
v___x_5037_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_5038_ = l_Lean_stringToMessageData(v___x_5037_);
return v___x_5038_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_5040_; lean_object* v___x_5041_; 
v___x_5040_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_5041_ = l_Lean_stringToMessageData(v___x_5040_);
return v___x_5041_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15(void){
_start:
{
lean_object* v___x_5043_; lean_object* v___x_5044_; 
v___x_5043_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14));
v___x_5044_ = l_Lean_stringToMessageData(v___x_5043_);
return v___x_5044_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17(void){
_start:
{
lean_object* v___x_5046_; lean_object* v___x_5047_; 
v___x_5046_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16));
v___x_5047_ = l_Lean_stringToMessageData(v___x_5046_);
return v___x_5047_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_5048_, lean_object* v_declHint_5049_, lean_object* v___y_5050_){
_start:
{
lean_object* v___x_5052_; lean_object* v_env_5053_; uint8_t v___x_5054_; 
v___x_5052_ = lean_st_ref_get(v___y_5050_);
v_env_5053_ = lean_ctor_get(v___x_5052_, 0);
lean_inc_ref(v_env_5053_);
lean_dec(v___x_5052_);
v___x_5054_ = l_Lean_Name_isAnonymous(v_declHint_5049_);
if (v___x_5054_ == 0)
{
uint8_t v_isExporting_5055_; 
v_isExporting_5055_ = lean_ctor_get_uint8(v_env_5053_, sizeof(void*)*8);
if (v_isExporting_5055_ == 0)
{
lean_object* v___x_5056_; 
lean_dec_ref(v_env_5053_);
lean_dec(v_declHint_5049_);
v___x_5056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5056_, 0, v_msg_5048_);
return v___x_5056_;
}
else
{
lean_object* v___x_5057_; uint8_t v___x_5058_; 
lean_inc_ref(v_env_5053_);
v___x_5057_ = l_Lean_Environment_setExporting(v_env_5053_, v___x_5054_);
lean_inc(v_declHint_5049_);
lean_inc_ref(v___x_5057_);
v___x_5058_ = l_Lean_Environment_contains(v___x_5057_, v_declHint_5049_, v_isExporting_5055_);
if (v___x_5058_ == 0)
{
lean_object* v___x_5059_; 
lean_dec_ref(v___x_5057_);
lean_dec_ref(v_env_5053_);
lean_dec(v_declHint_5049_);
v___x_5059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5059_, 0, v_msg_5048_);
return v___x_5059_;
}
else
{
lean_object* v___x_5060_; lean_object* v___x_5061_; lean_object* v___x_5062_; lean_object* v___x_5063_; lean_object* v___x_5064_; lean_object* v_c_5065_; lean_object* v___x_5066_; 
v___x_5060_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_5061_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_5062_ = l_Lean_Options_empty;
v___x_5063_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5063_, 0, v___x_5057_);
lean_ctor_set(v___x_5063_, 1, v___x_5060_);
lean_ctor_set(v___x_5063_, 2, v___x_5061_);
lean_ctor_set(v___x_5063_, 3, v___x_5062_);
lean_inc(v_declHint_5049_);
v___x_5064_ = l_Lean_MessageData_ofConstName(v_declHint_5049_, v___x_5054_);
v_c_5065_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_5065_, 0, v___x_5063_);
lean_ctor_set(v_c_5065_, 1, v___x_5064_);
v___x_5066_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_5053_, v_declHint_5049_);
if (lean_obj_tag(v___x_5066_) == 0)
{
lean_object* v___x_5067_; lean_object* v___x_5068_; lean_object* v___x_5069_; lean_object* v___x_5070_; lean_object* v___x_5071_; lean_object* v___x_5072_; lean_object* v___x_5073_; 
lean_dec_ref(v_env_5053_);
lean_dec(v_declHint_5049_);
v___x_5067_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_5068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5068_, 0, v___x_5067_);
lean_ctor_set(v___x_5068_, 1, v_c_5065_);
v___x_5069_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_5070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5070_, 0, v___x_5068_);
lean_ctor_set(v___x_5070_, 1, v___x_5069_);
v___x_5071_ = l_Lean_MessageData_note(v___x_5070_);
v___x_5072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5072_, 0, v_msg_5048_);
lean_ctor_set(v___x_5072_, 1, v___x_5071_);
v___x_5073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5073_, 0, v___x_5072_);
return v___x_5073_;
}
else
{
lean_object* v_val_5074_; lean_object* v___x_5076_; uint8_t v_isShared_5077_; uint8_t v_isSharedCheck_5109_; 
v_val_5074_ = lean_ctor_get(v___x_5066_, 0);
v_isSharedCheck_5109_ = !lean_is_exclusive(v___x_5066_);
if (v_isSharedCheck_5109_ == 0)
{
v___x_5076_ = v___x_5066_;
v_isShared_5077_ = v_isSharedCheck_5109_;
goto v_resetjp_5075_;
}
else
{
lean_inc(v_val_5074_);
lean_dec(v___x_5066_);
v___x_5076_ = lean_box(0);
v_isShared_5077_ = v_isSharedCheck_5109_;
goto v_resetjp_5075_;
}
v_resetjp_5075_:
{
lean_object* v___x_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; lean_object* v_mod_5081_; uint8_t v___x_5082_; 
v___x_5078_ = lean_box(0);
v___x_5079_ = l_Lean_Environment_header(v_env_5053_);
lean_dec_ref(v_env_5053_);
v___x_5080_ = l_Lean_EnvironmentHeader_moduleNames(v___x_5079_);
v_mod_5081_ = lean_array_get(v___x_5078_, v___x_5080_, v_val_5074_);
lean_dec(v_val_5074_);
lean_dec_ref(v___x_5080_);
v___x_5082_ = l_Lean_isPrivateName(v_declHint_5049_);
lean_dec(v_declHint_5049_);
if (v___x_5082_ == 0)
{
lean_object* v___x_5083_; lean_object* v___x_5084_; lean_object* v___x_5085_; lean_object* v___x_5086_; lean_object* v___x_5087_; lean_object* v___x_5088_; lean_object* v___x_5089_; lean_object* v___x_5090_; lean_object* v___x_5091_; lean_object* v___x_5092_; lean_object* v___x_5094_; 
v___x_5083_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_5084_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5084_, 0, v___x_5083_);
lean_ctor_set(v___x_5084_, 1, v_c_5065_);
v___x_5085_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_5086_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5086_, 0, v___x_5084_);
lean_ctor_set(v___x_5086_, 1, v___x_5085_);
v___x_5087_ = l_Lean_MessageData_ofName(v_mod_5081_);
v___x_5088_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5088_, 0, v___x_5086_);
lean_ctor_set(v___x_5088_, 1, v___x_5087_);
v___x_5089_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_5090_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5090_, 0, v___x_5088_);
lean_ctor_set(v___x_5090_, 1, v___x_5089_);
v___x_5091_ = l_Lean_MessageData_note(v___x_5090_);
v___x_5092_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5092_, 0, v_msg_5048_);
lean_ctor_set(v___x_5092_, 1, v___x_5091_);
if (v_isShared_5077_ == 0)
{
lean_ctor_set_tag(v___x_5076_, 0);
lean_ctor_set(v___x_5076_, 0, v___x_5092_);
v___x_5094_ = v___x_5076_;
goto v_reusejp_5093_;
}
else
{
lean_object* v_reuseFailAlloc_5095_; 
v_reuseFailAlloc_5095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5095_, 0, v___x_5092_);
v___x_5094_ = v_reuseFailAlloc_5095_;
goto v_reusejp_5093_;
}
v_reusejp_5093_:
{
return v___x_5094_;
}
}
else
{
lean_object* v___x_5096_; lean_object* v___x_5097_; lean_object* v___x_5098_; lean_object* v___x_5099_; lean_object* v___x_5100_; lean_object* v___x_5101_; lean_object* v___x_5102_; lean_object* v___x_5103_; lean_object* v___x_5104_; lean_object* v___x_5105_; lean_object* v___x_5107_; 
v___x_5096_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_5097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5097_, 0, v___x_5096_);
lean_ctor_set(v___x_5097_, 1, v_c_5065_);
v___x_5098_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_5099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5099_, 0, v___x_5097_);
lean_ctor_set(v___x_5099_, 1, v___x_5098_);
v___x_5100_ = l_Lean_MessageData_ofName(v_mod_5081_);
v___x_5101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5101_, 0, v___x_5099_);
lean_ctor_set(v___x_5101_, 1, v___x_5100_);
v___x_5102_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_5103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5103_, 0, v___x_5101_);
lean_ctor_set(v___x_5103_, 1, v___x_5102_);
v___x_5104_ = l_Lean_MessageData_note(v___x_5103_);
v___x_5105_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5105_, 0, v_msg_5048_);
lean_ctor_set(v___x_5105_, 1, v___x_5104_);
if (v_isShared_5077_ == 0)
{
lean_ctor_set_tag(v___x_5076_, 0);
lean_ctor_set(v___x_5076_, 0, v___x_5105_);
v___x_5107_ = v___x_5076_;
goto v_reusejp_5106_;
}
else
{
lean_object* v_reuseFailAlloc_5108_; 
v_reuseFailAlloc_5108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5108_, 0, v___x_5105_);
v___x_5107_ = v_reuseFailAlloc_5108_;
goto v_reusejp_5106_;
}
v_reusejp_5106_:
{
return v___x_5107_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_5110_; 
lean_dec_ref(v_env_5053_);
lean_dec(v_declHint_5049_);
v___x_5110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5110_, 0, v_msg_5048_);
return v___x_5110_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_5111_, lean_object* v_declHint_5112_, lean_object* v___y_5113_, lean_object* v___y_5114_){
_start:
{
lean_object* v_res_5115_; 
v_res_5115_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_5111_, v_declHint_5112_, v___y_5113_);
lean_dec(v___y_5113_);
return v_res_5115_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_msg_5116_, lean_object* v_declHint_5117_, lean_object* v___y_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_){
_start:
{
lean_object* v___x_5123_; lean_object* v_a_5124_; lean_object* v___x_5126_; uint8_t v_isShared_5127_; uint8_t v_isSharedCheck_5133_; 
v___x_5123_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_5116_, v_declHint_5117_, v___y_5121_);
v_a_5124_ = lean_ctor_get(v___x_5123_, 0);
v_isSharedCheck_5133_ = !lean_is_exclusive(v___x_5123_);
if (v_isSharedCheck_5133_ == 0)
{
v___x_5126_ = v___x_5123_;
v_isShared_5127_ = v_isSharedCheck_5133_;
goto v_resetjp_5125_;
}
else
{
lean_inc(v_a_5124_);
lean_dec(v___x_5123_);
v___x_5126_ = lean_box(0);
v_isShared_5127_ = v_isSharedCheck_5133_;
goto v_resetjp_5125_;
}
v_resetjp_5125_:
{
lean_object* v___x_5128_; lean_object* v___x_5129_; lean_object* v___x_5131_; 
v___x_5128_ = l_Lean_unknownIdentifierMessageTag;
v___x_5129_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_5129_, 0, v___x_5128_);
lean_ctor_set(v___x_5129_, 1, v_a_5124_);
if (v_isShared_5127_ == 0)
{
lean_ctor_set(v___x_5126_, 0, v___x_5129_);
v___x_5131_ = v___x_5126_;
goto v_reusejp_5130_;
}
else
{
lean_object* v_reuseFailAlloc_5132_; 
v_reuseFailAlloc_5132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5132_, 0, v___x_5129_);
v___x_5131_ = v_reuseFailAlloc_5132_;
goto v_reusejp_5130_;
}
v_reusejp_5130_:
{
return v___x_5131_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v_msg_5134_, lean_object* v_declHint_5135_, lean_object* v___y_5136_, lean_object* v___y_5137_, lean_object* v___y_5138_, lean_object* v___y_5139_, lean_object* v___y_5140_){
_start:
{
lean_object* v_res_5141_; 
v_res_5141_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_5134_, v_declHint_5135_, v___y_5136_, v___y_5137_, v___y_5138_, v___y_5139_);
lean_dec(v___y_5139_);
lean_dec_ref(v___y_5138_);
lean_dec(v___y_5137_);
lean_dec_ref(v___y_5136_);
return v_res_5141_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_5142_, lean_object* v_msg_5143_, lean_object* v___y_5144_, lean_object* v___y_5145_, lean_object* v___y_5146_, lean_object* v___y_5147_){
_start:
{
lean_object* v_fileName_5149_; lean_object* v_fileMap_5150_; lean_object* v_options_5151_; lean_object* v_currRecDepth_5152_; lean_object* v_maxRecDepth_5153_; lean_object* v_ref_5154_; lean_object* v_currNamespace_5155_; lean_object* v_openDecls_5156_; lean_object* v_initHeartbeats_5157_; lean_object* v_maxHeartbeats_5158_; lean_object* v_quotContext_5159_; lean_object* v_currMacroScope_5160_; uint8_t v_diag_5161_; lean_object* v_cancelTk_x3f_5162_; uint8_t v_suppressElabErrors_5163_; lean_object* v_inheritedTraceOptions_5164_; lean_object* v_ref_5165_; lean_object* v___x_5166_; lean_object* v___x_5167_; 
v_fileName_5149_ = lean_ctor_get(v___y_5146_, 0);
v_fileMap_5150_ = lean_ctor_get(v___y_5146_, 1);
v_options_5151_ = lean_ctor_get(v___y_5146_, 2);
v_currRecDepth_5152_ = lean_ctor_get(v___y_5146_, 3);
v_maxRecDepth_5153_ = lean_ctor_get(v___y_5146_, 4);
v_ref_5154_ = lean_ctor_get(v___y_5146_, 5);
v_currNamespace_5155_ = lean_ctor_get(v___y_5146_, 6);
v_openDecls_5156_ = lean_ctor_get(v___y_5146_, 7);
v_initHeartbeats_5157_ = lean_ctor_get(v___y_5146_, 8);
v_maxHeartbeats_5158_ = lean_ctor_get(v___y_5146_, 9);
v_quotContext_5159_ = lean_ctor_get(v___y_5146_, 10);
v_currMacroScope_5160_ = lean_ctor_get(v___y_5146_, 11);
v_diag_5161_ = lean_ctor_get_uint8(v___y_5146_, sizeof(void*)*14);
v_cancelTk_x3f_5162_ = lean_ctor_get(v___y_5146_, 12);
v_suppressElabErrors_5163_ = lean_ctor_get_uint8(v___y_5146_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_5164_ = lean_ctor_get(v___y_5146_, 13);
v_ref_5165_ = l_Lean_replaceRef(v_ref_5142_, v_ref_5154_);
lean_inc_ref(v_inheritedTraceOptions_5164_);
lean_inc(v_cancelTk_x3f_5162_);
lean_inc(v_currMacroScope_5160_);
lean_inc(v_quotContext_5159_);
lean_inc(v_maxHeartbeats_5158_);
lean_inc(v_initHeartbeats_5157_);
lean_inc(v_openDecls_5156_);
lean_inc(v_currNamespace_5155_);
lean_inc(v_maxRecDepth_5153_);
lean_inc(v_currRecDepth_5152_);
lean_inc_ref(v_options_5151_);
lean_inc_ref(v_fileMap_5150_);
lean_inc_ref(v_fileName_5149_);
v___x_5166_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_5166_, 0, v_fileName_5149_);
lean_ctor_set(v___x_5166_, 1, v_fileMap_5150_);
lean_ctor_set(v___x_5166_, 2, v_options_5151_);
lean_ctor_set(v___x_5166_, 3, v_currRecDepth_5152_);
lean_ctor_set(v___x_5166_, 4, v_maxRecDepth_5153_);
lean_ctor_set(v___x_5166_, 5, v_ref_5165_);
lean_ctor_set(v___x_5166_, 6, v_currNamespace_5155_);
lean_ctor_set(v___x_5166_, 7, v_openDecls_5156_);
lean_ctor_set(v___x_5166_, 8, v_initHeartbeats_5157_);
lean_ctor_set(v___x_5166_, 9, v_maxHeartbeats_5158_);
lean_ctor_set(v___x_5166_, 10, v_quotContext_5159_);
lean_ctor_set(v___x_5166_, 11, v_currMacroScope_5160_);
lean_ctor_set(v___x_5166_, 12, v_cancelTk_x3f_5162_);
lean_ctor_set(v___x_5166_, 13, v_inheritedTraceOptions_5164_);
lean_ctor_set_uint8(v___x_5166_, sizeof(void*)*14, v_diag_5161_);
lean_ctor_set_uint8(v___x_5166_, sizeof(void*)*14 + 1, v_suppressElabErrors_5163_);
v___x_5167_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v_msg_5143_, v___y_5144_, v___y_5145_, v___x_5166_, v___y_5147_);
lean_dec_ref(v___x_5166_);
return v___x_5167_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_5168_, lean_object* v_msg_5169_, lean_object* v___y_5170_, lean_object* v___y_5171_, lean_object* v___y_5172_, lean_object* v___y_5173_, lean_object* v___y_5174_){
_start:
{
lean_object* v_res_5175_; 
v_res_5175_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5168_, v_msg_5169_, v___y_5170_, v___y_5171_, v___y_5172_, v___y_5173_);
lean_dec(v___y_5173_);
lean_dec_ref(v___y_5172_);
lean_dec(v___y_5171_);
lean_dec_ref(v___y_5170_);
lean_dec(v_ref_5168_);
return v_res_5175_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_5176_, lean_object* v_msg_5177_, lean_object* v_declHint_5178_, lean_object* v___y_5179_, lean_object* v___y_5180_, lean_object* v___y_5181_, lean_object* v___y_5182_){
_start:
{
lean_object* v___x_5184_; lean_object* v_a_5185_; lean_object* v___x_5186_; 
v___x_5184_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_5177_, v_declHint_5178_, v___y_5179_, v___y_5180_, v___y_5181_, v___y_5182_);
v_a_5185_ = lean_ctor_get(v___x_5184_, 0);
lean_inc(v_a_5185_);
lean_dec_ref(v___x_5184_);
v___x_5186_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5176_, v_a_5185_, v___y_5179_, v___y_5180_, v___y_5181_, v___y_5182_);
return v___x_5186_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_5187_, lean_object* v_msg_5188_, lean_object* v_declHint_5189_, lean_object* v___y_5190_, lean_object* v___y_5191_, lean_object* v___y_5192_, lean_object* v___y_5193_, lean_object* v___y_5194_){
_start:
{
lean_object* v_res_5195_; 
v_res_5195_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5187_, v_msg_5188_, v_declHint_5189_, v___y_5190_, v___y_5191_, v___y_5192_, v___y_5193_);
lean_dec(v___y_5193_);
lean_dec_ref(v___y_5192_);
lean_dec(v___y_5191_);
lean_dec_ref(v___y_5190_);
lean_dec(v_ref_5187_);
return v_res_5195_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_5197_; lean_object* v___x_5198_; 
v___x_5197_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_5198_ = l_Lean_stringToMessageData(v___x_5197_);
return v___x_5198_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_5199_, lean_object* v_constName_5200_, lean_object* v___y_5201_, lean_object* v___y_5202_, lean_object* v___y_5203_, lean_object* v___y_5204_){
_start:
{
lean_object* v___x_5206_; uint8_t v___x_5207_; lean_object* v___x_5208_; lean_object* v___x_5209_; lean_object* v___x_5210_; lean_object* v___x_5211_; lean_object* v___x_5212_; 
v___x_5206_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_5207_ = 0;
lean_inc(v_constName_5200_);
v___x_5208_ = l_Lean_MessageData_ofConstName(v_constName_5200_, v___x_5207_);
v___x_5209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5209_, 0, v___x_5206_);
lean_ctor_set(v___x_5209_, 1, v___x_5208_);
v___x_5210_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_5211_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5211_, 0, v___x_5209_);
lean_ctor_set(v___x_5211_, 1, v___x_5210_);
v___x_5212_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5199_, v___x_5211_, v_constName_5200_, v___y_5201_, v___y_5202_, v___y_5203_, v___y_5204_);
return v___x_5212_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_5213_, lean_object* v_constName_5214_, lean_object* v___y_5215_, lean_object* v___y_5216_, lean_object* v___y_5217_, lean_object* v___y_5218_, lean_object* v___y_5219_){
_start:
{
lean_object* v_res_5220_; 
v_res_5220_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(v_ref_5213_, v_constName_5214_, v___y_5215_, v___y_5216_, v___y_5217_, v___y_5218_);
lean_dec(v___y_5218_);
lean_dec_ref(v___y_5217_);
lean_dec(v___y_5216_);
lean_dec_ref(v___y_5215_);
lean_dec(v_ref_5213_);
return v_res_5220_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(lean_object* v_constName_5221_, lean_object* v___y_5222_, lean_object* v___y_5223_, lean_object* v___y_5224_, lean_object* v___y_5225_){
_start:
{
lean_object* v_ref_5227_; lean_object* v___x_5228_; 
v_ref_5227_ = lean_ctor_get(v___y_5224_, 5);
v___x_5228_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(v_ref_5227_, v_constName_5221_, v___y_5222_, v___y_5223_, v___y_5224_, v___y_5225_);
return v___x_5228_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_constName_5229_, lean_object* v___y_5230_, lean_object* v___y_5231_, lean_object* v___y_5232_, lean_object* v___y_5233_, lean_object* v___y_5234_){
_start:
{
lean_object* v_res_5235_; 
v_res_5235_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(v_constName_5229_, v___y_5230_, v___y_5231_, v___y_5232_, v___y_5233_);
lean_dec(v___y_5233_);
lean_dec_ref(v___y_5232_);
lean_dec(v___y_5231_);
lean_dec_ref(v___y_5230_);
return v_res_5235_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(lean_object* v_constName_5236_, lean_object* v___y_5237_, lean_object* v___y_5238_, lean_object* v___y_5239_, lean_object* v___y_5240_){
_start:
{
lean_object* v___x_5242_; lean_object* v_env_5243_; uint8_t v___x_5244_; lean_object* v___x_5245_; 
v___x_5242_ = lean_st_ref_get(v___y_5240_);
v_env_5243_ = lean_ctor_get(v___x_5242_, 0);
lean_inc_ref(v_env_5243_);
lean_dec(v___x_5242_);
v___x_5244_ = 0;
lean_inc(v_constName_5236_);
v___x_5245_ = l_Lean_Environment_find_x3f(v_env_5243_, v_constName_5236_, v___x_5244_);
if (lean_obj_tag(v___x_5245_) == 0)
{
lean_object* v___x_5246_; 
v___x_5246_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(v_constName_5236_, v___y_5237_, v___y_5238_, v___y_5239_, v___y_5240_);
return v___x_5246_;
}
else
{
lean_object* v_val_5247_; lean_object* v___x_5249_; uint8_t v_isShared_5250_; uint8_t v_isSharedCheck_5254_; 
lean_dec(v_constName_5236_);
v_val_5247_ = lean_ctor_get(v___x_5245_, 0);
v_isSharedCheck_5254_ = !lean_is_exclusive(v___x_5245_);
if (v_isSharedCheck_5254_ == 0)
{
v___x_5249_ = v___x_5245_;
v_isShared_5250_ = v_isSharedCheck_5254_;
goto v_resetjp_5248_;
}
else
{
lean_inc(v_val_5247_);
lean_dec(v___x_5245_);
v___x_5249_ = lean_box(0);
v_isShared_5250_ = v_isSharedCheck_5254_;
goto v_resetjp_5248_;
}
v_resetjp_5248_:
{
lean_object* v___x_5252_; 
if (v_isShared_5250_ == 0)
{
lean_ctor_set_tag(v___x_5249_, 0);
v___x_5252_ = v___x_5249_;
goto v_reusejp_5251_;
}
else
{
lean_object* v_reuseFailAlloc_5253_; 
v_reuseFailAlloc_5253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5253_, 0, v_val_5247_);
v___x_5252_ = v_reuseFailAlloc_5253_;
goto v_reusejp_5251_;
}
v_reusejp_5251_:
{
return v___x_5252_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0___boxed(lean_object* v_constName_5255_, lean_object* v___y_5256_, lean_object* v___y_5257_, lean_object* v___y_5258_, lean_object* v___y_5259_, lean_object* v___y_5260_){
_start:
{
lean_object* v_res_5261_; 
v_res_5261_ = l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(v_constName_5255_, v___y_5256_, v___y_5257_, v___y_5258_, v___y_5259_);
lean_dec(v___y_5259_);
lean_dec_ref(v___y_5258_);
lean_dec(v___y_5257_);
lean_dec_ref(v___y_5256_);
return v_res_5261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(lean_object* v_x_5264_, lean_object* v_x_5265_, lean_object* v_x_5266_, lean_object* v___y_5267_, lean_object* v___y_5268_, lean_object* v___y_5269_, lean_object* v___y_5270_){
_start:
{
if (lean_obj_tag(v_x_5264_) == 5)
{
lean_object* v_fn_5272_; lean_object* v_arg_5273_; lean_object* v___x_5274_; lean_object* v___x_5275_; lean_object* v___x_5276_; 
v_fn_5272_ = lean_ctor_get(v_x_5264_, 0);
lean_inc_ref(v_fn_5272_);
v_arg_5273_ = lean_ctor_get(v_x_5264_, 1);
lean_inc_ref(v_arg_5273_);
lean_dec_ref(v_x_5264_);
v___x_5274_ = lean_array_set(v_x_5265_, v_x_5266_, v_arg_5273_);
v___x_5275_ = lean_unsigned_to_nat(1u);
v___x_5276_ = lean_nat_sub(v_x_5266_, v___x_5275_);
lean_dec(v_x_5266_);
v_x_5264_ = v_fn_5272_;
v_x_5265_ = v___x_5274_;
v_x_5266_ = v___x_5276_;
goto _start;
}
else
{
lean_dec(v_x_5266_);
if (lean_obj_tag(v_x_5264_) == 4)
{
lean_object* v_declName_5278_; lean_object* v___x_5279_; 
v_declName_5278_ = lean_ctor_get(v_x_5264_, 0);
lean_inc(v_declName_5278_);
lean_dec_ref(v_x_5264_);
v___x_5279_ = l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(v_declName_5278_, v___y_5267_, v___y_5268_, v___y_5269_, v___y_5270_);
if (lean_obj_tag(v___x_5279_) == 0)
{
lean_object* v_a_5280_; lean_object* v___x_5282_; uint8_t v_isShared_5283_; uint8_t v_isSharedCheck_5311_; 
v_a_5280_ = lean_ctor_get(v___x_5279_, 0);
v_isSharedCheck_5311_ = !lean_is_exclusive(v___x_5279_);
if (v_isSharedCheck_5311_ == 0)
{
v___x_5282_ = v___x_5279_;
v_isShared_5283_ = v_isSharedCheck_5311_;
goto v_resetjp_5281_;
}
else
{
lean_inc(v_a_5280_);
lean_dec(v___x_5279_);
v___x_5282_ = lean_box(0);
v_isShared_5283_ = v_isSharedCheck_5311_;
goto v_resetjp_5281_;
}
v_resetjp_5281_:
{
lean_object* v_lower_5285_; lean_object* v_upper_5286_; 
if (lean_obj_tag(v_a_5280_) == 5)
{
lean_object* v_val_5294_; lean_object* v___x_5296_; uint8_t v_isShared_5297_; uint8_t v_isSharedCheck_5308_; 
v_val_5294_ = lean_ctor_get(v_a_5280_, 0);
v_isSharedCheck_5308_ = !lean_is_exclusive(v_a_5280_);
if (v_isSharedCheck_5308_ == 0)
{
v___x_5296_ = v_a_5280_;
v_isShared_5297_ = v_isSharedCheck_5308_;
goto v_resetjp_5295_;
}
else
{
lean_inc(v_val_5294_);
lean_dec(v_a_5280_);
v___x_5296_ = lean_box(0);
v_isShared_5297_ = v_isSharedCheck_5308_;
goto v_resetjp_5295_;
}
v_resetjp_5295_:
{
lean_object* v_numParams_5298_; lean_object* v_numIndices_5299_; lean_object* v___x_5300_; uint8_t v___x_5301_; 
v_numParams_5298_ = lean_ctor_get(v_val_5294_, 1);
lean_inc(v_numParams_5298_);
v_numIndices_5299_ = lean_ctor_get(v_val_5294_, 2);
lean_inc(v_numIndices_5299_);
lean_dec_ref(v_val_5294_);
v___x_5300_ = lean_unsigned_to_nat(0u);
v___x_5301_ = lean_nat_dec_eq(v_numIndices_5299_, v___x_5300_);
lean_dec(v_numIndices_5299_);
if (v___x_5301_ == 0)
{
lean_object* v___x_5302_; uint8_t v___x_5303_; 
lean_del_object(v___x_5296_);
v___x_5302_ = lean_array_get_size(v_x_5265_);
v___x_5303_ = lean_nat_dec_le(v_numParams_5298_, v___x_5300_);
if (v___x_5303_ == 0)
{
v_lower_5285_ = v_numParams_5298_;
v_upper_5286_ = v___x_5302_;
goto v___jp_5284_;
}
else
{
lean_dec(v_numParams_5298_);
v_lower_5285_ = v___x_5300_;
v_upper_5286_ = v___x_5302_;
goto v___jp_5284_;
}
}
else
{
lean_object* v___x_5304_; lean_object* v___x_5306_; 
lean_dec(v_numParams_5298_);
lean_del_object(v___x_5282_);
lean_dec_ref(v_x_5265_);
v___x_5304_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2___closed__0));
if (v_isShared_5297_ == 0)
{
lean_ctor_set_tag(v___x_5296_, 0);
lean_ctor_set(v___x_5296_, 0, v___x_5304_);
v___x_5306_ = v___x_5296_;
goto v_reusejp_5305_;
}
else
{
lean_object* v_reuseFailAlloc_5307_; 
v_reuseFailAlloc_5307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5307_, 0, v___x_5304_);
v___x_5306_ = v_reuseFailAlloc_5307_;
goto v_reusejp_5305_;
}
v_reusejp_5305_:
{
return v___x_5306_;
}
}
}
}
else
{
lean_object* v___x_5309_; lean_object* v___x_5310_; 
lean_del_object(v___x_5282_);
lean_dec(v_a_5280_);
lean_dec_ref(v_x_5265_);
v___x_5309_ = lean_box(0);
v___x_5310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5310_, 0, v___x_5309_);
return v___x_5310_;
}
v___jp_5284_:
{
lean_object* v___x_5287_; lean_object* v___x_5288_; lean_object* v___x_5289_; lean_object* v___x_5290_; lean_object* v___x_5292_; 
v___x_5287_ = l_Array_toSubarray___redArg(v_x_5265_, v_lower_5285_, v_upper_5286_);
v___x_5288_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_5289_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(v___x_5287_, v___x_5288_);
v___x_5290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5290_, 0, v___x_5289_);
if (v_isShared_5283_ == 0)
{
lean_ctor_set(v___x_5282_, 0, v___x_5290_);
v___x_5292_ = v___x_5282_;
goto v_reusejp_5291_;
}
else
{
lean_object* v_reuseFailAlloc_5293_; 
v_reuseFailAlloc_5293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5293_, 0, v___x_5290_);
v___x_5292_ = v_reuseFailAlloc_5293_;
goto v_reusejp_5291_;
}
v_reusejp_5291_:
{
return v___x_5292_;
}
}
}
}
else
{
lean_object* v_a_5312_; lean_object* v___x_5314_; uint8_t v_isShared_5315_; uint8_t v_isSharedCheck_5319_; 
lean_dec_ref(v_x_5265_);
v_a_5312_ = lean_ctor_get(v___x_5279_, 0);
v_isSharedCheck_5319_ = !lean_is_exclusive(v___x_5279_);
if (v_isSharedCheck_5319_ == 0)
{
v___x_5314_ = v___x_5279_;
v_isShared_5315_ = v_isSharedCheck_5319_;
goto v_resetjp_5313_;
}
else
{
lean_inc(v_a_5312_);
lean_dec(v___x_5279_);
v___x_5314_ = lean_box(0);
v_isShared_5315_ = v_isSharedCheck_5319_;
goto v_resetjp_5313_;
}
v_resetjp_5313_:
{
lean_object* v___x_5317_; 
if (v_isShared_5315_ == 0)
{
v___x_5317_ = v___x_5314_;
goto v_reusejp_5316_;
}
else
{
lean_object* v_reuseFailAlloc_5318_; 
v_reuseFailAlloc_5318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5318_, 0, v_a_5312_);
v___x_5317_ = v_reuseFailAlloc_5318_;
goto v_reusejp_5316_;
}
v_reusejp_5316_:
{
return v___x_5317_;
}
}
}
}
else
{
lean_object* v___x_5320_; lean_object* v___x_5321_; 
lean_dec_ref(v_x_5265_);
lean_dec_ref(v_x_5264_);
v___x_5320_ = lean_box(0);
v___x_5321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5321_, 0, v___x_5320_);
return v___x_5321_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2___boxed(lean_object* v_x_5322_, lean_object* v_x_5323_, lean_object* v_x_5324_, lean_object* v___y_5325_, lean_object* v___y_5326_, lean_object* v___y_5327_, lean_object* v___y_5328_, lean_object* v___y_5329_){
_start:
{
lean_object* v_res_5330_; 
v_res_5330_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(v_x_5322_, v_x_5323_, v_x_5324_, v___y_5325_, v___y_5326_, v___y_5327_, v___y_5328_);
lean_dec(v___y_5328_);
lean_dec_ref(v___y_5327_);
lean_dec(v___y_5326_);
lean_dec_ref(v___y_5325_);
return v_res_5330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorAppIndices_x3f(lean_object* v_ctorApp_5331_, lean_object* v_a_5332_, lean_object* v_a_5333_, lean_object* v_a_5334_, lean_object* v_a_5335_){
_start:
{
lean_object* v___x_5337_; 
lean_inc(v_a_5335_);
lean_inc_ref(v_a_5334_);
lean_inc(v_a_5333_);
lean_inc_ref(v_a_5332_);
v___x_5337_ = lean_infer_type(v_ctorApp_5331_, v_a_5332_, v_a_5333_, v_a_5334_, v_a_5335_);
if (lean_obj_tag(v___x_5337_) == 0)
{
lean_object* v_a_5338_; lean_object* v___x_5339_; 
v_a_5338_ = lean_ctor_get(v___x_5337_, 0);
lean_inc(v_a_5338_);
lean_dec_ref(v___x_5337_);
v___x_5339_ = l_Lean_Meta_whnfD(v_a_5338_, v_a_5332_, v_a_5333_, v_a_5334_, v_a_5335_);
if (lean_obj_tag(v___x_5339_) == 0)
{
lean_object* v_a_5340_; lean_object* v_dummy_5341_; lean_object* v_nargs_5342_; lean_object* v___x_5343_; lean_object* v___x_5344_; lean_object* v___x_5345_; lean_object* v___x_5346_; 
v_a_5340_ = lean_ctor_get(v___x_5339_, 0);
lean_inc(v_a_5340_);
lean_dec_ref(v___x_5339_);
v_dummy_5341_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0);
v_nargs_5342_ = l_Lean_Expr_getAppNumArgs(v_a_5340_);
lean_inc(v_nargs_5342_);
v___x_5343_ = lean_mk_array(v_nargs_5342_, v_dummy_5341_);
v___x_5344_ = lean_unsigned_to_nat(1u);
v___x_5345_ = lean_nat_sub(v_nargs_5342_, v___x_5344_);
lean_dec(v_nargs_5342_);
v___x_5346_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(v_a_5340_, v___x_5343_, v___x_5345_, v_a_5332_, v_a_5333_, v_a_5334_, v_a_5335_);
return v___x_5346_;
}
else
{
lean_object* v_a_5347_; lean_object* v___x_5349_; uint8_t v_isShared_5350_; uint8_t v_isSharedCheck_5354_; 
v_a_5347_ = lean_ctor_get(v___x_5339_, 0);
v_isSharedCheck_5354_ = !lean_is_exclusive(v___x_5339_);
if (v_isSharedCheck_5354_ == 0)
{
v___x_5349_ = v___x_5339_;
v_isShared_5350_ = v_isSharedCheck_5354_;
goto v_resetjp_5348_;
}
else
{
lean_inc(v_a_5347_);
lean_dec(v___x_5339_);
v___x_5349_ = lean_box(0);
v_isShared_5350_ = v_isSharedCheck_5354_;
goto v_resetjp_5348_;
}
v_resetjp_5348_:
{
lean_object* v___x_5352_; 
if (v_isShared_5350_ == 0)
{
v___x_5352_ = v___x_5349_;
goto v_reusejp_5351_;
}
else
{
lean_object* v_reuseFailAlloc_5353_; 
v_reuseFailAlloc_5353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5353_, 0, v_a_5347_);
v___x_5352_ = v_reuseFailAlloc_5353_;
goto v_reusejp_5351_;
}
v_reusejp_5351_:
{
return v___x_5352_;
}
}
}
}
else
{
lean_object* v_a_5355_; lean_object* v___x_5357_; uint8_t v_isShared_5358_; uint8_t v_isSharedCheck_5362_; 
v_a_5355_ = lean_ctor_get(v___x_5337_, 0);
v_isSharedCheck_5362_ = !lean_is_exclusive(v___x_5337_);
if (v_isSharedCheck_5362_ == 0)
{
v___x_5357_ = v___x_5337_;
v_isShared_5358_ = v_isSharedCheck_5362_;
goto v_resetjp_5356_;
}
else
{
lean_inc(v_a_5355_);
lean_dec(v___x_5337_);
v___x_5357_ = lean_box(0);
v_isShared_5358_ = v_isSharedCheck_5362_;
goto v_resetjp_5356_;
}
v_resetjp_5356_:
{
lean_object* v___x_5360_; 
if (v_isShared_5358_ == 0)
{
v___x_5360_ = v___x_5357_;
goto v_reusejp_5359_;
}
else
{
lean_object* v_reuseFailAlloc_5361_; 
v_reuseFailAlloc_5361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5361_, 0, v_a_5355_);
v___x_5360_ = v_reuseFailAlloc_5361_;
goto v_reusejp_5359_;
}
v_reusejp_5359_:
{
return v___x_5360_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorAppIndices_x3f___boxed(lean_object* v_ctorApp_5363_, lean_object* v_a_5364_, lean_object* v_a_5365_, lean_object* v_a_5366_, lean_object* v_a_5367_, lean_object* v_a_5368_){
_start:
{
lean_object* v_res_5369_; 
v_res_5369_ = l_Lean_Meta_getCtorAppIndices_x3f(v_ctorApp_5363_, v_a_5364_, v_a_5365_, v_a_5366_, v_a_5367_);
lean_dec(v_a_5367_);
lean_dec_ref(v_a_5366_);
lean_dec(v_a_5365_);
lean_dec_ref(v_a_5364_);
return v_res_5369_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1(lean_object* v_inst_5370_, lean_object* v_R_5371_, lean_object* v_a_5372_, lean_object* v_b_5373_){
_start:
{
lean_object* v___x_5374_; 
v___x_5374_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(v_a_5372_, v_b_5373_);
return v___x_5374_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0(lean_object* v_00_u03b1_5375_, lean_object* v_constName_5376_, lean_object* v___y_5377_, lean_object* v___y_5378_, lean_object* v___y_5379_, lean_object* v___y_5380_){
_start:
{
lean_object* v___x_5382_; 
v___x_5382_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(v_constName_5376_, v___y_5377_, v___y_5378_, v___y_5379_, v___y_5380_);
return v___x_5382_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b1_5383_, lean_object* v_constName_5384_, lean_object* v___y_5385_, lean_object* v___y_5386_, lean_object* v___y_5387_, lean_object* v___y_5388_, lean_object* v___y_5389_){
_start:
{
lean_object* v_res_5390_; 
v_res_5390_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0(v_00_u03b1_5383_, v_constName_5384_, v___y_5385_, v___y_5386_, v___y_5387_, v___y_5388_);
lean_dec(v___y_5388_);
lean_dec_ref(v___y_5387_);
lean_dec(v___y_5386_);
lean_dec_ref(v___y_5385_);
return v_res_5390_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_5391_, lean_object* v_ref_5392_, lean_object* v_constName_5393_, lean_object* v___y_5394_, lean_object* v___y_5395_, lean_object* v___y_5396_, lean_object* v___y_5397_){
_start:
{
lean_object* v___x_5399_; 
v___x_5399_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(v_ref_5392_, v_constName_5393_, v___y_5394_, v___y_5395_, v___y_5396_, v___y_5397_);
return v___x_5399_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_5400_, lean_object* v_ref_5401_, lean_object* v_constName_5402_, lean_object* v___y_5403_, lean_object* v___y_5404_, lean_object* v___y_5405_, lean_object* v___y_5406_, lean_object* v___y_5407_){
_start:
{
lean_object* v_res_5408_; 
v_res_5408_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1(v_00_u03b1_5400_, v_ref_5401_, v_constName_5402_, v___y_5403_, v___y_5404_, v___y_5405_, v___y_5406_);
lean_dec(v___y_5406_);
lean_dec_ref(v___y_5405_);
lean_dec(v___y_5404_);
lean_dec_ref(v___y_5403_);
lean_dec(v_ref_5401_);
return v_res_5408_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_5409_, lean_object* v_ref_5410_, lean_object* v_msg_5411_, lean_object* v_declHint_5412_, lean_object* v___y_5413_, lean_object* v___y_5414_, lean_object* v___y_5415_, lean_object* v___y_5416_){
_start:
{
lean_object* v___x_5418_; 
v___x_5418_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5410_, v_msg_5411_, v_declHint_5412_, v___y_5413_, v___y_5414_, v___y_5415_, v___y_5416_);
return v___x_5418_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_5419_, lean_object* v_ref_5420_, lean_object* v_msg_5421_, lean_object* v_declHint_5422_, lean_object* v___y_5423_, lean_object* v___y_5424_, lean_object* v___y_5425_, lean_object* v___y_5426_, lean_object* v___y_5427_){
_start:
{
lean_object* v_res_5428_; 
v_res_5428_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_5419_, v_ref_5420_, v_msg_5421_, v_declHint_5422_, v___y_5423_, v___y_5424_, v___y_5425_, v___y_5426_);
lean_dec(v___y_5426_);
lean_dec_ref(v___y_5425_);
lean_dec(v___y_5424_);
lean_dec_ref(v___y_5423_);
lean_dec(v_ref_5420_);
return v_res_5428_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_msg_5429_, lean_object* v_declHint_5430_, lean_object* v___y_5431_, lean_object* v___y_5432_, lean_object* v___y_5433_, lean_object* v___y_5434_){
_start:
{
lean_object* v___x_5436_; 
v___x_5436_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_5429_, v_declHint_5430_, v___y_5434_);
return v___x_5436_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_5437_, lean_object* v_declHint_5438_, lean_object* v___y_5439_, lean_object* v___y_5440_, lean_object* v___y_5441_, lean_object* v___y_5442_, lean_object* v___y_5443_){
_start:
{
lean_object* v_res_5444_; 
v_res_5444_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_5437_, v_declHint_5438_, v___y_5439_, v___y_5440_, v___y_5441_, v___y_5442_);
lean_dec(v___y_5442_);
lean_dec_ref(v___y_5441_);
lean_dec(v___y_5440_);
lean_dec_ref(v___y_5439_);
return v_res_5444_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_5445_, lean_object* v_ref_5446_, lean_object* v_msg_5447_, lean_object* v___y_5448_, lean_object* v___y_5449_, lean_object* v___y_5450_, lean_object* v___y_5451_){
_start:
{
lean_object* v___x_5453_; 
v___x_5453_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5446_, v_msg_5447_, v___y_5448_, v___y_5449_, v___y_5450_, v___y_5451_);
return v___x_5453_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_5454_, lean_object* v_ref_5455_, lean_object* v_msg_5456_, lean_object* v___y_5457_, lean_object* v___y_5458_, lean_object* v___y_5459_, lean_object* v___y_5460_, lean_object* v___y_5461_){
_start:
{
lean_object* v_res_5462_; 
v_res_5462_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_5454_, v_ref_5455_, v_msg_5456_, v___y_5457_, v___y_5458_, v___y_5459_, v___y_5460_);
lean_dec(v___y_5460_);
lean_dec_ref(v___y_5459_);
lean_dec(v___y_5458_);
lean_dec_ref(v___y_5457_);
lean_dec(v_ref_5455_);
return v_res_5462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0___boxed(lean_object* v_i_5463_, lean_object* v_body_5464_, lean_object* v_args2_5465_, lean_object* v_ctorVal_5466_, lean_object* v_args1_5467_, lean_object* v_k_5468_, lean_object* v_arg2_5469_, lean_object* v___y_5470_, lean_object* v___y_5471_, lean_object* v___y_5472_, lean_object* v___y_5473_, lean_object* v___y_5474_){
_start:
{
lean_object* v_res_5475_; 
v_res_5475_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0(v_i_5463_, v_body_5464_, v_args2_5465_, v_ctorVal_5466_, v_args1_5467_, v_k_5468_, v_arg2_5469_, v___y_5470_, v___y_5471_, v___y_5472_, v___y_5473_);
lean_dec(v___y_5473_);
lean_dec_ref(v___y_5472_);
lean_dec(v___y_5471_);
lean_dec_ref(v___y_5470_);
lean_dec_ref(v_body_5464_);
lean_dec(v_i_5463_);
return v_res_5475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(lean_object* v_ctorVal_5476_, lean_object* v_args1_5477_, lean_object* v_k_5478_, lean_object* v_i_5479_, lean_object* v_type_5480_, lean_object* v_args2_5481_, lean_object* v_a_5482_, lean_object* v_a_5483_, lean_object* v_a_5484_, lean_object* v_a_5485_){
_start:
{
lean_object* v___x_5487_; uint8_t v___x_5488_; 
v___x_5487_ = lean_array_get_size(v_args1_5477_);
v___x_5488_ = lean_nat_dec_lt(v_i_5479_, v___x_5487_);
if (v___x_5488_ == 0)
{
lean_object* v___x_5489_; 
lean_dec_ref(v_type_5480_);
lean_dec(v_i_5479_);
lean_dec_ref(v_args1_5477_);
lean_dec_ref(v_ctorVal_5476_);
lean_inc(v_a_5485_);
lean_inc_ref(v_a_5484_);
lean_inc(v_a_5483_);
lean_inc_ref(v_a_5482_);
v___x_5489_ = lean_apply_6(v_k_5478_, v_args2_5481_, v_a_5482_, v_a_5483_, v_a_5484_, v_a_5485_, lean_box(0));
return v___x_5489_;
}
else
{
lean_object* v___x_5490_; 
lean_inc(v_a_5485_);
lean_inc_ref(v_a_5484_);
lean_inc(v_a_5483_);
lean_inc_ref(v_a_5482_);
v___x_5490_ = lean_whnf(v_type_5480_, v_a_5482_, v_a_5483_, v_a_5484_, v_a_5485_);
if (lean_obj_tag(v___x_5490_) == 0)
{
lean_object* v_a_5491_; 
v_a_5491_ = lean_ctor_get(v___x_5490_, 0);
lean_inc(v_a_5491_);
lean_dec_ref(v___x_5490_);
if (lean_obj_tag(v_a_5491_) == 7)
{
lean_object* v_binderName_5492_; lean_object* v_binderType_5493_; lean_object* v_body_5494_; lean_object* v___f_5495_; uint8_t v___x_5496_; uint8_t v___x_5497_; lean_object* v___x_5498_; 
v_binderName_5492_ = lean_ctor_get(v_a_5491_, 0);
lean_inc(v_binderName_5492_);
v_binderType_5493_ = lean_ctor_get(v_a_5491_, 1);
lean_inc_ref(v_binderType_5493_);
v_body_5494_ = lean_ctor_get(v_a_5491_, 2);
lean_inc_ref(v_body_5494_);
lean_dec_ref(v_a_5491_);
v___f_5495_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0___boxed), 12, 6);
lean_closure_set(v___f_5495_, 0, v_i_5479_);
lean_closure_set(v___f_5495_, 1, v_body_5494_);
lean_closure_set(v___f_5495_, 2, v_args2_5481_);
lean_closure_set(v___f_5495_, 3, v_ctorVal_5476_);
lean_closure_set(v___f_5495_, 4, v_args1_5477_);
lean_closure_set(v___f_5495_, 5, v_k_5478_);
v___x_5496_ = 1;
v___x_5497_ = 0;
v___x_5498_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_binderName_5492_, v___x_5496_, v_binderType_5493_, v___f_5495_, v___x_5497_, v_a_5482_, v_a_5483_, v_a_5484_, v_a_5485_);
return v___x_5498_;
}
else
{
lean_object* v_toConstantVal_5499_; lean_object* v_name_5500_; lean_object* v___x_5501_; lean_object* v___x_5502_; lean_object* v___x_5503_; lean_object* v___x_5504_; lean_object* v___x_5505_; lean_object* v___x_5506_; 
lean_dec(v_a_5491_);
lean_dec_ref(v_args2_5481_);
lean_dec(v_i_5479_);
lean_dec_ref(v_k_5478_);
lean_dec_ref(v_args1_5477_);
v_toConstantVal_5499_ = lean_ctor_get(v_ctorVal_5476_, 0);
lean_inc_ref(v_toConstantVal_5499_);
lean_dec_ref(v_ctorVal_5476_);
v_name_5500_ = lean_ctor_get(v_toConstantVal_5499_, 0);
lean_inc(v_name_5500_);
lean_dec_ref(v_toConstantVal_5499_);
v___x_5501_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1);
v___x_5502_ = l_Lean_MessageData_ofName(v_name_5500_);
v___x_5503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5503_, 0, v___x_5501_);
lean_ctor_set(v___x_5503_, 1, v___x_5502_);
v___x_5504_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_5505_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5505_, 0, v___x_5503_);
lean_ctor_set(v___x_5505_, 1, v___x_5504_);
v___x_5506_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_5505_, v_a_5482_, v_a_5483_, v_a_5484_, v_a_5485_);
return v___x_5506_;
}
}
else
{
lean_object* v_a_5507_; lean_object* v___x_5509_; uint8_t v_isShared_5510_; uint8_t v_isSharedCheck_5514_; 
lean_dec_ref(v_args2_5481_);
lean_dec(v_i_5479_);
lean_dec_ref(v_k_5478_);
lean_dec_ref(v_args1_5477_);
lean_dec_ref(v_ctorVal_5476_);
v_a_5507_ = lean_ctor_get(v___x_5490_, 0);
v_isSharedCheck_5514_ = !lean_is_exclusive(v___x_5490_);
if (v_isSharedCheck_5514_ == 0)
{
v___x_5509_ = v___x_5490_;
v_isShared_5510_ = v_isSharedCheck_5514_;
goto v_resetjp_5508_;
}
else
{
lean_inc(v_a_5507_);
lean_dec(v___x_5490_);
v___x_5509_ = lean_box(0);
v_isShared_5510_ = v_isSharedCheck_5514_;
goto v_resetjp_5508_;
}
v_resetjp_5508_:
{
lean_object* v___x_5512_; 
if (v_isShared_5510_ == 0)
{
v___x_5512_ = v___x_5509_;
goto v_reusejp_5511_;
}
else
{
lean_object* v_reuseFailAlloc_5513_; 
v_reuseFailAlloc_5513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5513_, 0, v_a_5507_);
v___x_5512_ = v_reuseFailAlloc_5513_;
goto v_reusejp_5511_;
}
v_reusejp_5511_:
{
return v___x_5512_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0(lean_object* v_i_5515_, lean_object* v_body_5516_, lean_object* v_args2_5517_, lean_object* v_ctorVal_5518_, lean_object* v_args1_5519_, lean_object* v_k_5520_, lean_object* v_arg2_5521_, lean_object* v___y_5522_, lean_object* v___y_5523_, lean_object* v___y_5524_, lean_object* v___y_5525_){
_start:
{
lean_object* v___x_5527_; lean_object* v___x_5528_; lean_object* v___x_5529_; lean_object* v___x_5530_; lean_object* v___x_5531_; 
v___x_5527_ = lean_unsigned_to_nat(1u);
v___x_5528_ = lean_nat_add(v_i_5515_, v___x_5527_);
v___x_5529_ = lean_expr_instantiate1(v_body_5516_, v_arg2_5521_);
v___x_5530_ = lean_array_push(v_args2_5517_, v_arg2_5521_);
v___x_5531_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(v_ctorVal_5518_, v_args1_5519_, v_k_5520_, v___x_5528_, v___x_5529_, v___x_5530_, v___y_5522_, v___y_5523_, v___y_5524_, v___y_5525_);
return v___x_5531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___boxed(lean_object* v_ctorVal_5532_, lean_object* v_args1_5533_, lean_object* v_k_5534_, lean_object* v_i_5535_, lean_object* v_type_5536_, lean_object* v_args2_5537_, lean_object* v_a_5538_, lean_object* v_a_5539_, lean_object* v_a_5540_, lean_object* v_a_5541_, lean_object* v_a_5542_){
_start:
{
lean_object* v_res_5543_; 
v_res_5543_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(v_ctorVal_5532_, v_args1_5533_, v_k_5534_, v_i_5535_, v_type_5536_, v_args2_5537_, v_a_5538_, v_a_5539_, v_a_5540_, v_a_5541_);
lean_dec(v_a_5541_);
lean_dec_ref(v_a_5540_);
lean_dec(v_a_5539_);
lean_dec_ref(v_a_5538_);
return v_res_5543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0(lean_object* v_name_5544_, lean_object* v_us_5545_, lean_object* v_args1_5546_, lean_object* v___x_5547_, lean_object* v_numParams_5548_, lean_object* v___x_5549_, lean_object* v_args2_5550_, lean_object* v___y_5551_, lean_object* v___y_5552_, lean_object* v___y_5553_, lean_object* v___y_5554_){
_start:
{
lean_object* v___x_5556_; lean_object* v___x_5557_; lean_object* v___x_5558_; lean_object* v___x_5559_; 
lean_inc(v_us_5545_);
v___x_5556_ = l_Lean_mkConst(v_name_5544_, v_us_5545_);
lean_inc_ref(v___x_5556_);
v___x_5557_ = l_Lean_mkAppN(v___x_5556_, v_args1_5546_);
v___x_5558_ = l_Lean_mkAppN(v___x_5556_, v_args2_5550_);
lean_inc_ref(v___x_5558_);
lean_inc_ref(v___x_5557_);
v___x_5559_ = l_Lean_Meta_mkEqHEq(v___x_5557_, v___x_5558_, v___y_5551_, v___y_5552_, v___y_5553_, v___y_5554_);
if (lean_obj_tag(v___x_5559_) == 0)
{
lean_object* v_a_5560_; lean_object* v___x_5561_; uint8_t v___x_5562_; lean_object* v___x_5563_; 
v_a_5560_ = lean_ctor_get(v___x_5559_, 0);
lean_inc(v_a_5560_);
lean_dec_ref(v___x_5559_);
lean_inc_ref_n(v_args2_5550_, 2);
v___x_5561_ = l_Array_toSubarray___redArg(v_args2_5550_, v___x_5547_, v_numParams_5548_);
v___x_5562_ = 1;
v___x_5563_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v_args1_5546_, v_args2_5550_, v___x_5562_, v___y_5551_, v___y_5552_, v___y_5553_, v___y_5554_);
if (lean_obj_tag(v___x_5563_) == 0)
{
lean_object* v_a_5564_; lean_object* v___x_5566_; uint8_t v_isShared_5567_; uint8_t v_isSharedCheck_5684_; 
v_a_5564_ = lean_ctor_get(v___x_5563_, 0);
v_isSharedCheck_5684_ = !lean_is_exclusive(v___x_5563_);
if (v_isSharedCheck_5684_ == 0)
{
v___x_5566_ = v___x_5563_;
v_isShared_5567_ = v_isSharedCheck_5684_;
goto v_resetjp_5565_;
}
else
{
lean_inc(v_a_5564_);
lean_dec(v___x_5563_);
v___x_5566_ = lean_box(0);
v_isShared_5567_ = v_isSharedCheck_5684_;
goto v_resetjp_5565_;
}
v_resetjp_5565_:
{
lean_object* v___x_5568_; 
v___x_5568_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f(v_a_5564_);
if (lean_obj_tag(v___x_5568_) == 1)
{
lean_object* v_val_5569_; lean_object* v___x_5570_; 
lean_del_object(v___x_5566_);
v_val_5569_ = lean_ctor_get(v___x_5568_, 0);
lean_inc(v_val_5569_);
lean_dec_ref(v___x_5568_);
v___x_5570_ = l_Lean_mkArrow(v_a_5560_, v_val_5569_, v___y_5553_, v___y_5554_);
if (lean_obj_tag(v___x_5570_) == 0)
{
lean_object* v_a_5571_; lean_object* v___x_5572_; 
v_a_5571_ = lean_ctor_get(v___x_5570_, 0);
lean_inc(v_a_5571_);
lean_dec_ref(v___x_5570_);
v___x_5572_ = l_Lean_Meta_getCtorAppIndices_x3f(v___x_5557_, v___y_5551_, v___y_5552_, v___y_5553_, v___y_5554_);
if (lean_obj_tag(v___x_5572_) == 0)
{
lean_object* v_a_5573_; lean_object* v___x_5575_; uint8_t v_isShared_5576_; uint8_t v_isSharedCheck_5663_; 
v_a_5573_ = lean_ctor_get(v___x_5572_, 0);
v_isSharedCheck_5663_ = !lean_is_exclusive(v___x_5572_);
if (v_isSharedCheck_5663_ == 0)
{
v___x_5575_ = v___x_5572_;
v_isShared_5576_ = v_isSharedCheck_5663_;
goto v_resetjp_5574_;
}
else
{
lean_inc(v_a_5573_);
lean_dec(v___x_5572_);
v___x_5575_ = lean_box(0);
v_isShared_5576_ = v_isSharedCheck_5663_;
goto v_resetjp_5574_;
}
v_resetjp_5574_:
{
if (lean_obj_tag(v_a_5573_) == 1)
{
lean_object* v_val_5577_; lean_object* v___x_5578_; 
lean_del_object(v___x_5575_);
v_val_5577_ = lean_ctor_get(v_a_5573_, 0);
lean_inc(v_val_5577_);
lean_dec_ref(v_a_5573_);
v___x_5578_ = l_Lean_Meta_getCtorAppIndices_x3f(v___x_5558_, v___y_5551_, v___y_5552_, v___y_5553_, v___y_5554_);
if (lean_obj_tag(v___x_5578_) == 0)
{
lean_object* v_a_5579_; lean_object* v___x_5581_; uint8_t v_isShared_5582_; uint8_t v_isSharedCheck_5650_; 
v_a_5579_ = lean_ctor_get(v___x_5578_, 0);
v_isSharedCheck_5650_ = !lean_is_exclusive(v___x_5578_);
if (v_isSharedCheck_5650_ == 0)
{
v___x_5581_ = v___x_5578_;
v_isShared_5582_ = v_isSharedCheck_5650_;
goto v_resetjp_5580_;
}
else
{
lean_inc(v_a_5579_);
lean_dec(v___x_5578_);
v___x_5581_ = lean_box(0);
v_isShared_5582_ = v_isSharedCheck_5650_;
goto v_resetjp_5580_;
}
v_resetjp_5580_:
{
if (lean_obj_tag(v_a_5579_) == 1)
{
lean_object* v_val_5583_; lean_object* v___x_5585_; uint8_t v_isShared_5586_; uint8_t v_isSharedCheck_5645_; 
lean_del_object(v___x_5581_);
v_val_5583_ = lean_ctor_get(v_a_5579_, 0);
v_isSharedCheck_5645_ = !lean_is_exclusive(v_a_5579_);
if (v_isSharedCheck_5645_ == 0)
{
v___x_5585_ = v_a_5579_;
v_isShared_5586_ = v_isSharedCheck_5645_;
goto v_resetjp_5584_;
}
else
{
lean_inc(v_val_5583_);
lean_dec(v_a_5579_);
v___x_5585_ = lean_box(0);
v_isShared_5586_ = v_isSharedCheck_5645_;
goto v_resetjp_5584_;
}
v_resetjp_5584_:
{
lean_object* v___x_5587_; lean_object* v___x_5588_; lean_object* v___x_5589_; lean_object* v___x_5590_; uint8_t v___x_5591_; lean_object* v___x_5592_; 
v___x_5587_ = l_Subarray_copy___redArg(v___x_5549_);
v___x_5588_ = l_Array_append___redArg(v___x_5587_, v_val_5577_);
v___x_5589_ = l_Subarray_copy___redArg(v___x_5561_);
v___x_5590_ = l_Array_append___redArg(v___x_5589_, v_val_5583_);
lean_dec(v_val_5583_);
v___x_5591_ = 0;
v___x_5592_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v___x_5588_, v___x_5590_, v___x_5591_, v___y_5551_, v___y_5552_, v___y_5553_, v___y_5554_);
lean_dec_ref(v___x_5588_);
if (lean_obj_tag(v___x_5592_) == 0)
{
lean_object* v_a_5593_; lean_object* v___x_5594_; 
v_a_5593_ = lean_ctor_get(v___x_5592_, 0);
lean_inc(v_a_5593_);
lean_dec_ref(v___x_5592_);
v___x_5594_ = l_Lean_mkArrowN(v_a_5593_, v_a_5571_, v___y_5553_, v___y_5554_);
lean_dec(v_a_5593_);
if (lean_obj_tag(v___x_5594_) == 0)
{
lean_object* v_a_5595_; uint8_t v___x_5596_; lean_object* v___x_5597_; 
v_a_5595_ = lean_ctor_get(v___x_5594_, 0);
lean_inc(v_a_5595_);
lean_dec_ref(v___x_5594_);
v___x_5596_ = 1;
v___x_5597_ = l_Lean_Meta_mkForallFVars(v_args2_5550_, v_a_5595_, v___x_5591_, v___x_5562_, v___x_5562_, v___x_5596_, v___y_5551_, v___y_5552_, v___y_5553_, v___y_5554_);
lean_dec_ref(v_args2_5550_);
if (lean_obj_tag(v___x_5597_) == 0)
{
lean_object* v_a_5598_; lean_object* v___x_5599_; 
v_a_5598_ = lean_ctor_get(v___x_5597_, 0);
lean_inc(v_a_5598_);
lean_dec_ref(v___x_5597_);
v___x_5599_ = l_Lean_Meta_mkForallFVars(v_args1_5546_, v_a_5598_, v___x_5591_, v___x_5562_, v___x_5562_, v___x_5596_, v___y_5551_, v___y_5552_, v___y_5553_, v___y_5554_);
if (lean_obj_tag(v___x_5599_) == 0)
{
lean_object* v_a_5600_; lean_object* v___x_5602_; uint8_t v_isShared_5603_; uint8_t v_isSharedCheck_5612_; 
v_a_5600_ = lean_ctor_get(v___x_5599_, 0);
v_isSharedCheck_5612_ = !lean_is_exclusive(v___x_5599_);
if (v_isSharedCheck_5612_ == 0)
{
v___x_5602_ = v___x_5599_;
v_isShared_5603_ = v_isSharedCheck_5612_;
goto v_resetjp_5601_;
}
else
{
lean_inc(v_a_5600_);
lean_dec(v___x_5599_);
v___x_5602_ = lean_box(0);
v_isShared_5603_ = v_isSharedCheck_5612_;
goto v_resetjp_5601_;
}
v_resetjp_5601_:
{
lean_object* v___x_5604_; lean_object* v___x_5605_; lean_object* v___x_5607_; 
v___x_5604_ = lean_array_get_size(v_val_5577_);
lean_dec(v_val_5577_);
v___x_5605_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5605_, 0, v_a_5600_);
lean_ctor_set(v___x_5605_, 1, v_us_5545_);
lean_ctor_set(v___x_5605_, 2, v___x_5604_);
if (v_isShared_5586_ == 0)
{
lean_ctor_set(v___x_5585_, 0, v___x_5605_);
v___x_5607_ = v___x_5585_;
goto v_reusejp_5606_;
}
else
{
lean_object* v_reuseFailAlloc_5611_; 
v_reuseFailAlloc_5611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5611_, 0, v___x_5605_);
v___x_5607_ = v_reuseFailAlloc_5611_;
goto v_reusejp_5606_;
}
v_reusejp_5606_:
{
lean_object* v___x_5609_; 
if (v_isShared_5603_ == 0)
{
lean_ctor_set(v___x_5602_, 0, v___x_5607_);
v___x_5609_ = v___x_5602_;
goto v_reusejp_5608_;
}
else
{
lean_object* v_reuseFailAlloc_5610_; 
v_reuseFailAlloc_5610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5610_, 0, v___x_5607_);
v___x_5609_ = v_reuseFailAlloc_5610_;
goto v_reusejp_5608_;
}
v_reusejp_5608_:
{
return v___x_5609_;
}
}
}
}
else
{
lean_object* v_a_5613_; lean_object* v___x_5615_; uint8_t v_isShared_5616_; uint8_t v_isSharedCheck_5620_; 
lean_del_object(v___x_5585_);
lean_dec(v_val_5577_);
lean_dec(v_us_5545_);
v_a_5613_ = lean_ctor_get(v___x_5599_, 0);
v_isSharedCheck_5620_ = !lean_is_exclusive(v___x_5599_);
if (v_isSharedCheck_5620_ == 0)
{
v___x_5615_ = v___x_5599_;
v_isShared_5616_ = v_isSharedCheck_5620_;
goto v_resetjp_5614_;
}
else
{
lean_inc(v_a_5613_);
lean_dec(v___x_5599_);
v___x_5615_ = lean_box(0);
v_isShared_5616_ = v_isSharedCheck_5620_;
goto v_resetjp_5614_;
}
v_resetjp_5614_:
{
lean_object* v___x_5618_; 
if (v_isShared_5616_ == 0)
{
v___x_5618_ = v___x_5615_;
goto v_reusejp_5617_;
}
else
{
lean_object* v_reuseFailAlloc_5619_; 
v_reuseFailAlloc_5619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5619_, 0, v_a_5613_);
v___x_5618_ = v_reuseFailAlloc_5619_;
goto v_reusejp_5617_;
}
v_reusejp_5617_:
{
return v___x_5618_;
}
}
}
}
else
{
lean_object* v_a_5621_; lean_object* v___x_5623_; uint8_t v_isShared_5624_; uint8_t v_isSharedCheck_5628_; 
lean_del_object(v___x_5585_);
lean_dec(v_val_5577_);
lean_dec(v_us_5545_);
v_a_5621_ = lean_ctor_get(v___x_5597_, 0);
v_isSharedCheck_5628_ = !lean_is_exclusive(v___x_5597_);
if (v_isSharedCheck_5628_ == 0)
{
v___x_5623_ = v___x_5597_;
v_isShared_5624_ = v_isSharedCheck_5628_;
goto v_resetjp_5622_;
}
else
{
lean_inc(v_a_5621_);
lean_dec(v___x_5597_);
v___x_5623_ = lean_box(0);
v_isShared_5624_ = v_isSharedCheck_5628_;
goto v_resetjp_5622_;
}
v_resetjp_5622_:
{
lean_object* v___x_5626_; 
if (v_isShared_5624_ == 0)
{
v___x_5626_ = v___x_5623_;
goto v_reusejp_5625_;
}
else
{
lean_object* v_reuseFailAlloc_5627_; 
v_reuseFailAlloc_5627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5627_, 0, v_a_5621_);
v___x_5626_ = v_reuseFailAlloc_5627_;
goto v_reusejp_5625_;
}
v_reusejp_5625_:
{
return v___x_5626_;
}
}
}
}
else
{
lean_object* v_a_5629_; lean_object* v___x_5631_; uint8_t v_isShared_5632_; uint8_t v_isSharedCheck_5636_; 
lean_del_object(v___x_5585_);
lean_dec(v_val_5577_);
lean_dec_ref(v_args2_5550_);
lean_dec(v_us_5545_);
v_a_5629_ = lean_ctor_get(v___x_5594_, 0);
v_isSharedCheck_5636_ = !lean_is_exclusive(v___x_5594_);
if (v_isSharedCheck_5636_ == 0)
{
v___x_5631_ = v___x_5594_;
v_isShared_5632_ = v_isSharedCheck_5636_;
goto v_resetjp_5630_;
}
else
{
lean_inc(v_a_5629_);
lean_dec(v___x_5594_);
v___x_5631_ = lean_box(0);
v_isShared_5632_ = v_isSharedCheck_5636_;
goto v_resetjp_5630_;
}
v_resetjp_5630_:
{
lean_object* v___x_5634_; 
if (v_isShared_5632_ == 0)
{
v___x_5634_ = v___x_5631_;
goto v_reusejp_5633_;
}
else
{
lean_object* v_reuseFailAlloc_5635_; 
v_reuseFailAlloc_5635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5635_, 0, v_a_5629_);
v___x_5634_ = v_reuseFailAlloc_5635_;
goto v_reusejp_5633_;
}
v_reusejp_5633_:
{
return v___x_5634_;
}
}
}
}
else
{
lean_object* v_a_5637_; lean_object* v___x_5639_; uint8_t v_isShared_5640_; uint8_t v_isSharedCheck_5644_; 
lean_del_object(v___x_5585_);
lean_dec(v_val_5577_);
lean_dec(v_a_5571_);
lean_dec_ref(v_args2_5550_);
lean_dec(v_us_5545_);
v_a_5637_ = lean_ctor_get(v___x_5592_, 0);
v_isSharedCheck_5644_ = !lean_is_exclusive(v___x_5592_);
if (v_isSharedCheck_5644_ == 0)
{
v___x_5639_ = v___x_5592_;
v_isShared_5640_ = v_isSharedCheck_5644_;
goto v_resetjp_5638_;
}
else
{
lean_inc(v_a_5637_);
lean_dec(v___x_5592_);
v___x_5639_ = lean_box(0);
v_isShared_5640_ = v_isSharedCheck_5644_;
goto v_resetjp_5638_;
}
v_resetjp_5638_:
{
lean_object* v___x_5642_; 
if (v_isShared_5640_ == 0)
{
v___x_5642_ = v___x_5639_;
goto v_reusejp_5641_;
}
else
{
lean_object* v_reuseFailAlloc_5643_; 
v_reuseFailAlloc_5643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5643_, 0, v_a_5637_);
v___x_5642_ = v_reuseFailAlloc_5643_;
goto v_reusejp_5641_;
}
v_reusejp_5641_:
{
return v___x_5642_;
}
}
}
}
}
else
{
lean_object* v___x_5646_; lean_object* v___x_5648_; 
lean_dec(v_a_5579_);
lean_dec(v_val_5577_);
lean_dec(v_a_5571_);
lean_dec_ref(v___x_5561_);
lean_dec_ref(v_args2_5550_);
lean_dec_ref(v___x_5549_);
lean_dec(v_us_5545_);
v___x_5646_ = lean_box(0);
if (v_isShared_5582_ == 0)
{
lean_ctor_set(v___x_5581_, 0, v___x_5646_);
v___x_5648_ = v___x_5581_;
goto v_reusejp_5647_;
}
else
{
lean_object* v_reuseFailAlloc_5649_; 
v_reuseFailAlloc_5649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5649_, 0, v___x_5646_);
v___x_5648_ = v_reuseFailAlloc_5649_;
goto v_reusejp_5647_;
}
v_reusejp_5647_:
{
return v___x_5648_;
}
}
}
}
else
{
lean_object* v_a_5651_; lean_object* v___x_5653_; uint8_t v_isShared_5654_; uint8_t v_isSharedCheck_5658_; 
lean_dec(v_val_5577_);
lean_dec(v_a_5571_);
lean_dec_ref(v___x_5561_);
lean_dec_ref(v_args2_5550_);
lean_dec_ref(v___x_5549_);
lean_dec(v_us_5545_);
v_a_5651_ = lean_ctor_get(v___x_5578_, 0);
v_isSharedCheck_5658_ = !lean_is_exclusive(v___x_5578_);
if (v_isSharedCheck_5658_ == 0)
{
v___x_5653_ = v___x_5578_;
v_isShared_5654_ = v_isSharedCheck_5658_;
goto v_resetjp_5652_;
}
else
{
lean_inc(v_a_5651_);
lean_dec(v___x_5578_);
v___x_5653_ = lean_box(0);
v_isShared_5654_ = v_isSharedCheck_5658_;
goto v_resetjp_5652_;
}
v_resetjp_5652_:
{
lean_object* v___x_5656_; 
if (v_isShared_5654_ == 0)
{
v___x_5656_ = v___x_5653_;
goto v_reusejp_5655_;
}
else
{
lean_object* v_reuseFailAlloc_5657_; 
v_reuseFailAlloc_5657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5657_, 0, v_a_5651_);
v___x_5656_ = v_reuseFailAlloc_5657_;
goto v_reusejp_5655_;
}
v_reusejp_5655_:
{
return v___x_5656_;
}
}
}
}
else
{
lean_object* v___x_5659_; lean_object* v___x_5661_; 
lean_dec(v_a_5573_);
lean_dec(v_a_5571_);
lean_dec_ref(v___x_5561_);
lean_dec_ref(v___x_5558_);
lean_dec_ref(v_args2_5550_);
lean_dec_ref(v___x_5549_);
lean_dec(v_us_5545_);
v___x_5659_ = lean_box(0);
if (v_isShared_5576_ == 0)
{
lean_ctor_set(v___x_5575_, 0, v___x_5659_);
v___x_5661_ = v___x_5575_;
goto v_reusejp_5660_;
}
else
{
lean_object* v_reuseFailAlloc_5662_; 
v_reuseFailAlloc_5662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5662_, 0, v___x_5659_);
v___x_5661_ = v_reuseFailAlloc_5662_;
goto v_reusejp_5660_;
}
v_reusejp_5660_:
{
return v___x_5661_;
}
}
}
}
else
{
lean_object* v_a_5664_; lean_object* v___x_5666_; uint8_t v_isShared_5667_; uint8_t v_isSharedCheck_5671_; 
lean_dec(v_a_5571_);
lean_dec_ref(v___x_5561_);
lean_dec_ref(v___x_5558_);
lean_dec_ref(v_args2_5550_);
lean_dec_ref(v___x_5549_);
lean_dec(v_us_5545_);
v_a_5664_ = lean_ctor_get(v___x_5572_, 0);
v_isSharedCheck_5671_ = !lean_is_exclusive(v___x_5572_);
if (v_isSharedCheck_5671_ == 0)
{
v___x_5666_ = v___x_5572_;
v_isShared_5667_ = v_isSharedCheck_5671_;
goto v_resetjp_5665_;
}
else
{
lean_inc(v_a_5664_);
lean_dec(v___x_5572_);
v___x_5666_ = lean_box(0);
v_isShared_5667_ = v_isSharedCheck_5671_;
goto v_resetjp_5665_;
}
v_resetjp_5665_:
{
lean_object* v___x_5669_; 
if (v_isShared_5667_ == 0)
{
v___x_5669_ = v___x_5666_;
goto v_reusejp_5668_;
}
else
{
lean_object* v_reuseFailAlloc_5670_; 
v_reuseFailAlloc_5670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5670_, 0, v_a_5664_);
v___x_5669_ = v_reuseFailAlloc_5670_;
goto v_reusejp_5668_;
}
v_reusejp_5668_:
{
return v___x_5669_;
}
}
}
}
else
{
lean_object* v_a_5672_; lean_object* v___x_5674_; uint8_t v_isShared_5675_; uint8_t v_isSharedCheck_5679_; 
lean_dec_ref(v___x_5561_);
lean_dec_ref(v___x_5558_);
lean_dec_ref(v___x_5557_);
lean_dec_ref(v_args2_5550_);
lean_dec_ref(v___x_5549_);
lean_dec(v_us_5545_);
v_a_5672_ = lean_ctor_get(v___x_5570_, 0);
v_isSharedCheck_5679_ = !lean_is_exclusive(v___x_5570_);
if (v_isSharedCheck_5679_ == 0)
{
v___x_5674_ = v___x_5570_;
v_isShared_5675_ = v_isSharedCheck_5679_;
goto v_resetjp_5673_;
}
else
{
lean_inc(v_a_5672_);
lean_dec(v___x_5570_);
v___x_5674_ = lean_box(0);
v_isShared_5675_ = v_isSharedCheck_5679_;
goto v_resetjp_5673_;
}
v_resetjp_5673_:
{
lean_object* v___x_5677_; 
if (v_isShared_5675_ == 0)
{
v___x_5677_ = v___x_5674_;
goto v_reusejp_5676_;
}
else
{
lean_object* v_reuseFailAlloc_5678_; 
v_reuseFailAlloc_5678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5678_, 0, v_a_5672_);
v___x_5677_ = v_reuseFailAlloc_5678_;
goto v_reusejp_5676_;
}
v_reusejp_5676_:
{
return v___x_5677_;
}
}
}
}
else
{
lean_object* v___x_5680_; lean_object* v___x_5682_; 
lean_dec(v___x_5568_);
lean_dec_ref(v___x_5561_);
lean_dec(v_a_5560_);
lean_dec_ref(v___x_5558_);
lean_dec_ref(v___x_5557_);
lean_dec_ref(v_args2_5550_);
lean_dec_ref(v___x_5549_);
lean_dec(v_us_5545_);
v___x_5680_ = lean_box(0);
if (v_isShared_5567_ == 0)
{
lean_ctor_set(v___x_5566_, 0, v___x_5680_);
v___x_5682_ = v___x_5566_;
goto v_reusejp_5681_;
}
else
{
lean_object* v_reuseFailAlloc_5683_; 
v_reuseFailAlloc_5683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5683_, 0, v___x_5680_);
v___x_5682_ = v_reuseFailAlloc_5683_;
goto v_reusejp_5681_;
}
v_reusejp_5681_:
{
return v___x_5682_;
}
}
}
}
else
{
lean_object* v_a_5685_; lean_object* v___x_5687_; uint8_t v_isShared_5688_; uint8_t v_isSharedCheck_5692_; 
lean_dec_ref(v___x_5561_);
lean_dec(v_a_5560_);
lean_dec_ref(v___x_5558_);
lean_dec_ref(v___x_5557_);
lean_dec_ref(v_args2_5550_);
lean_dec_ref(v___x_5549_);
lean_dec(v_us_5545_);
v_a_5685_ = lean_ctor_get(v___x_5563_, 0);
v_isSharedCheck_5692_ = !lean_is_exclusive(v___x_5563_);
if (v_isSharedCheck_5692_ == 0)
{
v___x_5687_ = v___x_5563_;
v_isShared_5688_ = v_isSharedCheck_5692_;
goto v_resetjp_5686_;
}
else
{
lean_inc(v_a_5685_);
lean_dec(v___x_5563_);
v___x_5687_ = lean_box(0);
v_isShared_5688_ = v_isSharedCheck_5692_;
goto v_resetjp_5686_;
}
v_resetjp_5686_:
{
lean_object* v___x_5690_; 
if (v_isShared_5688_ == 0)
{
v___x_5690_ = v___x_5687_;
goto v_reusejp_5689_;
}
else
{
lean_object* v_reuseFailAlloc_5691_; 
v_reuseFailAlloc_5691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5691_, 0, v_a_5685_);
v___x_5690_ = v_reuseFailAlloc_5691_;
goto v_reusejp_5689_;
}
v_reusejp_5689_:
{
return v___x_5690_;
}
}
}
}
else
{
lean_object* v_a_5693_; lean_object* v___x_5695_; uint8_t v_isShared_5696_; uint8_t v_isSharedCheck_5700_; 
lean_dec_ref(v___x_5558_);
lean_dec_ref(v___x_5557_);
lean_dec_ref(v_args2_5550_);
lean_dec_ref(v___x_5549_);
lean_dec(v_numParams_5548_);
lean_dec(v___x_5547_);
lean_dec(v_us_5545_);
v_a_5693_ = lean_ctor_get(v___x_5559_, 0);
v_isSharedCheck_5700_ = !lean_is_exclusive(v___x_5559_);
if (v_isSharedCheck_5700_ == 0)
{
v___x_5695_ = v___x_5559_;
v_isShared_5696_ = v_isSharedCheck_5700_;
goto v_resetjp_5694_;
}
else
{
lean_inc(v_a_5693_);
lean_dec(v___x_5559_);
v___x_5695_ = lean_box(0);
v_isShared_5696_ = v_isSharedCheck_5700_;
goto v_resetjp_5694_;
}
v_resetjp_5694_:
{
lean_object* v___x_5698_; 
if (v_isShared_5696_ == 0)
{
v___x_5698_ = v___x_5695_;
goto v_reusejp_5697_;
}
else
{
lean_object* v_reuseFailAlloc_5699_; 
v_reuseFailAlloc_5699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5699_, 0, v_a_5693_);
v___x_5698_ = v_reuseFailAlloc_5699_;
goto v_reusejp_5697_;
}
v_reusejp_5697_:
{
return v___x_5698_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0___boxed(lean_object* v_name_5701_, lean_object* v_us_5702_, lean_object* v_args1_5703_, lean_object* v___x_5704_, lean_object* v_numParams_5705_, lean_object* v___x_5706_, lean_object* v_args2_5707_, lean_object* v___y_5708_, lean_object* v___y_5709_, lean_object* v___y_5710_, lean_object* v___y_5711_, lean_object* v___y_5712_){
_start:
{
lean_object* v_res_5713_; 
v_res_5713_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0(v_name_5701_, v_us_5702_, v_args1_5703_, v___x_5704_, v_numParams_5705_, v___x_5706_, v_args2_5707_, v___y_5708_, v___y_5709_, v___y_5710_, v___y_5711_);
lean_dec(v___y_5711_);
lean_dec_ref(v___y_5710_);
lean_dec(v___y_5709_);
lean_dec_ref(v___y_5708_);
lean_dec_ref(v_args1_5703_);
return v_res_5713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1(lean_object* v_numParams_5714_, lean_object* v_name_5715_, lean_object* v_us_5716_, lean_object* v_ctorVal_5717_, lean_object* v_a_5718_, lean_object* v_args1_5719_, lean_object* v_x_5720_, lean_object* v___y_5721_, lean_object* v___y_5722_, lean_object* v___y_5723_, lean_object* v___y_5724_){
_start:
{
lean_object* v___x_5726_; lean_object* v___x_5727_; lean_object* v___f_5728_; lean_object* v___x_5729_; lean_object* v___x_5730_; lean_object* v___x_5731_; 
v___x_5726_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_5714_);
lean_inc_ref_n(v_args1_5719_, 3);
v___x_5727_ = l_Array_toSubarray___redArg(v_args1_5719_, v___x_5726_, v_numParams_5714_);
v___f_5728_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0___boxed), 12, 6);
lean_closure_set(v___f_5728_, 0, v_name_5715_);
lean_closure_set(v___f_5728_, 1, v_us_5716_);
lean_closure_set(v___f_5728_, 2, v_args1_5719_);
lean_closure_set(v___f_5728_, 3, v___x_5726_);
lean_closure_set(v___f_5728_, 4, v_numParams_5714_);
lean_closure_set(v___f_5728_, 5, v___x_5727_);
v___x_5729_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_5730_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___boxed), 11, 6);
lean_closure_set(v___x_5730_, 0, v_ctorVal_5717_);
lean_closure_set(v___x_5730_, 1, v_args1_5719_);
lean_closure_set(v___x_5730_, 2, v___f_5728_);
lean_closure_set(v___x_5730_, 3, v___x_5726_);
lean_closure_set(v___x_5730_, 4, v_a_5718_);
lean_closure_set(v___x_5730_, 5, v___x_5729_);
v___x_5731_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v_args1_5719_, v___x_5730_, v___y_5721_, v___y_5722_, v___y_5723_, v___y_5724_);
return v___x_5731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1___boxed(lean_object* v_numParams_5732_, lean_object* v_name_5733_, lean_object* v_us_5734_, lean_object* v_ctorVal_5735_, lean_object* v_a_5736_, lean_object* v_args1_5737_, lean_object* v_x_5738_, lean_object* v___y_5739_, lean_object* v___y_5740_, lean_object* v___y_5741_, lean_object* v___y_5742_, lean_object* v___y_5743_){
_start:
{
lean_object* v_res_5744_; 
v_res_5744_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1(v_numParams_5732_, v_name_5733_, v_us_5734_, v_ctorVal_5735_, v_a_5736_, v_args1_5737_, v_x_5738_, v___y_5739_, v___y_5740_, v___y_5741_, v___y_5742_);
lean_dec(v___y_5742_);
lean_dec_ref(v___y_5741_);
lean_dec(v___y_5740_);
lean_dec_ref(v___y_5739_);
lean_dec_ref(v_x_5738_);
return v_res_5744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(lean_object* v_ctorVal_5745_, lean_object* v_a_5746_, lean_object* v_a_5747_, lean_object* v_a_5748_, lean_object* v_a_5749_){
_start:
{
lean_object* v_toConstantVal_5751_; lean_object* v_numParams_5752_; lean_object* v_name_5753_; lean_object* v_levelParams_5754_; lean_object* v_type_5755_; lean_object* v___x_5756_; 
v_toConstantVal_5751_ = lean_ctor_get(v_ctorVal_5745_, 0);
v_numParams_5752_ = lean_ctor_get(v_ctorVal_5745_, 3);
lean_inc(v_numParams_5752_);
v_name_5753_ = lean_ctor_get(v_toConstantVal_5751_, 0);
lean_inc(v_name_5753_);
v_levelParams_5754_ = lean_ctor_get(v_toConstantVal_5751_, 1);
v_type_5755_ = lean_ctor_get(v_toConstantVal_5751_, 2);
lean_inc_ref(v_type_5755_);
v___x_5756_ = l_Lean_Meta_elimOptParam(v_type_5755_, v_a_5748_, v_a_5749_);
if (lean_obj_tag(v___x_5756_) == 0)
{
lean_object* v_a_5757_; lean_object* v___x_5758_; lean_object* v_us_5759_; lean_object* v___f_5760_; uint8_t v___x_5761_; lean_object* v___x_5762_; 
v_a_5757_ = lean_ctor_get(v___x_5756_, 0);
lean_inc_n(v_a_5757_, 2);
lean_dec_ref(v___x_5756_);
v___x_5758_ = lean_box(0);
lean_inc(v_levelParams_5754_);
v_us_5759_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(v_levelParams_5754_, v___x_5758_);
v___f_5760_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1___boxed), 12, 5);
lean_closure_set(v___f_5760_, 0, v_numParams_5752_);
lean_closure_set(v___f_5760_, 1, v_name_5753_);
lean_closure_set(v___f_5760_, 2, v_us_5759_);
lean_closure_set(v___f_5760_, 3, v_ctorVal_5745_);
lean_closure_set(v___f_5760_, 4, v_a_5757_);
v___x_5761_ = 0;
v___x_5762_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_a_5757_, v___f_5760_, v___x_5761_, v_a_5746_, v_a_5747_, v_a_5748_, v_a_5749_);
return v___x_5762_;
}
else
{
lean_object* v_a_5763_; lean_object* v___x_5765_; uint8_t v_isShared_5766_; uint8_t v_isSharedCheck_5770_; 
lean_dec(v_name_5753_);
lean_dec(v_numParams_5752_);
lean_dec_ref(v_ctorVal_5745_);
v_a_5763_ = lean_ctor_get(v___x_5756_, 0);
v_isSharedCheck_5770_ = !lean_is_exclusive(v___x_5756_);
if (v_isSharedCheck_5770_ == 0)
{
v___x_5765_ = v___x_5756_;
v_isShared_5766_ = v_isSharedCheck_5770_;
goto v_resetjp_5764_;
}
else
{
lean_inc(v_a_5763_);
lean_dec(v___x_5756_);
v___x_5765_ = lean_box(0);
v_isShared_5766_ = v_isSharedCheck_5770_;
goto v_resetjp_5764_;
}
v_resetjp_5764_:
{
lean_object* v___x_5768_; 
if (v_isShared_5766_ == 0)
{
v___x_5768_ = v___x_5765_;
goto v_reusejp_5767_;
}
else
{
lean_object* v_reuseFailAlloc_5769_; 
v_reuseFailAlloc_5769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5769_, 0, v_a_5763_);
v___x_5768_ = v_reuseFailAlloc_5769_;
goto v_reusejp_5767_;
}
v_reusejp_5767_:
{
return v___x_5768_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___boxed(lean_object* v_ctorVal_5771_, lean_object* v_a_5772_, lean_object* v_a_5773_, lean_object* v_a_5774_, lean_object* v_a_5775_, lean_object* v_a_5776_){
_start:
{
lean_object* v_res_5777_; 
v_res_5777_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(v_ctorVal_5771_, v_a_5772_, v_a_5773_, v_a_5774_, v_a_5775_);
lean_dec(v_a_5775_);
lean_dec_ref(v_a_5774_);
lean_dec(v_a_5773_);
lean_dec_ref(v_a_5772_);
return v_res_5777_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1(void){
_start:
{
lean_object* v___x_5779_; lean_object* v___x_5780_; 
v___x_5779_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__0));
v___x_5780_ = l_Lean_stringToMessageData(v___x_5779_);
return v___x_5780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(lean_object* v_ctorVal_5781_, lean_object* v_a_5782_, lean_object* v_a_5783_, lean_object* v_a_5784_, lean_object* v_a_5785_){
_start:
{
lean_object* v_toConstantVal_5787_; lean_object* v_name_5788_; lean_object* v___x_5789_; lean_object* v___x_5790_; lean_object* v___x_5791_; lean_object* v___x_5792_; lean_object* v___x_5793_; lean_object* v___x_5794_; 
v_toConstantVal_5787_ = lean_ctor_get(v_ctorVal_5781_, 0);
lean_inc_ref(v_toConstantVal_5787_);
lean_dec_ref(v_ctorVal_5781_);
v_name_5788_ = lean_ctor_get(v_toConstantVal_5787_, 0);
lean_inc(v_name_5788_);
lean_dec_ref(v_toConstantVal_5787_);
v___x_5789_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1);
v___x_5790_ = l_Lean_MessageData_ofName(v_name_5788_);
v___x_5791_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5791_, 0, v___x_5789_);
lean_ctor_set(v___x_5791_, 1, v___x_5790_);
v___x_5792_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_5793_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5793_, 0, v___x_5791_);
lean_ctor_set(v___x_5793_, 1, v___x_5792_);
v___x_5794_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_5793_, v_a_5782_, v_a_5783_, v_a_5784_, v_a_5785_);
return v___x_5794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___boxed(lean_object* v_ctorVal_5795_, lean_object* v_a_5796_, lean_object* v_a_5797_, lean_object* v_a_5798_, lean_object* v_a_5799_, lean_object* v_a_5800_){
_start:
{
lean_object* v_res_5801_; 
v_res_5801_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5795_, v_a_5796_, v_a_5797_, v_a_5798_, v_a_5799_);
lean_dec(v_a_5799_);
lean_dec_ref(v_a_5798_);
lean_dec(v_a_5797_);
lean_dec_ref(v_a_5796_);
return v_res_5801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj(lean_object* v_00_u03b1_5802_, lean_object* v_ctorVal_5803_, lean_object* v_a_5804_, lean_object* v_a_5805_, lean_object* v_a_5806_, lean_object* v_a_5807_){
_start:
{
lean_object* v___x_5809_; 
v___x_5809_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5803_, v_a_5804_, v_a_5805_, v_a_5806_, v_a_5807_);
return v___x_5809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___boxed(lean_object* v_00_u03b1_5810_, lean_object* v_ctorVal_5811_, lean_object* v_a_5812_, lean_object* v_a_5813_, lean_object* v_a_5814_, lean_object* v_a_5815_, lean_object* v_a_5816_){
_start:
{
lean_object* v_res_5817_; 
v_res_5817_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj(v_00_u03b1_5810_, v_ctorVal_5811_, v_a_5812_, v_a_5813_, v_a_5814_, v_a_5815_);
lean_dec(v_a_5815_);
lean_dec_ref(v_a_5814_);
lean_dec(v_a_5813_);
lean_dec_ref(v_a_5812_);
return v_res_5817_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(lean_object* v_ctorVal_5823_, size_t v_sz_5824_, size_t v_i_5825_, lean_object* v_bs_5826_, lean_object* v___y_5827_, lean_object* v___y_5828_, lean_object* v___y_5829_, lean_object* v___y_5830_){
_start:
{
uint8_t v___x_5832_; 
v___x_5832_ = lean_usize_dec_lt(v_i_5825_, v_sz_5824_);
if (v___x_5832_ == 0)
{
lean_object* v___x_5833_; 
lean_dec_ref(v_ctorVal_5823_);
v___x_5833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5833_, 0, v_bs_5826_);
return v___x_5833_;
}
else
{
lean_object* v_v_5834_; lean_object* v___x_5835_; 
v_v_5834_ = lean_array_uget_borrowed(v_bs_5826_, v_i_5825_);
lean_inc(v___y_5830_);
lean_inc_ref(v___y_5829_);
lean_inc(v___y_5828_);
lean_inc_ref(v___y_5827_);
lean_inc(v_v_5834_);
v___x_5835_ = lean_infer_type(v_v_5834_, v___y_5827_, v___y_5828_, v___y_5829_, v___y_5830_);
if (lean_obj_tag(v___x_5835_) == 0)
{
lean_object* v_a_5836_; lean_object* v___x_5837_; 
v_a_5836_ = lean_ctor_get(v___x_5835_, 0);
lean_inc(v_a_5836_);
lean_dec_ref(v___x_5835_);
v___x_5837_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_5836_, v___y_5828_);
if (lean_obj_tag(v___x_5837_) == 0)
{
lean_object* v_a_5838_; lean_object* v___x_5839_; lean_object* v_bs_x27_5840_; lean_object* v_a_5842_; lean_object* v___y_5848_; lean_object* v_lhs_5859_; lean_object* v_rhs_5860_; lean_object* v___x_5862_; uint8_t v___x_5863_; 
v_a_5838_ = lean_ctor_get(v___x_5837_, 0);
lean_inc(v_a_5838_);
lean_dec_ref(v___x_5837_);
v___x_5839_ = lean_unsigned_to_nat(0u);
v_bs_x27_5840_ = lean_array_uset(v_bs_5826_, v_i_5825_, v___x_5839_);
v___x_5862_ = l_Lean_Expr_cleanupAnnotations(v_a_5838_);
v___x_5863_ = l_Lean_Expr_isApp(v___x_5862_);
if (v___x_5863_ == 0)
{
lean_object* v___x_5864_; 
lean_dec_ref(v___x_5862_);
lean_inc_ref(v_ctorVal_5823_);
v___x_5864_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5823_, v___y_5827_, v___y_5828_, v___y_5829_, v___y_5830_);
v___y_5848_ = v___x_5864_;
goto v___jp_5847_;
}
else
{
lean_object* v_arg_5865_; lean_object* v___x_5866_; uint8_t v___x_5867_; 
v_arg_5865_ = lean_ctor_get(v___x_5862_, 1);
lean_inc_ref(v_arg_5865_);
v___x_5866_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5862_);
v___x_5867_ = l_Lean_Expr_isApp(v___x_5866_);
if (v___x_5867_ == 0)
{
lean_object* v___x_5868_; 
lean_dec_ref(v___x_5866_);
lean_dec_ref(v_arg_5865_);
lean_inc_ref(v_ctorVal_5823_);
v___x_5868_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5823_, v___y_5827_, v___y_5828_, v___y_5829_, v___y_5830_);
v___y_5848_ = v___x_5868_;
goto v___jp_5847_;
}
else
{
lean_object* v_arg_5869_; lean_object* v___x_5870_; uint8_t v___x_5871_; 
v_arg_5869_ = lean_ctor_get(v___x_5866_, 1);
lean_inc_ref(v_arg_5869_);
v___x_5870_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5866_);
v___x_5871_ = l_Lean_Expr_isApp(v___x_5870_);
if (v___x_5871_ == 0)
{
lean_object* v___x_5872_; 
lean_dec_ref(v___x_5870_);
lean_dec_ref(v_arg_5869_);
lean_dec_ref(v_arg_5865_);
lean_inc_ref(v_ctorVal_5823_);
v___x_5872_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5823_, v___y_5827_, v___y_5828_, v___y_5829_, v___y_5830_);
v___y_5848_ = v___x_5872_;
goto v___jp_5847_;
}
else
{
lean_object* v_arg_5873_; lean_object* v___x_5874_; lean_object* v___x_5875_; uint8_t v___x_5876_; 
v_arg_5873_ = lean_ctor_get(v___x_5870_, 1);
lean_inc_ref(v_arg_5873_);
v___x_5874_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5870_);
v___x_5875_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__0));
v___x_5876_ = l_Lean_Expr_isConstOf(v___x_5874_, v___x_5875_);
if (v___x_5876_ == 0)
{
uint8_t v___x_5877_; 
lean_dec_ref(v_arg_5869_);
v___x_5877_ = l_Lean_Expr_isApp(v___x_5874_);
if (v___x_5877_ == 0)
{
lean_object* v___x_5878_; 
lean_dec_ref(v___x_5874_);
lean_dec_ref(v_arg_5873_);
lean_dec_ref(v_arg_5865_);
lean_inc_ref(v_ctorVal_5823_);
v___x_5878_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5823_, v___y_5827_, v___y_5828_, v___y_5829_, v___y_5830_);
v___y_5848_ = v___x_5878_;
goto v___jp_5847_;
}
else
{
lean_object* v___x_5879_; lean_object* v___x_5880_; uint8_t v___x_5881_; 
v___x_5879_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5874_);
v___x_5880_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__2));
v___x_5881_ = l_Lean_Expr_isConstOf(v___x_5879_, v___x_5880_);
lean_dec_ref(v___x_5879_);
if (v___x_5881_ == 0)
{
lean_object* v___x_5882_; 
lean_dec_ref(v_arg_5873_);
lean_dec_ref(v_arg_5865_);
lean_inc_ref(v_ctorVal_5823_);
v___x_5882_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5823_, v___y_5827_, v___y_5828_, v___y_5829_, v___y_5830_);
v___y_5848_ = v___x_5882_;
goto v___jp_5847_;
}
else
{
v_lhs_5859_ = v_arg_5873_;
v_rhs_5860_ = v_arg_5865_;
goto v___jp_5858_;
}
}
}
else
{
lean_dec_ref(v___x_5874_);
lean_dec_ref(v_arg_5873_);
v_lhs_5859_ = v_arg_5869_;
v_rhs_5860_ = v_arg_5865_;
goto v___jp_5858_;
}
}
}
}
v___jp_5841_:
{
size_t v___x_5843_; size_t v___x_5844_; lean_object* v___x_5845_; 
v___x_5843_ = ((size_t)1ULL);
v___x_5844_ = lean_usize_add(v_i_5825_, v___x_5843_);
v___x_5845_ = lean_array_uset(v_bs_x27_5840_, v_i_5825_, v_a_5842_);
v_i_5825_ = v___x_5844_;
v_bs_5826_ = v___x_5845_;
goto _start;
}
v___jp_5847_:
{
if (lean_obj_tag(v___y_5848_) == 0)
{
lean_object* v_a_5849_; 
v_a_5849_ = lean_ctor_get(v___y_5848_, 0);
lean_inc(v_a_5849_);
lean_dec_ref(v___y_5848_);
v_a_5842_ = v_a_5849_;
goto v___jp_5841_;
}
else
{
lean_object* v_a_5850_; lean_object* v___x_5852_; uint8_t v_isShared_5853_; uint8_t v_isSharedCheck_5857_; 
lean_dec_ref(v_bs_x27_5840_);
lean_dec_ref(v_ctorVal_5823_);
v_a_5850_ = lean_ctor_get(v___y_5848_, 0);
v_isSharedCheck_5857_ = !lean_is_exclusive(v___y_5848_);
if (v_isSharedCheck_5857_ == 0)
{
v___x_5852_ = v___y_5848_;
v_isShared_5853_ = v_isSharedCheck_5857_;
goto v_resetjp_5851_;
}
else
{
lean_inc(v_a_5850_);
lean_dec(v___y_5848_);
v___x_5852_ = lean_box(0);
v_isShared_5853_ = v_isSharedCheck_5857_;
goto v_resetjp_5851_;
}
v_resetjp_5851_:
{
lean_object* v___x_5855_; 
if (v_isShared_5853_ == 0)
{
v___x_5855_ = v___x_5852_;
goto v_reusejp_5854_;
}
else
{
lean_object* v_reuseFailAlloc_5856_; 
v_reuseFailAlloc_5856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5856_, 0, v_a_5850_);
v___x_5855_ = v_reuseFailAlloc_5856_;
goto v_reusejp_5854_;
}
v_reusejp_5854_:
{
return v___x_5855_;
}
}
}
}
v___jp_5858_:
{
lean_object* v___x_5861_; 
v___x_5861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5861_, 0, v_lhs_5859_);
lean_ctor_set(v___x_5861_, 1, v_rhs_5860_);
v_a_5842_ = v___x_5861_;
goto v___jp_5841_;
}
}
else
{
lean_object* v_a_5883_; lean_object* v___x_5885_; uint8_t v_isShared_5886_; uint8_t v_isSharedCheck_5890_; 
lean_dec_ref(v_bs_5826_);
lean_dec_ref(v_ctorVal_5823_);
v_a_5883_ = lean_ctor_get(v___x_5837_, 0);
v_isSharedCheck_5890_ = !lean_is_exclusive(v___x_5837_);
if (v_isSharedCheck_5890_ == 0)
{
v___x_5885_ = v___x_5837_;
v_isShared_5886_ = v_isSharedCheck_5890_;
goto v_resetjp_5884_;
}
else
{
lean_inc(v_a_5883_);
lean_dec(v___x_5837_);
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
lean_dec_ref(v_bs_5826_);
lean_dec_ref(v_ctorVal_5823_);
v_a_5891_ = lean_ctor_get(v___x_5835_, 0);
v_isSharedCheck_5898_ = !lean_is_exclusive(v___x_5835_);
if (v_isSharedCheck_5898_ == 0)
{
v___x_5893_ = v___x_5835_;
v_isShared_5894_ = v_isSharedCheck_5898_;
goto v_resetjp_5892_;
}
else
{
lean_inc(v_a_5891_);
lean_dec(v___x_5835_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___boxed(lean_object* v_ctorVal_5899_, lean_object* v_sz_5900_, lean_object* v_i_5901_, lean_object* v_bs_5902_, lean_object* v___y_5903_, lean_object* v___y_5904_, lean_object* v___y_5905_, lean_object* v___y_5906_, lean_object* v___y_5907_){
_start:
{
size_t v_sz_boxed_5908_; size_t v_i_boxed_5909_; lean_object* v_res_5910_; 
v_sz_boxed_5908_ = lean_unbox_usize(v_sz_5900_);
lean_dec(v_sz_5900_);
v_i_boxed_5909_ = lean_unbox_usize(v_i_5901_);
lean_dec(v_i_5901_);
v_res_5910_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(v_ctorVal_5899_, v_sz_boxed_5908_, v_i_boxed_5909_, v_bs_5902_, v___y_5903_, v___y_5904_, v___y_5905_, v___y_5906_);
lean_dec(v___y_5906_);
lean_dec_ref(v___y_5905_);
lean_dec(v___y_5904_);
lean_dec_ref(v___y_5903_);
return v_res_5910_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5912_; lean_object* v___x_5913_; 
v___x_5912_ = lean_unsigned_to_nat(0u);
v___x_5913_ = l_Lean_Level_ofNat(v___x_5912_);
return v___x_5913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0(lean_object* v_ctorVal_5914_, lean_object* v_us_5915_, lean_object* v_numIndices_5916_, lean_object* v_xs_5917_, lean_object* v_type_5918_, lean_object* v___y_5919_, lean_object* v___y_5920_, lean_object* v___y_5921_, lean_object* v___y_5922_){
_start:
{
lean_object* v_toConstantVal_5924_; lean_object* v_induct_5925_; lean_object* v_numParams_5926_; lean_object* v___x_5927_; lean_object* v_noConfusionName_5928_; lean_object* v___x_5929_; lean_object* v___x_5930_; lean_object* v___x_5931_; lean_object* v_noConfusion_5932_; lean_object* v_noConfusion_5933_; lean_object* v_lower_5935_; lean_object* v_upper_5936_; lean_object* v___x_6043_; lean_object* v___x_6044_; lean_object* v___x_6045_; lean_object* v___x_6046_; lean_object* v_n_6047_; uint8_t v___x_6048_; 
v_toConstantVal_5924_ = lean_ctor_get(v_ctorVal_5914_, 0);
v_induct_5925_ = lean_ctor_get(v_ctorVal_5914_, 1);
v_numParams_5926_ = lean_ctor_get(v_ctorVal_5914_, 3);
v___x_5927_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__0));
lean_inc(v_induct_5925_);
v_noConfusionName_5928_ = l_Lean_Name_str___override(v_induct_5925_, v___x_5927_);
v___x_5929_ = lean_unsigned_to_nat(0u);
v___x_5930_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1);
v___x_5931_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5931_, 0, v___x_5930_);
lean_ctor_set(v___x_5931_, 1, v_us_5915_);
v_noConfusion_5932_ = l_Lean_mkConst(v_noConfusionName_5928_, v___x_5931_);
v_noConfusion_5933_ = l_Lean_Expr_app___override(v_noConfusion_5932_, v_type_5918_);
v___x_6043_ = lean_array_get_size(v_xs_5917_);
v___x_6044_ = lean_nat_sub(v___x_6043_, v_numParams_5926_);
v___x_6045_ = lean_nat_sub(v___x_6044_, v_numIndices_5916_);
lean_dec(v___x_6044_);
v___x_6046_ = lean_unsigned_to_nat(1u);
v_n_6047_ = lean_nat_sub(v___x_6045_, v___x_6046_);
lean_dec(v___x_6045_);
v___x_6048_ = lean_nat_dec_le(v_n_6047_, v___x_5929_);
if (v___x_6048_ == 0)
{
v_lower_5935_ = v_n_6047_;
v_upper_5936_ = v___x_6043_;
goto v___jp_5934_;
}
else
{
lean_dec(v_n_6047_);
v_lower_5935_ = v___x_5929_;
v_upper_5936_ = v___x_6043_;
goto v___jp_5934_;
}
v___jp_5934_:
{
lean_object* v___x_5937_; lean_object* v___x_5938_; lean_object* v_eqs_5939_; size_t v_sz_5940_; size_t v___x_5941_; lean_object* v___x_5942_; 
lean_inc_ref(v_xs_5917_);
v___x_5937_ = l_Array_toSubarray___redArg(v_xs_5917_, v_lower_5935_, v_upper_5936_);
v___x_5938_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v_eqs_5939_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(v___x_5937_, v___x_5938_);
v_sz_5940_ = lean_array_size(v_eqs_5939_);
v___x_5941_ = ((size_t)0ULL);
lean_inc_ref(v_eqs_5939_);
lean_inc_ref(v_ctorVal_5914_);
v___x_5942_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(v_ctorVal_5914_, v_sz_5940_, v___x_5941_, v_eqs_5939_, v___y_5919_, v___y_5920_, v___y_5921_, v___y_5922_);
if (lean_obj_tag(v___x_5942_) == 0)
{
lean_object* v_a_5943_; lean_object* v___x_5944_; lean_object* v_fst_5945_; lean_object* v_snd_5946_; lean_object* v___x_5947_; lean_object* v___x_5948_; lean_object* v___x_5949_; lean_object* v___x_5950_; 
v_a_5943_ = lean_ctor_get(v___x_5942_, 0);
lean_inc(v_a_5943_);
lean_dec_ref(v___x_5942_);
v___x_5944_ = l_Array_unzip___redArg(v_a_5943_);
lean_dec(v_a_5943_);
v_fst_5945_ = lean_ctor_get(v___x_5944_, 0);
lean_inc(v_fst_5945_);
v_snd_5946_ = lean_ctor_get(v___x_5944_, 1);
lean_inc(v_snd_5946_);
lean_dec_ref(v___x_5944_);
v___x_5947_ = l_Lean_mkAppN(v_noConfusion_5933_, v_fst_5945_);
lean_dec(v_fst_5945_);
v___x_5948_ = l_Lean_mkAppN(v___x_5947_, v_snd_5946_);
lean_dec(v_snd_5946_);
v___x_5949_ = l_Lean_mkAppN(v___x_5948_, v_eqs_5939_);
lean_dec_ref(v_eqs_5939_);
lean_inc(v___y_5922_);
lean_inc_ref(v___y_5921_);
lean_inc(v___y_5920_);
lean_inc_ref(v___y_5919_);
lean_inc_ref(v___x_5949_);
v___x_5950_ = lean_infer_type(v___x_5949_, v___y_5919_, v___y_5920_, v___y_5921_, v___y_5922_);
if (lean_obj_tag(v___x_5950_) == 0)
{
lean_object* v_a_5951_; lean_object* v___x_5952_; 
v_a_5951_ = lean_ctor_get(v___x_5950_, 0);
lean_inc(v_a_5951_);
lean_dec_ref(v___x_5950_);
lean_inc(v___y_5922_);
lean_inc_ref(v___y_5921_);
lean_inc(v___y_5920_);
lean_inc_ref(v___y_5919_);
v___x_5952_ = lean_whnf(v_a_5951_, v___y_5919_, v___y_5920_, v___y_5921_, v___y_5922_);
if (lean_obj_tag(v___x_5952_) == 0)
{
lean_object* v_a_5953_; 
v_a_5953_ = lean_ctor_get(v___x_5952_, 0);
lean_inc(v_a_5953_);
lean_dec_ref(v___x_5952_);
if (lean_obj_tag(v_a_5953_) == 7)
{
lean_object* v_binderType_5954_; lean_object* v___x_5955_; lean_object* v___x_5956_; 
lean_inc_ref(v_toConstantVal_5924_);
lean_dec_ref(v_ctorVal_5914_);
v_binderType_5954_ = lean_ctor_get(v_a_5953_, 1);
lean_inc_ref(v_binderType_5954_);
lean_dec_ref(v_a_5953_);
v___x_5955_ = lean_box(0);
v___x_5956_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_binderType_5954_, v___x_5955_, v___y_5919_, v___y_5920_, v___y_5921_, v___y_5922_);
if (lean_obj_tag(v___x_5956_) == 0)
{
lean_object* v_a_5957_; lean_object* v___x_5958_; lean_object* v___x_5959_; 
v_a_5957_ = lean_ctor_get(v___x_5956_, 0);
lean_inc(v_a_5957_);
lean_dec_ref(v___x_5956_);
v___x_5958_ = l_Lean_Expr_mvarId_x21(v_a_5957_);
v___x_5959_ = l_Lean_MVarId_intros(v___x_5958_, v___y_5919_, v___y_5920_, v___y_5921_, v___y_5922_);
if (lean_obj_tag(v___x_5959_) == 0)
{
lean_object* v_a_5960_; lean_object* v_snd_5961_; lean_object* v_name_5962_; lean_object* v___x_5963_; 
v_a_5960_ = lean_ctor_get(v___x_5959_, 0);
lean_inc(v_a_5960_);
lean_dec_ref(v___x_5959_);
v_snd_5961_ = lean_ctor_get(v_a_5960_, 1);
lean_inc(v_snd_5961_);
lean_dec(v_a_5960_);
v_name_5962_ = lean_ctor_get(v_toConstantVal_5924_, 0);
lean_inc(v_name_5962_);
lean_dec_ref(v_toConstantVal_5924_);
v___x_5963_ = l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(v_snd_5961_, v_name_5962_, v___y_5919_, v___y_5920_, v___y_5921_, v___y_5922_);
if (lean_obj_tag(v___x_5963_) == 0)
{
lean_object* v___x_5964_; lean_object* v___x_5965_; lean_object* v_a_5966_; lean_object* v___x_5968_; uint8_t v_isShared_5969_; uint8_t v_isSharedCheck_5993_; 
lean_dec_ref(v___x_5963_);
v___x_5964_ = l_Lean_Expr_app___override(v___x_5949_, v_a_5957_);
v___x_5965_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v___x_5964_, v___y_5920_);
v_a_5966_ = lean_ctor_get(v___x_5965_, 0);
v_isSharedCheck_5993_ = !lean_is_exclusive(v___x_5965_);
if (v_isSharedCheck_5993_ == 0)
{
v___x_5968_ = v___x_5965_;
v_isShared_5969_ = v_isSharedCheck_5993_;
goto v_resetjp_5967_;
}
else
{
lean_inc(v_a_5966_);
lean_dec(v___x_5965_);
v___x_5968_ = lean_box(0);
v_isShared_5969_ = v_isSharedCheck_5993_;
goto v_resetjp_5967_;
}
v_resetjp_5967_:
{
uint8_t v___x_5970_; uint8_t v___x_5971_; uint8_t v___x_5972_; lean_object* v___x_5973_; 
v___x_5970_ = 0;
v___x_5971_ = 1;
v___x_5972_ = 1;
v___x_5973_ = l_Lean_Meta_mkLambdaFVars(v_xs_5917_, v_a_5966_, v___x_5970_, v___x_5971_, v___x_5970_, v___x_5971_, v___x_5972_, v___y_5919_, v___y_5920_, v___y_5921_, v___y_5922_);
lean_dec_ref(v_xs_5917_);
if (lean_obj_tag(v___x_5973_) == 0)
{
lean_object* v_a_5974_; lean_object* v___x_5976_; uint8_t v_isShared_5977_; uint8_t v_isSharedCheck_5984_; 
v_a_5974_ = lean_ctor_get(v___x_5973_, 0);
v_isSharedCheck_5984_ = !lean_is_exclusive(v___x_5973_);
if (v_isSharedCheck_5984_ == 0)
{
v___x_5976_ = v___x_5973_;
v_isShared_5977_ = v_isSharedCheck_5984_;
goto v_resetjp_5975_;
}
else
{
lean_inc(v_a_5974_);
lean_dec(v___x_5973_);
v___x_5976_ = lean_box(0);
v_isShared_5977_ = v_isSharedCheck_5984_;
goto v_resetjp_5975_;
}
v_resetjp_5975_:
{
lean_object* v___x_5979_; 
if (v_isShared_5969_ == 0)
{
lean_ctor_set_tag(v___x_5968_, 1);
lean_ctor_set(v___x_5968_, 0, v_a_5974_);
v___x_5979_ = v___x_5968_;
goto v_reusejp_5978_;
}
else
{
lean_object* v_reuseFailAlloc_5983_; 
v_reuseFailAlloc_5983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5983_, 0, v_a_5974_);
v___x_5979_ = v_reuseFailAlloc_5983_;
goto v_reusejp_5978_;
}
v_reusejp_5978_:
{
lean_object* v___x_5981_; 
if (v_isShared_5977_ == 0)
{
lean_ctor_set(v___x_5976_, 0, v___x_5979_);
v___x_5981_ = v___x_5976_;
goto v_reusejp_5980_;
}
else
{
lean_object* v_reuseFailAlloc_5982_; 
v_reuseFailAlloc_5982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5982_, 0, v___x_5979_);
v___x_5981_ = v_reuseFailAlloc_5982_;
goto v_reusejp_5980_;
}
v_reusejp_5980_:
{
return v___x_5981_;
}
}
}
}
else
{
lean_object* v_a_5985_; lean_object* v___x_5987_; uint8_t v_isShared_5988_; uint8_t v_isSharedCheck_5992_; 
lean_del_object(v___x_5968_);
v_a_5985_ = lean_ctor_get(v___x_5973_, 0);
v_isSharedCheck_5992_ = !lean_is_exclusive(v___x_5973_);
if (v_isSharedCheck_5992_ == 0)
{
v___x_5987_ = v___x_5973_;
v_isShared_5988_ = v_isSharedCheck_5992_;
goto v_resetjp_5986_;
}
else
{
lean_inc(v_a_5985_);
lean_dec(v___x_5973_);
v___x_5987_ = lean_box(0);
v_isShared_5988_ = v_isSharedCheck_5992_;
goto v_resetjp_5986_;
}
v_resetjp_5986_:
{
lean_object* v___x_5990_; 
if (v_isShared_5988_ == 0)
{
v___x_5990_ = v___x_5987_;
goto v_reusejp_5989_;
}
else
{
lean_object* v_reuseFailAlloc_5991_; 
v_reuseFailAlloc_5991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5991_, 0, v_a_5985_);
v___x_5990_ = v_reuseFailAlloc_5991_;
goto v_reusejp_5989_;
}
v_reusejp_5989_:
{
return v___x_5990_;
}
}
}
}
}
else
{
lean_object* v_a_5994_; lean_object* v___x_5996_; uint8_t v_isShared_5997_; uint8_t v_isSharedCheck_6001_; 
lean_dec(v_a_5957_);
lean_dec_ref(v___x_5949_);
lean_dec_ref(v_xs_5917_);
v_a_5994_ = lean_ctor_get(v___x_5963_, 0);
v_isSharedCheck_6001_ = !lean_is_exclusive(v___x_5963_);
if (v_isSharedCheck_6001_ == 0)
{
v___x_5996_ = v___x_5963_;
v_isShared_5997_ = v_isSharedCheck_6001_;
goto v_resetjp_5995_;
}
else
{
lean_inc(v_a_5994_);
lean_dec(v___x_5963_);
v___x_5996_ = lean_box(0);
v_isShared_5997_ = v_isSharedCheck_6001_;
goto v_resetjp_5995_;
}
v_resetjp_5995_:
{
lean_object* v___x_5999_; 
if (v_isShared_5997_ == 0)
{
v___x_5999_ = v___x_5996_;
goto v_reusejp_5998_;
}
else
{
lean_object* v_reuseFailAlloc_6000_; 
v_reuseFailAlloc_6000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6000_, 0, v_a_5994_);
v___x_5999_ = v_reuseFailAlloc_6000_;
goto v_reusejp_5998_;
}
v_reusejp_5998_:
{
return v___x_5999_;
}
}
}
}
else
{
lean_object* v_a_6002_; lean_object* v___x_6004_; uint8_t v_isShared_6005_; uint8_t v_isSharedCheck_6009_; 
lean_dec(v_a_5957_);
lean_dec_ref(v___x_5949_);
lean_dec_ref(v_toConstantVal_5924_);
lean_dec_ref(v_xs_5917_);
v_a_6002_ = lean_ctor_get(v___x_5959_, 0);
v_isSharedCheck_6009_ = !lean_is_exclusive(v___x_5959_);
if (v_isSharedCheck_6009_ == 0)
{
v___x_6004_ = v___x_5959_;
v_isShared_6005_ = v_isSharedCheck_6009_;
goto v_resetjp_6003_;
}
else
{
lean_inc(v_a_6002_);
lean_dec(v___x_5959_);
v___x_6004_ = lean_box(0);
v_isShared_6005_ = v_isSharedCheck_6009_;
goto v_resetjp_6003_;
}
v_resetjp_6003_:
{
lean_object* v___x_6007_; 
if (v_isShared_6005_ == 0)
{
v___x_6007_ = v___x_6004_;
goto v_reusejp_6006_;
}
else
{
lean_object* v_reuseFailAlloc_6008_; 
v_reuseFailAlloc_6008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6008_, 0, v_a_6002_);
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
else
{
lean_object* v_a_6010_; lean_object* v___x_6012_; uint8_t v_isShared_6013_; uint8_t v_isSharedCheck_6017_; 
lean_dec_ref(v___x_5949_);
lean_dec_ref(v_toConstantVal_5924_);
lean_dec_ref(v_xs_5917_);
v_a_6010_ = lean_ctor_get(v___x_5956_, 0);
v_isSharedCheck_6017_ = !lean_is_exclusive(v___x_5956_);
if (v_isSharedCheck_6017_ == 0)
{
v___x_6012_ = v___x_5956_;
v_isShared_6013_ = v_isSharedCheck_6017_;
goto v_resetjp_6011_;
}
else
{
lean_inc(v_a_6010_);
lean_dec(v___x_5956_);
v___x_6012_ = lean_box(0);
v_isShared_6013_ = v_isSharedCheck_6017_;
goto v_resetjp_6011_;
}
v_resetjp_6011_:
{
lean_object* v___x_6015_; 
if (v_isShared_6013_ == 0)
{
v___x_6015_ = v___x_6012_;
goto v_reusejp_6014_;
}
else
{
lean_object* v_reuseFailAlloc_6016_; 
v_reuseFailAlloc_6016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6016_, 0, v_a_6010_);
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
lean_object* v___x_6018_; 
lean_dec(v_a_5953_);
lean_dec_ref(v___x_5949_);
lean_dec_ref(v_xs_5917_);
v___x_6018_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5914_, v___y_5919_, v___y_5920_, v___y_5921_, v___y_5922_);
return v___x_6018_;
}
}
else
{
lean_object* v_a_6019_; lean_object* v___x_6021_; uint8_t v_isShared_6022_; uint8_t v_isSharedCheck_6026_; 
lean_dec_ref(v___x_5949_);
lean_dec_ref(v_xs_5917_);
lean_dec_ref(v_ctorVal_5914_);
v_a_6019_ = lean_ctor_get(v___x_5952_, 0);
v_isSharedCheck_6026_ = !lean_is_exclusive(v___x_5952_);
if (v_isSharedCheck_6026_ == 0)
{
v___x_6021_ = v___x_5952_;
v_isShared_6022_ = v_isSharedCheck_6026_;
goto v_resetjp_6020_;
}
else
{
lean_inc(v_a_6019_);
lean_dec(v___x_5952_);
v___x_6021_ = lean_box(0);
v_isShared_6022_ = v_isSharedCheck_6026_;
goto v_resetjp_6020_;
}
v_resetjp_6020_:
{
lean_object* v___x_6024_; 
if (v_isShared_6022_ == 0)
{
v___x_6024_ = v___x_6021_;
goto v_reusejp_6023_;
}
else
{
lean_object* v_reuseFailAlloc_6025_; 
v_reuseFailAlloc_6025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6025_, 0, v_a_6019_);
v___x_6024_ = v_reuseFailAlloc_6025_;
goto v_reusejp_6023_;
}
v_reusejp_6023_:
{
return v___x_6024_;
}
}
}
}
else
{
lean_object* v_a_6027_; lean_object* v___x_6029_; uint8_t v_isShared_6030_; uint8_t v_isSharedCheck_6034_; 
lean_dec_ref(v___x_5949_);
lean_dec_ref(v_xs_5917_);
lean_dec_ref(v_ctorVal_5914_);
v_a_6027_ = lean_ctor_get(v___x_5950_, 0);
v_isSharedCheck_6034_ = !lean_is_exclusive(v___x_5950_);
if (v_isSharedCheck_6034_ == 0)
{
v___x_6029_ = v___x_5950_;
v_isShared_6030_ = v_isSharedCheck_6034_;
goto v_resetjp_6028_;
}
else
{
lean_inc(v_a_6027_);
lean_dec(v___x_5950_);
v___x_6029_ = lean_box(0);
v_isShared_6030_ = v_isSharedCheck_6034_;
goto v_resetjp_6028_;
}
v_resetjp_6028_:
{
lean_object* v___x_6032_; 
if (v_isShared_6030_ == 0)
{
v___x_6032_ = v___x_6029_;
goto v_reusejp_6031_;
}
else
{
lean_object* v_reuseFailAlloc_6033_; 
v_reuseFailAlloc_6033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6033_, 0, v_a_6027_);
v___x_6032_ = v_reuseFailAlloc_6033_;
goto v_reusejp_6031_;
}
v_reusejp_6031_:
{
return v___x_6032_;
}
}
}
}
else
{
lean_object* v_a_6035_; lean_object* v___x_6037_; uint8_t v_isShared_6038_; uint8_t v_isSharedCheck_6042_; 
lean_dec_ref(v_eqs_5939_);
lean_dec_ref(v_noConfusion_5933_);
lean_dec_ref(v_xs_5917_);
lean_dec_ref(v_ctorVal_5914_);
v_a_6035_ = lean_ctor_get(v___x_5942_, 0);
v_isSharedCheck_6042_ = !lean_is_exclusive(v___x_5942_);
if (v_isSharedCheck_6042_ == 0)
{
v___x_6037_ = v___x_5942_;
v_isShared_6038_ = v_isSharedCheck_6042_;
goto v_resetjp_6036_;
}
else
{
lean_inc(v_a_6035_);
lean_dec(v___x_5942_);
v___x_6037_ = lean_box(0);
v_isShared_6038_ = v_isSharedCheck_6042_;
goto v_resetjp_6036_;
}
v_resetjp_6036_:
{
lean_object* v___x_6040_; 
if (v_isShared_6038_ == 0)
{
v___x_6040_ = v___x_6037_;
goto v_reusejp_6039_;
}
else
{
lean_object* v_reuseFailAlloc_6041_; 
v_reuseFailAlloc_6041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6041_, 0, v_a_6035_);
v___x_6040_ = v_reuseFailAlloc_6041_;
goto v_reusejp_6039_;
}
v_reusejp_6039_:
{
return v___x_6040_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___boxed(lean_object* v_ctorVal_6049_, lean_object* v_us_6050_, lean_object* v_numIndices_6051_, lean_object* v_xs_6052_, lean_object* v_type_6053_, lean_object* v___y_6054_, lean_object* v___y_6055_, lean_object* v___y_6056_, lean_object* v___y_6057_, lean_object* v___y_6058_){
_start:
{
lean_object* v_res_6059_; 
v_res_6059_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0(v_ctorVal_6049_, v_us_6050_, v_numIndices_6051_, v_xs_6052_, v_type_6053_, v___y_6054_, v___y_6055_, v___y_6056_, v___y_6057_);
lean_dec(v___y_6057_);
lean_dec_ref(v___y_6056_);
lean_dec(v___y_6055_);
lean_dec_ref(v___y_6054_);
lean_dec(v_numIndices_6051_);
return v_res_6059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(lean_object* v_ctorVal_6060_, lean_object* v_typeInfo_6061_, lean_object* v_a_6062_, lean_object* v_a_6063_, lean_object* v_a_6064_, lean_object* v_a_6065_){
_start:
{
lean_object* v_thmType_6067_; lean_object* v_us_6068_; lean_object* v_numIndices_6069_; lean_object* v___f_6070_; uint8_t v___x_6071_; lean_object* v___x_6072_; 
v_thmType_6067_ = lean_ctor_get(v_typeInfo_6061_, 0);
lean_inc_ref(v_thmType_6067_);
v_us_6068_ = lean_ctor_get(v_typeInfo_6061_, 1);
lean_inc(v_us_6068_);
v_numIndices_6069_ = lean_ctor_get(v_typeInfo_6061_, 2);
lean_inc(v_numIndices_6069_);
lean_dec_ref(v_typeInfo_6061_);
v___f_6070_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___boxed), 10, 3);
lean_closure_set(v___f_6070_, 0, v_ctorVal_6060_);
lean_closure_set(v___f_6070_, 1, v_us_6068_);
lean_closure_set(v___f_6070_, 2, v_numIndices_6069_);
v___x_6071_ = 0;
v___x_6072_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_thmType_6067_, v___f_6070_, v___x_6071_, v___x_6071_, v_a_6062_, v_a_6063_, v_a_6064_, v_a_6065_);
return v___x_6072_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___boxed(lean_object* v_ctorVal_6073_, lean_object* v_typeInfo_6074_, lean_object* v_a_6075_, lean_object* v_a_6076_, lean_object* v_a_6077_, lean_object* v_a_6078_, lean_object* v_a_6079_){
_start:
{
lean_object* v_res_6080_; 
v_res_6080_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(v_ctorVal_6073_, v_typeInfo_6074_, v_a_6075_, v_a_6076_, v_a_6077_, v_a_6078_);
lean_dec(v_a_6078_);
lean_dec_ref(v_a_6077_);
lean_dec(v_a_6076_);
lean_dec_ref(v_a_6075_);
return v_res_6080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHInjectiveTheoremNameFor(lean_object* v_ctorName_6083_){
_start:
{
lean_object* v___x_6084_; lean_object* v___x_6085_; 
v___x_6084_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0));
v___x_6085_ = l_Lean_Name_str___override(v_ctorName_6083_, v___x_6084_);
return v___x_6085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(lean_object* v_thmName_6086_, lean_object* v_ctorVal_6087_, lean_object* v_a_6088_, lean_object* v_a_6089_, lean_object* v_a_6090_, lean_object* v_a_6091_){
_start:
{
lean_object* v___x_6093_; 
lean_inc_ref(v_ctorVal_6087_);
v___x_6093_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(v_ctorVal_6087_, v_a_6088_, v_a_6089_, v_a_6090_, v_a_6091_);
if (lean_obj_tag(v___x_6093_) == 0)
{
lean_object* v_a_6094_; lean_object* v___x_6096_; uint8_t v_isShared_6097_; uint8_t v_isSharedCheck_6155_; 
v_a_6094_ = lean_ctor_get(v___x_6093_, 0);
v_isSharedCheck_6155_ = !lean_is_exclusive(v___x_6093_);
if (v_isSharedCheck_6155_ == 0)
{
v___x_6096_ = v___x_6093_;
v_isShared_6097_ = v_isSharedCheck_6155_;
goto v_resetjp_6095_;
}
else
{
lean_inc(v_a_6094_);
lean_dec(v___x_6093_);
v___x_6096_ = lean_box(0);
v_isShared_6097_ = v_isSharedCheck_6155_;
goto v_resetjp_6095_;
}
v_resetjp_6095_:
{
if (lean_obj_tag(v_a_6094_) == 1)
{
lean_object* v_val_6098_; lean_object* v___x_6099_; 
lean_del_object(v___x_6096_);
v_val_6098_ = lean_ctor_get(v_a_6094_, 0);
lean_inc_n(v_val_6098_, 2);
lean_dec_ref(v_a_6094_);
lean_inc_ref(v_ctorVal_6087_);
v___x_6099_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(v_ctorVal_6087_, v_val_6098_, v_a_6088_, v_a_6089_, v_a_6090_, v_a_6091_);
if (lean_obj_tag(v___x_6099_) == 0)
{
lean_object* v_a_6100_; lean_object* v___x_6102_; uint8_t v_isShared_6103_; uint8_t v_isSharedCheck_6142_; 
v_a_6100_ = lean_ctor_get(v___x_6099_, 0);
v_isSharedCheck_6142_ = !lean_is_exclusive(v___x_6099_);
if (v_isSharedCheck_6142_ == 0)
{
v___x_6102_ = v___x_6099_;
v_isShared_6103_ = v_isSharedCheck_6142_;
goto v_resetjp_6101_;
}
else
{
lean_inc(v_a_6100_);
lean_dec(v___x_6099_);
v___x_6102_ = lean_box(0);
v_isShared_6103_ = v_isSharedCheck_6142_;
goto v_resetjp_6101_;
}
v_resetjp_6101_:
{
if (lean_obj_tag(v_a_6100_) == 1)
{
lean_object* v_toConstantVal_6104_; lean_object* v_val_6105_; lean_object* v___x_6107_; uint8_t v_isShared_6108_; uint8_t v_isSharedCheck_6137_; 
v_toConstantVal_6104_ = lean_ctor_get(v_ctorVal_6087_, 0);
lean_inc_ref(v_toConstantVal_6104_);
lean_dec_ref(v_ctorVal_6087_);
v_val_6105_ = lean_ctor_get(v_a_6100_, 0);
v_isSharedCheck_6137_ = !lean_is_exclusive(v_a_6100_);
if (v_isSharedCheck_6137_ == 0)
{
v___x_6107_ = v_a_6100_;
v_isShared_6108_ = v_isSharedCheck_6137_;
goto v_resetjp_6106_;
}
else
{
lean_inc(v_val_6105_);
lean_dec(v_a_6100_);
v___x_6107_ = lean_box(0);
v_isShared_6108_ = v_isSharedCheck_6137_;
goto v_resetjp_6106_;
}
v_resetjp_6106_:
{
lean_object* v_levelParams_6109_; lean_object* v___x_6111_; uint8_t v_isShared_6112_; uint8_t v_isSharedCheck_6134_; 
v_levelParams_6109_ = lean_ctor_get(v_toConstantVal_6104_, 1);
v_isSharedCheck_6134_ = !lean_is_exclusive(v_toConstantVal_6104_);
if (v_isSharedCheck_6134_ == 0)
{
lean_object* v_unused_6135_; lean_object* v_unused_6136_; 
v_unused_6135_ = lean_ctor_get(v_toConstantVal_6104_, 2);
lean_dec(v_unused_6135_);
v_unused_6136_ = lean_ctor_get(v_toConstantVal_6104_, 0);
lean_dec(v_unused_6136_);
v___x_6111_ = v_toConstantVal_6104_;
v_isShared_6112_ = v_isSharedCheck_6134_;
goto v_resetjp_6110_;
}
else
{
lean_inc(v_levelParams_6109_);
lean_dec(v_toConstantVal_6104_);
v___x_6111_ = lean_box(0);
v_isShared_6112_ = v_isSharedCheck_6134_;
goto v_resetjp_6110_;
}
v_resetjp_6110_:
{
lean_object* v_thmType_6113_; lean_object* v___x_6115_; uint8_t v_isShared_6116_; uint8_t v_isSharedCheck_6131_; 
v_thmType_6113_ = lean_ctor_get(v_val_6098_, 0);
v_isSharedCheck_6131_ = !lean_is_exclusive(v_val_6098_);
if (v_isSharedCheck_6131_ == 0)
{
lean_object* v_unused_6132_; lean_object* v_unused_6133_; 
v_unused_6132_ = lean_ctor_get(v_val_6098_, 2);
lean_dec(v_unused_6132_);
v_unused_6133_ = lean_ctor_get(v_val_6098_, 1);
lean_dec(v_unused_6133_);
v___x_6115_ = v_val_6098_;
v_isShared_6116_ = v_isSharedCheck_6131_;
goto v_resetjp_6114_;
}
else
{
lean_inc(v_thmType_6113_);
lean_dec(v_val_6098_);
v___x_6115_ = lean_box(0);
v_isShared_6116_ = v_isSharedCheck_6131_;
goto v_resetjp_6114_;
}
v_resetjp_6114_:
{
lean_object* v___x_6118_; 
lean_inc(v_thmName_6086_);
if (v_isShared_6112_ == 0)
{
lean_ctor_set(v___x_6111_, 2, v_thmType_6113_);
lean_ctor_set(v___x_6111_, 0, v_thmName_6086_);
v___x_6118_ = v___x_6111_;
goto v_reusejp_6117_;
}
else
{
lean_object* v_reuseFailAlloc_6130_; 
v_reuseFailAlloc_6130_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6130_, 0, v_thmName_6086_);
lean_ctor_set(v_reuseFailAlloc_6130_, 1, v_levelParams_6109_);
lean_ctor_set(v_reuseFailAlloc_6130_, 2, v_thmType_6113_);
v___x_6118_ = v_reuseFailAlloc_6130_;
goto v_reusejp_6117_;
}
v_reusejp_6117_:
{
lean_object* v___x_6119_; lean_object* v___x_6120_; lean_object* v___x_6122_; 
v___x_6119_ = lean_box(0);
v___x_6120_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6120_, 0, v_thmName_6086_);
lean_ctor_set(v___x_6120_, 1, v___x_6119_);
if (v_isShared_6116_ == 0)
{
lean_ctor_set(v___x_6115_, 2, v___x_6120_);
lean_ctor_set(v___x_6115_, 1, v_val_6105_);
lean_ctor_set(v___x_6115_, 0, v___x_6118_);
v___x_6122_ = v___x_6115_;
goto v_reusejp_6121_;
}
else
{
lean_object* v_reuseFailAlloc_6129_; 
v_reuseFailAlloc_6129_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6129_, 0, v___x_6118_);
lean_ctor_set(v_reuseFailAlloc_6129_, 1, v_val_6105_);
lean_ctor_set(v_reuseFailAlloc_6129_, 2, v___x_6120_);
v___x_6122_ = v_reuseFailAlloc_6129_;
goto v_reusejp_6121_;
}
v_reusejp_6121_:
{
lean_object* v___x_6124_; 
if (v_isShared_6108_ == 0)
{
lean_ctor_set(v___x_6107_, 0, v___x_6122_);
v___x_6124_ = v___x_6107_;
goto v_reusejp_6123_;
}
else
{
lean_object* v_reuseFailAlloc_6128_; 
v_reuseFailAlloc_6128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6128_, 0, v___x_6122_);
v___x_6124_ = v_reuseFailAlloc_6128_;
goto v_reusejp_6123_;
}
v_reusejp_6123_:
{
lean_object* v___x_6126_; 
if (v_isShared_6103_ == 0)
{
lean_ctor_set(v___x_6102_, 0, v___x_6124_);
v___x_6126_ = v___x_6102_;
goto v_reusejp_6125_;
}
else
{
lean_object* v_reuseFailAlloc_6127_; 
v_reuseFailAlloc_6127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6127_, 0, v___x_6124_);
v___x_6126_ = v_reuseFailAlloc_6127_;
goto v_reusejp_6125_;
}
v_reusejp_6125_:
{
return v___x_6126_;
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
lean_object* v___x_6138_; lean_object* v___x_6140_; 
lean_dec(v_a_6100_);
lean_dec(v_val_6098_);
lean_dec_ref(v_ctorVal_6087_);
lean_dec(v_thmName_6086_);
v___x_6138_ = lean_box(0);
if (v_isShared_6103_ == 0)
{
lean_ctor_set(v___x_6102_, 0, v___x_6138_);
v___x_6140_ = v___x_6102_;
goto v_reusejp_6139_;
}
else
{
lean_object* v_reuseFailAlloc_6141_; 
v_reuseFailAlloc_6141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6141_, 0, v___x_6138_);
v___x_6140_ = v_reuseFailAlloc_6141_;
goto v_reusejp_6139_;
}
v_reusejp_6139_:
{
return v___x_6140_;
}
}
}
}
else
{
lean_object* v_a_6143_; lean_object* v___x_6145_; uint8_t v_isShared_6146_; uint8_t v_isSharedCheck_6150_; 
lean_dec(v_val_6098_);
lean_dec_ref(v_ctorVal_6087_);
lean_dec(v_thmName_6086_);
v_a_6143_ = lean_ctor_get(v___x_6099_, 0);
v_isSharedCheck_6150_ = !lean_is_exclusive(v___x_6099_);
if (v_isSharedCheck_6150_ == 0)
{
v___x_6145_ = v___x_6099_;
v_isShared_6146_ = v_isSharedCheck_6150_;
goto v_resetjp_6144_;
}
else
{
lean_inc(v_a_6143_);
lean_dec(v___x_6099_);
v___x_6145_ = lean_box(0);
v_isShared_6146_ = v_isSharedCheck_6150_;
goto v_resetjp_6144_;
}
v_resetjp_6144_:
{
lean_object* v___x_6148_; 
if (v_isShared_6146_ == 0)
{
v___x_6148_ = v___x_6145_;
goto v_reusejp_6147_;
}
else
{
lean_object* v_reuseFailAlloc_6149_; 
v_reuseFailAlloc_6149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6149_, 0, v_a_6143_);
v___x_6148_ = v_reuseFailAlloc_6149_;
goto v_reusejp_6147_;
}
v_reusejp_6147_:
{
return v___x_6148_;
}
}
}
}
else
{
lean_object* v___x_6151_; lean_object* v___x_6153_; 
lean_dec(v_a_6094_);
lean_dec_ref(v_ctorVal_6087_);
lean_dec(v_thmName_6086_);
v___x_6151_ = lean_box(0);
if (v_isShared_6097_ == 0)
{
lean_ctor_set(v___x_6096_, 0, v___x_6151_);
v___x_6153_ = v___x_6096_;
goto v_reusejp_6152_;
}
else
{
lean_object* v_reuseFailAlloc_6154_; 
v_reuseFailAlloc_6154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6154_, 0, v___x_6151_);
v___x_6153_ = v_reuseFailAlloc_6154_;
goto v_reusejp_6152_;
}
v_reusejp_6152_:
{
return v___x_6153_;
}
}
}
}
else
{
lean_object* v_a_6156_; lean_object* v___x_6158_; uint8_t v_isShared_6159_; uint8_t v_isSharedCheck_6163_; 
lean_dec_ref(v_ctorVal_6087_);
lean_dec(v_thmName_6086_);
v_a_6156_ = lean_ctor_get(v___x_6093_, 0);
v_isSharedCheck_6163_ = !lean_is_exclusive(v___x_6093_);
if (v_isSharedCheck_6163_ == 0)
{
v___x_6158_ = v___x_6093_;
v_isShared_6159_ = v_isSharedCheck_6163_;
goto v_resetjp_6157_;
}
else
{
lean_inc(v_a_6156_);
lean_dec(v___x_6093_);
v___x_6158_ = lean_box(0);
v_isShared_6159_ = v_isSharedCheck_6163_;
goto v_resetjp_6157_;
}
v_resetjp_6157_:
{
lean_object* v___x_6161_; 
if (v_isShared_6159_ == 0)
{
v___x_6161_ = v___x_6158_;
goto v_reusejp_6160_;
}
else
{
lean_object* v_reuseFailAlloc_6162_; 
v_reuseFailAlloc_6162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6162_, 0, v_a_6156_);
v___x_6161_ = v_reuseFailAlloc_6162_;
goto v_reusejp_6160_;
}
v_reusejp_6160_:
{
return v___x_6161_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f___boxed(lean_object* v_thmName_6164_, lean_object* v_ctorVal_6165_, lean_object* v_a_6166_, lean_object* v_a_6167_, lean_object* v_a_6168_, lean_object* v_a_6169_, lean_object* v_a_6170_){
_start:
{
lean_object* v_res_6171_; 
v_res_6171_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(v_thmName_6164_, v_ctorVal_6165_, v_a_6166_, v_a_6167_, v_a_6168_, v_a_6169_);
lean_dec(v_a_6169_);
lean_dec_ref(v_a_6168_);
lean_dec(v_a_6167_);
lean_dec_ref(v_a_6166_);
return v_res_6171_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(lean_object* v_env_6172_, lean_object* v_n_6173_){
_start:
{
if (lean_obj_tag(v_n_6173_) == 1)
{
lean_object* v_pre_6174_; lean_object* v_str_6175_; lean_object* v___x_6176_; uint8_t v___x_6177_; 
v_pre_6174_ = lean_ctor_get(v_n_6173_, 0);
lean_inc(v_pre_6174_);
v_str_6175_ = lean_ctor_get(v_n_6173_, 1);
lean_inc_ref(v_str_6175_);
lean_dec_ref(v_n_6173_);
v___x_6176_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0));
v___x_6177_ = lean_string_dec_eq(v_str_6175_, v___x_6176_);
lean_dec_ref(v_str_6175_);
if (v___x_6177_ == 0)
{
lean_dec(v_pre_6174_);
lean_dec_ref(v_env_6172_);
return v___x_6177_;
}
else
{
uint8_t v___x_6178_; lean_object* v___x_6179_; 
v___x_6178_ = 0;
v___x_6179_ = l_Lean_Environment_find_x3f(v_env_6172_, v_pre_6174_, v___x_6178_);
if (lean_obj_tag(v___x_6179_) == 1)
{
lean_object* v_val_6180_; 
v_val_6180_ = lean_ctor_get(v___x_6179_, 0);
lean_inc(v_val_6180_);
lean_dec_ref(v___x_6179_);
if (lean_obj_tag(v_val_6180_) == 6)
{
lean_dec_ref(v_val_6180_);
return v___x_6177_;
}
else
{
lean_dec(v_val_6180_);
return v___x_6178_;
}
}
else
{
lean_dec(v___x_6179_);
return v___x_6178_;
}
}
}
else
{
uint8_t v___x_6181_; 
lean_dec(v_n_6173_);
lean_dec_ref(v_env_6172_);
v___x_6181_ = 0;
return v___x_6181_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2____boxed(lean_object* v_env_6182_, lean_object* v_n_6183_){
_start:
{
uint8_t v_res_6184_; lean_object* v_r_6185_; 
v_res_6184_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(v_env_6182_, v_n_6183_);
v_r_6185_ = lean_box(v_res_6184_);
return v_r_6185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_6188_; lean_object* v___x_6189_; 
v___f_6188_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_));
v___x_6189_ = l_Lean_registerReservedNamePredicate(v___f_6188_);
return v___x_6189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2____boxed(lean_object* v_a_6190_){
_start:
{
lean_object* v_res_6191_; 
v_res_6191_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_();
return v_res_6191_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(lean_object* v_thm_6192_, lean_object* v___y_6193_){
_start:
{
lean_object* v___x_6195_; lean_object* v_env_6196_; lean_object* v_toConstantVal_6197_; lean_object* v_value_6198_; lean_object* v_all_6199_; uint8_t v___y_6201_; lean_object* v_type_6209_; uint8_t v___x_6210_; 
v___x_6195_ = lean_st_ref_get(v___y_6193_);
v_env_6196_ = lean_ctor_get(v___x_6195_, 0);
lean_inc_ref_n(v_env_6196_, 2);
lean_dec(v___x_6195_);
v_toConstantVal_6197_ = lean_ctor_get(v_thm_6192_, 0);
v_value_6198_ = lean_ctor_get(v_thm_6192_, 1);
v_all_6199_ = lean_ctor_get(v_thm_6192_, 2);
v_type_6209_ = lean_ctor_get(v_toConstantVal_6197_, 2);
v___x_6210_ = l_Lean_Environment_hasUnsafe(v_env_6196_, v_type_6209_);
if (v___x_6210_ == 0)
{
uint8_t v___x_6211_; 
v___x_6211_ = l_Lean_Environment_hasUnsafe(v_env_6196_, v_value_6198_);
v___y_6201_ = v___x_6211_;
goto v___jp_6200_;
}
else
{
lean_dec_ref(v_env_6196_);
v___y_6201_ = v___x_6210_;
goto v___jp_6200_;
}
v___jp_6200_:
{
if (v___y_6201_ == 0)
{
lean_object* v___x_6202_; lean_object* v___x_6203_; 
v___x_6202_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_6202_, 0, v_thm_6192_);
v___x_6203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6203_, 0, v___x_6202_);
return v___x_6203_;
}
else
{
lean_object* v___x_6204_; uint8_t v___x_6205_; lean_object* v___x_6206_; lean_object* v___x_6207_; lean_object* v___x_6208_; 
lean_inc(v_all_6199_);
lean_inc_ref(v_value_6198_);
lean_inc_ref(v_toConstantVal_6197_);
lean_dec_ref(v_thm_6192_);
v___x_6204_ = lean_box(0);
v___x_6205_ = 0;
v___x_6206_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_6206_, 0, v_toConstantVal_6197_);
lean_ctor_set(v___x_6206_, 1, v_value_6198_);
lean_ctor_set(v___x_6206_, 2, v___x_6204_);
lean_ctor_set(v___x_6206_, 3, v_all_6199_);
lean_ctor_set_uint8(v___x_6206_, sizeof(void*)*4, v___x_6205_);
v___x_6207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6207_, 0, v___x_6206_);
v___x_6208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6208_, 0, v___x_6207_);
return v___x_6208_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_thm_6212_, lean_object* v___y_6213_, lean_object* v___y_6214_){
_start:
{
lean_object* v_res_6215_; 
v_res_6215_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(v_thm_6212_, v___y_6213_);
lean_dec(v___y_6213_);
return v_res_6215_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0(lean_object* v_thm_6216_, lean_object* v___y_6217_, lean_object* v___y_6218_, lean_object* v___y_6219_, lean_object* v___y_6220_){
_start:
{
lean_object* v___x_6222_; 
v___x_6222_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(v_thm_6216_, v___y_6220_);
return v___x_6222_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___boxed(lean_object* v_thm_6223_, lean_object* v___y_6224_, lean_object* v___y_6225_, lean_object* v___y_6226_, lean_object* v___y_6227_, lean_object* v___y_6228_){
_start:
{
lean_object* v_res_6229_; 
v_res_6229_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0(v_thm_6223_, v___y_6224_, v___y_6225_, v___y_6226_, v___y_6227_);
lean_dec(v___y_6227_);
lean_dec_ref(v___y_6226_);
lean_dec(v___y_6225_);
lean_dec_ref(v___y_6224_);
return v_res_6229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(lean_object* v_val_6230_, uint8_t v___x_6231_, lean_object* v___y_6232_, lean_object* v___y_6233_, lean_object* v___y_6234_, lean_object* v___y_6235_){
_start:
{
lean_object* v___x_6237_; lean_object* v_a_6238_; lean_object* v___x_6239_; 
v___x_6237_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(v_val_6230_, v___y_6235_);
v_a_6238_ = lean_ctor_get(v___x_6237_, 0);
lean_inc(v_a_6238_);
lean_dec_ref(v___x_6237_);
v___x_6239_ = l_Lean_addDecl(v_a_6238_, v___x_6231_, v___y_6234_, v___y_6235_);
return v___x_6239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object* v_val_6240_, lean_object* v___x_6241_, lean_object* v___y_6242_, lean_object* v___y_6243_, lean_object* v___y_6244_, lean_object* v___y_6245_, lean_object* v___y_6246_){
_start:
{
uint8_t v___x_2124__boxed_6247_; lean_object* v_res_6248_; 
v___x_2124__boxed_6247_ = lean_unbox(v___x_6241_);
v_res_6248_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(v_val_6240_, v___x_2124__boxed_6247_, v___y_6242_, v___y_6243_, v___y_6244_, v___y_6245_);
lean_dec(v___y_6245_);
lean_dec_ref(v___y_6244_);
lean_dec(v___y_6243_);
lean_dec_ref(v___y_6242_);
return v_res_6248_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6251_; lean_object* v___x_6252_; lean_object* v___x_6253_; 
v___x_6251_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_6252_ = lean_unsigned_to_nat(0u);
v___x_6253_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_6253_, 0, v___x_6252_);
lean_ctor_set(v___x_6253_, 1, v___x_6252_);
lean_ctor_set(v___x_6253_, 2, v___x_6252_);
lean_ctor_set(v___x_6253_, 3, v___x_6252_);
lean_ctor_set(v___x_6253_, 4, v___x_6251_);
lean_ctor_set(v___x_6253_, 5, v___x_6251_);
lean_ctor_set(v___x_6253_, 6, v___x_6251_);
lean_ctor_set(v___x_6253_, 7, v___x_6251_);
lean_ctor_set(v___x_6253_, 8, v___x_6251_);
lean_ctor_set(v___x_6253_, 9, v___x_6251_);
return v___x_6253_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6254_; lean_object* v___x_6255_; 
v___x_6254_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_6255_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6255_, 0, v___x_6254_);
lean_ctor_set(v___x_6255_, 1, v___x_6254_);
lean_ctor_set(v___x_6255_, 2, v___x_6254_);
lean_ctor_set(v___x_6255_, 3, v___x_6254_);
lean_ctor_set(v___x_6255_, 4, v___x_6254_);
lean_ctor_set(v___x_6255_, 5, v___x_6254_);
return v___x_6255_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6256_; lean_object* v___x_6257_; 
v___x_6256_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_6257_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6257_, 0, v___x_6256_);
lean_ctor_set(v___x_6257_, 1, v___x_6256_);
lean_ctor_set(v___x_6257_, 2, v___x_6256_);
lean_ctor_set(v___x_6257_, 3, v___x_6256_);
lean_ctor_set(v___x_6257_, 4, v___x_6256_);
return v___x_6257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(lean_object* v___x_6258_, lean_object* v_name_6259_, lean_object* v___y_6260_, lean_object* v___y_6261_){
_start:
{
if (lean_obj_tag(v_name_6259_) == 1)
{
lean_object* v_pre_6271_; lean_object* v_str_6272_; lean_object* v___x_6273_; uint8_t v___x_6274_; 
v_pre_6271_ = lean_ctor_get(v_name_6259_, 0);
lean_inc(v_pre_6271_);
v_str_6272_ = lean_ctor_get(v_name_6259_, 1);
v___x_6273_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0));
v___x_6274_ = lean_string_dec_eq(v_str_6272_, v___x_6273_);
if (v___x_6274_ == 0)
{
lean_dec(v_pre_6271_);
lean_dec_ref(v_name_6259_);
lean_dec(v___x_6258_);
goto v___jp_6267_;
}
else
{
lean_object* v___x_6275_; lean_object* v_env_6276_; uint8_t v___x_6277_; lean_object* v___x_6278_; 
v___x_6275_ = lean_st_ref_get(v___y_6261_);
v_env_6276_ = lean_ctor_get(v___x_6275_, 0);
lean_inc_ref(v_env_6276_);
lean_dec(v___x_6275_);
v___x_6277_ = 0;
lean_inc(v_pre_6271_);
v___x_6278_ = l_Lean_Environment_find_x3f(v_env_6276_, v_pre_6271_, v___x_6277_);
if (lean_obj_tag(v___x_6278_) == 1)
{
lean_object* v_val_6279_; 
v_val_6279_ = lean_ctor_get(v___x_6278_, 0);
lean_inc(v_val_6279_);
lean_dec_ref(v___x_6278_);
if (lean_obj_tag(v_val_6279_) == 6)
{
lean_object* v_val_6280_; lean_object* v___x_6282_; uint8_t v_isShared_6283_; uint8_t v_isSharedCheck_6330_; 
v_val_6280_ = lean_ctor_get(v_val_6279_, 0);
v_isSharedCheck_6330_ = !lean_is_exclusive(v_val_6279_);
if (v_isSharedCheck_6330_ == 0)
{
v___x_6282_ = v_val_6279_;
v_isShared_6283_ = v_isSharedCheck_6330_;
goto v_resetjp_6281_;
}
else
{
lean_inc(v_val_6280_);
lean_dec(v_val_6279_);
v___x_6282_ = lean_box(0);
v_isShared_6283_ = v_isSharedCheck_6330_;
goto v_resetjp_6281_;
}
v_resetjp_6281_:
{
uint8_t v___x_6284_; uint8_t v___x_6285_; uint8_t v___x_6286_; lean_object* v___x_6287_; uint64_t v___x_6288_; lean_object* v___x_6289_; lean_object* v___x_6290_; lean_object* v___x_6291_; lean_object* v___x_6292_; lean_object* v___x_6293_; lean_object* v___x_6294_; lean_object* v___x_6295_; lean_object* v___x_6296_; lean_object* v___x_6297_; lean_object* v___x_6298_; lean_object* v___x_6299_; lean_object* v___x_6300_; uint8_t v_a_6302_; lean_object* v___x_6308_; 
v___x_6284_ = 1;
v___x_6285_ = 0;
v___x_6286_ = 2;
v___x_6287_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_6287_, 0, v___x_6277_);
lean_ctor_set_uint8(v___x_6287_, 1, v___x_6277_);
lean_ctor_set_uint8(v___x_6287_, 2, v___x_6277_);
lean_ctor_set_uint8(v___x_6287_, 3, v___x_6277_);
lean_ctor_set_uint8(v___x_6287_, 4, v___x_6277_);
lean_ctor_set_uint8(v___x_6287_, 5, v___x_6274_);
lean_ctor_set_uint8(v___x_6287_, 6, v___x_6274_);
lean_ctor_set_uint8(v___x_6287_, 7, v___x_6277_);
lean_ctor_set_uint8(v___x_6287_, 8, v___x_6274_);
lean_ctor_set_uint8(v___x_6287_, 9, v___x_6284_);
lean_ctor_set_uint8(v___x_6287_, 10, v___x_6285_);
lean_ctor_set_uint8(v___x_6287_, 11, v___x_6274_);
lean_ctor_set_uint8(v___x_6287_, 12, v___x_6274_);
lean_ctor_set_uint8(v___x_6287_, 13, v___x_6274_);
lean_ctor_set_uint8(v___x_6287_, 14, v___x_6286_);
lean_ctor_set_uint8(v___x_6287_, 15, v___x_6274_);
lean_ctor_set_uint8(v___x_6287_, 16, v___x_6274_);
lean_ctor_set_uint8(v___x_6287_, 17, v___x_6274_);
lean_ctor_set_uint8(v___x_6287_, 18, v___x_6274_);
v___x_6288_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_6287_);
v___x_6289_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_6289_, 0, v___x_6287_);
lean_ctor_set_uint64(v___x_6289_, sizeof(void*)*1, v___x_6288_);
v___x_6290_ = lean_unsigned_to_nat(0u);
v___x_6291_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_6292_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_6293_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_));
v___x_6294_ = lean_box(0);
lean_inc(v___x_6258_);
v___x_6295_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_6295_, 0, v___x_6289_);
lean_ctor_set(v___x_6295_, 1, v___x_6258_);
lean_ctor_set(v___x_6295_, 2, v___x_6292_);
lean_ctor_set(v___x_6295_, 3, v___x_6293_);
lean_ctor_set(v___x_6295_, 4, v___x_6294_);
lean_ctor_set(v___x_6295_, 5, v___x_6290_);
lean_ctor_set(v___x_6295_, 6, v___x_6294_);
lean_ctor_set_uint8(v___x_6295_, sizeof(void*)*7, v___x_6277_);
lean_ctor_set_uint8(v___x_6295_, sizeof(void*)*7 + 1, v___x_6277_);
lean_ctor_set_uint8(v___x_6295_, sizeof(void*)*7 + 2, v___x_6277_);
lean_ctor_set_uint8(v___x_6295_, sizeof(void*)*7 + 3, v___x_6274_);
v___x_6296_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6297_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6298_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6299_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6299_, 0, v___x_6296_);
lean_ctor_set(v___x_6299_, 1, v___x_6297_);
lean_ctor_set(v___x_6299_, 2, v___x_6258_);
lean_ctor_set(v___x_6299_, 3, v___x_6291_);
lean_ctor_set(v___x_6299_, 4, v___x_6298_);
v___x_6300_ = lean_st_mk_ref(v___x_6299_);
lean_inc_ref(v_name_6259_);
v___x_6308_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(v_name_6259_, v_val_6280_, v___x_6295_, v___x_6300_, v___y_6260_, v___y_6261_);
if (lean_obj_tag(v___x_6308_) == 0)
{
lean_object* v_a_6309_; 
v_a_6309_ = lean_ctor_get(v___x_6308_, 0);
lean_inc(v_a_6309_);
lean_dec_ref(v___x_6308_);
if (lean_obj_tag(v_a_6309_) == 1)
{
lean_object* v_val_6310_; lean_object* v___x_6311_; lean_object* v___f_6312_; lean_object* v___x_6313_; 
v_val_6310_ = lean_ctor_get(v_a_6309_, 0);
lean_inc(v_val_6310_);
lean_dec_ref(v_a_6309_);
v___x_6311_ = lean_box(v___x_6277_);
v___f_6312_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed), 7, 2);
lean_closure_set(v___f_6312_, 0, v_val_6310_);
lean_closure_set(v___f_6312_, 1, v___x_6311_);
v___x_6313_ = l_Lean_Meta_realizeConst(v_pre_6271_, v_name_6259_, v___f_6312_, v___x_6295_, v___x_6300_, v___y_6260_, v___y_6261_);
lean_dec_ref(v___x_6295_);
if (lean_obj_tag(v___x_6313_) == 0)
{
lean_dec_ref(v___x_6313_);
v_a_6302_ = v___x_6274_;
goto v___jp_6301_;
}
else
{
lean_object* v_a_6314_; lean_object* v___x_6316_; uint8_t v_isShared_6317_; uint8_t v_isSharedCheck_6321_; 
lean_dec(v___x_6300_);
lean_del_object(v___x_6282_);
v_a_6314_ = lean_ctor_get(v___x_6313_, 0);
v_isSharedCheck_6321_ = !lean_is_exclusive(v___x_6313_);
if (v_isSharedCheck_6321_ == 0)
{
v___x_6316_ = v___x_6313_;
v_isShared_6317_ = v_isSharedCheck_6321_;
goto v_resetjp_6315_;
}
else
{
lean_inc(v_a_6314_);
lean_dec(v___x_6313_);
v___x_6316_ = lean_box(0);
v_isShared_6317_ = v_isSharedCheck_6321_;
goto v_resetjp_6315_;
}
v_resetjp_6315_:
{
lean_object* v___x_6319_; 
if (v_isShared_6317_ == 0)
{
v___x_6319_ = v___x_6316_;
goto v_reusejp_6318_;
}
else
{
lean_object* v_reuseFailAlloc_6320_; 
v_reuseFailAlloc_6320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6320_, 0, v_a_6314_);
v___x_6319_ = v_reuseFailAlloc_6320_;
goto v_reusejp_6318_;
}
v_reusejp_6318_:
{
return v___x_6319_;
}
}
}
}
else
{
lean_dec(v_a_6309_);
lean_dec_ref(v___x_6295_);
lean_dec_ref(v_name_6259_);
lean_dec(v_pre_6271_);
v_a_6302_ = v___x_6277_;
goto v___jp_6301_;
}
}
else
{
lean_object* v_a_6322_; lean_object* v___x_6324_; uint8_t v_isShared_6325_; uint8_t v_isSharedCheck_6329_; 
lean_dec(v___x_6300_);
lean_dec_ref(v___x_6295_);
lean_del_object(v___x_6282_);
lean_dec_ref(v_name_6259_);
lean_dec(v_pre_6271_);
v_a_6322_ = lean_ctor_get(v___x_6308_, 0);
v_isSharedCheck_6329_ = !lean_is_exclusive(v___x_6308_);
if (v_isSharedCheck_6329_ == 0)
{
v___x_6324_ = v___x_6308_;
v_isShared_6325_ = v_isSharedCheck_6329_;
goto v_resetjp_6323_;
}
else
{
lean_inc(v_a_6322_);
lean_dec(v___x_6308_);
v___x_6324_ = lean_box(0);
v_isShared_6325_ = v_isSharedCheck_6329_;
goto v_resetjp_6323_;
}
v_resetjp_6323_:
{
lean_object* v___x_6327_; 
if (v_isShared_6325_ == 0)
{
v___x_6327_ = v___x_6324_;
goto v_reusejp_6326_;
}
else
{
lean_object* v_reuseFailAlloc_6328_; 
v_reuseFailAlloc_6328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6328_, 0, v_a_6322_);
v___x_6327_ = v_reuseFailAlloc_6328_;
goto v_reusejp_6326_;
}
v_reusejp_6326_:
{
return v___x_6327_;
}
}
}
v___jp_6301_:
{
lean_object* v___x_6303_; lean_object* v___x_6304_; lean_object* v___x_6306_; 
v___x_6303_ = lean_st_ref_get(v___x_6300_);
lean_dec(v___x_6300_);
lean_dec(v___x_6303_);
v___x_6304_ = lean_box(v_a_6302_);
if (v_isShared_6283_ == 0)
{
lean_ctor_set_tag(v___x_6282_, 0);
lean_ctor_set(v___x_6282_, 0, v___x_6304_);
v___x_6306_ = v___x_6282_;
goto v_reusejp_6305_;
}
else
{
lean_object* v_reuseFailAlloc_6307_; 
v_reuseFailAlloc_6307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6307_, 0, v___x_6304_);
v___x_6306_ = v_reuseFailAlloc_6307_;
goto v_reusejp_6305_;
}
v_reusejp_6305_:
{
return v___x_6306_;
}
}
}
}
else
{
lean_dec(v_val_6279_);
lean_dec(v_pre_6271_);
lean_dec_ref(v_name_6259_);
lean_dec(v___x_6258_);
goto v___jp_6263_;
}
}
else
{
lean_dec(v___x_6278_);
lean_dec(v_pre_6271_);
lean_dec_ref(v_name_6259_);
lean_dec(v___x_6258_);
goto v___jp_6263_;
}
}
}
else
{
lean_dec(v_name_6259_);
lean_dec(v___x_6258_);
goto v___jp_6267_;
}
v___jp_6263_:
{
uint8_t v___x_6264_; lean_object* v___x_6265_; lean_object* v___x_6266_; 
v___x_6264_ = 0;
v___x_6265_ = lean_box(v___x_6264_);
v___x_6266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6266_, 0, v___x_6265_);
return v___x_6266_;
}
v___jp_6267_:
{
uint8_t v___x_6268_; lean_object* v___x_6269_; lean_object* v___x_6270_; 
v___x_6268_ = 0;
v___x_6269_ = lean_box(v___x_6268_);
v___x_6270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6270_, 0, v___x_6269_);
return v___x_6270_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object* v___x_6331_, lean_object* v_name_6332_, lean_object* v___y_6333_, lean_object* v___y_6334_, lean_object* v___y_6335_){
_start:
{
lean_object* v_res_6336_; 
v_res_6336_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(v___x_6331_, v_name_6332_, v___y_6333_, v___y_6334_);
lean_dec(v___y_6334_);
lean_dec_ref(v___y_6333_);
return v_res_6336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_6340_; lean_object* v___x_6341_; 
v___f_6340_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_));
v___x_6341_ = l_Lean_registerReservedNameAction(v___f_6340_);
return v___x_6341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object* v_a_6342_){
_start:
{
lean_object* v_res_6343_; 
v_res_6343_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_();
return v_res_6343_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Refl(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Assumption(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_SameCtorUtils(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Injection(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Attr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Injective(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
