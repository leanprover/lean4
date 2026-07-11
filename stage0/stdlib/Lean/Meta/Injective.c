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
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
uint8_t l_IO_CancelToken_isSet(lean_object*);
extern lean_object* l_Lean_interruptExceptionId;
size_t lean_usize_add(size_t, size_t);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
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
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "generating `"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2_spec__4___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2_spec__2_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2_spec__5___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0;
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "type: "};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1 = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "unexpected number of goals after applying `Lean.and_imp`"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___closed__0_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___closed__1;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__0_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "injEq_helper"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__1_value;
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(167, 111, 180, 146, 132, 58, 155, 57)}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__2 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__2_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__4_value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Injective"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(55, 101, 109, 194, 24, 99, 201, 78)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(74, 76, 255, 124, 31, 108, 47, 16)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 106, 16, 37, 3, 60, 11, 157)}};
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
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 151, 10, 103, 183, 199, 62, 165)}};
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
lean_object* v___y_254_; lean_object* v___y_264_; uint8_t v___y_265_; lean_object* v___y_266_; lean_object* v___y_267_; uint8_t v___y_268_; lean_object* v___y_269_; lean_object* v___y_270_; lean_object* v___y_271_; lean_object* v___y_272_; lean_object* v___y_273_; lean_object* v___y_274_; lean_object* v___y_275_; lean_object* v___y_276_; lean_object* v___y_277_; lean_object* v___y_278_; lean_object* v___y_279_; uint8_t v___y_280_; lean_object* v_fileName_286_; lean_object* v_fileMap_287_; lean_object* v_options_288_; lean_object* v_currRecDepth_289_; lean_object* v_maxRecDepth_290_; lean_object* v_ref_291_; lean_object* v_currNamespace_292_; lean_object* v_openDecls_293_; lean_object* v_initHeartbeats_294_; lean_object* v_maxHeartbeats_295_; lean_object* v_quotContext_296_; lean_object* v_currMacroScope_297_; uint8_t v_diag_298_; lean_object* v_cancelTk_x3f_299_; uint8_t v_suppressElabErrors_300_; lean_object* v_inheritedTraceOptions_301_; 
v_fileName_286_ = lean_ctor_get(v___y_250_, 0);
v_fileMap_287_ = lean_ctor_get(v___y_250_, 1);
v_options_288_ = lean_ctor_get(v___y_250_, 2);
v_currRecDepth_289_ = lean_ctor_get(v___y_250_, 3);
v_maxRecDepth_290_ = lean_ctor_get(v___y_250_, 4);
v_ref_291_ = lean_ctor_get(v___y_250_, 5);
v_currNamespace_292_ = lean_ctor_get(v___y_250_, 6);
v_openDecls_293_ = lean_ctor_get(v___y_250_, 7);
v_initHeartbeats_294_ = lean_ctor_get(v___y_250_, 8);
v_maxHeartbeats_295_ = lean_ctor_get(v___y_250_, 9);
v_quotContext_296_ = lean_ctor_get(v___y_250_, 10);
v_currMacroScope_297_ = lean_ctor_get(v___y_250_, 11);
v_diag_298_ = lean_ctor_get_uint8(v___y_250_, sizeof(void*)*14);
v_cancelTk_x3f_299_ = lean_ctor_get(v___y_250_, 12);
v_suppressElabErrors_300_ = lean_ctor_get_uint8(v___y_250_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_301_ = lean_ctor_get(v___y_250_, 13);
if (lean_obj_tag(v_cancelTk_x3f_299_) == 1)
{
lean_object* v_val_307_; uint8_t v___x_308_; 
v_val_307_ = lean_ctor_get(v_cancelTk_x3f_299_, 0);
v___x_308_ = l_IO_CancelToken_isSet(v_val_307_);
if (v___x_308_ == 0)
{
goto v___jp_302_;
}
else
{
lean_object* v___x_309_; lean_object* v_a_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_317_; 
lean_dec_ref(v_x_248_);
v___x_309_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg();
v_a_310_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_317_ == 0)
{
v___x_312_ = v___x_309_;
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_a_310_);
lean_dec(v___x_309_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_315_; 
if (v_isShared_313_ == 0)
{
v___x_315_ = v___x_312_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_a_310_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
}
}
else
{
goto v___jp_302_;
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
if (v___y_280_ == 0)
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_281_ = lean_unsigned_to_nat(1u);
v___x_282_ = lean_nat_add(v___y_266_, v___x_281_);
lean_inc_ref(v___y_269_);
lean_inc(v___y_277_);
lean_inc(v___y_276_);
lean_inc(v___y_278_);
lean_inc(v___y_264_);
lean_inc(v___y_267_);
lean_inc(v___y_271_);
lean_inc(v___y_275_);
lean_inc(v___y_274_);
lean_inc(v___y_270_);
lean_inc_ref(v___y_279_);
lean_inc_ref(v___y_272_);
lean_inc_ref(v___y_273_);
v___x_283_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_283_, 0, v___y_273_);
lean_ctor_set(v___x_283_, 1, v___y_272_);
lean_ctor_set(v___x_283_, 2, v___y_279_);
lean_ctor_set(v___x_283_, 3, v___x_282_);
lean_ctor_set(v___x_283_, 4, v___y_270_);
lean_ctor_set(v___x_283_, 5, v___y_274_);
lean_ctor_set(v___x_283_, 6, v___y_275_);
lean_ctor_set(v___x_283_, 7, v___y_271_);
lean_ctor_set(v___x_283_, 8, v___y_267_);
lean_ctor_set(v___x_283_, 9, v___y_264_);
lean_ctor_set(v___x_283_, 10, v___y_278_);
lean_ctor_set(v___x_283_, 11, v___y_276_);
lean_ctor_set(v___x_283_, 12, v___y_277_);
lean_ctor_set(v___x_283_, 13, v___y_269_);
lean_ctor_set_uint8(v___x_283_, sizeof(void*)*14, v___y_265_);
lean_ctor_set_uint8(v___x_283_, sizeof(void*)*14 + 1, v___y_268_);
lean_inc(v___y_251_);
lean_inc(v___y_249_);
v___x_284_ = lean_apply_4(v_x_248_, v___y_249_, v___x_283_, v___y_251_, lean_box(0));
v___y_254_ = v___x_284_;
goto v___jp_253_;
}
else
{
lean_object* v___x_285_; 
lean_dec_ref(v_x_248_);
lean_inc(v___y_274_);
v___x_285_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg(v___y_274_);
v___y_254_ = v___x_285_;
goto v___jp_253_;
}
}
v___jp_302_:
{
lean_object* v___x_303_; uint8_t v___x_304_; uint8_t v___x_305_; 
v___x_303_ = lean_unsigned_to_nat(0u);
v___x_304_ = lean_nat_dec_eq(v_maxRecDepth_290_, v___x_303_);
v___x_305_ = lean_bool_not(v___x_304_);
if (v___x_305_ == 0)
{
v___y_264_ = v_maxHeartbeats_295_;
v___y_265_ = v_diag_298_;
v___y_266_ = v_currRecDepth_289_;
v___y_267_ = v_initHeartbeats_294_;
v___y_268_ = v_suppressElabErrors_300_;
v___y_269_ = v_inheritedTraceOptions_301_;
v___y_270_ = v_maxRecDepth_290_;
v___y_271_ = v_openDecls_293_;
v___y_272_ = v_fileMap_287_;
v___y_273_ = v_fileName_286_;
v___y_274_ = v_ref_291_;
v___y_275_ = v_currNamespace_292_;
v___y_276_ = v_currMacroScope_297_;
v___y_277_ = v_cancelTk_x3f_299_;
v___y_278_ = v_quotContext_296_;
v___y_279_ = v_options_288_;
v___y_280_ = v___x_305_;
goto v___jp_263_;
}
else
{
uint8_t v___x_306_; 
v___x_306_ = lean_nat_dec_eq(v_currRecDepth_289_, v_maxRecDepth_290_);
v___y_264_ = v_maxHeartbeats_295_;
v___y_265_ = v_diag_298_;
v___y_266_ = v_currRecDepth_289_;
v___y_267_ = v_initHeartbeats_294_;
v___y_268_ = v_suppressElabErrors_300_;
v___y_269_ = v_inheritedTraceOptions_301_;
v___y_270_ = v_maxRecDepth_290_;
v___y_271_ = v_openDecls_293_;
v___y_272_ = v_fileMap_287_;
v___y_273_ = v_fileName_286_;
v___y_274_ = v_ref_291_;
v___y_275_ = v_currNamespace_292_;
v___y_276_ = v_currMacroScope_297_;
v___y_277_ = v_cancelTk_x3f_299_;
v___y_278_ = v_quotContext_296_;
v___y_279_ = v_options_288_;
v___y_280_ = v___x_306_;
goto v___jp_263_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(v_x_318_, v___y_319_, v___y_320_, v___y_321_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
lean_dec(v___y_319_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_324_, lean_object* v_x_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_329_ = lean_apply_1(v_x_325_, lean_box(0));
v___x_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_331_, lean_object* v_x_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(v_00_u03b1_331_, v_x_332_, v___y_333_, v___y_334_);
lean_dec(v___y_334_);
lean_dec_ref(v___y_333_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_a_337_, lean_object* v_x_338_){
_start:
{
if (lean_obj_tag(v_x_338_) == 0)
{
lean_object* v___x_339_; 
v___x_339_ = lean_box(0);
return v___x_339_;
}
else
{
lean_object* v_key_340_; lean_object* v_value_341_; lean_object* v_tail_342_; uint8_t v___x_343_; 
v_key_340_ = lean_ctor_get(v_x_338_, 0);
v_value_341_ = lean_ctor_get(v_x_338_, 1);
v_tail_342_ = lean_ctor_get(v_x_338_, 2);
v___x_343_ = l_Lean_ExprStructEq_beq(v_key_340_, v_a_337_);
if (v___x_343_ == 0)
{
v_x_338_ = v_tail_342_;
goto _start;
}
else
{
lean_object* v___x_345_; 
lean_inc(v_value_341_);
v___x_345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_345_, 0, v_value_341_);
return v___x_345_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_a_346_, lean_object* v_x_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(v_a_346_, v_x_347_);
lean_dec(v_x_347_);
lean_dec_ref(v_a_346_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(lean_object* v_m_349_, lean_object* v_a_350_){
_start:
{
lean_object* v_buckets_351_; lean_object* v___x_352_; uint64_t v___x_353_; uint64_t v___x_354_; uint64_t v___x_355_; uint64_t v_fold_356_; uint64_t v___x_357_; uint64_t v___x_358_; uint64_t v___x_359_; size_t v___x_360_; size_t v___x_361_; size_t v___x_362_; size_t v___x_363_; size_t v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v_buckets_351_ = lean_ctor_get(v_m_349_, 1);
v___x_352_ = lean_array_get_size(v_buckets_351_);
v___x_353_ = l_Lean_ExprStructEq_hash(v_a_350_);
v___x_354_ = 32ULL;
v___x_355_ = lean_uint64_shift_right(v___x_353_, v___x_354_);
v_fold_356_ = lean_uint64_xor(v___x_353_, v___x_355_);
v___x_357_ = 16ULL;
v___x_358_ = lean_uint64_shift_right(v_fold_356_, v___x_357_);
v___x_359_ = lean_uint64_xor(v_fold_356_, v___x_358_);
v___x_360_ = lean_uint64_to_usize(v___x_359_);
v___x_361_ = lean_usize_of_nat(v___x_352_);
v___x_362_ = ((size_t)1ULL);
v___x_363_ = lean_usize_sub(v___x_361_, v___x_362_);
v___x_364_ = lean_usize_land(v___x_360_, v___x_363_);
v___x_365_ = lean_array_uget_borrowed(v_buckets_351_, v___x_364_);
v___x_366_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(v_a_350_, v___x_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_367_, lean_object* v_a_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(v_m_367_, v_a_368_);
lean_dec_ref(v_a_368_);
lean_dec_ref(v_m_367_);
return v_res_369_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0(void){
_start:
{
lean_object* v___x_371_; lean_object* v_dummy_372_; 
v___x_371_ = lean_box(0);
v_dummy_372_ = l_Lean_Expr_sort___override(v___x_371_);
return v_dummy_372_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1(lean_object* v_pre_373_, lean_object* v_post_374_, size_t v_sz_375_, size_t v_i_376_, lean_object* v_bs_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
uint8_t v___x_382_; 
v___x_382_ = lean_usize_dec_lt(v_i_376_, v_sz_375_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; 
lean_dec_ref(v_post_374_);
lean_dec_ref(v_pre_373_);
v___x_383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_383_, 0, v_bs_377_);
return v___x_383_;
}
else
{
lean_object* v_v_384_; lean_object* v___x_385_; 
v_v_384_ = lean_array_uget_borrowed(v_bs_377_, v_i_376_);
lean_inc(v_v_384_);
lean_inc_ref(v_post_374_);
lean_inc_ref(v_pre_373_);
v___x_385_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_373_, v_post_374_, v_v_384_, v___y_378_, v___y_379_, v___y_380_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_object* v_a_386_; lean_object* v___x_387_; lean_object* v_bs_x27_388_; size_t v___x_389_; size_t v___x_390_; lean_object* v___x_391_; 
v_a_386_ = lean_ctor_get(v___x_385_, 0);
lean_inc(v_a_386_);
lean_dec_ref_known(v___x_385_, 1);
v___x_387_ = lean_unsigned_to_nat(0u);
v_bs_x27_388_ = lean_array_uset(v_bs_377_, v_i_376_, v___x_387_);
v___x_389_ = ((size_t)1ULL);
v___x_390_ = lean_usize_add(v_i_376_, v___x_389_);
v___x_391_ = lean_array_uset(v_bs_x27_388_, v_i_376_, v_a_386_);
v_i_376_ = v___x_390_;
v_bs_377_ = v___x_391_;
goto _start;
}
else
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_400_; 
lean_dec_ref(v_bs_377_);
lean_dec_ref(v_post_374_);
lean_dec_ref(v_pre_373_);
v_a_393_ = lean_ctor_get(v___x_385_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_400_ == 0)
{
v___x_395_ = v___x_385_;
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_385_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_398_; 
if (v_isShared_396_ == 0)
{
v___x_398_ = v___x_395_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_a_393_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4(lean_object* v_pre_401_, lean_object* v_post_402_, lean_object* v_x_403_, lean_object* v_x_404_, lean_object* v_x_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_){
_start:
{
if (lean_obj_tag(v_x_403_) == 5)
{
lean_object* v_fn_410_; lean_object* v_arg_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v_fn_410_ = lean_ctor_get(v_x_403_, 0);
lean_inc_ref(v_fn_410_);
v_arg_411_ = lean_ctor_get(v_x_403_, 1);
lean_inc_ref(v_arg_411_);
lean_dec_ref_known(v_x_403_, 2);
v___x_412_ = lean_array_set(v_x_404_, v_x_405_, v_arg_411_);
v___x_413_ = lean_unsigned_to_nat(1u);
v___x_414_ = lean_nat_sub(v_x_405_, v___x_413_);
lean_dec(v_x_405_);
v_x_403_ = v_fn_410_;
v_x_404_ = v___x_412_;
v_x_405_ = v___x_414_;
goto _start;
}
else
{
lean_object* v___x_416_; 
lean_dec(v_x_405_);
lean_inc_ref(v_post_402_);
lean_inc_ref(v_pre_401_);
v___x_416_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_401_, v_post_402_, v_x_403_, v___y_406_, v___y_407_, v___y_408_);
if (lean_obj_tag(v___x_416_) == 0)
{
lean_object* v_a_417_; size_t v_sz_418_; size_t v___x_419_; lean_object* v___x_420_; 
v_a_417_ = lean_ctor_get(v___x_416_, 0);
lean_inc(v_a_417_);
lean_dec_ref_known(v___x_416_, 1);
v_sz_418_ = lean_array_size(v_x_404_);
v___x_419_ = ((size_t)0ULL);
lean_inc_ref(v_post_402_);
lean_inc_ref(v_pre_401_);
v___x_420_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1(v_pre_401_, v_post_402_, v_sz_418_, v___x_419_, v_x_404_, v___y_406_, v___y_407_, v___y_408_);
if (lean_obj_tag(v___x_420_) == 0)
{
lean_object* v_a_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v_a_421_ = lean_ctor_get(v___x_420_, 0);
lean_inc(v_a_421_);
lean_dec_ref_known(v___x_420_, 1);
v___x_422_ = l_Lean_mkAppN(v_a_417_, v_a_421_);
lean_dec(v_a_421_);
v___x_423_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_401_, v_post_402_, v___x_422_, v___y_406_, v___y_407_, v___y_408_);
return v___x_423_;
}
else
{
lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_431_; 
lean_dec(v_a_417_);
lean_dec_ref(v_post_402_);
lean_dec_ref(v_pre_401_);
v_a_424_ = lean_ctor_get(v___x_420_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_431_ == 0)
{
v___x_426_ = v___x_420_;
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_dec(v___x_420_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_429_; 
if (v_isShared_427_ == 0)
{
v___x_429_ = v___x_426_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_a_424_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
else
{
lean_dec_ref(v_x_404_);
lean_dec_ref(v_post_402_);
lean_dec_ref(v_pre_401_);
return v___x_416_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1(lean_object* v___x_432_, lean_object* v_pre_433_, lean_object* v_e_434_, lean_object* v_post_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_){
_start:
{
lean_object* v___y_441_; lean_object* v___y_442_; uint8_t v___y_443_; lean_object* v___y_444_; lean_object* v___y_445_; lean_object* v___y_446_; lean_object* v___y_447_; uint8_t v___y_448_; lean_object* v___y_458_; uint8_t v___y_459_; lean_object* v___y_460_; lean_object* v___y_461_; lean_object* v___y_462_; uint8_t v___y_463_; lean_object* v___y_471_; lean_object* v___y_472_; uint8_t v___y_473_; lean_object* v___y_474_; lean_object* v___y_475_; uint8_t v___y_476_; lean_object* v___x_483_; 
v___x_483_ = l_Lean_Core_checkSystem(v___x_432_, v___y_437_, v___y_438_);
if (lean_obj_tag(v___x_483_) == 0)
{
lean_object* v___x_484_; 
lean_dec_ref_known(v___x_483_, 1);
lean_inc_ref(v_pre_433_);
lean_inc(v___y_438_);
lean_inc_ref(v___y_437_);
lean_inc_ref(v_e_434_);
v___x_484_ = lean_apply_4(v_pre_433_, v_e_434_, v___y_437_, v___y_438_, lean_box(0));
if (lean_obj_tag(v___x_484_) == 0)
{
lean_object* v_a_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_574_; 
v_a_485_ = lean_ctor_get(v___x_484_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_574_ == 0)
{
v___x_487_ = v___x_484_;
v_isShared_488_ = v_isSharedCheck_574_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_a_485_);
lean_dec(v___x_484_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_574_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___y_490_; 
switch(lean_obj_tag(v_a_485_))
{
case 0:
{
lean_object* v_e_564_; lean_object* v___x_566_; 
lean_dec_ref(v_post_435_);
lean_dec_ref(v_e_434_);
lean_dec_ref(v_pre_433_);
v_e_564_ = lean_ctor_get(v_a_485_, 0);
lean_inc_ref(v_e_564_);
lean_dec_ref_known(v_a_485_, 1);
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 0, v_e_564_);
v___x_566_ = v___x_487_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_e_564_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
case 1:
{
lean_object* v_e_568_; lean_object* v___x_569_; 
lean_del_object(v___x_487_);
lean_dec_ref(v_e_434_);
v_e_568_ = lean_ctor_get(v_a_485_, 0);
lean_inc_ref(v_e_568_);
lean_dec_ref_known(v_a_485_, 1);
lean_inc_ref(v_post_435_);
lean_inc_ref(v_pre_433_);
v___x_569_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_433_, v_post_435_, v_e_568_, v___y_436_, v___y_437_, v___y_438_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v_a_570_; lean_object* v___x_571_; 
v_a_570_ = lean_ctor_get(v___x_569_, 0);
lean_inc(v_a_570_);
lean_dec_ref_known(v___x_569_, 1);
v___x_571_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_433_, v_post_435_, v_a_570_, v___y_436_, v___y_437_, v___y_438_);
return v___x_571_;
}
else
{
lean_dec_ref(v_post_435_);
lean_dec_ref(v_pre_433_);
return v___x_569_;
}
}
default: 
{
lean_object* v_e_x3f_572_; 
lean_del_object(v___x_487_);
v_e_x3f_572_ = lean_ctor_get(v_a_485_, 0);
lean_inc(v_e_x3f_572_);
lean_dec_ref_known(v_a_485_, 1);
if (lean_obj_tag(v_e_x3f_572_) == 0)
{
v___y_490_ = v_e_434_;
goto v___jp_489_;
}
else
{
lean_object* v_val_573_; 
lean_dec_ref(v_e_434_);
v_val_573_ = lean_ctor_get(v_e_x3f_572_, 0);
lean_inc(v_val_573_);
lean_dec_ref_known(v_e_x3f_572_, 1);
v___y_490_ = v_val_573_;
goto v___jp_489_;
}
}
}
v___jp_489_:
{
switch(lean_obj_tag(v___y_490_))
{
case 7:
{
lean_object* v_binderName_491_; lean_object* v_binderType_492_; lean_object* v_body_493_; uint8_t v_binderInfo_494_; lean_object* v___x_495_; 
v_binderName_491_ = lean_ctor_get(v___y_490_, 0);
lean_inc(v_binderName_491_);
v_binderType_492_ = lean_ctor_get(v___y_490_, 1);
v_body_493_ = lean_ctor_get(v___y_490_, 2);
v_binderInfo_494_ = lean_ctor_get_uint8(v___y_490_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_492_);
lean_inc_ref(v_post_435_);
lean_inc_ref(v_pre_433_);
v___x_495_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_433_, v_post_435_, v_binderType_492_, v___y_436_, v___y_437_, v___y_438_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v_a_496_; lean_object* v___x_497_; 
v_a_496_ = lean_ctor_get(v___x_495_, 0);
lean_inc(v_a_496_);
lean_dec_ref_known(v___x_495_, 1);
lean_inc_ref(v_body_493_);
lean_inc_ref(v_post_435_);
lean_inc_ref(v_pre_433_);
v___x_497_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_433_, v_post_435_, v_body_493_, v___y_436_, v___y_437_, v___y_438_);
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v_a_498_; size_t v___x_499_; size_t v___x_500_; uint8_t v___x_501_; 
v_a_498_ = lean_ctor_get(v___x_497_, 0);
lean_inc(v_a_498_);
lean_dec_ref_known(v___x_497_, 1);
v___x_499_ = lean_ptr_addr(v_binderType_492_);
v___x_500_ = lean_ptr_addr(v_a_496_);
v___x_501_ = lean_usize_dec_eq(v___x_499_, v___x_500_);
if (v___x_501_ == 0)
{
v___y_471_ = v_a_498_;
v___y_472_ = v_binderName_491_;
v___y_473_ = v_binderInfo_494_;
v___y_474_ = v___y_490_;
v___y_475_ = v_a_496_;
v___y_476_ = v___x_501_;
goto v___jp_470_;
}
else
{
size_t v___x_502_; size_t v___x_503_; uint8_t v___x_504_; 
v___x_502_ = lean_ptr_addr(v_body_493_);
v___x_503_ = lean_ptr_addr(v_a_498_);
v___x_504_ = lean_usize_dec_eq(v___x_502_, v___x_503_);
v___y_471_ = v_a_498_;
v___y_472_ = v_binderName_491_;
v___y_473_ = v_binderInfo_494_;
v___y_474_ = v___y_490_;
v___y_475_ = v_a_496_;
v___y_476_ = v___x_504_;
goto v___jp_470_;
}
}
else
{
lean_dec(v_a_496_);
lean_dec_ref_known(v___y_490_, 3);
lean_dec(v_binderName_491_);
lean_dec_ref(v_post_435_);
lean_dec_ref(v_pre_433_);
return v___x_497_;
}
}
else
{
lean_dec(v_binderName_491_);
lean_dec_ref_known(v___y_490_, 3);
lean_dec_ref(v_post_435_);
lean_dec_ref(v_pre_433_);
return v___x_495_;
}
}
case 6:
{
lean_object* v_binderName_505_; lean_object* v_binderType_506_; lean_object* v_body_507_; uint8_t v_binderInfo_508_; lean_object* v___x_509_; 
v_binderName_505_ = lean_ctor_get(v___y_490_, 0);
lean_inc(v_binderName_505_);
v_binderType_506_ = lean_ctor_get(v___y_490_, 1);
v_body_507_ = lean_ctor_get(v___y_490_, 2);
v_binderInfo_508_ = lean_ctor_get_uint8(v___y_490_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_506_);
lean_inc_ref(v_post_435_);
lean_inc_ref(v_pre_433_);
v___x_509_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_433_, v_post_435_, v_binderType_506_, v___y_436_, v___y_437_, v___y_438_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v_a_510_; lean_object* v___x_511_; 
v_a_510_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_a_510_);
lean_dec_ref_known(v___x_509_, 1);
lean_inc_ref(v_body_507_);
lean_inc_ref(v_post_435_);
lean_inc_ref(v_pre_433_);
v___x_511_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_433_, v_post_435_, v_body_507_, v___y_436_, v___y_437_, v___y_438_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v_a_512_; size_t v___x_513_; size_t v___x_514_; uint8_t v___x_515_; 
v_a_512_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_a_512_);
lean_dec_ref_known(v___x_511_, 1);
v___x_513_ = lean_ptr_addr(v_binderType_506_);
v___x_514_ = lean_ptr_addr(v_a_510_);
v___x_515_ = lean_usize_dec_eq(v___x_513_, v___x_514_);
if (v___x_515_ == 0)
{
v___y_458_ = v_a_512_;
v___y_459_ = v_binderInfo_508_;
v___y_460_ = v_a_510_;
v___y_461_ = v___y_490_;
v___y_462_ = v_binderName_505_;
v___y_463_ = v___x_515_;
goto v___jp_457_;
}
else
{
size_t v___x_516_; size_t v___x_517_; uint8_t v___x_518_; 
v___x_516_ = lean_ptr_addr(v_body_507_);
v___x_517_ = lean_ptr_addr(v_a_512_);
v___x_518_ = lean_usize_dec_eq(v___x_516_, v___x_517_);
v___y_458_ = v_a_512_;
v___y_459_ = v_binderInfo_508_;
v___y_460_ = v_a_510_;
v___y_461_ = v___y_490_;
v___y_462_ = v_binderName_505_;
v___y_463_ = v___x_518_;
goto v___jp_457_;
}
}
else
{
lean_dec(v_a_510_);
lean_dec(v_binderName_505_);
lean_dec_ref_known(v___y_490_, 3);
lean_dec_ref(v_post_435_);
lean_dec_ref(v_pre_433_);
return v___x_511_;
}
}
else
{
lean_dec(v_binderName_505_);
lean_dec_ref_known(v___y_490_, 3);
lean_dec_ref(v_post_435_);
lean_dec_ref(v_pre_433_);
return v___x_509_;
}
}
case 8:
{
lean_object* v_declName_519_; lean_object* v_type_520_; lean_object* v_value_521_; lean_object* v_body_522_; uint8_t v_nondep_523_; lean_object* v___x_524_; 
v_declName_519_ = lean_ctor_get(v___y_490_, 0);
lean_inc(v_declName_519_);
v_type_520_ = lean_ctor_get(v___y_490_, 1);
v_value_521_ = lean_ctor_get(v___y_490_, 2);
v_body_522_ = lean_ctor_get(v___y_490_, 3);
lean_inc_ref(v_body_522_);
v_nondep_523_ = lean_ctor_get_uint8(v___y_490_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_520_);
lean_inc_ref(v_post_435_);
lean_inc_ref(v_pre_433_);
v___x_524_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_433_, v_post_435_, v_type_520_, v___y_436_, v___y_437_, v___y_438_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_object* v_a_525_; lean_object* v___x_526_; 
v_a_525_ = lean_ctor_get(v___x_524_, 0);
lean_inc(v_a_525_);
lean_dec_ref_known(v___x_524_, 1);
lean_inc_ref(v_value_521_);
lean_inc_ref(v_post_435_);
lean_inc_ref(v_pre_433_);
v___x_526_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_433_, v_post_435_, v_value_521_, v___y_436_, v___y_437_, v___y_438_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_object* v_a_527_; lean_object* v___x_528_; 
v_a_527_ = lean_ctor_get(v___x_526_, 0);
lean_inc(v_a_527_);
lean_dec_ref_known(v___x_526_, 1);
lean_inc_ref(v_body_522_);
lean_inc_ref(v_post_435_);
lean_inc_ref(v_pre_433_);
v___x_528_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_433_, v_post_435_, v_body_522_, v___y_436_, v___y_437_, v___y_438_);
if (lean_obj_tag(v___x_528_) == 0)
{
lean_object* v_a_529_; size_t v___x_530_; size_t v___x_531_; uint8_t v___x_532_; 
v_a_529_ = lean_ctor_get(v___x_528_, 0);
lean_inc(v_a_529_);
lean_dec_ref_known(v___x_528_, 1);
v___x_530_ = lean_ptr_addr(v_type_520_);
v___x_531_ = lean_ptr_addr(v_a_525_);
v___x_532_ = lean_usize_dec_eq(v___x_530_, v___x_531_);
if (v___x_532_ == 0)
{
v___y_441_ = v_a_529_;
v___y_442_ = v_declName_519_;
v___y_443_ = v_nondep_523_;
v___y_444_ = v_a_525_;
v___y_445_ = v___y_490_;
v___y_446_ = v_body_522_;
v___y_447_ = v_a_527_;
v___y_448_ = v___x_532_;
goto v___jp_440_;
}
else
{
size_t v___x_533_; size_t v___x_534_; uint8_t v___x_535_; 
v___x_533_ = lean_ptr_addr(v_value_521_);
v___x_534_ = lean_ptr_addr(v_a_527_);
v___x_535_ = lean_usize_dec_eq(v___x_533_, v___x_534_);
v___y_441_ = v_a_529_;
v___y_442_ = v_declName_519_;
v___y_443_ = v_nondep_523_;
v___y_444_ = v_a_525_;
v___y_445_ = v___y_490_;
v___y_446_ = v_body_522_;
v___y_447_ = v_a_527_;
v___y_448_ = v___x_535_;
goto v___jp_440_;
}
}
else
{
lean_dec(v_a_527_);
lean_dec(v_a_525_);
lean_dec_ref(v_body_522_);
lean_dec(v_declName_519_);
lean_dec_ref_known(v___y_490_, 4);
lean_dec_ref(v_post_435_);
lean_dec_ref(v_pre_433_);
return v___x_528_;
}
}
else
{
lean_dec(v_a_525_);
lean_dec_ref(v_body_522_);
lean_dec(v_declName_519_);
lean_dec_ref_known(v___y_490_, 4);
lean_dec_ref(v_post_435_);
lean_dec_ref(v_pre_433_);
return v___x_526_;
}
}
else
{
lean_dec_ref(v_body_522_);
lean_dec(v_declName_519_);
lean_dec_ref_known(v___y_490_, 4);
lean_dec_ref(v_post_435_);
lean_dec_ref(v_pre_433_);
return v___x_524_;
}
}
case 5:
{
lean_object* v_dummy_536_; lean_object* v_nargs_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v_dummy_536_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0);
v_nargs_537_ = l_Lean_Expr_getAppNumArgs(v___y_490_);
lean_inc(v_nargs_537_);
v___x_538_ = lean_mk_array(v_nargs_537_, v_dummy_536_);
v___x_539_ = lean_unsigned_to_nat(1u);
v___x_540_ = lean_nat_sub(v_nargs_537_, v___x_539_);
lean_dec(v_nargs_537_);
v___x_541_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4(v_pre_433_, v_post_435_, v___y_490_, v___x_538_, v___x_540_, v___y_436_, v___y_437_, v___y_438_);
return v___x_541_;
}
case 10:
{
lean_object* v_data_542_; lean_object* v_expr_543_; lean_object* v___x_544_; 
v_data_542_ = lean_ctor_get(v___y_490_, 0);
v_expr_543_ = lean_ctor_get(v___y_490_, 1);
lean_inc_ref(v_expr_543_);
lean_inc_ref(v_post_435_);
lean_inc_ref(v_pre_433_);
v___x_544_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_433_, v_post_435_, v_expr_543_, v___y_436_, v___y_437_, v___y_438_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v_a_545_; size_t v___x_546_; size_t v___x_547_; uint8_t v___x_548_; 
v_a_545_ = lean_ctor_get(v___x_544_, 0);
lean_inc(v_a_545_);
lean_dec_ref_known(v___x_544_, 1);
v___x_546_ = lean_ptr_addr(v_expr_543_);
v___x_547_ = lean_ptr_addr(v_a_545_);
v___x_548_ = lean_usize_dec_eq(v___x_546_, v___x_547_);
if (v___x_548_ == 0)
{
lean_object* v___x_549_; lean_object* v___x_550_; 
lean_inc(v_data_542_);
lean_dec_ref_known(v___y_490_, 2);
v___x_549_ = l_Lean_Expr_mdata___override(v_data_542_, v_a_545_);
v___x_550_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_433_, v_post_435_, v___x_549_, v___y_436_, v___y_437_, v___y_438_);
return v___x_550_;
}
else
{
lean_object* v___x_551_; 
lean_dec(v_a_545_);
v___x_551_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_433_, v_post_435_, v___y_490_, v___y_436_, v___y_437_, v___y_438_);
return v___x_551_;
}
}
else
{
lean_dec_ref_known(v___y_490_, 2);
lean_dec_ref(v_post_435_);
lean_dec_ref(v_pre_433_);
return v___x_544_;
}
}
case 11:
{
lean_object* v_typeName_552_; lean_object* v_idx_553_; lean_object* v_struct_554_; lean_object* v___x_555_; 
v_typeName_552_ = lean_ctor_get(v___y_490_, 0);
v_idx_553_ = lean_ctor_get(v___y_490_, 1);
v_struct_554_ = lean_ctor_get(v___y_490_, 2);
lean_inc_ref(v_struct_554_);
lean_inc_ref(v_post_435_);
lean_inc_ref(v_pre_433_);
v___x_555_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_433_, v_post_435_, v_struct_554_, v___y_436_, v___y_437_, v___y_438_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v_a_556_; size_t v___x_557_; size_t v___x_558_; uint8_t v___x_559_; 
v_a_556_ = lean_ctor_get(v___x_555_, 0);
lean_inc(v_a_556_);
lean_dec_ref_known(v___x_555_, 1);
v___x_557_ = lean_ptr_addr(v_struct_554_);
v___x_558_ = lean_ptr_addr(v_a_556_);
v___x_559_ = lean_usize_dec_eq(v___x_557_, v___x_558_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; lean_object* v___x_561_; 
lean_inc(v_idx_553_);
lean_inc(v_typeName_552_);
lean_dec_ref_known(v___y_490_, 3);
v___x_560_ = l_Lean_Expr_proj___override(v_typeName_552_, v_idx_553_, v_a_556_);
v___x_561_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_433_, v_post_435_, v___x_560_, v___y_436_, v___y_437_, v___y_438_);
return v___x_561_;
}
else
{
lean_object* v___x_562_; 
lean_dec(v_a_556_);
v___x_562_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_433_, v_post_435_, v___y_490_, v___y_436_, v___y_437_, v___y_438_);
return v___x_562_;
}
}
else
{
lean_dec_ref_known(v___y_490_, 3);
lean_dec_ref(v_post_435_);
lean_dec_ref(v_pre_433_);
return v___x_555_;
}
}
default: 
{
lean_object* v___x_563_; 
v___x_563_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_433_, v_post_435_, v___y_490_, v___y_436_, v___y_437_, v___y_438_);
return v___x_563_;
}
}
}
}
}
else
{
lean_object* v_a_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_582_; 
lean_dec_ref(v_post_435_);
lean_dec_ref(v_e_434_);
lean_dec_ref(v_pre_433_);
v_a_575_ = lean_ctor_get(v___x_484_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_582_ == 0)
{
v___x_577_ = v___x_484_;
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_a_575_);
lean_dec(v___x_484_);
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
else
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_590_; 
lean_dec_ref(v_post_435_);
lean_dec_ref(v_e_434_);
lean_dec_ref(v_pre_433_);
v_a_583_ = lean_ctor_get(v___x_483_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_590_ == 0)
{
v___x_585_ = v___x_483_;
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_483_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_588_; 
if (v_isShared_586_ == 0)
{
v___x_588_ = v___x_585_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_583_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
v___jp_440_:
{
if (v___y_448_ == 0)
{
lean_object* v___x_449_; lean_object* v___x_450_; 
lean_dec_ref(v___y_446_);
lean_dec_ref(v___y_445_);
v___x_449_ = l_Lean_Expr_letE___override(v___y_442_, v___y_444_, v___y_447_, v___y_441_, v___y_443_);
v___x_450_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_433_, v_post_435_, v___x_449_, v___y_436_, v___y_437_, v___y_438_);
return v___x_450_;
}
else
{
size_t v___x_451_; size_t v___x_452_; uint8_t v___x_453_; 
v___x_451_ = lean_ptr_addr(v___y_446_);
lean_dec_ref(v___y_446_);
v___x_452_ = lean_ptr_addr(v___y_441_);
v___x_453_ = lean_usize_dec_eq(v___x_451_, v___x_452_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; lean_object* v___x_455_; 
lean_dec_ref(v___y_445_);
v___x_454_ = l_Lean_Expr_letE___override(v___y_442_, v___y_444_, v___y_447_, v___y_441_, v___y_443_);
v___x_455_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_433_, v_post_435_, v___x_454_, v___y_436_, v___y_437_, v___y_438_);
return v___x_455_;
}
else
{
lean_object* v___x_456_; 
lean_dec_ref(v___y_447_);
lean_dec_ref(v___y_444_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
v___x_456_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_433_, v_post_435_, v___y_445_, v___y_436_, v___y_437_, v___y_438_);
return v___x_456_;
}
}
}
v___jp_457_:
{
if (v___y_463_ == 0)
{
lean_object* v___x_464_; lean_object* v___x_465_; 
lean_dec_ref(v___y_461_);
v___x_464_ = l_Lean_Expr_lam___override(v___y_462_, v___y_460_, v___y_458_, v___y_459_);
v___x_465_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_433_, v_post_435_, v___x_464_, v___y_436_, v___y_437_, v___y_438_);
return v___x_465_;
}
else
{
uint8_t v___x_466_; 
v___x_466_ = l_Lean_instBEqBinderInfo_beq(v___y_459_, v___y_459_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; lean_object* v___x_468_; 
lean_dec_ref(v___y_461_);
v___x_467_ = l_Lean_Expr_lam___override(v___y_462_, v___y_460_, v___y_458_, v___y_459_);
v___x_468_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_433_, v_post_435_, v___x_467_, v___y_436_, v___y_437_, v___y_438_);
return v___x_468_;
}
else
{
lean_object* v___x_469_; 
lean_dec(v___y_462_);
lean_dec_ref(v___y_460_);
lean_dec_ref(v___y_458_);
v___x_469_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_433_, v_post_435_, v___y_461_, v___y_436_, v___y_437_, v___y_438_);
return v___x_469_;
}
}
}
v___jp_470_:
{
if (v___y_476_ == 0)
{
lean_object* v___x_477_; lean_object* v___x_478_; 
lean_dec_ref(v___y_474_);
v___x_477_ = l_Lean_Expr_forallE___override(v___y_472_, v___y_475_, v___y_471_, v___y_473_);
v___x_478_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_433_, v_post_435_, v___x_477_, v___y_436_, v___y_437_, v___y_438_);
return v___x_478_;
}
else
{
uint8_t v___x_479_; 
v___x_479_ = l_Lean_instBEqBinderInfo_beq(v___y_473_, v___y_473_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; lean_object* v___x_481_; 
lean_dec_ref(v___y_474_);
v___x_480_ = l_Lean_Expr_forallE___override(v___y_472_, v___y_475_, v___y_471_, v___y_473_);
v___x_481_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_433_, v_post_435_, v___x_480_, v___y_436_, v___y_437_, v___y_438_);
return v___x_481_;
}
else
{
lean_object* v___x_482_; 
lean_dec_ref(v___y_475_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
v___x_482_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_433_, v_post_435_, v___y_474_, v___y_436_, v___y_437_, v___y_438_);
return v___x_482_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___boxed(lean_object* v___x_591_, lean_object* v_pre_592_, lean_object* v_e_593_, lean_object* v_post_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1(v___x_591_, v_pre_592_, v_e_593_, v_post_594_, v___y_595_, v___y_596_, v___y_597_);
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
lean_dec(v___y_595_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(lean_object* v_pre_600_, lean_object* v_post_601_, lean_object* v_e_602_, lean_object* v_a_603_, lean_object* v___y_604_, lean_object* v___y_605_){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; 
lean_inc(v_a_603_);
v___x_607_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_607_, 0, lean_box(0));
lean_closure_set(v___x_607_, 1, lean_box(0));
lean_closure_set(v___x_607_, 2, v_a_603_);
v___x_608_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(lean_box(0), v___x_607_, v___y_604_, v___y_605_);
if (lean_obj_tag(v___x_608_) == 0)
{
lean_object* v_a_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_640_; 
v_a_609_ = lean_ctor_get(v___x_608_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_640_ == 0)
{
v___x_611_ = v___x_608_;
v_isShared_612_ = v_isSharedCheck_640_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_a_609_);
lean_dec(v___x_608_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_640_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_613_; 
v___x_613_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(v_a_609_, v_e_602_);
lean_dec(v_a_609_);
if (lean_obj_tag(v___x_613_) == 0)
{
lean_object* v___x_614_; lean_object* v___f_615_; lean_object* v___x_616_; 
lean_del_object(v___x_611_);
v___x_614_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___closed__0));
lean_inc_ref(v_e_602_);
v___f_615_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___boxed), 8, 4);
lean_closure_set(v___f_615_, 0, v___x_614_);
lean_closure_set(v___f_615_, 1, v_pre_600_);
lean_closure_set(v___f_615_, 2, v_e_602_);
lean_closure_set(v___f_615_, 3, v_post_601_);
v___x_616_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(v___f_615_, v_a_603_, v___y_604_, v___y_605_);
if (lean_obj_tag(v___x_616_) == 0)
{
lean_object* v_a_617_; lean_object* v___f_618_; lean_object* v___x_619_; 
v_a_617_ = lean_ctor_get(v___x_616_, 0);
lean_inc_n(v_a_617_, 2);
lean_dec_ref_known(v___x_616_, 1);
lean_inc(v_a_603_);
v___f_618_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_618_, 0, v_a_603_);
lean_closure_set(v___f_618_, 1, v_e_602_);
lean_closure_set(v___f_618_, 2, v_a_617_);
v___x_619_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(lean_box(0), v___f_618_, v___y_604_, v___y_605_);
if (lean_obj_tag(v___x_619_) == 0)
{
lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_626_; 
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_619_);
if (v_isSharedCheck_626_ == 0)
{
lean_object* v_unused_627_; 
v_unused_627_ = lean_ctor_get(v___x_619_, 0);
lean_dec(v_unused_627_);
v___x_621_ = v___x_619_;
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
else
{
lean_dec(v___x_619_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_624_; 
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v_a_617_);
v___x_624_ = v___x_621_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_a_617_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
else
{
lean_object* v_a_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_635_; 
lean_dec(v_a_617_);
v_a_628_ = lean_ctor_get(v___x_619_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_619_);
if (v_isSharedCheck_635_ == 0)
{
v___x_630_ = v___x_619_;
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_a_628_);
lean_dec(v___x_619_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_633_; 
if (v_isShared_631_ == 0)
{
v___x_633_ = v___x_630_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_a_628_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
}
else
{
lean_dec_ref(v_e_602_);
return v___x_616_;
}
}
else
{
lean_object* v_val_636_; lean_object* v___x_638_; 
lean_dec_ref(v_e_602_);
lean_dec_ref(v_post_601_);
lean_dec_ref(v_pre_600_);
v_val_636_ = lean_ctor_get(v___x_613_, 0);
lean_inc(v_val_636_);
lean_dec_ref_known(v___x_613_, 1);
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 0, v_val_636_);
v___x_638_ = v___x_611_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_val_636_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
}
else
{
lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_648_; 
lean_dec_ref(v_e_602_);
lean_dec_ref(v_post_601_);
lean_dec_ref(v_pre_600_);
v_a_641_ = lean_ctor_get(v___x_608_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_648_ == 0)
{
v___x_643_ = v___x_608_;
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_dec(v___x_608_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_646_; 
if (v_isShared_644_ == 0)
{
v___x_646_ = v___x_643_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_a_641_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(lean_object* v_pre_649_, lean_object* v_post_650_, lean_object* v_e_651_, lean_object* v_a_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
lean_object* v___x_656_; 
lean_inc_ref(v_post_650_);
lean_inc(v___y_654_);
lean_inc_ref(v___y_653_);
lean_inc_ref(v_e_651_);
v___x_656_ = lean_apply_4(v_post_650_, v_e_651_, v___y_653_, v___y_654_, lean_box(0));
if (lean_obj_tag(v___x_656_) == 0)
{
lean_object* v_a_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_675_; 
v_a_657_ = lean_ctor_get(v___x_656_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_675_ == 0)
{
v___x_659_ = v___x_656_;
v_isShared_660_ = v_isSharedCheck_675_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_a_657_);
lean_dec(v___x_656_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_675_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
switch(lean_obj_tag(v_a_657_))
{
case 0:
{
lean_object* v_e_661_; lean_object* v___x_663_; 
lean_dec_ref(v_e_651_);
lean_dec_ref(v_post_650_);
lean_dec_ref(v_pre_649_);
v_e_661_ = lean_ctor_get(v_a_657_, 0);
lean_inc_ref(v_e_661_);
lean_dec_ref_known(v_a_657_, 1);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 0, v_e_661_);
v___x_663_ = v___x_659_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_e_661_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
case 1:
{
lean_object* v_e_665_; lean_object* v___x_666_; 
lean_del_object(v___x_659_);
lean_dec_ref(v_e_651_);
v_e_665_ = lean_ctor_get(v_a_657_, 0);
lean_inc_ref(v_e_665_);
lean_dec_ref_known(v_a_657_, 1);
v___x_666_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_649_, v_post_650_, v_e_665_, v_a_652_, v___y_653_, v___y_654_);
return v___x_666_;
}
default: 
{
lean_object* v_e_x3f_667_; 
lean_dec_ref(v_post_650_);
lean_dec_ref(v_pre_649_);
v_e_x3f_667_ = lean_ctor_get(v_a_657_, 0);
lean_inc(v_e_x3f_667_);
lean_dec_ref_known(v_a_657_, 1);
if (lean_obj_tag(v_e_x3f_667_) == 0)
{
lean_object* v___x_669_; 
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 0, v_e_651_);
v___x_669_ = v___x_659_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_e_651_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
else
{
lean_object* v_val_671_; lean_object* v___x_673_; 
lean_dec_ref(v_e_651_);
v_val_671_ = lean_ctor_get(v_e_x3f_667_, 0);
lean_inc(v_val_671_);
lean_dec_ref_known(v_e_x3f_667_, 1);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 0, v_val_671_);
v___x_673_ = v___x_659_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_val_671_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
}
}
}
else
{
lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_683_; 
lean_dec_ref(v_e_651_);
lean_dec_ref(v_post_650_);
lean_dec_ref(v_pre_649_);
v_a_676_ = lean_ctor_get(v___x_656_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_683_ == 0)
{
v___x_678_ = v___x_656_;
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v___x_656_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_681_; 
if (v_isShared_679_ == 0)
{
v___x_681_ = v___x_678_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_a_676_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_684_, lean_object* v_post_685_, lean_object* v_e_686_, lean_object* v_a_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_684_, v_post_685_, v_e_686_, v_a_687_, v___y_688_, v___y_689_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v_a_687_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_692_, lean_object* v_post_693_, lean_object* v_sz_694_, lean_object* v_i_695_, lean_object* v_bs_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
size_t v_sz_boxed_701_; size_t v_i_boxed_702_; lean_object* v_res_703_; 
v_sz_boxed_701_ = lean_unbox_usize(v_sz_694_);
lean_dec(v_sz_694_);
v_i_boxed_702_ = lean_unbox_usize(v_i_695_);
lean_dec(v_i_695_);
v_res_703_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1(v_pre_692_, v_post_693_, v_sz_boxed_701_, v_i_boxed_702_, v_bs_696_, v___y_697_, v___y_698_, v___y_699_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
lean_dec(v___y_697_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_704_, lean_object* v_post_705_, lean_object* v_x_706_, lean_object* v_x_707_, lean_object* v_x_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4(v_pre_704_, v_post_705_, v_x_706_, v_x_707_, v_x_708_, v___y_709_, v___y_710_, v___y_711_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
lean_dec(v___y_709_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___boxed(lean_object* v_pre_714_, lean_object* v_post_715_, lean_object* v_e_716_, lean_object* v_a_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_714_, v_post_715_, v_e_716_, v_a_717_, v___y_718_, v___y_719_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v_a_717_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(lean_object* v_00_u03b1_722_, lean_object* v_x_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_727_ = lean_apply_1(v_x_723_, lean_box(0));
v___x_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_728_, 0, v___x_727_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0___boxed(lean_object* v_00_u03b1_729_, lean_object* v_x_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(v_00_u03b1_729_, v_x_730_, v___y_731_, v___y_732_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
return v_res_734_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0(void){
_start:
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_735_ = lean_box(0);
v___x_736_ = lean_unsigned_to_nat(16u);
v___x_737_ = lean_mk_array(v___x_736_, v___x_735_);
return v___x_737_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1(void){
_start:
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_738_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0);
v___x_739_ = lean_unsigned_to_nat(0u);
v___x_740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_740_, 0, v___x_739_);
lean_ctor_set(v___x_740_, 1, v___x_738_);
return v___x_740_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2(void){
_start:
{
lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_741_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1, &l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1);
v___x_742_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_742_, 0, lean_box(0));
lean_closure_set(v___x_742_, 1, lean_box(0));
lean_closure_set(v___x_742_, 2, v___x_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0(lean_object* v_input_743_, lean_object* v_pre_744_, lean_object* v_post_745_, lean_object* v___y_746_, lean_object* v___y_747_){
_start:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v_a_751_; lean_object* v___x_752_; 
v___x_749_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2);
v___x_750_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(lean_box(0), v___x_749_, v___y_746_, v___y_747_);
v_a_751_ = lean_ctor_get(v___x_750_, 0);
lean_inc(v_a_751_);
lean_dec_ref(v___x_750_);
v___x_752_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_744_, v_post_745_, v_input_743_, v_a_751_, v___y_746_, v___y_747_);
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v_a_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_762_; 
v_a_753_ = lean_ctor_get(v___x_752_, 0);
lean_inc(v_a_753_);
lean_dec_ref_known(v___x_752_, 1);
v___x_754_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_754_, 0, lean_box(0));
lean_closure_set(v___x_754_, 1, lean_box(0));
lean_closure_set(v___x_754_, 2, v_a_751_);
v___x_755_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(lean_box(0), v___x_754_, v___y_746_, v___y_747_);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_762_ == 0)
{
lean_object* v_unused_763_; 
v_unused_763_ = lean_ctor_get(v___x_755_, 0);
lean_dec(v_unused_763_);
v___x_757_ = v___x_755_;
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
else
{
lean_dec(v___x_755_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_760_; 
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 0, v_a_753_);
v___x_760_ = v___x_757_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_a_753_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
else
{
lean_dec(v_a_751_);
return v___x_752_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___boxed(lean_object* v_input_764_, lean_object* v_pre_765_, lean_object* v_post_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0(v_input_764_, v_pre_765_, v_post_766_, v___y_767_, v___y_768_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam(lean_object* v_type_773_, lean_object* v_a_774_, lean_object* v_a_775_){
_start:
{
lean_object* v___f_777_; lean_object* v___f_778_; lean_object* v___x_779_; 
v___f_777_ = ((lean_object*)(l_Lean_Meta_elimOptParam___closed__0));
v___f_778_ = ((lean_object*)(l_Lean_Meta_elimOptParam___closed__1));
v___x_779_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0(v_type_773_, v___f_777_, v___f_778_, v_a_774_, v_a_775_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam___boxed(lean_object* v_type_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Lean_Meta_elimOptParam(v_type_780_, v_a_781_, v_a_782_);
lean_dec(v_a_782_);
lean_dec_ref(v_a_781_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_785_, lean_object* v_m_786_, lean_object* v_a_787_){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(v_m_786_, v_a_787_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_789_, lean_object* v_m_790_, lean_object* v_a_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(v_00_u03b2_789_, v_m_790_, v_a_791_);
lean_dec_ref(v_a_791_);
lean_dec_ref(v_m_790_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_793_, lean_object* v_ref_794_, lean_object* v___y_795_, lean_object* v___y_796_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_794_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_799_, lean_object* v_ref_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_799_, v_ref_800_, v___y_801_, v___y_802_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8(lean_object* v_00_u03b1_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg();
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___boxed(lean_object* v_00_u03b1_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_810_, v___y_811_, v___y_812_);
lean_dec(v___y_812_);
lean_dec_ref(v___y_811_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_815_, lean_object* v_x_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(v_x_816_, v___y_817_, v___y_818_, v___y_819_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_822_, lean_object* v_x_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5(v_00_u03b1_822_, v_x_823_, v___y_824_, v___y_825_, v___y_826_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec(v___y_824_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_829_, lean_object* v_m_830_, lean_object* v_a_831_, lean_object* v_b_832_){
_start:
{
lean_object* v___x_833_; 
v___x_833_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6___redArg(v_m_830_, v_a_831_, v_b_832_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_834_, lean_object* v_a_835_, lean_object* v_x_836_){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(v_a_835_, v_x_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_838_, lean_object* v_a_839_, lean_object* v_x_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_838_, v_a_839_, v_x_840_);
lean_dec(v_x_840_);
lean_dec_ref(v_a_839_);
return v_res_841_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_842_, lean_object* v_a_843_, lean_object* v_x_844_){
_start:
{
uint8_t v___x_845_; 
v___x_845_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___redArg(v_a_843_, v_x_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___boxed(lean_object* v_00_u03b2_846_, lean_object* v_a_847_, lean_object* v_x_848_){
_start:
{
uint8_t v_res_849_; lean_object* v_r_850_; 
v_res_849_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_846_, v_a_847_, v_x_848_);
lean_dec(v_x_848_);
lean_dec_ref(v_a_847_);
v_r_850_ = lean_box(v_res_849_);
return v_r_850_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_851_, lean_object* v_data_852_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11___redArg(v_data_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__12(lean_object* v_00_u03b2_854_, lean_object* v_a_855_, lean_object* v_b_856_, lean_object* v_x_857_){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__12___redArg(v_a_855_, v_b_856_, v_x_857_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12(lean_object* v_00_u03b2_859_, lean_object* v_i_860_, lean_object* v_source_861_, lean_object* v_target_862_){
_start:
{
lean_object* v___x_863_; 
v___x_863_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v_i_860_, v_source_861_, v_target_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_864_, lean_object* v_x_865_, lean_object* v_x_866_){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_x_865_, v_x_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0(uint8_t v_skipIfPropOrEq_868_, lean_object* v_as_869_, size_t v_sz_870_, size_t v_i_871_, lean_object* v_b_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_){
_start:
{
lean_object* v_a_879_; uint8_t v___x_883_; 
v___x_883_ = lean_usize_dec_lt(v_i_871_, v_sz_870_);
if (v___x_883_ == 0)
{
lean_object* v___x_884_; 
v___x_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_884_, 0, v_b_872_);
return v___x_884_;
}
else
{
lean_object* v_snd_885_; lean_object* v_fst_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_970_; 
v_snd_885_ = lean_ctor_get(v_b_872_, 1);
v_fst_886_ = lean_ctor_get(v_b_872_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v_b_872_);
if (v_isSharedCheck_970_ == 0)
{
v___x_888_ = v_b_872_;
v_isShared_889_ = v_isSharedCheck_970_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_snd_885_);
lean_inc(v_fst_886_);
lean_dec(v_b_872_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_970_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v_array_890_; lean_object* v_start_891_; lean_object* v_stop_892_; uint8_t v___x_893_; 
v_array_890_ = lean_ctor_get(v_snd_885_, 0);
v_start_891_ = lean_ctor_get(v_snd_885_, 1);
v_stop_892_ = lean_ctor_get(v_snd_885_, 2);
v___x_893_ = lean_nat_dec_lt(v_start_891_, v_stop_892_);
if (v___x_893_ == 0)
{
lean_object* v___x_895_; 
if (v_isShared_889_ == 0)
{
v___x_895_ = v___x_888_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_fst_886_);
lean_ctor_set(v_reuseFailAlloc_897_, 1, v_snd_885_);
v___x_895_ = v_reuseFailAlloc_897_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
lean_object* v___x_896_; 
v___x_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_896_, 0, v___x_895_);
return v___x_896_;
}
}
else
{
lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_966_; 
lean_inc(v_stop_892_);
lean_inc(v_start_891_);
lean_inc_ref(v_array_890_);
v_isSharedCheck_966_ = !lean_is_exclusive(v_snd_885_);
if (v_isSharedCheck_966_ == 0)
{
lean_object* v_unused_967_; lean_object* v_unused_968_; lean_object* v_unused_969_; 
v_unused_967_ = lean_ctor_get(v_snd_885_, 2);
lean_dec(v_unused_967_);
v_unused_968_ = lean_ctor_get(v_snd_885_, 1);
lean_dec(v_unused_968_);
v_unused_969_ = lean_ctor_get(v_snd_885_, 0);
lean_dec(v_unused_969_);
v___x_899_ = v_snd_885_;
v_isShared_900_ = v_isSharedCheck_966_;
goto v_resetjp_898_;
}
else
{
lean_dec(v_snd_885_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_966_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v_a_901_; lean_object* v___x_902_; 
v_a_901_ = lean_array_uget_borrowed(v_as_869_, v_i_871_);
lean_inc(v___y_876_);
lean_inc_ref(v___y_875_);
lean_inc(v___y_874_);
lean_inc_ref(v___y_873_);
lean_inc(v_a_901_);
v___x_902_ = lean_infer_type(v_a_901_, v___y_873_, v___y_874_, v___y_875_, v___y_876_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v_a_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_908_; 
v_a_903_ = lean_ctor_get(v___x_902_, 0);
lean_inc(v_a_903_);
lean_dec_ref_known(v___x_902_, 1);
v___x_904_ = lean_array_fget(v_array_890_, v_start_891_);
v___x_905_ = lean_unsigned_to_nat(1u);
v___x_906_ = lean_nat_add(v_start_891_, v___x_905_);
lean_dec(v_start_891_);
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 1, v___x_906_);
v___x_908_ = v___x_899_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_array_890_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v___x_906_);
lean_ctor_set(v_reuseFailAlloc_957_, 2, v_stop_892_);
v___x_908_ = v_reuseFailAlloc_957_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
uint8_t v___x_909_; 
v___x_909_ = lean_bool_not(v_skipIfPropOrEq_868_);
if (v___x_909_ == 0)
{
lean_object* v___x_910_; 
v___x_910_ = l_Lean_Meta_isProp(v_a_903_, v___y_873_, v___y_874_, v___y_875_, v___y_876_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_object* v_a_911_; uint8_t v___y_913_; uint8_t v___x_931_; uint8_t v___x_932_; 
v_a_911_ = lean_ctor_get(v___x_910_, 0);
lean_inc(v_a_911_);
lean_dec_ref_known(v___x_910_, 1);
v___x_931_ = lean_unbox(v_a_911_);
lean_dec(v_a_911_);
v___x_932_ = lean_bool_not(v___x_931_);
if (v___x_932_ == 0)
{
v___y_913_ = v___x_932_;
goto v___jp_912_;
}
else
{
uint8_t v___x_933_; uint8_t v___x_934_; 
v___x_933_ = lean_expr_eqv(v_a_901_, v___x_904_);
v___x_934_ = lean_bool_not(v___x_933_);
v___y_913_ = v___x_934_;
goto v___jp_912_;
}
v___jp_912_:
{
if (v___y_913_ == 0)
{
lean_object* v___x_915_; 
lean_dec(v___x_904_);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 1, v___x_908_);
v___x_915_ = v___x_888_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_fst_886_);
lean_ctor_set(v_reuseFailAlloc_916_, 1, v___x_908_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
v_a_879_ = v___x_915_;
goto v___jp_878_;
}
}
else
{
lean_object* v___x_917_; 
lean_inc(v_a_901_);
v___x_917_ = l_Lean_Meta_mkEqHEq(v_a_901_, v___x_904_, v___y_873_, v___y_874_, v___y_875_, v___y_876_);
if (lean_obj_tag(v___x_917_) == 0)
{
lean_object* v_a_918_; lean_object* v___x_919_; lean_object* v___x_921_; 
v_a_918_ = lean_ctor_get(v___x_917_, 0);
lean_inc(v_a_918_);
lean_dec_ref_known(v___x_917_, 1);
v___x_919_ = lean_array_push(v_fst_886_, v_a_918_);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 1, v___x_908_);
lean_ctor_set(v___x_888_, 0, v___x_919_);
v___x_921_ = v___x_888_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v___x_919_);
lean_ctor_set(v_reuseFailAlloc_922_, 1, v___x_908_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
v_a_879_ = v___x_921_;
goto v___jp_878_;
}
}
else
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_930_; 
lean_dec_ref(v___x_908_);
lean_del_object(v___x_888_);
lean_dec(v_fst_886_);
v_a_923_ = lean_ctor_get(v___x_917_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_930_ == 0)
{
v___x_925_ = v___x_917_;
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_917_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_928_; 
if (v_isShared_926_ == 0)
{
v___x_928_ = v___x_925_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_a_923_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
}
}
else
{
lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_942_; 
lean_dec_ref(v___x_908_);
lean_dec(v___x_904_);
lean_del_object(v___x_888_);
lean_dec(v_fst_886_);
v_a_935_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_942_ == 0)
{
v___x_937_ = v___x_910_;
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_dec(v___x_910_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_940_; 
if (v_isShared_938_ == 0)
{
v___x_940_ = v___x_937_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_a_935_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
}
else
{
lean_object* v___x_943_; 
lean_dec(v_a_903_);
lean_inc(v_a_901_);
v___x_943_ = l_Lean_Meta_mkEqHEq(v_a_901_, v___x_904_, v___y_873_, v___y_874_, v___y_875_, v___y_876_);
if (lean_obj_tag(v___x_943_) == 0)
{
lean_object* v_a_944_; lean_object* v___x_945_; lean_object* v___x_947_; 
v_a_944_ = lean_ctor_get(v___x_943_, 0);
lean_inc(v_a_944_);
lean_dec_ref_known(v___x_943_, 1);
v___x_945_ = lean_array_push(v_fst_886_, v_a_944_);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 1, v___x_908_);
lean_ctor_set(v___x_888_, 0, v___x_945_);
v___x_947_ = v___x_888_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_945_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v___x_908_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
v_a_879_ = v___x_947_;
goto v___jp_878_;
}
}
else
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_956_; 
lean_dec_ref(v___x_908_);
lean_del_object(v___x_888_);
lean_dec(v_fst_886_);
v_a_949_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_956_ == 0)
{
v___x_951_ = v___x_943_;
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_943_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_954_; 
if (v_isShared_952_ == 0)
{
v___x_954_ = v___x_951_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_a_949_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
}
}
}
else
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_965_; 
lean_del_object(v___x_899_);
lean_dec(v_stop_892_);
lean_dec(v_start_891_);
lean_dec_ref(v_array_890_);
lean_del_object(v___x_888_);
lean_dec(v_fst_886_);
v_a_958_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_965_ == 0)
{
v___x_960_ = v___x_902_;
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_902_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_963_; 
if (v_isShared_961_ == 0)
{
v___x_963_ = v___x_960_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_a_958_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
}
}
}
}
v___jp_878_:
{
size_t v___x_880_; size_t v___x_881_; 
v___x_880_ = ((size_t)1ULL);
v___x_881_ = lean_usize_add(v_i_871_, v___x_880_);
v_i_871_ = v___x_881_;
v_b_872_ = v_a_879_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0___boxed(lean_object* v_skipIfPropOrEq_971_, lean_object* v_as_972_, lean_object* v_sz_973_, lean_object* v_i_974_, lean_object* v_b_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
uint8_t v_skipIfPropOrEq_boxed_981_; size_t v_sz_boxed_982_; size_t v_i_boxed_983_; lean_object* v_res_984_; 
v_skipIfPropOrEq_boxed_981_ = lean_unbox(v_skipIfPropOrEq_971_);
v_sz_boxed_982_ = lean_unbox_usize(v_sz_973_);
lean_dec(v_sz_973_);
v_i_boxed_983_ = lean_unbox_usize(v_i_974_);
lean_dec(v_i_974_);
v_res_984_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0(v_skipIfPropOrEq_boxed_981_, v_as_972_, v_sz_boxed_982_, v_i_boxed_983_, v_b_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec_ref(v_as_972_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(lean_object* v_args1_987_, lean_object* v_args2_988_, uint8_t v_skipIfPropOrEq_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_){
_start:
{
lean_object* v___x_995_; lean_object* v_eqs_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; size_t v_sz_1000_; size_t v___x_1001_; lean_object* v___x_1002_; 
v___x_995_ = lean_unsigned_to_nat(0u);
v_eqs_996_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_997_ = lean_array_get_size(v_args2_988_);
v___x_998_ = l_Array_toSubarray___redArg(v_args2_988_, v___x_995_, v___x_997_);
v___x_999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_999_, 0, v_eqs_996_);
lean_ctor_set(v___x_999_, 1, v___x_998_);
v_sz_1000_ = lean_array_size(v_args1_987_);
v___x_1001_ = ((size_t)0ULL);
v___x_1002_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0(v_skipIfPropOrEq_989_, v_args1_987_, v_sz_1000_, v___x_1001_, v___x_999_, v_a_990_, v_a_991_, v_a_992_, v_a_993_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1011_; 
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1005_ = v___x_1002_;
v_isShared_1006_ = v_isSharedCheck_1011_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_1002_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1011_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v_fst_1007_; lean_object* v___x_1009_; 
v_fst_1007_ = lean_ctor_get(v_a_1003_, 0);
lean_inc(v_fst_1007_);
lean_dec(v_a_1003_);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 0, v_fst_1007_);
v___x_1009_ = v___x_1005_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_fst_1007_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
else
{
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1019_; 
v_a_1012_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1014_ = v___x_1002_;
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_1002_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___boxed(lean_object* v_args1_1020_, lean_object* v_args2_1021_, lean_object* v_skipIfPropOrEq_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_){
_start:
{
uint8_t v_skipIfPropOrEq_boxed_1028_; lean_object* v_res_1029_; 
v_skipIfPropOrEq_boxed_1028_ = lean_unbox(v_skipIfPropOrEq_1022_);
v_res_1029_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v_args1_1020_, v_args2_1021_, v_skipIfPropOrEq_boxed_1028_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_);
lean_dec(v_a_1026_);
lean_dec_ref(v_a_1025_);
lean_dec(v_a_1024_);
lean_dec_ref(v_a_1023_);
lean_dec_ref(v_args1_1020_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0(lean_object* v_k_1030_, lean_object* v_b_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v___x_1037_; 
lean_inc(v___y_1035_);
lean_inc_ref(v___y_1034_);
lean_inc(v___y_1033_);
lean_inc_ref(v___y_1032_);
v___x_1037_ = lean_apply_6(v_k_1030_, v_b_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, lean_box(0));
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0___boxed(lean_object* v_k_1038_, lean_object* v_b_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0(v_k_1038_, v_b_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(lean_object* v_name_1046_, uint8_t v_bi_1047_, lean_object* v_type_1048_, lean_object* v_k_1049_, uint8_t v_kind_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v___f_1056_; lean_object* v___x_1057_; 
v___f_1056_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1056_, 0, v_k_1049_);
v___x_1057_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1046_, v_bi_1047_, v_type_1048_, v___f_1056_, v_kind_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
if (lean_obj_tag(v___x_1057_) == 0)
{
lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1065_; 
v_a_1058_ = lean_ctor_get(v___x_1057_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1060_ = v___x_1057_;
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v___x_1057_);
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
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1073_; 
v_a_1066_ = lean_ctor_get(v___x_1057_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1068_ = v___x_1057_;
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_a_1066_);
lean_dec(v___x_1057_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1071_; 
if (v_isShared_1069_ == 0)
{
v___x_1071_ = v___x_1068_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_a_1066_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___boxed(lean_object* v_name_1074_, lean_object* v_bi_1075_, lean_object* v_type_1076_, lean_object* v_k_1077_, lean_object* v_kind_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
uint8_t v_bi_boxed_1084_; uint8_t v_kind_boxed_1085_; lean_object* v_res_1086_; 
v_bi_boxed_1084_ = lean_unbox(v_bi_1075_);
v_kind_boxed_1085_ = lean_unbox(v_kind_1078_);
v_res_1086_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_name_1074_, v_bi_boxed_1084_, v_type_1076_, v_k_1077_, v_kind_boxed_1085_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0(lean_object* v_00_u03b1_1087_, lean_object* v_name_1088_, uint8_t v_bi_1089_, lean_object* v_type_1090_, lean_object* v_k_1091_, uint8_t v_kind_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v___x_1098_; 
v___x_1098_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_name_1088_, v_bi_1089_, v_type_1090_, v_k_1091_, v_kind_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___boxed(lean_object* v_00_u03b1_1099_, lean_object* v_name_1100_, lean_object* v_bi_1101_, lean_object* v_type_1102_, lean_object* v_k_1103_, lean_object* v_kind_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
uint8_t v_bi_boxed_1110_; uint8_t v_kind_boxed_1111_; lean_object* v_res_1112_; 
v_bi_boxed_1110_ = lean_unbox(v_bi_1101_);
v_kind_boxed_1111_ = lean_unbox(v_kind_1104_);
v_res_1112_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0(v_00_u03b1_1099_, v_name_1100_, v_bi_boxed_1110_, v_type_1102_, v_k_1103_, v_kind_boxed_1111_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(lean_object* v_msgData_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v___x_1119_; lean_object* v_env_1120_; lean_object* v___x_1121_; lean_object* v_mctx_1122_; lean_object* v_lctx_1123_; lean_object* v_options_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1119_ = lean_st_ref_get(v___y_1117_);
v_env_1120_ = lean_ctor_get(v___x_1119_, 0);
lean_inc_ref(v_env_1120_);
lean_dec(v___x_1119_);
v___x_1121_ = lean_st_ref_get(v___y_1115_);
v_mctx_1122_ = lean_ctor_get(v___x_1121_, 0);
lean_inc_ref(v_mctx_1122_);
lean_dec(v___x_1121_);
v_lctx_1123_ = lean_ctor_get(v___y_1114_, 2);
v_options_1124_ = lean_ctor_get(v___y_1116_, 2);
lean_inc_ref(v_options_1124_);
lean_inc_ref(v_lctx_1123_);
v___x_1125_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1125_, 0, v_env_1120_);
lean_ctor_set(v___x_1125_, 1, v_mctx_1122_);
lean_ctor_set(v___x_1125_, 2, v_lctx_1123_);
lean_ctor_set(v___x_1125_, 3, v_options_1124_);
v___x_1126_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1125_);
lean_ctor_set(v___x_1126_, 1, v_msgData_1113_);
v___x_1127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1126_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1___boxed(lean_object* v_msgData_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_){
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msgData_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(lean_object* v_msg_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
lean_object* v_ref_1141_; lean_object* v___x_1142_; lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1151_; 
v_ref_1141_ = lean_ctor_get(v___y_1138_, 5);
v___x_1142_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msg_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1145_ = v___x_1142_;
v_isShared_1146_ = v_isSharedCheck_1151_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_dec(v___x_1142_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1151_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1147_; lean_object* v___x_1149_; 
lean_inc(v_ref_1141_);
v___x_1147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1147_, 0, v_ref_1141_);
lean_ctor_set(v___x_1147_, 1, v_a_1143_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set_tag(v___x_1145_, 1);
lean_ctor_set(v___x_1145_, 0, v___x_1147_);
v___x_1149_ = v___x_1145_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v___x_1147_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg___boxed(lean_object* v_msg_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v_msg_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_);
lean_dec(v___y_1156_);
lean_dec_ref(v___y_1155_);
lean_dec(v___y_1154_);
lean_dec_ref(v___y_1153_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0___boxed(lean_object* v_i_1159_, lean_object* v_body_1160_, lean_object* v_args2_1161_, lean_object* v_args2New_1162_, lean_object* v_ctorVal_1163_, lean_object* v_useEq_1164_, lean_object* v_args1_1165_, lean_object* v_resultType_1166_, lean_object* v_k_1167_, lean_object* v_arg2_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
uint8_t v_useEq_boxed_1174_; lean_object* v_res_1175_; 
v_useEq_boxed_1174_ = lean_unbox(v_useEq_1164_);
v_res_1175_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0(v_i_1159_, v_body_1160_, v_args2_1161_, v_args2New_1162_, v_ctorVal_1163_, v_useEq_boxed_1174_, v_args1_1165_, v_resultType_1166_, v_k_1167_, v_arg2_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec_ref(v_body_1160_);
lean_dec(v_i_1159_);
return v_res_1175_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1(void){
_start:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__0));
v___x_1178_ = l_Lean_stringToMessageData(v___x_1177_);
return v___x_1178_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3(void){
_start:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1180_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__2));
v___x_1181_ = l_Lean_stringToMessageData(v___x_1180_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(lean_object* v_ctorVal_1182_, uint8_t v_useEq_1183_, lean_object* v_args1_1184_, lean_object* v_resultType_1185_, lean_object* v_k_1186_, lean_object* v_i_1187_, lean_object* v_type_1188_, lean_object* v_args2_1189_, lean_object* v_args2New_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_){
_start:
{
lean_object* v___x_1196_; uint8_t v___x_1197_; 
v___x_1196_ = lean_array_get_size(v_args1_1184_);
v___x_1197_ = lean_nat_dec_lt(v_i_1187_, v___x_1196_);
if (v___x_1197_ == 0)
{
lean_object* v___x_1198_; 
lean_dec_ref(v_type_1188_);
lean_dec(v_i_1187_);
lean_dec_ref(v_resultType_1185_);
lean_dec_ref(v_args1_1184_);
lean_dec_ref(v_ctorVal_1182_);
lean_inc(v_a_1194_);
lean_inc_ref(v_a_1193_);
lean_inc(v_a_1192_);
lean_inc_ref(v_a_1191_);
v___x_1198_ = lean_apply_7(v_k_1186_, v_args2_1189_, v_args2New_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, lean_box(0));
return v___x_1198_;
}
else
{
lean_object* v___x_1199_; 
lean_inc(v_a_1194_);
lean_inc_ref(v_a_1193_);
lean_inc(v_a_1192_);
lean_inc_ref(v_a_1191_);
v___x_1199_ = lean_whnf(v_type_1188_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_);
if (lean_obj_tag(v___x_1199_) == 0)
{
lean_object* v_a_1200_; 
v_a_1200_ = lean_ctor_get(v___x_1199_, 0);
lean_inc(v_a_1200_);
lean_dec_ref_known(v___x_1199_, 1);
if (lean_obj_tag(v_a_1200_) == 7)
{
lean_object* v_binderName_1201_; lean_object* v_binderType_1202_; lean_object* v_body_1203_; lean_object* v_lctx_1204_; lean_object* v___x_1205_; uint8_t v___x_1206_; 
v_binderName_1201_ = lean_ctor_get(v_a_1200_, 0);
lean_inc(v_binderName_1201_);
v_binderType_1202_ = lean_ctor_get(v_a_1200_, 1);
lean_inc_ref(v_binderType_1202_);
v_body_1203_ = lean_ctor_get(v_a_1200_, 2);
lean_inc_ref(v_body_1203_);
lean_dec_ref_known(v_a_1200_, 3);
v_lctx_1204_ = lean_ctor_get(v_a_1191_, 2);
v___x_1205_ = lean_array_fget_borrowed(v_args1_1184_, v_i_1187_);
lean_inc(v___x_1205_);
lean_inc_ref(v_lctx_1204_);
v___x_1206_ = l_Lean_Meta_occursOrInType(v_lctx_1204_, v___x_1205_, v_resultType_1185_);
if (v___x_1206_ == 0)
{
lean_object* v___x_1207_; lean_object* v___f_1208_; uint8_t v___y_1210_; 
v___x_1207_ = lean_box(v_useEq_1183_);
v___f_1208_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0___boxed), 15, 9);
lean_closure_set(v___f_1208_, 0, v_i_1187_);
lean_closure_set(v___f_1208_, 1, v_body_1203_);
lean_closure_set(v___f_1208_, 2, v_args2_1189_);
lean_closure_set(v___f_1208_, 3, v_args2New_1190_);
lean_closure_set(v___f_1208_, 4, v_ctorVal_1182_);
lean_closure_set(v___f_1208_, 5, v___x_1207_);
lean_closure_set(v___f_1208_, 6, v_args1_1184_);
lean_closure_set(v___f_1208_, 7, v_resultType_1185_);
lean_closure_set(v___f_1208_, 8, v_k_1186_);
if (v_useEq_1183_ == 0)
{
uint8_t v___x_1213_; 
v___x_1213_ = 1;
v___y_1210_ = v___x_1213_;
goto v___jp_1209_;
}
else
{
uint8_t v___x_1214_; 
v___x_1214_ = 0;
v___y_1210_ = v___x_1214_;
goto v___jp_1209_;
}
v___jp_1209_:
{
uint8_t v___x_1211_; lean_object* v___x_1212_; 
v___x_1211_ = 0;
v___x_1212_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_binderName_1201_, v___y_1210_, v_binderType_1202_, v___f_1208_, v___x_1211_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_);
return v___x_1212_;
}
}
else
{
lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
lean_dec_ref(v_binderType_1202_);
lean_dec(v_binderName_1201_);
v___x_1215_ = lean_unsigned_to_nat(1u);
v___x_1216_ = lean_nat_add(v_i_1187_, v___x_1215_);
lean_dec(v_i_1187_);
v___x_1217_ = lean_expr_instantiate1(v_body_1203_, v___x_1205_);
lean_dec_ref(v_body_1203_);
lean_inc(v___x_1205_);
v___x_1218_ = lean_array_push(v_args2_1189_, v___x_1205_);
v_i_1187_ = v___x_1216_;
v_type_1188_ = v___x_1217_;
v_args2_1189_ = v___x_1218_;
goto _start;
}
}
else
{
lean_object* v_toConstantVal_1220_; lean_object* v_name_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
lean_dec(v_a_1200_);
lean_dec_ref(v_args2New_1190_);
lean_dec_ref(v_args2_1189_);
lean_dec(v_i_1187_);
lean_dec_ref(v_k_1186_);
lean_dec_ref(v_resultType_1185_);
lean_dec_ref(v_args1_1184_);
v_toConstantVal_1220_ = lean_ctor_get(v_ctorVal_1182_, 0);
lean_inc_ref(v_toConstantVal_1220_);
lean_dec_ref(v_ctorVal_1182_);
v_name_1221_ = lean_ctor_get(v_toConstantVal_1220_, 0);
lean_inc(v_name_1221_);
lean_dec_ref(v_toConstantVal_1220_);
v___x_1222_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1);
v___x_1223_ = l_Lean_MessageData_ofName(v_name_1221_);
v___x_1224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1222_);
lean_ctor_set(v___x_1224_, 1, v___x_1223_);
v___x_1225_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_1226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1224_);
lean_ctor_set(v___x_1226_, 1, v___x_1225_);
v___x_1227_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_1226_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_);
return v___x_1227_;
}
}
else
{
lean_object* v_a_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1235_; 
lean_dec_ref(v_args2New_1190_);
lean_dec_ref(v_args2_1189_);
lean_dec(v_i_1187_);
lean_dec_ref(v_k_1186_);
lean_dec_ref(v_resultType_1185_);
lean_dec_ref(v_args1_1184_);
lean_dec_ref(v_ctorVal_1182_);
v_a_1228_ = lean_ctor_get(v___x_1199_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1199_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1230_ = v___x_1199_;
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_a_1228_);
lean_dec(v___x_1199_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1233_; 
if (v_isShared_1231_ == 0)
{
v___x_1233_ = v___x_1230_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_a_1228_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0(lean_object* v_i_1236_, lean_object* v_body_1237_, lean_object* v_args2_1238_, lean_object* v_args2New_1239_, lean_object* v_ctorVal_1240_, uint8_t v_useEq_1241_, lean_object* v_args1_1242_, lean_object* v_resultType_1243_, lean_object* v_k_1244_, lean_object* v_arg2_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1251_ = lean_unsigned_to_nat(1u);
v___x_1252_ = lean_nat_add(v_i_1236_, v___x_1251_);
v___x_1253_ = lean_expr_instantiate1(v_body_1237_, v_arg2_1245_);
lean_inc_ref(v_arg2_1245_);
v___x_1254_ = lean_array_push(v_args2_1238_, v_arg2_1245_);
v___x_1255_ = lean_array_push(v_args2New_1239_, v_arg2_1245_);
v___x_1256_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(v_ctorVal_1240_, v_useEq_1241_, v_args1_1242_, v_resultType_1243_, v_k_1244_, v___x_1252_, v___x_1253_, v___x_1254_, v___x_1255_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___boxed(lean_object* v_ctorVal_1257_, lean_object* v_useEq_1258_, lean_object* v_args1_1259_, lean_object* v_resultType_1260_, lean_object* v_k_1261_, lean_object* v_i_1262_, lean_object* v_type_1263_, lean_object* v_args2_1264_, lean_object* v_args2New_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_){
_start:
{
uint8_t v_useEq_boxed_1271_; lean_object* v_res_1272_; 
v_useEq_boxed_1271_ = lean_unbox(v_useEq_1258_);
v_res_1272_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(v_ctorVal_1257_, v_useEq_boxed_1271_, v_args1_1259_, v_resultType_1260_, v_k_1261_, v_i_1262_, v_type_1263_, v_args2_1264_, v_args2New_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
lean_dec(v_a_1269_);
lean_dec_ref(v_a_1268_);
lean_dec(v_a_1267_);
lean_dec_ref(v_a_1266_);
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1(lean_object* v_00_u03b1_1273_, lean_object* v_msg_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
lean_object* v___x_1280_; 
v___x_1280_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v_msg_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___boxed(lean_object* v_00_u03b1_1281_, lean_object* v_msg_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1(v_00_u03b1_1281_, v_msg_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
return v_res_1288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_match__1_splitter___redArg(lean_object* v_____x_1289_, lean_object* v_h__1_1290_, lean_object* v_h__2_1291_){
_start:
{
if (lean_obj_tag(v_____x_1289_) == 7)
{
lean_object* v_binderName_1292_; lean_object* v_binderType_1293_; lean_object* v_body_1294_; uint8_t v_binderInfo_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
lean_dec(v_h__2_1291_);
v_binderName_1292_ = lean_ctor_get(v_____x_1289_, 0);
lean_inc(v_binderName_1292_);
v_binderType_1293_ = lean_ctor_get(v_____x_1289_, 1);
lean_inc_ref(v_binderType_1293_);
v_body_1294_ = lean_ctor_get(v_____x_1289_, 2);
lean_inc_ref(v_body_1294_);
v_binderInfo_1295_ = lean_ctor_get_uint8(v_____x_1289_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_____x_1289_, 3);
v___x_1296_ = lean_box(v_binderInfo_1295_);
v___x_1297_ = lean_apply_4(v_h__1_1290_, v_binderName_1292_, v_binderType_1293_, v_body_1294_, v___x_1296_);
return v___x_1297_;
}
else
{
lean_object* v___x_1298_; 
lean_dec(v_h__1_1290_);
v___x_1298_ = lean_apply_2(v_h__2_1291_, v_____x_1289_, lean_box(0));
return v___x_1298_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_match__1_splitter(lean_object* v_motive_1299_, lean_object* v_____x_1300_, lean_object* v_h__1_1301_, lean_object* v_h__2_1302_){
_start:
{
if (lean_obj_tag(v_____x_1300_) == 7)
{
lean_object* v_binderName_1303_; lean_object* v_binderType_1304_; lean_object* v_body_1305_; uint8_t v_binderInfo_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
lean_dec(v_h__2_1302_);
v_binderName_1303_ = lean_ctor_get(v_____x_1300_, 0);
lean_inc(v_binderName_1303_);
v_binderType_1304_ = lean_ctor_get(v_____x_1300_, 1);
lean_inc_ref(v_binderType_1304_);
v_body_1305_ = lean_ctor_get(v_____x_1300_, 2);
lean_inc_ref(v_body_1305_);
v_binderInfo_1306_ = lean_ctor_get_uint8(v_____x_1300_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_____x_1300_, 3);
v___x_1307_ = lean_box(v_binderInfo_1306_);
v___x_1308_ = lean_apply_4(v_h__1_1301_, v_binderName_1303_, v_binderType_1304_, v_body_1305_, v___x_1307_);
return v___x_1308_;
}
else
{
lean_object* v___x_1309_; 
lean_dec(v_h__1_1301_);
v___x_1309_ = lean_apply_2(v_h__2_1302_, v_____x_1300_, lean_box(0));
return v___x_1309_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0(lean_object* v_k_1310_, lean_object* v_b_1311_, lean_object* v_c_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v___x_1318_; 
lean_inc(v___y_1316_);
lean_inc_ref(v___y_1315_);
lean_inc(v___y_1314_);
lean_inc_ref(v___y_1313_);
v___x_1318_ = lean_apply_7(v_k_1310_, v_b_1311_, v_c_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, lean_box(0));
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed(lean_object* v_k_1319_, lean_object* v_b_1320_, lean_object* v_c_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0(v_k_1319_, v_b_1320_, v_c_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(lean_object* v_type_1328_, lean_object* v_k_1329_, uint8_t v_cleanupAnnotations_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_){
_start:
{
lean_object* v___f_1336_; uint8_t v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___f_1336_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1336_, 0, v_k_1329_);
v___x_1337_ = 0;
v___x_1338_ = lean_box(0);
v___x_1339_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_1337_, v___x_1338_, v_type_1328_, v___f_1336_, v_cleanupAnnotations_1330_, v___x_1337_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v_a_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1347_; 
v_a_1340_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1342_ = v___x_1339_;
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_a_1340_);
lean_dec(v___x_1339_);
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
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1355_; 
v_a_1348_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1355_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1350_ = v___x_1339_;
v_isShared_1351_ = v_isSharedCheck_1355_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_a_1348_);
lean_dec(v___x_1339_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___boxed(lean_object* v_type_1356_, lean_object* v_k_1357_, lean_object* v_cleanupAnnotations_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1364_; lean_object* v_res_1365_; 
v_cleanupAnnotations_boxed_1364_ = lean_unbox(v_cleanupAnnotations_1358_);
v_res_1365_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_type_1356_, v_k_1357_, v_cleanupAnnotations_boxed_1364_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2(lean_object* v_00_u03b1_1366_, lean_object* v_type_1367_, lean_object* v_k_1368_, uint8_t v_cleanupAnnotations_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_){
_start:
{
lean_object* v___x_1375_; 
v___x_1375_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_type_1367_, v_k_1368_, v_cleanupAnnotations_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_);
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___boxed(lean_object* v_00_u03b1_1376_, lean_object* v_type_1377_, lean_object* v_k_1378_, lean_object* v_cleanupAnnotations_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1385_; lean_object* v_res_1386_; 
v_cleanupAnnotations_boxed_1385_ = lean_unbox(v_cleanupAnnotations_1379_);
v_res_1386_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2(v_00_u03b1_1376_, v_type_1377_, v_k_1378_, v_cleanupAnnotations_boxed_1385_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(lean_object* v_type_1387_, lean_object* v_maxFVars_x3f_1388_, lean_object* v_k_1389_, uint8_t v_cleanupAnnotations_1390_, uint8_t v_whnfType_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
lean_object* v___f_1397_; lean_object* v___x_1398_; 
v___f_1397_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1397_, 0, v_k_1389_);
v___x_1398_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_1387_, v_maxFVars_x3f_1388_, v___f_1397_, v_cleanupAnnotations_1390_, v_whnfType_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_object* v_a_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1406_; 
v_a_1399_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1401_ = v___x_1398_;
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_a_1399_);
lean_dec(v___x_1398_);
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
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1414_; 
v_a_1407_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1409_ = v___x_1398_;
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1398_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1412_; 
if (v_isShared_1410_ == 0)
{
v___x_1412_ = v___x_1409_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_a_1407_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg___boxed(lean_object* v_type_1415_, lean_object* v_maxFVars_x3f_1416_, lean_object* v_k_1417_, lean_object* v_cleanupAnnotations_1418_, lean_object* v_whnfType_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1425_; uint8_t v_whnfType_boxed_1426_; lean_object* v_res_1427_; 
v_cleanupAnnotations_boxed_1425_ = lean_unbox(v_cleanupAnnotations_1418_);
v_whnfType_boxed_1426_ = lean_unbox(v_whnfType_1419_);
v_res_1427_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(v_type_1415_, v_maxFVars_x3f_1416_, v_k_1417_, v_cleanupAnnotations_boxed_1425_, v_whnfType_boxed_1426_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3(lean_object* v_00_u03b1_1428_, lean_object* v_type_1429_, lean_object* v_maxFVars_x3f_1430_, lean_object* v_k_1431_, uint8_t v_cleanupAnnotations_1432_, uint8_t v_whnfType_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_){
_start:
{
lean_object* v___x_1439_; 
v___x_1439_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(v_type_1429_, v_maxFVars_x3f_1430_, v_k_1431_, v_cleanupAnnotations_1432_, v_whnfType_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___boxed(lean_object* v_00_u03b1_1440_, lean_object* v_type_1441_, lean_object* v_maxFVars_x3f_1442_, lean_object* v_k_1443_, lean_object* v_cleanupAnnotations_1444_, lean_object* v_whnfType_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1451_; uint8_t v_whnfType_boxed_1452_; lean_object* v_res_1453_; 
v_cleanupAnnotations_boxed_1451_ = lean_unbox(v_cleanupAnnotations_1444_);
v_whnfType_boxed_1452_ = lean_unbox(v_whnfType_1445_);
v_res_1453_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3(v_00_u03b1_1440_, v_type_1441_, v_maxFVars_x3f_1442_, v_k_1443_, v_cleanupAnnotations_boxed_1451_, v_whnfType_boxed_1452_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_);
lean_dec(v___y_1449_);
lean_dec_ref(v___y_1448_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
return v_res_1453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0(lean_object* v_name_1454_, lean_object* v_us_1455_, lean_object* v_params_1456_, lean_object* v_args1_1457_, uint8_t v_useEq_1458_, lean_object* v_args2_1459_, lean_object* v_args2New_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1466_ = l_Lean_mkConst(v_name_1454_, v_us_1455_);
v___x_1467_ = l_Lean_mkAppN(v___x_1466_, v_params_1456_);
lean_inc_ref(v___x_1467_);
v___x_1468_ = l_Lean_mkAppN(v___x_1467_, v_args1_1457_);
v___x_1469_ = l_Lean_mkAppN(v___x_1467_, v_args2_1459_);
v___x_1470_ = l_Lean_Meta_mkEq(v___x_1468_, v___x_1469_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v_a_1471_; uint8_t v___x_1472_; lean_object* v_result_1474_; lean_object* v___y_1475_; lean_object* v___y_1476_; lean_object* v___y_1477_; lean_object* v___y_1478_; lean_object* v___x_1519_; 
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
lean_inc(v_a_1471_);
lean_dec_ref_known(v___x_1470_, 1);
v___x_1472_ = 1;
v___x_1519_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v_args1_1457_, v_args2_1459_, v___x_1472_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
if (lean_obj_tag(v___x_1519_) == 0)
{
lean_object* v_a_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1551_; 
v_a_1520_ = lean_ctor_get(v___x_1519_, 0);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1522_ = v___x_1519_;
v_isShared_1523_ = v_isSharedCheck_1551_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_a_1520_);
lean_dec(v___x_1519_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1551_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1524_; 
v___x_1524_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f(v_a_1520_);
if (lean_obj_tag(v___x_1524_) == 1)
{
lean_del_object(v___x_1522_);
if (v_useEq_1458_ == 0)
{
lean_object* v_val_1525_; lean_object* v___x_1526_; 
v_val_1525_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_val_1525_);
lean_dec_ref_known(v___x_1524_, 1);
v___x_1526_ = l_Lean_mkArrow(v_a_1471_, v_val_1525_, v___y_1463_, v___y_1464_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_object* v_a_1527_; 
v_a_1527_ = lean_ctor_get(v___x_1526_, 0);
lean_inc(v_a_1527_);
lean_dec_ref_known(v___x_1526_, 1);
v_result_1474_ = v_a_1527_;
v___y_1475_ = v___y_1461_;
v___y_1476_ = v___y_1462_;
v___y_1477_ = v___y_1463_;
v___y_1478_ = v___y_1464_;
goto v___jp_1473_;
}
else
{
lean_object* v_a_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1535_; 
v_a_1528_ = lean_ctor_get(v___x_1526_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1530_ = v___x_1526_;
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_a_1528_);
lean_dec(v___x_1526_);
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
else
{
lean_object* v_val_1536_; lean_object* v___x_1537_; 
v_val_1536_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_val_1536_);
lean_dec_ref_known(v___x_1524_, 1);
v___x_1537_ = l_Lean_Meta_mkEq(v_a_1471_, v_val_1536_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v_a_1538_; 
v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
lean_inc(v_a_1538_);
lean_dec_ref_known(v___x_1537_, 1);
v_result_1474_ = v_a_1538_;
v___y_1475_ = v___y_1461_;
v___y_1476_ = v___y_1462_;
v___y_1477_ = v___y_1463_;
v___y_1478_ = v___y_1464_;
goto v___jp_1473_;
}
else
{
lean_object* v_a_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1546_; 
v_a_1539_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1541_ = v___x_1537_;
v_isShared_1542_ = v_isSharedCheck_1546_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_a_1539_);
lean_dec(v___x_1537_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1546_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1544_; 
if (v_isShared_1542_ == 0)
{
v___x_1544_ = v___x_1541_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_a_1539_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
}
}
}
else
{
lean_object* v___x_1547_; lean_object* v___x_1549_; 
lean_dec(v___x_1524_);
lean_dec(v_a_1471_);
v___x_1547_ = lean_box(0);
if (v_isShared_1523_ == 0)
{
lean_ctor_set(v___x_1522_, 0, v___x_1547_);
v___x_1549_ = v___x_1522_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v___x_1547_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
}
}
else
{
lean_object* v_a_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1559_; 
lean_dec(v_a_1471_);
v_a_1552_ = lean_ctor_get(v___x_1519_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1554_ = v___x_1519_;
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_a_1552_);
lean_dec(v___x_1519_);
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
v___jp_1473_:
{
uint8_t v___x_1479_; uint8_t v___x_1480_; lean_object* v___x_1481_; 
v___x_1479_ = 0;
v___x_1480_ = 1;
v___x_1481_ = l_Lean_Meta_mkForallFVars(v_args2New_1460_, v_result_1474_, v___x_1479_, v___x_1472_, v___x_1472_, v___x_1480_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
if (lean_obj_tag(v___x_1481_) == 0)
{
lean_object* v_a_1482_; lean_object* v___x_1483_; 
v_a_1482_ = lean_ctor_get(v___x_1481_, 0);
lean_inc(v_a_1482_);
lean_dec_ref_known(v___x_1481_, 1);
v___x_1483_ = l_Lean_Meta_mkForallFVars(v_args1_1457_, v_a_1482_, v___x_1479_, v___x_1472_, v___x_1472_, v___x_1480_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_object* v_a_1484_; lean_object* v___x_1485_; 
v_a_1484_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_a_1484_);
lean_dec_ref_known(v___x_1483_, 1);
v___x_1485_ = l_Lean_Meta_mkForallFVars(v_params_1456_, v_a_1484_, v___x_1479_, v___x_1472_, v___x_1472_, v___x_1480_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1494_; 
v_a_1486_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1488_ = v___x_1485_;
v_isShared_1489_ = v_isSharedCheck_1494_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___x_1485_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1494_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1490_; lean_object* v___x_1492_; 
v___x_1490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1490_, 0, v_a_1486_);
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 0, v___x_1490_);
v___x_1492_ = v___x_1488_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___x_1490_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
else
{
lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1502_; 
v_a_1495_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1497_ = v___x_1485_;
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v___x_1485_);
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
v_a_1503_ = lean_ctor_get(v___x_1483_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1483_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1505_ = v___x_1483_;
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_a_1503_);
lean_dec(v___x_1483_);
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
else
{
lean_object* v_a_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1518_; 
v_a_1511_ = lean_ctor_get(v___x_1481_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1481_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1513_ = v___x_1481_;
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_a_1511_);
lean_dec(v___x_1481_);
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
}
else
{
lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1567_; 
lean_dec_ref(v_args2_1459_);
v_a_1560_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1562_ = v___x_1470_;
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v___x_1470_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1565_; 
if (v_isShared_1563_ == 0)
{
v___x_1565_ = v___x_1562_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_a_1560_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0___boxed(lean_object* v_name_1568_, lean_object* v_us_1569_, lean_object* v_params_1570_, lean_object* v_args1_1571_, lean_object* v_useEq_1572_, lean_object* v_args2_1573_, lean_object* v_args2New_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
uint8_t v_useEq_boxed_1580_; lean_object* v_res_1581_; 
v_useEq_boxed_1580_ = lean_unbox(v_useEq_1572_);
v_res_1581_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0(v_name_1568_, v_us_1569_, v_params_1570_, v_args1_1571_, v_useEq_boxed_1580_, v_args2_1573_, v_args2New_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
lean_dec(v___y_1576_);
lean_dec_ref(v___y_1575_);
lean_dec_ref(v_args2New_1574_);
lean_dec_ref(v_args1_1571_);
lean_dec_ref(v_params_1570_);
return v_res_1581_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1(size_t v_sz_1582_, size_t v_i_1583_, lean_object* v_bs_1584_){
_start:
{
uint8_t v___x_1585_; 
v___x_1585_ = lean_usize_dec_lt(v_i_1583_, v_sz_1582_);
if (v___x_1585_ == 0)
{
return v_bs_1584_;
}
else
{
lean_object* v_v_1586_; lean_object* v___x_1587_; lean_object* v_bs_x27_1588_; lean_object* v___x_1589_; uint8_t v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; size_t v___x_1593_; size_t v___x_1594_; lean_object* v___x_1595_; 
v_v_1586_ = lean_array_uget(v_bs_1584_, v_i_1583_);
v___x_1587_ = lean_unsigned_to_nat(0u);
v_bs_x27_1588_ = lean_array_uset(v_bs_1584_, v_i_1583_, v___x_1587_);
v___x_1589_ = l_Lean_Expr_fvarId_x21(v_v_1586_);
lean_dec(v_v_1586_);
v___x_1590_ = 1;
v___x_1591_ = lean_box(v___x_1590_);
v___x_1592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1589_);
lean_ctor_set(v___x_1592_, 1, v___x_1591_);
v___x_1593_ = ((size_t)1ULL);
v___x_1594_ = lean_usize_add(v_i_1583_, v___x_1593_);
v___x_1595_ = lean_array_uset(v_bs_x27_1588_, v_i_1583_, v___x_1592_);
v_i_1583_ = v___x_1594_;
v_bs_1584_ = v___x_1595_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1___boxed(lean_object* v_sz_1597_, lean_object* v_i_1598_, lean_object* v_bs_1599_){
_start:
{
size_t v_sz_boxed_1600_; size_t v_i_boxed_1601_; lean_object* v_res_1602_; 
v_sz_boxed_1600_ = lean_unbox_usize(v_sz_1597_);
lean_dec(v_sz_1597_);
v_i_boxed_1601_ = lean_unbox_usize(v_i_1598_);
lean_dec(v_i_1598_);
v_res_1602_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1(v_sz_boxed_1600_, v_i_boxed_1601_, v_bs_1599_);
return v_res_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(lean_object* v_bs_1603_, lean_object* v_k_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
lean_object* v___x_1610_; 
v___x_1610_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_box(0), v_bs_1603_, v_k_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1618_; 
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1613_ = v___x_1610_;
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1610_);
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
v_reuseFailAlloc_1617_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1626_; 
v_a_1619_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1621_ = v___x_1610_;
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1610_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1624_; 
if (v_isShared_1622_ == 0)
{
v___x_1624_ = v___x_1621_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_a_1619_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_bs_1627_, lean_object* v_k_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_){
_start:
{
lean_object* v_res_1634_; 
v_res_1634_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(v_bs_1627_, v_k_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
lean_dec(v___y_1632_);
lean_dec_ref(v___y_1631_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
lean_dec_ref(v_bs_1627_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(lean_object* v_bs_1635_, lean_object* v_k_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_){
_start:
{
size_t v_sz_1642_; size_t v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; 
v_sz_1642_ = lean_array_size(v_bs_1635_);
v___x_1643_ = ((size_t)0ULL);
v___x_1644_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1(v_sz_1642_, v___x_1643_, v_bs_1635_);
v___x_1645_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(v___x_1644_, v_k_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_);
lean_dec_ref(v___x_1644_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg___boxed(lean_object* v_bs_1646_, lean_object* v_k_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v_bs_1646_, v_k_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_);
lean_dec(v___y_1651_);
lean_dec_ref(v___y_1650_);
lean_dec(v___y_1649_);
lean_dec_ref(v___y_1648_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1(lean_object* v_name_1654_, lean_object* v_us_1655_, lean_object* v_params_1656_, uint8_t v_useEq_1657_, lean_object* v_ctorVal_1658_, lean_object* v_type_1659_, lean_object* v_args1_1660_, lean_object* v_resultType_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_){
_start:
{
lean_object* v___x_1667_; lean_object* v___f_1668_; 
v___x_1667_ = lean_box(v_useEq_1657_);
lean_inc_ref(v_args1_1660_);
lean_inc_ref(v_params_1656_);
v___f_1668_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1668_, 0, v_name_1654_);
lean_closure_set(v___f_1668_, 1, v_us_1655_);
lean_closure_set(v___f_1668_, 2, v_params_1656_);
lean_closure_set(v___f_1668_, 3, v_args1_1660_);
lean_closure_set(v___f_1668_, 4, v___x_1667_);
if (v_useEq_1657_ == 0)
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1669_ = l_Array_append___redArg(v_params_1656_, v_args1_1660_);
v___x_1670_ = lean_unsigned_to_nat(0u);
v___x_1671_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_1672_ = lean_box(v_useEq_1657_);
v___x_1673_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___boxed), 14, 9);
lean_closure_set(v___x_1673_, 0, v_ctorVal_1658_);
lean_closure_set(v___x_1673_, 1, v___x_1672_);
lean_closure_set(v___x_1673_, 2, v_args1_1660_);
lean_closure_set(v___x_1673_, 3, v_resultType_1661_);
lean_closure_set(v___x_1673_, 4, v___f_1668_);
lean_closure_set(v___x_1673_, 5, v___x_1670_);
lean_closure_set(v___x_1673_, 6, v_type_1659_);
lean_closure_set(v___x_1673_, 7, v___x_1671_);
lean_closure_set(v___x_1673_, 8, v___x_1671_);
v___x_1674_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v___x_1669_, v___x_1673_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_);
return v___x_1674_;
}
else
{
lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
lean_dec_ref(v_params_1656_);
v___x_1675_ = lean_unsigned_to_nat(0u);
v___x_1676_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_1677_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(v_ctorVal_1658_, v_useEq_1657_, v_args1_1660_, v_resultType_1661_, v___f_1668_, v___x_1675_, v_type_1659_, v___x_1676_, v___x_1676_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_);
return v___x_1677_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1___boxed(lean_object* v_name_1678_, lean_object* v_us_1679_, lean_object* v_params_1680_, lean_object* v_useEq_1681_, lean_object* v_ctorVal_1682_, lean_object* v_type_1683_, lean_object* v_args1_1684_, lean_object* v_resultType_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
uint8_t v_useEq_boxed_1691_; lean_object* v_res_1692_; 
v_useEq_boxed_1691_ = lean_unbox(v_useEq_1681_);
v_res_1692_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1(v_name_1678_, v_us_1679_, v_params_1680_, v_useEq_boxed_1691_, v_ctorVal_1682_, v_type_1683_, v_args1_1684_, v_resultType_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2(lean_object* v_name_1693_, lean_object* v_us_1694_, uint8_t v_useEq_1695_, lean_object* v_ctorVal_1696_, lean_object* v_params_1697_, lean_object* v_type_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_){
_start:
{
lean_object* v___x_1704_; lean_object* v___f_1705_; uint8_t v___x_1706_; lean_object* v___x_1707_; 
v___x_1704_ = lean_box(v_useEq_1695_);
lean_inc_ref(v_type_1698_);
v___f_1705_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1___boxed), 13, 6);
lean_closure_set(v___f_1705_, 0, v_name_1693_);
lean_closure_set(v___f_1705_, 1, v_us_1694_);
lean_closure_set(v___f_1705_, 2, v_params_1697_);
lean_closure_set(v___f_1705_, 3, v___x_1704_);
lean_closure_set(v___f_1705_, 4, v_ctorVal_1696_);
lean_closure_set(v___f_1705_, 5, v_type_1698_);
v___x_1706_ = 0;
v___x_1707_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_type_1698_, v___f_1705_, v___x_1706_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2___boxed(lean_object* v_name_1708_, lean_object* v_us_1709_, lean_object* v_useEq_1710_, lean_object* v_ctorVal_1711_, lean_object* v_params_1712_, lean_object* v_type_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_){
_start:
{
uint8_t v_useEq_boxed_1719_; lean_object* v_res_1720_; 
v_useEq_boxed_1719_ = lean_unbox(v_useEq_1710_);
v_res_1720_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2(v_name_1708_, v_us_1709_, v_useEq_boxed_1719_, v_ctorVal_1711_, v_params_1712_, v_type_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_);
lean_dec(v___y_1717_);
lean_dec_ref(v___y_1716_);
lean_dec(v___y_1715_);
lean_dec_ref(v___y_1714_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(lean_object* v_a_1721_, lean_object* v_a_1722_){
_start:
{
if (lean_obj_tag(v_a_1721_) == 0)
{
lean_object* v___x_1723_; 
v___x_1723_ = l_List_reverse___redArg(v_a_1722_);
return v___x_1723_;
}
else
{
lean_object* v_head_1724_; lean_object* v_tail_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1734_; 
v_head_1724_ = lean_ctor_get(v_a_1721_, 0);
v_tail_1725_ = lean_ctor_get(v_a_1721_, 1);
v_isSharedCheck_1734_ = !lean_is_exclusive(v_a_1721_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1727_ = v_a_1721_;
v_isShared_1728_ = v_isSharedCheck_1734_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_tail_1725_);
lean_inc(v_head_1724_);
lean_dec(v_a_1721_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1734_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1729_; lean_object* v___x_1731_; 
v___x_1729_ = l_Lean_mkLevelParam(v_head_1724_);
if (v_isShared_1728_ == 0)
{
lean_ctor_set(v___x_1727_, 1, v_a_1722_);
lean_ctor_set(v___x_1727_, 0, v___x_1729_);
v___x_1731_ = v___x_1727_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v___x_1729_);
lean_ctor_set(v_reuseFailAlloc_1733_, 1, v_a_1722_);
v___x_1731_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
v_a_1721_ = v_tail_1725_;
v_a_1722_ = v___x_1731_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(lean_object* v_ctorVal_1735_, uint8_t v_useEq_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_){
_start:
{
lean_object* v_toConstantVal_1742_; lean_object* v_numParams_1743_; lean_object* v_name_1744_; lean_object* v_levelParams_1745_; lean_object* v_type_1746_; lean_object* v___x_1747_; 
v_toConstantVal_1742_ = lean_ctor_get(v_ctorVal_1735_, 0);
v_numParams_1743_ = lean_ctor_get(v_ctorVal_1735_, 3);
lean_inc(v_numParams_1743_);
v_name_1744_ = lean_ctor_get(v_toConstantVal_1742_, 0);
lean_inc(v_name_1744_);
v_levelParams_1745_ = lean_ctor_get(v_toConstantVal_1742_, 1);
v_type_1746_ = lean_ctor_get(v_toConstantVal_1742_, 2);
lean_inc_ref(v_type_1746_);
v___x_1747_ = l_Lean_Meta_elimOptParam(v_type_1746_, v_a_1739_, v_a_1740_);
if (lean_obj_tag(v___x_1747_) == 0)
{
lean_object* v_a_1748_; lean_object* v___x_1749_; lean_object* v_us_1750_; lean_object* v___x_1751_; lean_object* v___f_1752_; lean_object* v___x_1753_; uint8_t v___x_1754_; lean_object* v___x_1755_; 
v_a_1748_ = lean_ctor_get(v___x_1747_, 0);
lean_inc(v_a_1748_);
lean_dec_ref_known(v___x_1747_, 1);
v___x_1749_ = lean_box(0);
lean_inc(v_levelParams_1745_);
v_us_1750_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(v_levelParams_1745_, v___x_1749_);
v___x_1751_ = lean_box(v_useEq_1736_);
v___f_1752_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2___boxed), 11, 4);
lean_closure_set(v___f_1752_, 0, v_name_1744_);
lean_closure_set(v___f_1752_, 1, v_us_1750_);
lean_closure_set(v___f_1752_, 2, v___x_1751_);
lean_closure_set(v___f_1752_, 3, v_ctorVal_1735_);
v___x_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1753_, 0, v_numParams_1743_);
v___x_1754_ = 0;
v___x_1755_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(v_a_1748_, v___x_1753_, v___f_1752_, v___x_1754_, v___x_1754_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
return v___x_1755_;
}
else
{
lean_object* v_a_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1763_; 
lean_dec(v_name_1744_);
lean_dec(v_numParams_1743_);
lean_dec_ref(v_ctorVal_1735_);
v_a_1756_ = lean_ctor_get(v___x_1747_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1758_ = v___x_1747_;
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_a_1756_);
lean_dec(v___x_1747_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1761_; 
if (v_isShared_1759_ == 0)
{
v___x_1761_ = v___x_1758_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_a_1756_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___boxed(lean_object* v_ctorVal_1764_, lean_object* v_useEq_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_){
_start:
{
uint8_t v_useEq_boxed_1771_; lean_object* v_res_1772_; 
v_useEq_boxed_1771_ = lean_unbox(v_useEq_1765_);
v_res_1772_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(v_ctorVal_1764_, v_useEq_boxed_1771_, v_a_1766_, v_a_1767_, v_a_1768_, v_a_1769_);
lean_dec(v_a_1769_);
lean_dec_ref(v_a_1768_);
lean_dec(v_a_1767_);
lean_dec_ref(v_a_1766_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2(lean_object* v_00_u03b1_1773_, lean_object* v_bs_1774_, lean_object* v_k_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_){
_start:
{
lean_object* v___x_1781_; 
v___x_1781_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(v_bs_1774_, v_k_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1782_, lean_object* v_bs_1783_, lean_object* v_k_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2(v_00_u03b1_1782_, v_bs_1783_, v_k_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec_ref(v_bs_1783_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1(lean_object* v_00_u03b1_1791_, lean_object* v_bs_1792_, lean_object* v_k_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v___x_1799_; 
v___x_1799_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v_bs_1792_, v_k_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___boxed(lean_object* v_00_u03b1_1800_, lean_object* v_bs_1801_, lean_object* v_k_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1(v_00_u03b1_1800_, v_bs_1801_, v_k_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_);
lean_dec(v___y_1806_);
lean_dec_ref(v___y_1805_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(lean_object* v_ctorVal_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_){
_start:
{
uint8_t v___x_1815_; lean_object* v___x_1816_; 
v___x_1815_ = 0;
v___x_1816_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(v_ctorVal_1809_, v___x_1815_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f___boxed(lean_object* v_ctorVal_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_);
lean_dec(v_a_1821_);
lean_dec_ref(v_a_1820_);
lean_dec(v_a_1819_);
lean_dec_ref(v_a_1818_);
return v_res_1823_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1(void){
_start:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1825_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__0));
v___x_1826_ = l_Lean_stringToMessageData(v___x_1825_);
return v___x_1826_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3(void){
_start:
{
lean_object* v___x_1828_; lean_object* v___x_1829_; 
v___x_1828_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__2));
v___x_1829_ = l_Lean_stringToMessageData(v___x_1828_);
return v___x_1829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(lean_object* v_ctorName_1830_){
_start:
{
lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1831_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1);
v___x_1832_ = l_Lean_MessageData_ofName(v_ctorName_1830_);
v___x_1833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1831_);
lean_ctor_set(v___x_1833_, 1, v___x_1832_);
v___x_1834_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3);
v___x_1835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1833_);
lean_ctor_set(v___x_1835_, 1, v___x_1834_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(lean_object* v_ctorName_1836_, lean_object* v_mvarId_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_){
_start:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1843_ = l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(v_ctorName_1836_);
v___x_1844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1844_, 0, v_mvarId_1837_);
v___x_1845_ = l_Lean_indentD(v___x_1844_);
v___x_1846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1843_);
lean_ctor_set(v___x_1846_, 1, v___x_1845_);
v___x_1847_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_1846_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg___boxed(lean_object* v_ctorName_1848_, lean_object* v_mvarId_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_){
_start:
{
lean_object* v_res_1855_; 
v_res_1855_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(v_ctorName_1848_, v_mvarId_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_);
lean_dec(v_a_1853_);
lean_dec_ref(v_a_1852_);
lean_dec(v_a_1851_);
lean_dec_ref(v_a_1850_);
return v_res_1855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure(lean_object* v_00_u03b1_1856_, lean_object* v_ctorName_1857_, lean_object* v_mvarId_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_){
_start:
{
lean_object* v___x_1864_; 
v___x_1864_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(v_ctorName_1857_, v_mvarId_1858_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___boxed(lean_object* v_00_u03b1_1865_, lean_object* v_ctorName_1866_, lean_object* v_mvarId_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_){
_start:
{
lean_object* v_res_1873_; 
v_res_1873_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure(v_00_u03b1_1865_, v_ctorName_1866_, v_mvarId_1867_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_);
lean_dec(v_a_1871_);
lean_dec_ref(v_a_1870_);
lean_dec(v_a_1869_);
lean_dec_ref(v_a_1868_);
return v_res_1873_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0(lean_object* v_ctorName_1874_, lean_object* v_as_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_){
_start:
{
if (lean_obj_tag(v_as_1875_) == 0)
{
lean_object* v___x_1881_; lean_object* v___x_1882_; 
lean_dec(v_ctorName_1874_);
v___x_1881_ = lean_box(0);
v___x_1882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1881_);
return v___x_1882_;
}
else
{
lean_object* v_head_1883_; lean_object* v_tail_1884_; lean_object* v___x_1885_; 
v_head_1883_ = lean_ctor_get(v_as_1875_, 0);
lean_inc_n(v_head_1883_, 2);
v_tail_1884_ = lean_ctor_get(v_as_1875_, 1);
lean_inc(v_tail_1884_);
lean_dec_ref_known(v_as_1875_, 2);
v___x_1885_ = l_Lean_MVarId_assumptionCore(v_head_1883_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_object* v_a_1886_; uint8_t v___x_1887_; 
v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
lean_inc(v_a_1886_);
lean_dec_ref_known(v___x_1885_, 1);
v___x_1887_ = lean_unbox(v_a_1886_);
lean_dec(v_a_1886_);
if (v___x_1887_ == 0)
{
lean_object* v___x_1888_; 
lean_dec(v_tail_1884_);
v___x_1888_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(v_ctorName_1874_, v_head_1883_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_);
return v___x_1888_;
}
else
{
lean_dec(v_head_1883_);
v_as_1875_ = v_tail_1884_;
goto _start;
}
}
else
{
lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1897_; 
lean_dec(v_tail_1884_);
lean_dec(v_head_1883_);
lean_dec(v_ctorName_1874_);
v_a_1890_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1892_ = v___x_1885_;
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v___x_1885_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1895_; 
if (v_isShared_1893_ == 0)
{
v___x_1895_ = v___x_1892_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_a_1890_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0___boxed(lean_object* v_ctorName_1898_, lean_object* v_as_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0(v_ctorName_1898_, v_as_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(lean_object* v_mvarId_1906_, lean_object* v_ctorName_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_){
_start:
{
lean_object* v___x_1913_; 
v___x_1913_ = l_Lean_MVarId_splitAndCore(v_mvarId_1906_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_a_1914_; lean_object* v___x_1915_; 
v_a_1914_ = lean_ctor_get(v___x_1913_, 0);
lean_inc(v_a_1914_);
lean_dec_ref_known(v___x_1913_, 1);
v___x_1915_ = l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0(v_ctorName_1907_, v_a_1914_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_);
return v___x_1915_;
}
else
{
lean_object* v_a_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1923_; 
lean_dec(v_ctorName_1907_);
v_a_1916_ = lean_ctor_get(v___x_1913_, 0);
v_isSharedCheck_1923_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1918_ = v___x_1913_;
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_a_1916_);
lean_dec(v___x_1913_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1921_; 
if (v_isShared_1919_ == 0)
{
v___x_1921_ = v___x_1918_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_a_1916_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption___boxed(lean_object* v_mvarId_1924_, lean_object* v_ctorName_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_){
_start:
{
lean_object* v_res_1931_; 
v_res_1931_ = l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(v_mvarId_1924_, v_ctorName_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_);
lean_dec(v_a_1929_);
lean_dec_ref(v_a_1928_);
lean_dec(v_a_1927_);
lean_dec_ref(v_a_1926_);
return v_res_1931_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0(lean_object* v_msg_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_){
_start:
{
lean_object* v___f_1939_; lean_object* v___x_1015__overap_1940_; lean_object* v___x_1941_; 
v___f_1939_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0___closed__0));
v___x_1015__overap_1940_ = lean_panic_fn_borrowed(v___f_1939_, v_msg_1933_);
lean_inc(v___y_1937_);
lean_inc_ref(v___y_1936_);
lean_inc(v___y_1935_);
lean_inc_ref(v___y_1934_);
v___x_1941_ = lean_apply_5(v___x_1015__overap_1940_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, lean_box(0));
return v___x_1941_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0___boxed(lean_object* v_msg_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0(v_msg_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
return v_res_1948_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1949_; double v___x_1950_; 
v___x_1949_ = lean_unsigned_to_nat(0u);
v___x_1950_ = lean_float_of_nat(v___x_1949_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(lean_object* v_cls_1954_, lean_object* v_msg_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_){
_start:
{
lean_object* v_ref_1961_; lean_object* v___x_1962_; lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_2007_; 
v_ref_1961_ = lean_ctor_get(v___y_1958_, 5);
v___x_1962_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msg_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_1965_ = v___x_1962_;
v_isShared_1966_ = v_isSharedCheck_2007_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_dec(v___x_1962_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_2007_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1967_; lean_object* v_traceState_1968_; lean_object* v_env_1969_; lean_object* v_nextMacroScope_1970_; lean_object* v_ngen_1971_; lean_object* v_auxDeclNGen_1972_; lean_object* v_cache_1973_; lean_object* v_messages_1974_; lean_object* v_infoState_1975_; lean_object* v_snapshotTasks_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_2006_; 
v___x_1967_ = lean_st_ref_take(v___y_1959_);
v_traceState_1968_ = lean_ctor_get(v___x_1967_, 4);
v_env_1969_ = lean_ctor_get(v___x_1967_, 0);
v_nextMacroScope_1970_ = lean_ctor_get(v___x_1967_, 1);
v_ngen_1971_ = lean_ctor_get(v___x_1967_, 2);
v_auxDeclNGen_1972_ = lean_ctor_get(v___x_1967_, 3);
v_cache_1973_ = lean_ctor_get(v___x_1967_, 5);
v_messages_1974_ = lean_ctor_get(v___x_1967_, 6);
v_infoState_1975_ = lean_ctor_get(v___x_1967_, 7);
v_snapshotTasks_1976_ = lean_ctor_get(v___x_1967_, 8);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_1978_ = v___x_1967_;
v_isShared_1979_ = v_isSharedCheck_2006_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_snapshotTasks_1976_);
lean_inc(v_infoState_1975_);
lean_inc(v_messages_1974_);
lean_inc(v_cache_1973_);
lean_inc(v_traceState_1968_);
lean_inc(v_auxDeclNGen_1972_);
lean_inc(v_ngen_1971_);
lean_inc(v_nextMacroScope_1970_);
lean_inc(v_env_1969_);
lean_dec(v___x_1967_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_2006_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
uint64_t v_tid_1980_; lean_object* v_traces_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_2005_; 
v_tid_1980_ = lean_ctor_get_uint64(v_traceState_1968_, sizeof(void*)*1);
v_traces_1981_ = lean_ctor_get(v_traceState_1968_, 0);
v_isSharedCheck_2005_ = !lean_is_exclusive(v_traceState_1968_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_1983_ = v_traceState_1968_;
v_isShared_1984_ = v_isSharedCheck_2005_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_traces_1981_);
lean_dec(v_traceState_1968_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_2005_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1985_; double v___x_1986_; uint8_t v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1995_; 
v___x_1985_ = lean_box(0);
v___x_1986_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0);
v___x_1987_ = 0;
v___x_1988_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_1989_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1989_, 0, v_cls_1954_);
lean_ctor_set(v___x_1989_, 1, v___x_1985_);
lean_ctor_set(v___x_1989_, 2, v___x_1988_);
lean_ctor_set_float(v___x_1989_, sizeof(void*)*3, v___x_1986_);
lean_ctor_set_float(v___x_1989_, sizeof(void*)*3 + 8, v___x_1986_);
lean_ctor_set_uint8(v___x_1989_, sizeof(void*)*3 + 16, v___x_1987_);
v___x_1990_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__2));
v___x_1991_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1989_);
lean_ctor_set(v___x_1991_, 1, v_a_1963_);
lean_ctor_set(v___x_1991_, 2, v___x_1990_);
lean_inc(v_ref_1961_);
v___x_1992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1992_, 0, v_ref_1961_);
lean_ctor_set(v___x_1992_, 1, v___x_1991_);
v___x_1993_ = l_Lean_PersistentArray_push___redArg(v_traces_1981_, v___x_1992_);
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 0, v___x_1993_);
v___x_1995_ = v___x_1983_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v___x_1993_);
lean_ctor_set_uint64(v_reuseFailAlloc_2004_, sizeof(void*)*1, v_tid_1980_);
v___x_1995_ = v_reuseFailAlloc_2004_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
lean_object* v___x_1997_; 
if (v_isShared_1979_ == 0)
{
lean_ctor_set(v___x_1978_, 4, v___x_1995_);
v___x_1997_ = v___x_1978_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_env_1969_);
lean_ctor_set(v_reuseFailAlloc_2003_, 1, v_nextMacroScope_1970_);
lean_ctor_set(v_reuseFailAlloc_2003_, 2, v_ngen_1971_);
lean_ctor_set(v_reuseFailAlloc_2003_, 3, v_auxDeclNGen_1972_);
lean_ctor_set(v_reuseFailAlloc_2003_, 4, v___x_1995_);
lean_ctor_set(v_reuseFailAlloc_2003_, 5, v_cache_1973_);
lean_ctor_set(v_reuseFailAlloc_2003_, 6, v_messages_1974_);
lean_ctor_set(v_reuseFailAlloc_2003_, 7, v_infoState_1975_);
lean_ctor_set(v_reuseFailAlloc_2003_, 8, v_snapshotTasks_1976_);
v___x_1997_ = v_reuseFailAlloc_2003_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2001_; 
v___x_1998_ = lean_st_ref_set(v___y_1959_, v___x_1997_);
v___x_1999_ = lean_box(0);
if (v_isShared_1966_ == 0)
{
lean_ctor_set(v___x_1965_, 0, v___x_1999_);
v___x_2001_ = v___x_1965_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1999_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___boxed(lean_object* v_cls_2008_, lean_object* v_msg_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_){
_start:
{
lean_object* v_res_2015_; 
v_res_2015_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2008_, v_msg_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_);
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
lean_dec(v___y_2011_);
lean_dec_ref(v___y_2010_);
return v_res_2015_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3(void){
_start:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; 
v___x_2019_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__2));
v___x_2020_ = lean_unsigned_to_nat(30u);
v___x_2021_ = lean_unsigned_to_nat(96u);
v___x_2022_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__1));
v___x_2023_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__0));
v___x_2024_ = l_mkPanicMessageWithDecl(v___x_2023_, v___x_2022_, v___x_2021_, v___x_2020_, v___x_2019_);
return v___x_2024_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9(void){
_start:
{
lean_object* v_cls_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; 
v_cls_2033_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_2034_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__8));
v___x_2035_ = l_Lean_Name_append(v___x_2034_, v_cls_2033_);
return v___x_2035_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11(void){
_start:
{
lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2037_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__10));
v___x_2038_ = l_Lean_stringToMessageData(v___x_2037_);
return v___x_2038_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13(void){
_start:
{
lean_object* v___x_2040_; lean_object* v___x_2041_; 
v___x_2040_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__12));
v___x_2041_ = l_Lean_stringToMessageData(v___x_2040_);
return v___x_2041_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15(void){
_start:
{
lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2043_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__14));
v___x_2044_ = l_Lean_stringToMessageData(v___x_2043_);
return v___x_2044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(lean_object* v_ctorName_2045_, lean_object* v_mvarId_2046_, lean_object* v_h_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_){
_start:
{
lean_object* v___y_2054_; lean_object* v___y_2055_; lean_object* v___y_2056_; lean_object* v___y_2057_; lean_object* v_options_2073_; uint8_t v_hasTrace_2074_; 
v_options_2073_ = lean_ctor_get(v_a_2050_, 2);
v_hasTrace_2074_ = lean_ctor_get_uint8(v_options_2073_, sizeof(void*)*1);
if (v_hasTrace_2074_ == 0)
{
v___y_2054_ = v_a_2048_;
v___y_2055_ = v_a_2049_;
v___y_2056_ = v_a_2050_;
v___y_2057_ = v_a_2051_;
goto v___jp_2053_;
}
else
{
lean_object* v_inheritedTraceOptions_2075_; lean_object* v_cls_2076_; lean_object* v___x_2077_; uint8_t v___x_2078_; 
v_inheritedTraceOptions_2075_ = lean_ctor_get(v_a_2050_, 13);
v_cls_2076_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_2077_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_2078_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2075_, v_options_2073_, v___x_2077_);
if (v___x_2078_ == 0)
{
v___y_2054_ = v_a_2048_;
v___y_2055_ = v_a_2049_;
v___y_2056_ = v_a_2050_;
v___y_2057_ = v_a_2051_;
goto v___jp_2053_;
}
else
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; 
v___x_2079_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11);
lean_inc(v_ctorName_2045_);
v___x_2080_ = l_Lean_MessageData_ofName(v_ctorName_2045_);
v___x_2081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2079_);
lean_ctor_set(v___x_2081_, 1, v___x_2080_);
v___x_2082_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13);
v___x_2083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2081_);
lean_ctor_set(v___x_2083_, 1, v___x_2082_);
lean_inc(v_h_2047_);
v___x_2084_ = l_Lean_mkFVar(v_h_2047_);
v___x_2085_ = l_Lean_MessageData_ofExpr(v___x_2084_);
v___x_2086_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2083_);
lean_ctor_set(v___x_2086_, 1, v___x_2085_);
v___x_2087_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15);
v___x_2088_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2086_);
lean_ctor_set(v___x_2088_, 1, v___x_2087_);
lean_inc(v_mvarId_2046_);
v___x_2089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2089_, 0, v_mvarId_2046_);
v___x_2090_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2088_);
lean_ctor_set(v___x_2090_, 1, v___x_2089_);
v___x_2091_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2076_, v___x_2090_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_dec_ref_known(v___x_2091_, 1);
v___y_2054_ = v_a_2048_;
v___y_2055_ = v_a_2049_;
v___y_2056_ = v_a_2050_;
v___y_2057_ = v_a_2051_;
goto v___jp_2053_;
}
else
{
lean_dec(v_h_2047_);
lean_dec(v_mvarId_2046_);
lean_dec(v_ctorName_2045_);
return v___x_2091_;
}
}
}
v___jp_2053_:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2058_ = lean_box(0);
v___x_2059_ = l_Lean_Meta_injection(v_mvarId_2046_, v_h_2047_, v___x_2058_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
if (lean_obj_tag(v___x_2059_) == 0)
{
lean_object* v_a_2060_; 
v_a_2060_ = lean_ctor_get(v___x_2059_, 0);
lean_inc(v_a_2060_);
lean_dec_ref_known(v___x_2059_, 1);
if (lean_obj_tag(v_a_2060_) == 0)
{
lean_object* v___x_2061_; lean_object* v___x_2062_; 
lean_dec(v_ctorName_2045_);
v___x_2061_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3);
v___x_2062_ = l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0(v___x_2061_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
return v___x_2062_;
}
else
{
lean_object* v_mvarId_2063_; lean_object* v___x_2064_; 
v_mvarId_2063_ = lean_ctor_get(v_a_2060_, 0);
lean_inc(v_mvarId_2063_);
lean_dec_ref_known(v_a_2060_, 3);
v___x_2064_ = l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(v_mvarId_2063_, v_ctorName_2045_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
return v___x_2064_;
}
}
else
{
lean_object* v_a_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2072_; 
lean_dec(v_ctorName_2045_);
v_a_2065_ = lean_ctor_get(v___x_2059_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2067_ = v___x_2059_;
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_a_2065_);
lean_dec(v___x_2059_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2070_; 
if (v_isShared_2068_ == 0)
{
v___x_2070_ = v___x_2067_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_a_2065_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___boxed(lean_object* v_ctorName_2092_, lean_object* v_mvarId_2093_, lean_object* v_h_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_){
_start:
{
lean_object* v_res_2100_; 
v_res_2100_ = l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(v_ctorName_2092_, v_mvarId_2093_, v_h_2094_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_);
lean_dec(v_a_2098_);
lean_dec_ref(v_a_2097_);
lean_dec(v_a_2096_);
lean_dec_ref(v_a_2095_);
return v_res_2100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(lean_object* v_type_2101_, lean_object* v_k_2102_, uint8_t v_cleanupAnnotations_2103_, uint8_t v_whnfType_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_){
_start:
{
lean_object* v___f_2110_; lean_object* v___x_2111_; 
v___f_2110_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2110_, 0, v_k_2102_);
v___x_2111_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_2101_, v___f_2110_, v_cleanupAnnotations_2103_, v_whnfType_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2119_; 
v_a_2112_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2114_ = v___x_2111_;
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2111_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2117_; 
if (v_isShared_2115_ == 0)
{
v___x_2117_ = v___x_2114_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_a_2112_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
else
{
lean_object* v_a_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2127_; 
v_a_2120_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2122_ = v___x_2111_;
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_a_2120_);
lean_dec(v___x_2111_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2125_; 
if (v_isShared_2123_ == 0)
{
v___x_2125_ = v___x_2122_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_a_2120_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg___boxed(lean_object* v_type_2128_, lean_object* v_k_2129_, lean_object* v_cleanupAnnotations_2130_, lean_object* v_whnfType_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2137_; uint8_t v_whnfType_boxed_2138_; lean_object* v_res_2139_; 
v_cleanupAnnotations_boxed_2137_ = lean_unbox(v_cleanupAnnotations_2130_);
v_whnfType_boxed_2138_ = lean_unbox(v_whnfType_2131_);
v_res_2139_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_type_2128_, v_k_2129_, v_cleanupAnnotations_boxed_2137_, v_whnfType_boxed_2138_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_);
lean_dec(v___y_2135_);
lean_dec_ref(v___y_2134_);
lean_dec(v___y_2133_);
lean_dec_ref(v___y_2132_);
return v_res_2139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0(lean_object* v_00_u03b1_2140_, lean_object* v_type_2141_, lean_object* v_k_2142_, uint8_t v_cleanupAnnotations_2143_, uint8_t v_whnfType_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_){
_start:
{
lean_object* v___x_2150_; 
v___x_2150_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_type_2141_, v_k_2142_, v_cleanupAnnotations_2143_, v_whnfType_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_);
return v___x_2150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___boxed(lean_object* v_00_u03b1_2151_, lean_object* v_type_2152_, lean_object* v_k_2153_, lean_object* v_cleanupAnnotations_2154_, lean_object* v_whnfType_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2161_; uint8_t v_whnfType_boxed_2162_; lean_object* v_res_2163_; 
v_cleanupAnnotations_boxed_2161_ = lean_unbox(v_cleanupAnnotations_2154_);
v_whnfType_boxed_2162_ = lean_unbox(v_whnfType_2155_);
v_res_2163_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0(v_00_u03b1_2151_, v_type_2152_, v_k_2153_, v_cleanupAnnotations_boxed_2161_, v_whnfType_boxed_2162_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_);
lean_dec(v___y_2159_);
lean_dec_ref(v___y_2158_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
return v_res_2163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0(lean_object* v___x_2164_, lean_object* v_ctorName_2165_, lean_object* v_xs_2166_, lean_object* v_type_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_){
_start:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2173_ = lean_box(0);
v___x_2174_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_2167_, v___x_2173_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
if (lean_obj_tag(v___x_2174_) == 0)
{
lean_object* v_a_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; 
v_a_2175_ = lean_ctor_get(v___x_2174_, 0);
lean_inc(v_a_2175_);
lean_dec_ref_known(v___x_2174_, 1);
v___x_2176_ = l_Lean_Expr_mvarId_x21(v_a_2175_);
v___x_2177_ = lean_array_get_size(v_xs_2166_);
v___x_2178_ = lean_unsigned_to_nat(1u);
v___x_2179_ = lean_nat_sub(v___x_2177_, v___x_2178_);
v___x_2180_ = lean_array_get_borrowed(v___x_2164_, v_xs_2166_, v___x_2179_);
lean_dec(v___x_2179_);
v___x_2181_ = l_Lean_Expr_fvarId_x21(v___x_2180_);
v___x_2182_ = l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(v_ctorName_2165_, v___x_2176_, v___x_2181_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
if (lean_obj_tag(v___x_2182_) == 0)
{
uint8_t v___x_2183_; uint8_t v___x_2184_; uint8_t v___x_2185_; lean_object* v___x_2186_; 
lean_dec_ref_known(v___x_2182_, 1);
v___x_2183_ = 0;
v___x_2184_ = 1;
v___x_2185_ = 1;
v___x_2186_ = l_Lean_Meta_mkLambdaFVars(v_xs_2166_, v_a_2175_, v___x_2183_, v___x_2184_, v___x_2183_, v___x_2184_, v___x_2185_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
return v___x_2186_;
}
else
{
lean_object* v_a_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2194_; 
lean_dec(v_a_2175_);
v_a_2187_ = lean_ctor_get(v___x_2182_, 0);
v_isSharedCheck_2194_ = !lean_is_exclusive(v___x_2182_);
if (v_isSharedCheck_2194_ == 0)
{
v___x_2189_ = v___x_2182_;
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_a_2187_);
lean_dec(v___x_2182_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v___x_2192_; 
if (v_isShared_2190_ == 0)
{
v___x_2192_ = v___x_2189_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v_a_2187_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
}
}
else
{
lean_dec(v_ctorName_2165_);
return v___x_2174_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0___boxed(lean_object* v___x_2195_, lean_object* v_ctorName_2196_, lean_object* v_xs_2197_, lean_object* v_type_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
lean_object* v_res_2204_; 
v_res_2204_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0(v___x_2195_, v_ctorName_2196_, v_xs_2197_, v_type_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
lean_dec(v___y_2200_);
lean_dec_ref(v___y_2199_);
lean_dec_ref(v_xs_2197_);
lean_dec_ref(v___x_2195_);
return v_res_2204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(lean_object* v_ctorName_2205_, lean_object* v_targetType_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_){
_start:
{
lean_object* v___x_2212_; lean_object* v___f_2213_; uint8_t v___x_2214_; lean_object* v___x_2215_; 
v___x_2212_ = l_Lean_instInhabitedExpr;
v___f_2213_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2213_, 0, v___x_2212_);
lean_closure_set(v___f_2213_, 1, v_ctorName_2205_);
v___x_2214_ = 0;
v___x_2215_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_targetType_2206_, v___f_2213_, v___x_2214_, v___x_2214_, v_a_2207_, v_a_2208_, v_a_2209_, v_a_2210_);
return v___x_2215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___boxed(lean_object* v_ctorName_2216_, lean_object* v_targetType_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_){
_start:
{
lean_object* v_res_2223_; 
v_res_2223_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_ctorName_2216_, v_targetType_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
lean_dec(v_a_2221_);
lean_dec_ref(v_a_2220_);
lean_dec(v_a_2219_);
lean_dec_ref(v_a_2218_);
return v_res_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheoremNameFor(lean_object* v_ctorName_2227_){
_start:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2228_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheoremNameFor___closed__1));
v___x_2229_ = l_Lean_Name_append(v_ctorName_2227_, v___x_2228_);
return v___x_2229_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2230_ = lean_unsigned_to_nat(32u);
v___x_2231_ = lean_mk_empty_array_with_capacity(v___x_2230_);
v___x_2232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2231_);
return v___x_2232_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2233_ = ((size_t)5ULL);
v___x_2234_ = lean_unsigned_to_nat(0u);
v___x_2235_ = lean_unsigned_to_nat(32u);
v___x_2236_ = lean_mk_empty_array_with_capacity(v___x_2235_);
v___x_2237_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg___closed__0);
v___x_2238_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2238_, 0, v___x_2237_);
lean_ctor_set(v___x_2238_, 1, v___x_2236_);
lean_ctor_set(v___x_2238_, 2, v___x_2234_);
lean_ctor_set(v___x_2238_, 3, v___x_2234_);
lean_ctor_set_usize(v___x_2238_, 4, v___x_2233_);
return v___x_2238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(lean_object* v___y_2239_){
_start:
{
lean_object* v___x_2241_; lean_object* v_traceState_2242_; lean_object* v_traces_2243_; lean_object* v___x_2244_; lean_object* v_traceState_2245_; lean_object* v_env_2246_; lean_object* v_nextMacroScope_2247_; lean_object* v_ngen_2248_; lean_object* v_auxDeclNGen_2249_; lean_object* v_cache_2250_; lean_object* v_messages_2251_; lean_object* v_infoState_2252_; lean_object* v_snapshotTasks_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2272_; 
v___x_2241_ = lean_st_ref_get(v___y_2239_);
v_traceState_2242_ = lean_ctor_get(v___x_2241_, 4);
lean_inc_ref(v_traceState_2242_);
lean_dec(v___x_2241_);
v_traces_2243_ = lean_ctor_get(v_traceState_2242_, 0);
lean_inc_ref(v_traces_2243_);
lean_dec_ref(v_traceState_2242_);
v___x_2244_ = lean_st_ref_take(v___y_2239_);
v_traceState_2245_ = lean_ctor_get(v___x_2244_, 4);
v_env_2246_ = lean_ctor_get(v___x_2244_, 0);
v_nextMacroScope_2247_ = lean_ctor_get(v___x_2244_, 1);
v_ngen_2248_ = lean_ctor_get(v___x_2244_, 2);
v_auxDeclNGen_2249_ = lean_ctor_get(v___x_2244_, 3);
v_cache_2250_ = lean_ctor_get(v___x_2244_, 5);
v_messages_2251_ = lean_ctor_get(v___x_2244_, 6);
v_infoState_2252_ = lean_ctor_get(v___x_2244_, 7);
v_snapshotTasks_2253_ = lean_ctor_get(v___x_2244_, 8);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2244_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2255_ = v___x_2244_;
v_isShared_2256_ = v_isSharedCheck_2272_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_snapshotTasks_2253_);
lean_inc(v_infoState_2252_);
lean_inc(v_messages_2251_);
lean_inc(v_cache_2250_);
lean_inc(v_traceState_2245_);
lean_inc(v_auxDeclNGen_2249_);
lean_inc(v_ngen_2248_);
lean_inc(v_nextMacroScope_2247_);
lean_inc(v_env_2246_);
lean_dec(v___x_2244_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2272_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
uint64_t v_tid_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2270_; 
v_tid_2257_ = lean_ctor_get_uint64(v_traceState_2245_, sizeof(void*)*1);
v_isSharedCheck_2270_ = !lean_is_exclusive(v_traceState_2245_);
if (v_isSharedCheck_2270_ == 0)
{
lean_object* v_unused_2271_; 
v_unused_2271_ = lean_ctor_get(v_traceState_2245_, 0);
lean_dec(v_unused_2271_);
v___x_2259_ = v_traceState_2245_;
v_isShared_2260_ = v_isSharedCheck_2270_;
goto v_resetjp_2258_;
}
else
{
lean_dec(v_traceState_2245_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2270_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2261_; lean_object* v___x_2263_; 
v___x_2261_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg___closed__1);
if (v_isShared_2260_ == 0)
{
lean_ctor_set(v___x_2259_, 0, v___x_2261_);
v___x_2263_ = v___x_2259_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v___x_2261_);
lean_ctor_set_uint64(v_reuseFailAlloc_2269_, sizeof(void*)*1, v_tid_2257_);
v___x_2263_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
lean_object* v___x_2265_; 
if (v_isShared_2256_ == 0)
{
lean_ctor_set(v___x_2255_, 4, v___x_2263_);
v___x_2265_ = v___x_2255_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_env_2246_);
lean_ctor_set(v_reuseFailAlloc_2268_, 1, v_nextMacroScope_2247_);
lean_ctor_set(v_reuseFailAlloc_2268_, 2, v_ngen_2248_);
lean_ctor_set(v_reuseFailAlloc_2268_, 3, v_auxDeclNGen_2249_);
lean_ctor_set(v_reuseFailAlloc_2268_, 4, v___x_2263_);
lean_ctor_set(v_reuseFailAlloc_2268_, 5, v_cache_2250_);
lean_ctor_set(v_reuseFailAlloc_2268_, 6, v_messages_2251_);
lean_ctor_set(v_reuseFailAlloc_2268_, 7, v_infoState_2252_);
lean_ctor_set(v_reuseFailAlloc_2268_, 8, v_snapshotTasks_2253_);
v___x_2265_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2266_ = lean_st_ref_set(v___y_2239_, v___x_2265_);
v___x_2267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2267_, 0, v_traces_2243_);
return v___x_2267_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg___boxed(lean_object* v___y_2273_, lean_object* v___y_2274_){
_start:
{
lean_object* v_res_2275_; 
v_res_2275_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v___y_2273_);
lean_dec(v___y_2273_);
return v_res_2275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0(lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_){
_start:
{
lean_object* v___x_2281_; 
v___x_2281_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v___y_2279_);
return v___x_2281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___boxed(lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_){
_start:
{
lean_object* v_res_2287_; 
v_res_2287_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0(v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_);
lean_dec(v___y_2285_);
lean_dec_ref(v___y_2284_);
lean_dec(v___y_2283_);
lean_dec_ref(v___y_2282_);
return v_res_2287_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1(lean_object* v_opts_2288_, lean_object* v_opt_2289_){
_start:
{
lean_object* v_name_2290_; lean_object* v_defValue_2291_; lean_object* v_map_2292_; lean_object* v___x_2293_; 
v_name_2290_ = lean_ctor_get(v_opt_2289_, 0);
v_defValue_2291_ = lean_ctor_get(v_opt_2289_, 1);
v_map_2292_ = lean_ctor_get(v_opts_2288_, 0);
v___x_2293_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2292_, v_name_2290_);
if (lean_obj_tag(v___x_2293_) == 0)
{
uint8_t v___x_2294_; 
v___x_2294_ = lean_unbox(v_defValue_2291_);
return v___x_2294_;
}
else
{
lean_object* v_val_2295_; 
v_val_2295_ = lean_ctor_get(v___x_2293_, 0);
lean_inc(v_val_2295_);
lean_dec_ref_known(v___x_2293_, 1);
if (lean_obj_tag(v_val_2295_) == 1)
{
uint8_t v_v_2296_; 
v_v_2296_ = lean_ctor_get_uint8(v_val_2295_, 0);
lean_dec_ref_known(v_val_2295_, 0);
return v_v_2296_;
}
else
{
uint8_t v___x_2297_; 
lean_dec(v_val_2295_);
v___x_2297_ = lean_unbox(v_defValue_2291_);
return v___x_2297_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___boxed(lean_object* v_opts_2298_, lean_object* v_opt_2299_){
_start:
{
uint8_t v_res_2300_; lean_object* v_r_2301_; 
v_res_2300_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1(v_opts_2298_, v_opt_2299_);
lean_dec_ref(v_opt_2299_);
lean_dec_ref(v_opts_2298_);
v_r_2301_ = lean_box(v_res_2300_);
return v_r_2301_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___redArg(lean_object* v_e_2302_, lean_object* v___y_2303_){
_start:
{
uint8_t v___x_2305_; uint8_t v___x_2306_; 
v___x_2305_ = l_Lean_Expr_hasMVar(v_e_2302_);
v___x_2306_ = lean_bool_not(v___x_2305_);
if (v___x_2306_ == 0)
{
lean_object* v___x_2307_; lean_object* v_mctx_2308_; lean_object* v___x_2309_; lean_object* v_fst_2310_; lean_object* v_snd_2311_; lean_object* v___x_2312_; lean_object* v_cache_2313_; lean_object* v_zetaDeltaFVarIds_2314_; lean_object* v_postponed_2315_; lean_object* v_diag_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2325_; 
v___x_2307_ = lean_st_ref_get(v___y_2303_);
v_mctx_2308_ = lean_ctor_get(v___x_2307_, 0);
lean_inc_ref(v_mctx_2308_);
lean_dec(v___x_2307_);
v___x_2309_ = l_Lean_instantiateMVarsCore(v_mctx_2308_, v_e_2302_);
v_fst_2310_ = lean_ctor_get(v___x_2309_, 0);
lean_inc(v_fst_2310_);
v_snd_2311_ = lean_ctor_get(v___x_2309_, 1);
lean_inc(v_snd_2311_);
lean_dec_ref(v___x_2309_);
v___x_2312_ = lean_st_ref_take(v___y_2303_);
v_cache_2313_ = lean_ctor_get(v___x_2312_, 1);
v_zetaDeltaFVarIds_2314_ = lean_ctor_get(v___x_2312_, 2);
v_postponed_2315_ = lean_ctor_get(v___x_2312_, 3);
v_diag_2316_ = lean_ctor_get(v___x_2312_, 4);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2325_ == 0)
{
lean_object* v_unused_2326_; 
v_unused_2326_ = lean_ctor_get(v___x_2312_, 0);
lean_dec(v_unused_2326_);
v___x_2318_ = v___x_2312_;
v_isShared_2319_ = v_isSharedCheck_2325_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_diag_2316_);
lean_inc(v_postponed_2315_);
lean_inc(v_zetaDeltaFVarIds_2314_);
lean_inc(v_cache_2313_);
lean_dec(v___x_2312_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2325_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v___x_2321_; 
if (v_isShared_2319_ == 0)
{
lean_ctor_set(v___x_2318_, 0, v_snd_2311_);
v___x_2321_ = v___x_2318_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_snd_2311_);
lean_ctor_set(v_reuseFailAlloc_2324_, 1, v_cache_2313_);
lean_ctor_set(v_reuseFailAlloc_2324_, 2, v_zetaDeltaFVarIds_2314_);
lean_ctor_set(v_reuseFailAlloc_2324_, 3, v_postponed_2315_);
lean_ctor_set(v_reuseFailAlloc_2324_, 4, v_diag_2316_);
v___x_2321_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___x_2322_ = lean_st_ref_set(v___y_2303_, v___x_2321_);
v___x_2323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2323_, 0, v_fst_2310_);
return v___x_2323_;
}
}
}
else
{
lean_object* v___x_2327_; 
v___x_2327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2327_, 0, v_e_2302_);
return v___x_2327_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___redArg___boxed(lean_object* v_e_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_){
_start:
{
lean_object* v_res_2331_; 
v_res_2331_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___redArg(v_e_2328_, v___y_2329_);
lean_dec(v___y_2329_);
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(lean_object* v_e_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
lean_object* v___x_2338_; 
v___x_2338_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___redArg(v_e_2332_, v___y_2334_);
return v___x_2338_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___boxed(lean_object* v_e_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_){
_start:
{
lean_object* v_res_2345_; 
v_res_2345_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_e_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
lean_dec(v___y_2341_);
lean_dec_ref(v___y_2340_);
return v_res_2345_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2347_; lean_object* v___x_2348_; 
v___x_2347_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__0));
v___x_2348_ = l_Lean_stringToMessageData(v___x_2347_);
return v___x_2348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0(lean_object* v_name_2349_, lean_object* v_x_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_){
_start:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2356_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1);
v___x_2357_ = l_Lean_MessageData_ofName(v_name_2349_);
v___x_2358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2356_);
lean_ctor_set(v___x_2358_, 1, v___x_2357_);
v___x_2359_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_2360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2360_, 0, v___x_2358_);
lean_ctor_set(v___x_2360_, 1, v___x_2359_);
v___x_2361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2360_);
return v___x_2361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed(lean_object* v_name_2362_, lean_object* v_x_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_){
_start:
{
lean_object* v_res_2369_; 
v_res_2369_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0(v_name_2362_, v_x_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_);
lean_dec(v___y_2367_);
lean_dec_ref(v___y_2366_);
lean_dec(v___y_2365_);
lean_dec_ref(v___y_2364_);
lean_dec_ref(v_x_2363_);
return v_res_2369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(lean_object* v_name_2370_, lean_object* v_val_2371_, lean_object* v_name_2372_, lean_object* v_levelParams_2373_, uint8_t v___x_2374_, lean_object* v_____r_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_){
_start:
{
lean_object* v___x_2381_; 
lean_inc_ref(v_val_2371_);
v___x_2381_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2370_, v_val_2371_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_);
if (lean_obj_tag(v___x_2381_) == 0)
{
lean_object* v_a_2382_; lean_object* v___x_2383_; lean_object* v_a_2384_; lean_object* v___x_2385_; lean_object* v_a_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2398_; 
v_a_2382_ = lean_ctor_get(v___x_2381_, 0);
lean_inc(v_a_2382_);
lean_dec_ref_known(v___x_2381_, 1);
v___x_2383_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___redArg(v_val_2371_, v___y_2377_);
v_a_2384_ = lean_ctor_get(v___x_2383_, 0);
lean_inc(v_a_2384_);
lean_dec_ref(v___x_2383_);
v___x_2385_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___redArg(v_a_2382_, v___y_2377_);
v_a_2386_ = lean_ctor_get(v___x_2385_, 0);
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2388_ = v___x_2385_;
v_isShared_2389_ = v_isSharedCheck_2398_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_a_2386_);
lean_dec(v___x_2385_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2398_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2395_; 
lean_inc(v_name_2372_);
v___x_2390_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2390_, 0, v_name_2372_);
lean_ctor_set(v___x_2390_, 1, v_levelParams_2373_);
lean_ctor_set(v___x_2390_, 2, v_a_2384_);
v___x_2391_ = lean_box(0);
v___x_2392_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2392_, 0, v_name_2372_);
lean_ctor_set(v___x_2392_, 1, v___x_2391_);
v___x_2393_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2390_);
lean_ctor_set(v___x_2393_, 1, v_a_2386_);
lean_ctor_set(v___x_2393_, 2, v___x_2392_);
if (v_isShared_2389_ == 0)
{
lean_ctor_set_tag(v___x_2388_, 2);
lean_ctor_set(v___x_2388_, 0, v___x_2393_);
v___x_2395_ = v___x_2388_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v___x_2393_);
v___x_2395_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
lean_object* v___x_2396_; 
v___x_2396_ = l_Lean_addDecl(v___x_2395_, v___x_2374_, v___y_2378_, v___y_2379_);
return v___x_2396_;
}
}
}
else
{
lean_object* v_a_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2406_; 
lean_dec(v_levelParams_2373_);
lean_dec(v_name_2372_);
lean_dec_ref(v_val_2371_);
v_a_2399_ = lean_ctor_get(v___x_2381_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2381_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2401_ = v___x_2381_;
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_a_2399_);
lean_dec(v___x_2381_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
lean_object* v___x_2404_; 
if (v_isShared_2402_ == 0)
{
v___x_2404_ = v___x_2401_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_a_2399_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
return v___x_2404_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1___boxed(lean_object* v_name_2407_, lean_object* v_val_2408_, lean_object* v_name_2409_, lean_object* v_levelParams_2410_, lean_object* v___x_2411_, lean_object* v_____r_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_){
_start:
{
uint8_t v___x_12685__boxed_2418_; lean_object* v_res_2419_; 
v___x_12685__boxed_2418_ = lean_unbox(v___x_2411_);
v_res_2419_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(v_name_2407_, v_val_2408_, v_name_2409_, v_levelParams_2410_, v___x_12685__boxed_2418_, v_____r_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_);
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
return v_res_2419_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2_spec__4(lean_object* v_e_2420_){
_start:
{
if (lean_obj_tag(v_e_2420_) == 0)
{
uint8_t v___x_2421_; 
v___x_2421_ = 2;
return v___x_2421_;
}
else
{
uint8_t v___x_2422_; 
v___x_2422_ = 0;
return v___x_2422_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2_spec__4___boxed(lean_object* v_e_2423_){
_start:
{
uint8_t v_res_2424_; lean_object* v_r_2425_; 
v_res_2424_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2_spec__4(v_e_2423_);
lean_dec_ref(v_e_2423_);
v_r_2425_ = lean_box(v_res_2424_);
return v_r_2425_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2_spec__3___redArg(lean_object* v_x_2426_){
_start:
{
if (lean_obj_tag(v_x_2426_) == 0)
{
lean_object* v_a_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2435_; 
v_a_2428_ = lean_ctor_get(v_x_2426_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v_x_2426_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2430_ = v_x_2426_;
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_a_2428_);
lean_dec(v_x_2426_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
lean_object* v___x_2433_; 
if (v_isShared_2431_ == 0)
{
lean_ctor_set_tag(v___x_2430_, 1);
v___x_2433_ = v___x_2430_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_a_2428_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
}
}
}
else
{
lean_object* v_a_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2443_; 
v_a_2436_ = lean_ctor_get(v_x_2426_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v_x_2426_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2438_ = v_x_2426_;
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_dec(v_x_2426_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2441_; 
if (v_isShared_2439_ == 0)
{
lean_ctor_set_tag(v___x_2438_, 0);
v___x_2441_ = v___x_2438_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(0, 1, 0);
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
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2_spec__3___redArg___boxed(lean_object* v_x_2444_, lean_object* v___y_2445_){
_start:
{
lean_object* v_res_2446_; 
v_res_2446_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2_spec__3___redArg(v_x_2444_);
return v_res_2446_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2_spec__2_spec__4(size_t v_sz_2447_, size_t v_i_2448_, lean_object* v_bs_2449_){
_start:
{
uint8_t v___x_2450_; 
v___x_2450_ = lean_usize_dec_lt(v_i_2448_, v_sz_2447_);
if (v___x_2450_ == 0)
{
return v_bs_2449_;
}
else
{
lean_object* v_v_2451_; lean_object* v_msg_2452_; lean_object* v___x_2453_; lean_object* v_bs_x27_2454_; size_t v___x_2455_; size_t v___x_2456_; lean_object* v___x_2457_; 
v_v_2451_ = lean_array_uget_borrowed(v_bs_2449_, v_i_2448_);
v_msg_2452_ = lean_ctor_get(v_v_2451_, 1);
lean_inc_ref(v_msg_2452_);
v___x_2453_ = lean_unsigned_to_nat(0u);
v_bs_x27_2454_ = lean_array_uset(v_bs_2449_, v_i_2448_, v___x_2453_);
v___x_2455_ = ((size_t)1ULL);
v___x_2456_ = lean_usize_add(v_i_2448_, v___x_2455_);
v___x_2457_ = lean_array_uset(v_bs_x27_2454_, v_i_2448_, v_msg_2452_);
v_i_2448_ = v___x_2456_;
v_bs_2449_ = v___x_2457_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2_spec__2_spec__4___boxed(lean_object* v_sz_2459_, lean_object* v_i_2460_, lean_object* v_bs_2461_){
_start:
{
size_t v_sz_boxed_2462_; size_t v_i_boxed_2463_; lean_object* v_res_2464_; 
v_sz_boxed_2462_ = lean_unbox_usize(v_sz_2459_);
lean_dec(v_sz_2459_);
v_i_boxed_2463_ = lean_unbox_usize(v_i_2460_);
lean_dec(v_i_2460_);
v_res_2464_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2_spec__2_spec__4(v_sz_boxed_2462_, v_i_boxed_2463_, v_bs_2461_);
return v_res_2464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2_spec__2(lean_object* v_oldTraces_2465_, lean_object* v_data_2466_, lean_object* v_ref_2467_, lean_object* v_msg_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_){
_start:
{
lean_object* v_fileName_2474_; lean_object* v_fileMap_2475_; lean_object* v_options_2476_; lean_object* v_currRecDepth_2477_; lean_object* v_maxRecDepth_2478_; lean_object* v_ref_2479_; lean_object* v_currNamespace_2480_; lean_object* v_openDecls_2481_; lean_object* v_initHeartbeats_2482_; lean_object* v_maxHeartbeats_2483_; lean_object* v_quotContext_2484_; lean_object* v_currMacroScope_2485_; uint8_t v_diag_2486_; lean_object* v_cancelTk_x3f_2487_; uint8_t v_suppressElabErrors_2488_; lean_object* v_inheritedTraceOptions_2489_; lean_object* v___x_2490_; lean_object* v_traceState_2491_; lean_object* v_traces_2492_; lean_object* v_ref_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; size_t v_sz_2496_; size_t v___x_2497_; lean_object* v___x_2498_; lean_object* v_msg_2499_; lean_object* v___x_2500_; lean_object* v_a_2501_; lean_object* v___x_2503_; uint8_t v_isShared_2504_; uint8_t v_isSharedCheck_2538_; 
v_fileName_2474_ = lean_ctor_get(v___y_2471_, 0);
v_fileMap_2475_ = lean_ctor_get(v___y_2471_, 1);
v_options_2476_ = lean_ctor_get(v___y_2471_, 2);
v_currRecDepth_2477_ = lean_ctor_get(v___y_2471_, 3);
v_maxRecDepth_2478_ = lean_ctor_get(v___y_2471_, 4);
v_ref_2479_ = lean_ctor_get(v___y_2471_, 5);
v_currNamespace_2480_ = lean_ctor_get(v___y_2471_, 6);
v_openDecls_2481_ = lean_ctor_get(v___y_2471_, 7);
v_initHeartbeats_2482_ = lean_ctor_get(v___y_2471_, 8);
v_maxHeartbeats_2483_ = lean_ctor_get(v___y_2471_, 9);
v_quotContext_2484_ = lean_ctor_get(v___y_2471_, 10);
v_currMacroScope_2485_ = lean_ctor_get(v___y_2471_, 11);
v_diag_2486_ = lean_ctor_get_uint8(v___y_2471_, sizeof(void*)*14);
v_cancelTk_x3f_2487_ = lean_ctor_get(v___y_2471_, 12);
v_suppressElabErrors_2488_ = lean_ctor_get_uint8(v___y_2471_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2489_ = lean_ctor_get(v___y_2471_, 13);
v___x_2490_ = lean_st_ref_get(v___y_2472_);
v_traceState_2491_ = lean_ctor_get(v___x_2490_, 4);
lean_inc_ref(v_traceState_2491_);
lean_dec(v___x_2490_);
v_traces_2492_ = lean_ctor_get(v_traceState_2491_, 0);
lean_inc_ref(v_traces_2492_);
lean_dec_ref(v_traceState_2491_);
v_ref_2493_ = l_Lean_replaceRef(v_ref_2467_, v_ref_2479_);
lean_inc_ref(v_inheritedTraceOptions_2489_);
lean_inc(v_cancelTk_x3f_2487_);
lean_inc(v_currMacroScope_2485_);
lean_inc(v_quotContext_2484_);
lean_inc(v_maxHeartbeats_2483_);
lean_inc(v_initHeartbeats_2482_);
lean_inc(v_openDecls_2481_);
lean_inc(v_currNamespace_2480_);
lean_inc(v_maxRecDepth_2478_);
lean_inc(v_currRecDepth_2477_);
lean_inc_ref(v_options_2476_);
lean_inc_ref(v_fileMap_2475_);
lean_inc_ref(v_fileName_2474_);
v___x_2494_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2494_, 0, v_fileName_2474_);
lean_ctor_set(v___x_2494_, 1, v_fileMap_2475_);
lean_ctor_set(v___x_2494_, 2, v_options_2476_);
lean_ctor_set(v___x_2494_, 3, v_currRecDepth_2477_);
lean_ctor_set(v___x_2494_, 4, v_maxRecDepth_2478_);
lean_ctor_set(v___x_2494_, 5, v_ref_2493_);
lean_ctor_set(v___x_2494_, 6, v_currNamespace_2480_);
lean_ctor_set(v___x_2494_, 7, v_openDecls_2481_);
lean_ctor_set(v___x_2494_, 8, v_initHeartbeats_2482_);
lean_ctor_set(v___x_2494_, 9, v_maxHeartbeats_2483_);
lean_ctor_set(v___x_2494_, 10, v_quotContext_2484_);
lean_ctor_set(v___x_2494_, 11, v_currMacroScope_2485_);
lean_ctor_set(v___x_2494_, 12, v_cancelTk_x3f_2487_);
lean_ctor_set(v___x_2494_, 13, v_inheritedTraceOptions_2489_);
lean_ctor_set_uint8(v___x_2494_, sizeof(void*)*14, v_diag_2486_);
lean_ctor_set_uint8(v___x_2494_, sizeof(void*)*14 + 1, v_suppressElabErrors_2488_);
v___x_2495_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2492_);
lean_dec_ref(v_traces_2492_);
v_sz_2496_ = lean_array_size(v___x_2495_);
v___x_2497_ = ((size_t)0ULL);
v___x_2498_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2_spec__2_spec__4(v_sz_2496_, v___x_2497_, v___x_2495_);
v_msg_2499_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2499_, 0, v_data_2466_);
lean_ctor_set(v_msg_2499_, 1, v_msg_2468_);
lean_ctor_set(v_msg_2499_, 2, v___x_2498_);
v___x_2500_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msg_2499_, v___y_2469_, v___y_2470_, v___x_2494_, v___y_2472_);
lean_dec_ref_known(v___x_2494_, 14);
v_a_2501_ = lean_ctor_get(v___x_2500_, 0);
v_isSharedCheck_2538_ = !lean_is_exclusive(v___x_2500_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2503_ = v___x_2500_;
v_isShared_2504_ = v_isSharedCheck_2538_;
goto v_resetjp_2502_;
}
else
{
lean_inc(v_a_2501_);
lean_dec(v___x_2500_);
v___x_2503_ = lean_box(0);
v_isShared_2504_ = v_isSharedCheck_2538_;
goto v_resetjp_2502_;
}
v_resetjp_2502_:
{
lean_object* v___x_2505_; lean_object* v_traceState_2506_; lean_object* v_env_2507_; lean_object* v_nextMacroScope_2508_; lean_object* v_ngen_2509_; lean_object* v_auxDeclNGen_2510_; lean_object* v_cache_2511_; lean_object* v_messages_2512_; lean_object* v_infoState_2513_; lean_object* v_snapshotTasks_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2537_; 
v___x_2505_ = lean_st_ref_take(v___y_2472_);
v_traceState_2506_ = lean_ctor_get(v___x_2505_, 4);
v_env_2507_ = lean_ctor_get(v___x_2505_, 0);
v_nextMacroScope_2508_ = lean_ctor_get(v___x_2505_, 1);
v_ngen_2509_ = lean_ctor_get(v___x_2505_, 2);
v_auxDeclNGen_2510_ = lean_ctor_get(v___x_2505_, 3);
v_cache_2511_ = lean_ctor_get(v___x_2505_, 5);
v_messages_2512_ = lean_ctor_get(v___x_2505_, 6);
v_infoState_2513_ = lean_ctor_get(v___x_2505_, 7);
v_snapshotTasks_2514_ = lean_ctor_get(v___x_2505_, 8);
v_isSharedCheck_2537_ = !lean_is_exclusive(v___x_2505_);
if (v_isSharedCheck_2537_ == 0)
{
v___x_2516_ = v___x_2505_;
v_isShared_2517_ = v_isSharedCheck_2537_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_snapshotTasks_2514_);
lean_inc(v_infoState_2513_);
lean_inc(v_messages_2512_);
lean_inc(v_cache_2511_);
lean_inc(v_traceState_2506_);
lean_inc(v_auxDeclNGen_2510_);
lean_inc(v_ngen_2509_);
lean_inc(v_nextMacroScope_2508_);
lean_inc(v_env_2507_);
lean_dec(v___x_2505_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2537_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
uint64_t v_tid_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2535_; 
v_tid_2518_ = lean_ctor_get_uint64(v_traceState_2506_, sizeof(void*)*1);
v_isSharedCheck_2535_ = !lean_is_exclusive(v_traceState_2506_);
if (v_isSharedCheck_2535_ == 0)
{
lean_object* v_unused_2536_; 
v_unused_2536_ = lean_ctor_get(v_traceState_2506_, 0);
lean_dec(v_unused_2536_);
v___x_2520_ = v_traceState_2506_;
v_isShared_2521_ = v_isSharedCheck_2535_;
goto v_resetjp_2519_;
}
else
{
lean_dec(v_traceState_2506_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2535_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2525_; 
v___x_2522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2522_, 0, v_ref_2467_);
lean_ctor_set(v___x_2522_, 1, v_a_2501_);
v___x_2523_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2465_, v___x_2522_);
if (v_isShared_2521_ == 0)
{
lean_ctor_set(v___x_2520_, 0, v___x_2523_);
v___x_2525_ = v___x_2520_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v___x_2523_);
lean_ctor_set_uint64(v_reuseFailAlloc_2534_, sizeof(void*)*1, v_tid_2518_);
v___x_2525_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
lean_object* v___x_2527_; 
if (v_isShared_2517_ == 0)
{
lean_ctor_set(v___x_2516_, 4, v___x_2525_);
v___x_2527_ = v___x_2516_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_env_2507_);
lean_ctor_set(v_reuseFailAlloc_2533_, 1, v_nextMacroScope_2508_);
lean_ctor_set(v_reuseFailAlloc_2533_, 2, v_ngen_2509_);
lean_ctor_set(v_reuseFailAlloc_2533_, 3, v_auxDeclNGen_2510_);
lean_ctor_set(v_reuseFailAlloc_2533_, 4, v___x_2525_);
lean_ctor_set(v_reuseFailAlloc_2533_, 5, v_cache_2511_);
lean_ctor_set(v_reuseFailAlloc_2533_, 6, v_messages_2512_);
lean_ctor_set(v_reuseFailAlloc_2533_, 7, v_infoState_2513_);
lean_ctor_set(v_reuseFailAlloc_2533_, 8, v_snapshotTasks_2514_);
v___x_2527_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2531_; 
v___x_2528_ = lean_st_ref_set(v___y_2472_, v___x_2527_);
v___x_2529_ = lean_box(0);
if (v_isShared_2504_ == 0)
{
lean_ctor_set(v___x_2503_, 0, v___x_2529_);
v___x_2531_ = v___x_2503_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v___x_2529_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
return v___x_2531_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2_spec__2___boxed(lean_object* v_oldTraces_2539_, lean_object* v_data_2540_, lean_object* v_ref_2541_, lean_object* v_msg_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_){
_start:
{
lean_object* v_res_2548_; 
v_res_2548_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2_spec__2(v_oldTraces_2539_, v_data_2540_, v_ref_2541_, v_msg_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
return v_res_2548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2_spec__5(lean_object* v_opts_2549_, lean_object* v_opt_2550_){
_start:
{
lean_object* v_name_2551_; lean_object* v_defValue_2552_; lean_object* v_map_2553_; lean_object* v___x_2554_; 
v_name_2551_ = lean_ctor_get(v_opt_2550_, 0);
v_defValue_2552_ = lean_ctor_get(v_opt_2550_, 1);
v_map_2553_ = lean_ctor_get(v_opts_2549_, 0);
v___x_2554_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2553_, v_name_2551_);
if (lean_obj_tag(v___x_2554_) == 0)
{
lean_inc(v_defValue_2552_);
return v_defValue_2552_;
}
else
{
lean_object* v_val_2555_; 
v_val_2555_ = lean_ctor_get(v___x_2554_, 0);
lean_inc(v_val_2555_);
lean_dec_ref_known(v___x_2554_, 1);
if (lean_obj_tag(v_val_2555_) == 3)
{
lean_object* v_v_2556_; 
v_v_2556_ = lean_ctor_get(v_val_2555_, 0);
lean_inc(v_v_2556_);
lean_dec_ref_known(v_val_2555_, 1);
return v_v_2556_;
}
else
{
lean_dec(v_val_2555_);
lean_inc(v_defValue_2552_);
return v_defValue_2552_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2_spec__5___boxed(lean_object* v_opts_2557_, lean_object* v_opt_2558_){
_start:
{
lean_object* v_res_2559_; 
v_res_2559_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2_spec__5(v_opts_2557_, v_opt_2558_);
lean_dec_ref(v_opt_2558_);
lean_dec_ref(v_opts_2557_);
return v_res_2559_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2561_; lean_object* v___x_2562_; 
v___x_2561_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2___closed__0));
v___x_2562_ = l_Lean_stringToMessageData(v___x_2561_);
return v___x_2562_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2___closed__2(void){
_start:
{
lean_object* v___x_2563_; double v___x_2564_; 
v___x_2563_ = lean_unsigned_to_nat(1000u);
v___x_2564_ = lean_float_of_nat(v___x_2563_);
return v___x_2564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(lean_object* v_cls_2565_, uint8_t v_collapsed_2566_, lean_object* v_tag_2567_, lean_object* v_opts_2568_, uint8_t v_clsEnabled_2569_, lean_object* v_oldTraces_2570_, lean_object* v_msg_2571_, lean_object* v_resStartStop_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_){
_start:
{
lean_object* v_fst_2578_; lean_object* v_snd_2579_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v_data_2583_; lean_object* v_fst_2586_; lean_object* v_snd_2587_; lean_object* v___x_2588_; uint8_t v___x_2589_; lean_object* v___y_2591_; lean_object* v_a_2592_; uint8_t v___y_2607_; double v___y_2638_; 
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
v___x_2589_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1(v_opts_2568_, v___x_2588_);
if (v___x_2589_ == 0)
{
v___y_2607_ = v___x_2589_;
goto v___jp_2606_;
}
else
{
lean_object* v___x_2643_; uint8_t v___x_2644_; 
v___x_2643_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2644_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1(v_opts_2568_, v___x_2643_);
if (v___x_2644_ == 0)
{
lean_object* v___x_2645_; lean_object* v___x_2646_; double v___x_2647_; double v___x_2648_; double v___x_2649_; 
v___x_2645_ = l_Lean_trace_profiler_threshold;
v___x_2646_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2_spec__5(v_opts_2568_, v___x_2645_);
v___x_2647_ = lean_float_of_nat(v___x_2646_);
v___x_2648_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2___closed__2);
v___x_2649_ = lean_float_div(v___x_2647_, v___x_2648_);
v___y_2638_ = v___x_2649_;
goto v___jp_2637_;
}
else
{
lean_object* v___x_2650_; lean_object* v___x_2651_; double v___x_2652_; 
v___x_2650_ = l_Lean_trace_profiler_threshold;
v___x_2651_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2_spec__5(v_opts_2568_, v___x_2650_);
v___x_2652_ = lean_float_of_nat(v___x_2651_);
v___y_2638_ = v___x_2652_;
goto v___jp_2637_;
}
}
v___jp_2580_:
{
lean_object* v___x_2584_; 
lean_inc(v___y_2581_);
v___x_2584_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2_spec__2(v_oldTraces_2570_, v_data_2583_, v___y_2581_, v___y_2582_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_);
if (lean_obj_tag(v___x_2584_) == 0)
{
lean_object* v___x_2585_; 
lean_dec_ref_known(v___x_2584_, 1);
v___x_2585_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2_spec__3___redArg(v_fst_2578_);
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
v_result_2593_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2_spec__4(v_fst_2578_);
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
v___y_2581_ = v___y_2591_;
v___y_2582_ = v_a_2592_;
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
v___y_2581_ = v___y_2591_;
v___y_2582_ = v_a_2592_;
v_data_2583_ = v_data_2598_;
goto v___jp_2580_;
}
}
v___jp_2601_:
{
lean_object* v_ref_2602_; lean_object* v___x_2603_; 
v_ref_2602_ = lean_ctor_get(v___y_2575_, 5);
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
v___x_2605_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2___closed__1);
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
lean_object* v___x_2608_; lean_object* v_traceState_2609_; lean_object* v_env_2610_; lean_object* v_nextMacroScope_2611_; lean_object* v_ngen_2612_; lean_object* v_auxDeclNGen_2613_; lean_object* v_cache_2614_; lean_object* v_messages_2615_; lean_object* v_infoState_2616_; lean_object* v_snapshotTasks_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2636_; 
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
v_messages_2615_ = lean_ctor_get(v___x_2608_, 6);
v_infoState_2616_ = lean_ctor_get(v___x_2608_, 7);
v_snapshotTasks_2617_ = lean_ctor_get(v___x_2608_, 8);
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2619_ = v___x_2608_;
v_isShared_2620_ = v_isSharedCheck_2636_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_snapshotTasks_2617_);
lean_inc(v_infoState_2616_);
lean_inc(v_messages_2615_);
lean_inc(v_cache_2614_);
lean_inc(v_traceState_2609_);
lean_inc(v_auxDeclNGen_2613_);
lean_inc(v_ngen_2612_);
lean_inc(v_nextMacroScope_2611_);
lean_inc(v_env_2610_);
lean_dec(v___x_2608_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2636_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
uint64_t v_tid_2621_; lean_object* v_traces_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2635_; 
v_tid_2621_ = lean_ctor_get_uint64(v_traceState_2609_, sizeof(void*)*1);
v_traces_2622_ = lean_ctor_get(v_traceState_2609_, 0);
v_isSharedCheck_2635_ = !lean_is_exclusive(v_traceState_2609_);
if (v_isSharedCheck_2635_ == 0)
{
v___x_2624_ = v_traceState_2609_;
v_isShared_2625_ = v_isSharedCheck_2635_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_traces_2622_);
lean_dec(v_traceState_2609_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2635_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v___x_2626_; lean_object* v___x_2628_; 
v___x_2626_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2570_, v_traces_2622_);
lean_dec_ref(v_traces_2622_);
if (v_isShared_2625_ == 0)
{
lean_ctor_set(v___x_2624_, 0, v___x_2626_);
v___x_2628_ = v___x_2624_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v___x_2626_);
lean_ctor_set_uint64(v_reuseFailAlloc_2634_, sizeof(void*)*1, v_tid_2621_);
v___x_2628_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
lean_object* v___x_2630_; 
if (v_isShared_2620_ == 0)
{
lean_ctor_set(v___x_2619_, 4, v___x_2628_);
v___x_2630_ = v___x_2619_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_env_2610_);
lean_ctor_set(v_reuseFailAlloc_2633_, 1, v_nextMacroScope_2611_);
lean_ctor_set(v_reuseFailAlloc_2633_, 2, v_ngen_2612_);
lean_ctor_set(v_reuseFailAlloc_2633_, 3, v_auxDeclNGen_2613_);
lean_ctor_set(v_reuseFailAlloc_2633_, 4, v___x_2628_);
lean_ctor_set(v_reuseFailAlloc_2633_, 5, v_cache_2614_);
lean_ctor_set(v_reuseFailAlloc_2633_, 6, v_messages_2615_);
lean_ctor_set(v_reuseFailAlloc_2633_, 7, v_infoState_2616_);
lean_ctor_set(v_reuseFailAlloc_2633_, 8, v_snapshotTasks_2617_);
v___x_2630_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; 
v___x_2631_ = lean_st_ref_set(v___y_2576_, v___x_2630_);
v___x_2632_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2_spec__3___redArg(v_fst_2578_);
return v___x_2632_;
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
v___jp_2637_:
{
double v___x_2639_; double v___x_2640_; double v___x_2641_; uint8_t v___x_2642_; 
v___x_2639_ = lean_unbox_float(v_snd_2587_);
v___x_2640_ = lean_unbox_float(v_fst_2586_);
v___x_2641_ = lean_float_sub(v___x_2639_, v___x_2640_);
v___x_2642_ = lean_float_decLt(v___y_2638_, v___x_2641_);
v___y_2607_ = v___x_2642_;
goto v___jp_2606_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2___boxed(lean_object* v_cls_2653_, lean_object* v_collapsed_2654_, lean_object* v_tag_2655_, lean_object* v_opts_2656_, lean_object* v_clsEnabled_2657_, lean_object* v_oldTraces_2658_, lean_object* v_msg_2659_, lean_object* v_resStartStop_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_){
_start:
{
uint8_t v_collapsed_boxed_2666_; uint8_t v_clsEnabled_boxed_2667_; lean_object* v_res_2668_; 
v_collapsed_boxed_2666_ = lean_unbox(v_collapsed_2654_);
v_clsEnabled_boxed_2667_ = lean_unbox(v_clsEnabled_2657_);
v_res_2668_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_cls_2653_, v_collapsed_boxed_2666_, v_tag_2655_, v_opts_2656_, v_clsEnabled_boxed_2667_, v_oldTraces_2658_, v_msg_2659_, v_resStartStop_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_);
lean_dec(v___y_2664_);
lean_dec_ref(v___y_2663_);
lean_dec(v___y_2662_);
lean_dec_ref(v___y_2661_);
lean_dec_ref(v_opts_2656_);
return v_res_2668_;
}
}
static double _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0(void){
_start:
{
lean_object* v___x_2669_; double v___x_2670_; 
v___x_2669_ = lean_unsigned_to_nat(1000000000u);
v___x_2670_ = lean_float_of_nat(v___x_2669_);
return v___x_2670_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2(void){
_start:
{
lean_object* v___x_2672_; lean_object* v___x_2673_; 
v___x_2672_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1));
v___x_2673_ = l_Lean_stringToMessageData(v___x_2672_);
return v___x_2673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(lean_object* v_ctorVal_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_){
_start:
{
lean_object* v_toConstantVal_2680_; lean_object* v_options_2681_; lean_object* v_name_2682_; lean_object* v_levelParams_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2938_; 
v_toConstantVal_2680_ = lean_ctor_get(v_ctorVal_2674_, 0);
lean_inc_ref(v_toConstantVal_2680_);
v_options_2681_ = lean_ctor_get(v_a_2677_, 2);
v_name_2682_ = lean_ctor_get(v_toConstantVal_2680_, 0);
v_levelParams_2683_ = lean_ctor_get(v_toConstantVal_2680_, 1);
v_isSharedCheck_2938_ = !lean_is_exclusive(v_toConstantVal_2680_);
if (v_isSharedCheck_2938_ == 0)
{
lean_object* v_unused_2939_; 
v_unused_2939_ = lean_ctor_get(v_toConstantVal_2680_, 2);
lean_dec(v_unused_2939_);
v___x_2685_ = v_toConstantVal_2680_;
v_isShared_2686_ = v_isSharedCheck_2938_;
goto v_resetjp_2684_;
}
else
{
lean_inc(v_levelParams_2683_);
lean_inc(v_name_2682_);
lean_dec(v_toConstantVal_2680_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2938_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
lean_object* v_inheritedTraceOptions_2687_; uint8_t v_hasTrace_2688_; lean_object* v_name_2689_; uint8_t v___y_2691_; lean_object* v___y_2692_; lean_object* v___y_2693_; lean_object* v___y_2694_; lean_object* v___y_2695_; lean_object* v___y_2696_; lean_object* v_cls_2725_; uint8_t v___x_2726_; 
v_inheritedTraceOptions_2687_ = lean_ctor_get(v_a_2677_, 13);
v_hasTrace_2688_ = lean_ctor_get_uint8(v_options_2681_, sizeof(void*)*1);
lean_inc(v_name_2682_);
v_name_2689_ = l_Lean_Meta_mkInjectiveTheoremNameFor(v_name_2682_);
v_cls_2725_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_2726_ = lean_bool_not(v_hasTrace_2688_);
if (v___x_2726_ == 0)
{
lean_object* v___f_2727_; uint8_t v___x_2728_; lean_object* v___x_2729_; lean_object* v___y_2731_; lean_object* v___y_2732_; uint8_t v___y_2733_; lean_object* v_a_2734_; lean_object* v___y_2744_; lean_object* v___y_2745_; uint8_t v___y_2746_; lean_object* v_a_2747_; lean_object* v___y_2750_; lean_object* v___y_2751_; uint8_t v___y_2752_; lean_object* v_a_2753_; lean_object* v___y_2756_; lean_object* v___y_2757_; uint8_t v___y_2758_; lean_object* v___y_2759_; lean_object* v___y_2763_; lean_object* v___y_2764_; lean_object* v___y_2765_; uint8_t v___y_2766_; lean_object* v___y_2770_; lean_object* v___y_2771_; uint8_t v___y_2772_; lean_object* v_a_2773_; lean_object* v___y_2786_; lean_object* v___y_2787_; uint8_t v___y_2788_; lean_object* v_a_2789_; lean_object* v___y_2792_; lean_object* v___y_2793_; uint8_t v___y_2794_; lean_object* v_a_2795_; lean_object* v___y_2798_; lean_object* v___y_2799_; uint8_t v___y_2800_; lean_object* v___y_2801_; lean_object* v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2807_; uint8_t v___y_2808_; uint8_t v___y_2812_; uint8_t v_a_2850_; 
lean_inc(v_name_2689_);
v___f_2727_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2727_, 0, v_name_2689_);
v___x_2728_ = 1;
v___x_2729_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
if (v_hasTrace_2688_ == 0)
{
v_a_2850_ = v_hasTrace_2688_;
goto v___jp_2849_;
}
else
{
lean_object* v___x_2879_; uint8_t v___x_2880_; 
v___x_2879_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_2880_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2687_, v_options_2681_, v___x_2879_);
if (v___x_2880_ == 0)
{
v_a_2850_ = v___x_2880_;
goto v___jp_2849_;
}
else
{
lean_del_object(v___x_2685_);
v___y_2812_ = v___x_2880_;
goto v___jp_2811_;
}
}
v___jp_2730_:
{
lean_object* v___x_2735_; double v___x_2736_; double v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; 
v___x_2735_ = lean_io_get_num_heartbeats();
v___x_2736_ = lean_float_of_nat(v___y_2732_);
v___x_2737_ = lean_float_of_nat(v___x_2735_);
v___x_2738_ = lean_box_float(v___x_2736_);
v___x_2739_ = lean_box_float(v___x_2737_);
v___x_2740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2738_);
lean_ctor_set(v___x_2740_, 1, v___x_2739_);
v___x_2741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2741_, 0, v_a_2734_);
lean_ctor_set(v___x_2741_, 1, v___x_2740_);
v___x_2742_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_cls_2725_, v___x_2728_, v___x_2729_, v_options_2681_, v___y_2733_, v___y_2731_, v___f_2727_, v___x_2741_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_);
return v___x_2742_;
}
v___jp_2743_:
{
lean_object* v___x_2748_; 
v___x_2748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2748_, 0, v_a_2747_);
v___y_2731_ = v___y_2744_;
v___y_2732_ = v___y_2745_;
v___y_2733_ = v___y_2746_;
v_a_2734_ = v___x_2748_;
goto v___jp_2730_;
}
v___jp_2749_:
{
lean_object* v___x_2754_; 
v___x_2754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2754_, 0, v_a_2753_);
v___y_2731_ = v___y_2750_;
v___y_2732_ = v___y_2751_;
v___y_2733_ = v___y_2752_;
v_a_2734_ = v___x_2754_;
goto v___jp_2730_;
}
v___jp_2755_:
{
if (lean_obj_tag(v___y_2759_) == 0)
{
lean_object* v_a_2760_; 
v_a_2760_ = lean_ctor_get(v___y_2759_, 0);
lean_inc(v_a_2760_);
lean_dec_ref_known(v___y_2759_, 1);
v___y_2750_ = v___y_2756_;
v___y_2751_ = v___y_2757_;
v___y_2752_ = v___y_2758_;
v_a_2753_ = v_a_2760_;
goto v___jp_2749_;
}
else
{
lean_object* v_a_2761_; 
v_a_2761_ = lean_ctor_get(v___y_2759_, 0);
lean_inc(v_a_2761_);
lean_dec_ref_known(v___y_2759_, 1);
v___y_2744_ = v___y_2756_;
v___y_2745_ = v___y_2757_;
v___y_2746_ = v___y_2758_;
v_a_2747_ = v_a_2761_;
goto v___jp_2743_;
}
}
v___jp_2762_:
{
lean_object* v___x_2767_; lean_object* v___x_2768_; 
v___x_2767_ = lean_box(0);
lean_inc(v_a_2678_);
lean_inc_ref(v_a_2677_);
lean_inc(v_a_2676_);
lean_inc_ref(v_a_2675_);
v___x_2768_ = lean_apply_6(v___y_2764_, v___x_2767_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_, lean_box(0));
v___y_2756_ = v___y_2763_;
v___y_2757_ = v___y_2765_;
v___y_2758_ = v___y_2766_;
v___y_2759_ = v___x_2768_;
goto v___jp_2755_;
}
v___jp_2769_:
{
lean_object* v___x_2774_; double v___x_2775_; double v___x_2776_; double v___x_2777_; double v___x_2778_; double v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; 
v___x_2774_ = lean_io_mono_nanos_now();
v___x_2775_ = lean_float_of_nat(v___y_2771_);
v___x_2776_ = lean_float_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0);
v___x_2777_ = lean_float_div(v___x_2775_, v___x_2776_);
v___x_2778_ = lean_float_of_nat(v___x_2774_);
v___x_2779_ = lean_float_div(v___x_2778_, v___x_2776_);
v___x_2780_ = lean_box_float(v___x_2777_);
v___x_2781_ = lean_box_float(v___x_2779_);
v___x_2782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2782_, 0, v___x_2780_);
lean_ctor_set(v___x_2782_, 1, v___x_2781_);
v___x_2783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2783_, 0, v_a_2773_);
lean_ctor_set(v___x_2783_, 1, v___x_2782_);
v___x_2784_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_cls_2725_, v___x_2728_, v___x_2729_, v_options_2681_, v___y_2772_, v___y_2770_, v___f_2727_, v___x_2783_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_);
return v___x_2784_;
}
v___jp_2785_:
{
lean_object* v___x_2790_; 
v___x_2790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2790_, 0, v_a_2789_);
v___y_2770_ = v___y_2786_;
v___y_2771_ = v___y_2787_;
v___y_2772_ = v___y_2788_;
v_a_2773_ = v___x_2790_;
goto v___jp_2769_;
}
v___jp_2791_:
{
lean_object* v___x_2796_; 
v___x_2796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2796_, 0, v_a_2795_);
v___y_2770_ = v___y_2792_;
v___y_2771_ = v___y_2793_;
v___y_2772_ = v___y_2794_;
v_a_2773_ = v___x_2796_;
goto v___jp_2769_;
}
v___jp_2797_:
{
if (lean_obj_tag(v___y_2801_) == 0)
{
lean_object* v_a_2802_; 
v_a_2802_ = lean_ctor_get(v___y_2801_, 0);
lean_inc(v_a_2802_);
lean_dec_ref_known(v___y_2801_, 1);
v___y_2786_ = v___y_2798_;
v___y_2787_ = v___y_2799_;
v___y_2788_ = v___y_2800_;
v_a_2789_ = v_a_2802_;
goto v___jp_2785_;
}
else
{
lean_object* v_a_2803_; 
v_a_2803_ = lean_ctor_get(v___y_2801_, 0);
lean_inc(v_a_2803_);
lean_dec_ref_known(v___y_2801_, 1);
v___y_2792_ = v___y_2798_;
v___y_2793_ = v___y_2799_;
v___y_2794_ = v___y_2800_;
v_a_2795_ = v_a_2803_;
goto v___jp_2791_;
}
}
v___jp_2804_:
{
lean_object* v___x_2809_; lean_object* v___x_2810_; 
v___x_2809_ = lean_box(0);
lean_inc(v_a_2678_);
lean_inc_ref(v_a_2677_);
lean_inc(v_a_2676_);
lean_inc_ref(v_a_2675_);
v___x_2810_ = lean_apply_6(v___y_2806_, v___x_2809_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_, lean_box(0));
v___y_2798_ = v___y_2805_;
v___y_2799_ = v___y_2807_;
v___y_2800_ = v___y_2808_;
v___y_2801_ = v___x_2810_;
goto v___jp_2797_;
}
v___jp_2811_:
{
lean_object* v___x_2813_; lean_object* v_a_2814_; lean_object* v___x_2815_; uint8_t v___x_2816_; 
v___x_2813_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2678_);
v_a_2814_ = lean_ctor_get(v___x_2813_, 0);
lean_inc(v_a_2814_);
lean_dec_ref(v___x_2813_);
v___x_2815_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2816_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1(v_options_2681_, v___x_2815_);
if (v___x_2816_ == 0)
{
lean_object* v___x_2817_; lean_object* v___x_2818_; 
v___x_2817_ = lean_io_mono_nanos_now();
v___x_2818_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_);
if (lean_obj_tag(v___x_2818_) == 0)
{
lean_object* v_a_2819_; 
v_a_2819_ = lean_ctor_get(v___x_2818_, 0);
lean_inc(v_a_2819_);
lean_dec_ref_known(v___x_2818_, 1);
if (lean_obj_tag(v_a_2819_) == 1)
{
lean_object* v_val_2820_; lean_object* v___x_2821_; lean_object* v___f_2822_; 
v_val_2820_ = lean_ctor_get(v_a_2819_, 0);
lean_inc_n(v_val_2820_, 2);
lean_dec_ref_known(v_a_2819_, 1);
v___x_2821_ = lean_box(v___x_2816_);
lean_inc(v_levelParams_2683_);
lean_inc(v_name_2689_);
lean_inc(v_name_2682_);
v___f_2822_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1___boxed), 11, 5);
lean_closure_set(v___f_2822_, 0, v_name_2682_);
lean_closure_set(v___f_2822_, 1, v_val_2820_);
lean_closure_set(v___f_2822_, 2, v_name_2689_);
lean_closure_set(v___f_2822_, 3, v_levelParams_2683_);
lean_closure_set(v___f_2822_, 4, v___x_2821_);
if (v_hasTrace_2688_ == 0)
{
lean_dec(v_val_2820_);
lean_dec(v_name_2689_);
lean_dec(v_levelParams_2683_);
lean_dec(v_name_2682_);
v___y_2805_ = v_a_2814_;
v___y_2806_ = v___f_2822_;
v___y_2807_ = v___x_2817_;
v___y_2808_ = v___y_2812_;
goto v___jp_2804_;
}
else
{
lean_object* v___x_2823_; uint8_t v___x_2824_; 
v___x_2823_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_2824_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2687_, v_options_2681_, v___x_2823_);
if (v___x_2824_ == 0)
{
lean_dec(v_val_2820_);
lean_dec(v_name_2689_);
lean_dec(v_levelParams_2683_);
lean_dec(v_name_2682_);
v___y_2805_ = v_a_2814_;
v___y_2806_ = v___f_2822_;
v___y_2807_ = v___x_2817_;
v___y_2808_ = v___y_2812_;
goto v___jp_2804_;
}
else
{
lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; 
lean_dec_ref(v___f_2822_);
v___x_2825_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
lean_inc(v_val_2820_);
v___x_2826_ = l_Lean_MessageData_ofExpr(v_val_2820_);
v___x_2827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2827_, 0, v___x_2825_);
lean_ctor_set(v___x_2827_, 1, v___x_2826_);
v___x_2828_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2725_, v___x_2827_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_);
if (lean_obj_tag(v___x_2828_) == 0)
{
lean_object* v_a_2829_; lean_object* v___x_2830_; 
v_a_2829_ = lean_ctor_get(v___x_2828_, 0);
lean_inc(v_a_2829_);
lean_dec_ref_known(v___x_2828_, 1);
v___x_2830_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(v_name_2682_, v_val_2820_, v_name_2689_, v_levelParams_2683_, v___x_2816_, v_a_2829_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_);
v___y_2798_ = v_a_2814_;
v___y_2799_ = v___x_2817_;
v___y_2800_ = v___y_2812_;
v___y_2801_ = v___x_2830_;
goto v___jp_2797_;
}
else
{
lean_dec(v_val_2820_);
lean_dec(v_name_2689_);
lean_dec(v_levelParams_2683_);
lean_dec(v_name_2682_);
v___y_2798_ = v_a_2814_;
v___y_2799_ = v___x_2817_;
v___y_2800_ = v___y_2812_;
v___y_2801_ = v___x_2828_;
goto v___jp_2797_;
}
}
}
}
else
{
lean_object* v___x_2831_; 
lean_dec(v_a_2819_);
lean_dec(v_name_2689_);
lean_dec(v_levelParams_2683_);
lean_dec(v_name_2682_);
v___x_2831_ = lean_box(0);
v___y_2786_ = v_a_2814_;
v___y_2787_ = v___x_2817_;
v___y_2788_ = v___y_2812_;
v_a_2789_ = v___x_2831_;
goto v___jp_2785_;
}
}
else
{
lean_object* v_a_2832_; 
lean_dec(v_name_2689_);
lean_dec(v_levelParams_2683_);
lean_dec(v_name_2682_);
v_a_2832_ = lean_ctor_get(v___x_2818_, 0);
lean_inc(v_a_2832_);
lean_dec_ref_known(v___x_2818_, 1);
v___y_2792_ = v_a_2814_;
v___y_2793_ = v___x_2817_;
v___y_2794_ = v___y_2812_;
v_a_2795_ = v_a_2832_;
goto v___jp_2791_;
}
}
else
{
lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___x_2833_ = lean_io_get_num_heartbeats();
v___x_2834_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_);
if (lean_obj_tag(v___x_2834_) == 0)
{
lean_object* v_a_2835_; 
v_a_2835_ = lean_ctor_get(v___x_2834_, 0);
lean_inc(v_a_2835_);
lean_dec_ref_known(v___x_2834_, 1);
if (lean_obj_tag(v_a_2835_) == 1)
{
lean_object* v_val_2836_; lean_object* v___x_2837_; lean_object* v___f_2838_; 
v_val_2836_ = lean_ctor_get(v_a_2835_, 0);
lean_inc_n(v_val_2836_, 2);
lean_dec_ref_known(v_a_2835_, 1);
v___x_2837_ = lean_box(v___x_2726_);
lean_inc(v_levelParams_2683_);
lean_inc(v_name_2689_);
lean_inc(v_name_2682_);
v___f_2838_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1___boxed), 11, 5);
lean_closure_set(v___f_2838_, 0, v_name_2682_);
lean_closure_set(v___f_2838_, 1, v_val_2836_);
lean_closure_set(v___f_2838_, 2, v_name_2689_);
lean_closure_set(v___f_2838_, 3, v_levelParams_2683_);
lean_closure_set(v___f_2838_, 4, v___x_2837_);
if (v_hasTrace_2688_ == 0)
{
lean_dec(v_val_2836_);
lean_dec(v_name_2689_);
lean_dec(v_levelParams_2683_);
lean_dec(v_name_2682_);
v___y_2763_ = v_a_2814_;
v___y_2764_ = v___f_2838_;
v___y_2765_ = v___x_2833_;
v___y_2766_ = v___y_2812_;
goto v___jp_2762_;
}
else
{
lean_object* v___x_2839_; uint8_t v___x_2840_; 
v___x_2839_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_2840_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2687_, v_options_2681_, v___x_2839_);
if (v___x_2840_ == 0)
{
lean_dec(v_val_2836_);
lean_dec(v_name_2689_);
lean_dec(v_levelParams_2683_);
lean_dec(v_name_2682_);
v___y_2763_ = v_a_2814_;
v___y_2764_ = v___f_2838_;
v___y_2765_ = v___x_2833_;
v___y_2766_ = v___y_2812_;
goto v___jp_2762_;
}
else
{
lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; 
lean_dec_ref(v___f_2838_);
v___x_2841_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
lean_inc(v_val_2836_);
v___x_2842_ = l_Lean_MessageData_ofExpr(v_val_2836_);
v___x_2843_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2843_, 0, v___x_2841_);
lean_ctor_set(v___x_2843_, 1, v___x_2842_);
v___x_2844_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2725_, v___x_2843_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_);
if (lean_obj_tag(v___x_2844_) == 0)
{
lean_object* v_a_2845_; lean_object* v___x_2846_; 
v_a_2845_ = lean_ctor_get(v___x_2844_, 0);
lean_inc(v_a_2845_);
lean_dec_ref_known(v___x_2844_, 1);
v___x_2846_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(v_name_2682_, v_val_2836_, v_name_2689_, v_levelParams_2683_, v___x_2726_, v_a_2845_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_);
v___y_2756_ = v_a_2814_;
v___y_2757_ = v___x_2833_;
v___y_2758_ = v___y_2812_;
v___y_2759_ = v___x_2846_;
goto v___jp_2755_;
}
else
{
lean_dec(v_val_2836_);
lean_dec(v_name_2689_);
lean_dec(v_levelParams_2683_);
lean_dec(v_name_2682_);
v___y_2756_ = v_a_2814_;
v___y_2757_ = v___x_2833_;
v___y_2758_ = v___y_2812_;
v___y_2759_ = v___x_2844_;
goto v___jp_2755_;
}
}
}
}
else
{
lean_object* v___x_2847_; 
lean_dec(v_a_2835_);
lean_dec(v_name_2689_);
lean_dec(v_levelParams_2683_);
lean_dec(v_name_2682_);
v___x_2847_ = lean_box(0);
v___y_2750_ = v_a_2814_;
v___y_2751_ = v___x_2833_;
v___y_2752_ = v___y_2812_;
v_a_2753_ = v___x_2847_;
goto v___jp_2749_;
}
}
else
{
lean_object* v_a_2848_; 
lean_dec(v_name_2689_);
lean_dec(v_levelParams_2683_);
lean_dec(v_name_2682_);
v_a_2848_ = lean_ctor_get(v___x_2834_, 0);
lean_inc(v_a_2848_);
lean_dec_ref_known(v___x_2834_, 1);
v___y_2744_ = v_a_2814_;
v___y_2745_ = v___x_2833_;
v___y_2746_ = v___y_2812_;
v_a_2747_ = v_a_2848_;
goto v___jp_2743_;
}
}
}
v___jp_2849_:
{
lean_object* v___x_2851_; uint8_t v___x_2852_; 
v___x_2851_ = l_Lean_trace_profiler;
v___x_2852_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1(v_options_2681_, v___x_2851_);
if (v___x_2852_ == 0)
{
lean_object* v___x_2853_; 
lean_dec_ref(v___f_2727_);
v___x_2853_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_);
if (lean_obj_tag(v___x_2853_) == 0)
{
lean_object* v_a_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2870_; 
v_a_2854_ = lean_ctor_get(v___x_2853_, 0);
v_isSharedCheck_2870_ = !lean_is_exclusive(v___x_2853_);
if (v_isSharedCheck_2870_ == 0)
{
v___x_2856_ = v___x_2853_;
v_isShared_2857_ = v_isSharedCheck_2870_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_a_2854_);
lean_dec(v___x_2853_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2870_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
if (lean_obj_tag(v_a_2854_) == 1)
{
lean_del_object(v___x_2856_);
if (v_hasTrace_2688_ == 0)
{
lean_object* v_val_2858_; 
v_val_2858_ = lean_ctor_get(v_a_2854_, 0);
lean_inc(v_val_2858_);
lean_dec_ref_known(v_a_2854_, 1);
v___y_2691_ = v___x_2852_;
v___y_2692_ = v_val_2858_;
v___y_2693_ = v_a_2675_;
v___y_2694_ = v_a_2676_;
v___y_2695_ = v_a_2677_;
v___y_2696_ = v_a_2678_;
goto v___jp_2690_;
}
else
{
lean_object* v_val_2859_; lean_object* v___x_2860_; uint8_t v___x_2861_; 
v_val_2859_ = lean_ctor_get(v_a_2854_, 0);
lean_inc(v_val_2859_);
lean_dec_ref_known(v_a_2854_, 1);
v___x_2860_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_2861_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2687_, v_options_2681_, v___x_2860_);
if (v___x_2861_ == 0)
{
v___y_2691_ = v___x_2852_;
v___y_2692_ = v_val_2859_;
v___y_2693_ = v_a_2675_;
v___y_2694_ = v_a_2676_;
v___y_2695_ = v_a_2677_;
v___y_2696_ = v_a_2678_;
goto v___jp_2690_;
}
else
{
lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; 
v___x_2862_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
lean_inc(v_val_2859_);
v___x_2863_ = l_Lean_MessageData_ofExpr(v_val_2859_);
v___x_2864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2864_, 0, v___x_2862_);
lean_ctor_set(v___x_2864_, 1, v___x_2863_);
v___x_2865_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2725_, v___x_2864_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_);
if (lean_obj_tag(v___x_2865_) == 0)
{
lean_dec_ref_known(v___x_2865_, 1);
v___y_2691_ = v___x_2852_;
v___y_2692_ = v_val_2859_;
v___y_2693_ = v_a_2675_;
v___y_2694_ = v_a_2676_;
v___y_2695_ = v_a_2677_;
v___y_2696_ = v_a_2678_;
goto v___jp_2690_;
}
else
{
lean_dec(v_val_2859_);
lean_dec(v_name_2689_);
lean_del_object(v___x_2685_);
lean_dec(v_levelParams_2683_);
lean_dec(v_name_2682_);
return v___x_2865_;
}
}
}
}
else
{
lean_object* v___x_2866_; lean_object* v___x_2868_; 
lean_dec(v_a_2854_);
lean_dec(v_name_2689_);
lean_del_object(v___x_2685_);
lean_dec(v_levelParams_2683_);
lean_dec(v_name_2682_);
v___x_2866_ = lean_box(0);
if (v_isShared_2857_ == 0)
{
lean_ctor_set(v___x_2856_, 0, v___x_2866_);
v___x_2868_ = v___x_2856_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v___x_2866_);
v___x_2868_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
return v___x_2868_;
}
}
}
}
else
{
lean_object* v_a_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2878_; 
lean_dec(v_name_2689_);
lean_del_object(v___x_2685_);
lean_dec(v_levelParams_2683_);
lean_dec(v_name_2682_);
v_a_2871_ = lean_ctor_get(v___x_2853_, 0);
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2853_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2873_ = v___x_2853_;
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
else
{
lean_inc(v_a_2871_);
lean_dec(v___x_2853_);
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
else
{
lean_del_object(v___x_2685_);
v___y_2812_ = v_a_2850_;
goto v___jp_2811_;
}
}
}
else
{
lean_object* v___x_2881_; 
lean_del_object(v___x_2685_);
v___x_2881_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_);
if (lean_obj_tag(v___x_2881_) == 0)
{
lean_object* v_a_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2929_; 
v_a_2882_ = lean_ctor_get(v___x_2881_, 0);
v_isSharedCheck_2929_ = !lean_is_exclusive(v___x_2881_);
if (v_isSharedCheck_2929_ == 0)
{
v___x_2884_ = v___x_2881_;
v_isShared_2885_ = v_isSharedCheck_2929_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_a_2882_);
lean_dec(v___x_2881_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2929_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
if (lean_obj_tag(v_a_2882_) == 1)
{
lean_object* v_val_2886_; lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; 
lean_del_object(v___x_2884_);
v_val_2886_ = lean_ctor_get(v_a_2882_, 0);
lean_inc(v_val_2886_);
lean_dec_ref_known(v_a_2882_, 1);
if (v_hasTrace_2688_ == 0)
{
v___y_2888_ = v_a_2675_;
v___y_2889_ = v_a_2676_;
v___y_2890_ = v_a_2677_;
v___y_2891_ = v_a_2678_;
goto v___jp_2887_;
}
else
{
lean_object* v___x_2919_; uint8_t v___x_2920_; 
v___x_2919_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_2920_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2687_, v_options_2681_, v___x_2919_);
if (v___x_2920_ == 0)
{
v___y_2888_ = v_a_2675_;
v___y_2889_ = v_a_2676_;
v___y_2890_ = v_a_2677_;
v___y_2891_ = v_a_2678_;
goto v___jp_2887_;
}
else
{
lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; 
v___x_2921_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
lean_inc(v_val_2886_);
v___x_2922_ = l_Lean_MessageData_ofExpr(v_val_2886_);
v___x_2923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2923_, 0, v___x_2921_);
lean_ctor_set(v___x_2923_, 1, v___x_2922_);
v___x_2924_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2725_, v___x_2923_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_);
if (lean_obj_tag(v___x_2924_) == 0)
{
lean_dec_ref_known(v___x_2924_, 1);
v___y_2888_ = v_a_2675_;
v___y_2889_ = v_a_2676_;
v___y_2890_ = v_a_2677_;
v___y_2891_ = v_a_2678_;
goto v___jp_2887_;
}
else
{
lean_dec(v_val_2886_);
lean_dec(v_name_2689_);
lean_dec(v_levelParams_2683_);
lean_dec(v_name_2682_);
return v___x_2924_;
}
}
}
v___jp_2887_:
{
lean_object* v___x_2892_; 
lean_inc(v_val_2886_);
v___x_2892_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2682_, v_val_2886_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_);
if (lean_obj_tag(v___x_2892_) == 0)
{
lean_object* v_a_2893_; lean_object* v___x_2894_; lean_object* v_a_2895_; lean_object* v___x_2896_; lean_object* v_a_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2910_; 
v_a_2893_ = lean_ctor_get(v___x_2892_, 0);
lean_inc(v_a_2893_);
lean_dec_ref_known(v___x_2892_, 1);
v___x_2894_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___redArg(v_val_2886_, v___y_2889_);
v_a_2895_ = lean_ctor_get(v___x_2894_, 0);
lean_inc(v_a_2895_);
lean_dec_ref(v___x_2894_);
v___x_2896_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___redArg(v_a_2893_, v___y_2889_);
v_a_2897_ = lean_ctor_get(v___x_2896_, 0);
v_isSharedCheck_2910_ = !lean_is_exclusive(v___x_2896_);
if (v_isSharedCheck_2910_ == 0)
{
v___x_2899_ = v___x_2896_;
v_isShared_2900_ = v_isSharedCheck_2910_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_a_2897_);
lean_dec(v___x_2896_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2910_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2906_; 
lean_inc(v_name_2689_);
v___x_2901_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2901_, 0, v_name_2689_);
lean_ctor_set(v___x_2901_, 1, v_levelParams_2683_);
lean_ctor_set(v___x_2901_, 2, v_a_2895_);
v___x_2902_ = lean_box(0);
v___x_2903_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2903_, 0, v_name_2689_);
lean_ctor_set(v___x_2903_, 1, v___x_2902_);
v___x_2904_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2904_, 0, v___x_2901_);
lean_ctor_set(v___x_2904_, 1, v_a_2897_);
lean_ctor_set(v___x_2904_, 2, v___x_2903_);
if (v_isShared_2900_ == 0)
{
lean_ctor_set_tag(v___x_2899_, 2);
lean_ctor_set(v___x_2899_, 0, v___x_2904_);
v___x_2906_ = v___x_2899_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v___x_2904_);
v___x_2906_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
uint8_t v___x_2907_; lean_object* v___x_2908_; 
v___x_2907_ = 0;
v___x_2908_ = l_Lean_addDecl(v___x_2906_, v___x_2907_, v___y_2890_, v___y_2891_);
return v___x_2908_;
}
}
}
else
{
lean_object* v_a_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2918_; 
lean_dec(v_val_2886_);
lean_dec(v_name_2689_);
lean_dec(v_levelParams_2683_);
v_a_2911_ = lean_ctor_get(v___x_2892_, 0);
v_isSharedCheck_2918_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2913_ = v___x_2892_;
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_a_2911_);
lean_dec(v___x_2892_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___x_2916_; 
if (v_isShared_2914_ == 0)
{
v___x_2916_ = v___x_2913_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_a_2911_);
v___x_2916_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
return v___x_2916_;
}
}
}
}
}
else
{
lean_object* v___x_2925_; lean_object* v___x_2927_; 
lean_dec(v_a_2882_);
lean_dec(v_name_2689_);
lean_dec(v_levelParams_2683_);
lean_dec(v_name_2682_);
v___x_2925_ = lean_box(0);
if (v_isShared_2885_ == 0)
{
lean_ctor_set(v___x_2884_, 0, v___x_2925_);
v___x_2927_ = v___x_2884_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v___x_2925_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
return v___x_2927_;
}
}
}
}
else
{
lean_object* v_a_2930_; lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2937_; 
lean_dec(v_name_2689_);
lean_dec(v_levelParams_2683_);
lean_dec(v_name_2682_);
v_a_2930_ = lean_ctor_get(v___x_2881_, 0);
v_isSharedCheck_2937_ = !lean_is_exclusive(v___x_2881_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2932_ = v___x_2881_;
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
else
{
lean_inc(v_a_2930_);
lean_dec(v___x_2881_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
lean_object* v___x_2935_; 
if (v_isShared_2933_ == 0)
{
v___x_2935_ = v___x_2932_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_a_2930_);
v___x_2935_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
return v___x_2935_;
}
}
}
}
v___jp_2690_:
{
lean_object* v___x_2697_; 
lean_inc_ref(v___y_2692_);
v___x_2697_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2682_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_);
if (lean_obj_tag(v___x_2697_) == 0)
{
lean_object* v_a_2698_; lean_object* v___x_2699_; lean_object* v_a_2700_; lean_object* v___x_2701_; lean_object* v_a_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2716_; 
v_a_2698_ = lean_ctor_get(v___x_2697_, 0);
lean_inc(v_a_2698_);
lean_dec_ref_known(v___x_2697_, 1);
v___x_2699_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___redArg(v___y_2692_, v___y_2694_);
v_a_2700_ = lean_ctor_get(v___x_2699_, 0);
lean_inc(v_a_2700_);
lean_dec_ref(v___x_2699_);
v___x_2701_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___redArg(v_a_2698_, v___y_2694_);
v_a_2702_ = lean_ctor_get(v___x_2701_, 0);
v_isSharedCheck_2716_ = !lean_is_exclusive(v___x_2701_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2704_ = v___x_2701_;
v_isShared_2705_ = v_isSharedCheck_2716_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_a_2702_);
lean_dec(v___x_2701_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2716_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v___x_2707_; 
lean_inc(v_name_2689_);
if (v_isShared_2686_ == 0)
{
lean_ctor_set(v___x_2685_, 2, v_a_2700_);
lean_ctor_set(v___x_2685_, 0, v_name_2689_);
v___x_2707_ = v___x_2685_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v_name_2689_);
lean_ctor_set(v_reuseFailAlloc_2715_, 1, v_levelParams_2683_);
lean_ctor_set(v_reuseFailAlloc_2715_, 2, v_a_2700_);
v___x_2707_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2712_; 
v___x_2708_ = lean_box(0);
v___x_2709_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2709_, 0, v_name_2689_);
lean_ctor_set(v___x_2709_, 1, v___x_2708_);
v___x_2710_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2710_, 0, v___x_2707_);
lean_ctor_set(v___x_2710_, 1, v_a_2702_);
lean_ctor_set(v___x_2710_, 2, v___x_2709_);
if (v_isShared_2705_ == 0)
{
lean_ctor_set_tag(v___x_2704_, 2);
lean_ctor_set(v___x_2704_, 0, v___x_2710_);
v___x_2712_ = v___x_2704_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v___x_2710_);
v___x_2712_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
lean_object* v___x_2713_; 
v___x_2713_ = l_Lean_addDecl(v___x_2712_, v___y_2691_, v___y_2695_, v___y_2696_);
return v___x_2713_;
}
}
}
}
else
{
lean_object* v_a_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2724_; 
lean_dec_ref(v___y_2692_);
lean_dec(v_name_2689_);
lean_del_object(v___x_2685_);
lean_dec(v_levelParams_2683_);
v_a_2717_ = lean_ctor_get(v___x_2697_, 0);
v_isSharedCheck_2724_ = !lean_is_exclusive(v___x_2697_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2719_ = v___x_2697_;
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_a_2717_);
lean_dec(v___x_2697_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v___x_2722_; 
if (v_isShared_2720_ == 0)
{
v___x_2722_ = v___x_2719_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_a_2717_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___boxed(lean_object* v_ctorVal_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_){
_start:
{
lean_object* v_res_2946_; 
v_res_2946_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(v_ctorVal_2940_, v_a_2941_, v_a_2942_, v_a_2943_, v_a_2944_);
lean_dec(v_a_2944_);
lean_dec_ref(v_a_2943_);
lean_dec(v_a_2942_);
lean_dec_ref(v_a_2941_);
return v_res_2946_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2_spec__3(lean_object* v_00_u03b1_2947_, lean_object* v_x_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_){
_start:
{
lean_object* v___x_2954_; 
v___x_2954_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2_spec__3___redArg(v_x_2948_);
return v___x_2954_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2955_, lean_object* v_x_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_){
_start:
{
lean_object* v_res_2962_; 
v_res_2962_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2_spec__3(v_00_u03b1_2955_, v_x_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_);
lean_dec(v___y_2960_);
lean_dec_ref(v___y_2959_);
lean_dec(v___y_2958_);
lean_dec_ref(v___y_2957_);
return v_res_2962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveEqTheoremNameFor(lean_object* v_ctorName_2966_){
_start:
{
lean_object* v___x_2967_; lean_object* v___x_2968_; 
v___x_2967_ = ((lean_object*)(l_Lean_Meta_mkInjectiveEqTheoremNameFor___closed__1));
v___x_2968_ = l_Lean_Name_append(v_ctorName_2966_, v___x_2967_);
return v___x_2968_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(lean_object* v_ctorVal_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_){
_start:
{
uint8_t v___x_2975_; lean_object* v___x_2976_; 
v___x_2975_ = 1;
v___x_2976_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(v_ctorVal_2969_, v___x_2975_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_);
return v___x_2976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f___boxed(lean_object* v_ctorVal_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_){
_start:
{
lean_object* v_res_2983_; 
v_res_2983_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_2977_, v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_);
lean_dec(v_a_2981_);
lean_dec_ref(v_a_2980_);
lean_dec(v_a_2979_);
lean_dec_ref(v_a_2978_);
return v_res_2983_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(lean_object* v_e_2984_, lean_object* v_t_2985_, lean_object* v_acc_2986_, lean_object* v_a_2987_){
_start:
{
lean_object* v___x_2989_; 
v___x_2989_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_t_2985_, v_a_2987_);
if (lean_obj_tag(v___x_2989_) == 0)
{
lean_object* v_a_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_3013_; 
v_a_2990_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_3013_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_3013_ == 0)
{
v___x_2992_ = v___x_2989_;
v_isShared_2993_ = v_isSharedCheck_3013_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_a_2990_);
lean_dec(v___x_2989_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_3013_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v___x_2999_; uint8_t v___x_3000_; 
v___x_2999_ = l_Lean_Expr_cleanupAnnotations(v_a_2990_);
v___x_3000_ = l_Lean_Expr_isApp(v___x_2999_);
if (v___x_3000_ == 0)
{
lean_dec_ref(v___x_2999_);
goto v___jp_2994_;
}
else
{
lean_object* v_arg_3001_; lean_object* v___x_3002_; uint8_t v___x_3003_; 
v_arg_3001_ = lean_ctor_get(v___x_2999_, 1);
lean_inc_ref(v_arg_3001_);
v___x_3002_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2999_);
v___x_3003_ = l_Lean_Expr_isApp(v___x_3002_);
if (v___x_3003_ == 0)
{
lean_dec_ref(v___x_3002_);
lean_dec_ref(v_arg_3001_);
goto v___jp_2994_;
}
else
{
lean_object* v_arg_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; uint8_t v___x_3007_; 
v_arg_3004_ = lean_ctor_get(v___x_3002_, 1);
lean_inc_ref(v_arg_3004_);
v___x_3005_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3002_);
v___x_3006_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__1));
v___x_3007_ = l_Lean_Expr_isConstOf(v___x_3005_, v___x_3006_);
lean_dec_ref(v___x_3005_);
if (v___x_3007_ == 0)
{
lean_dec_ref(v_arg_3004_);
lean_dec_ref(v_arg_3001_);
goto v___jp_2994_;
}
else
{
lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; 
lean_del_object(v___x_2992_);
v___x_3008_ = lean_unsigned_to_nat(0u);
v___x_3009_ = l_Lean_mkProj(v___x_3006_, v___x_3008_, v_e_2984_);
lean_inc_ref(v___x_3009_);
v___x_3010_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v___x_3009_, v_arg_3004_, v_acc_2986_, v_a_2987_);
if (lean_obj_tag(v___x_3010_) == 0)
{
lean_object* v_a_3011_; 
v_a_3011_ = lean_ctor_get(v___x_3010_, 0);
lean_inc(v_a_3011_);
lean_dec_ref_known(v___x_3010_, 1);
v_e_2984_ = v___x_3009_;
v_t_2985_ = v_arg_3001_;
v_acc_2986_ = v_a_3011_;
goto _start;
}
else
{
lean_dec_ref(v___x_3009_);
lean_dec_ref(v_arg_3001_);
return v___x_3010_;
}
}
}
}
v___jp_2994_:
{
lean_object* v___x_2995_; lean_object* v___x_2997_; 
v___x_2995_ = lean_array_push(v_acc_2986_, v_e_2984_);
if (v_isShared_2993_ == 0)
{
lean_ctor_set(v___x_2992_, 0, v___x_2995_);
v___x_2997_ = v___x_2992_;
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
}
else
{
lean_object* v_a_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3021_; 
lean_dec_ref(v_acc_2986_);
lean_dec_ref(v_e_2984_);
v_a_3014_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_3021_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_3016_ = v___x_2989_;
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_a_3014_);
lean_dec(v___x_2989_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v___x_3019_; 
if (v_isShared_3017_ == 0)
{
v___x_3019_ = v___x_3016_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v_a_3014_);
v___x_3019_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
return v___x_3019_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg___boxed(lean_object* v_e_3022_, lean_object* v_t_3023_, lean_object* v_acc_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_){
_start:
{
lean_object* v_res_3027_; 
v_res_3027_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v_e_3022_, v_t_3023_, v_acc_3024_, v_a_3025_);
lean_dec(v_a_3025_);
return v_res_3027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go(lean_object* v_e_3028_, lean_object* v_t_3029_, lean_object* v_acc_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_){
_start:
{
lean_object* v___x_3036_; 
v___x_3036_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v_e_3028_, v_t_3029_, v_acc_3030_, v_a_3032_);
return v___x_3036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___boxed(lean_object* v_e_3037_, lean_object* v_t_3038_, lean_object* v_acc_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_){
_start:
{
lean_object* v_res_3045_; 
v_res_3045_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go(v_e_3037_, v_t_3038_, v_acc_3039_, v_a_3040_, v_a_3041_, v_a_3042_, v_a_3043_);
lean_dec(v_a_3043_);
lean_dec_ref(v_a_3042_);
lean_dec(v_a_3041_);
lean_dec_ref(v_a_3040_);
return v_res_3045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections(lean_object* v_e_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_){
_start:
{
lean_object* v___x_3052_; 
lean_inc(v_a_3050_);
lean_inc_ref(v_a_3049_);
lean_inc(v_a_3048_);
lean_inc_ref(v_a_3047_);
lean_inc_ref(v_e_3046_);
v___x_3052_ = lean_infer_type(v_e_3046_, v_a_3047_, v_a_3048_, v_a_3049_, v_a_3050_);
if (lean_obj_tag(v___x_3052_) == 0)
{
lean_object* v_a_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; 
v_a_3053_ = lean_ctor_get(v___x_3052_, 0);
lean_inc(v_a_3053_);
lean_dec_ref_known(v___x_3052_, 1);
v___x_3054_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_3055_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v_e_3046_, v_a_3053_, v___x_3054_, v_a_3048_);
return v___x_3055_;
}
else
{
lean_object* v_a_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3063_; 
lean_dec_ref(v_e_3046_);
v_a_3056_ = lean_ctor_get(v___x_3052_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_3052_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3058_ = v___x_3052_;
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_a_3056_);
lean_dec(v___x_3052_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3061_; 
if (v_isShared_3059_ == 0)
{
v___x_3061_ = v___x_3058_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_a_3056_);
v___x_3061_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
return v___x_3061_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections___boxed(lean_object* v_e_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_){
_start:
{
lean_object* v_res_3070_; 
v_res_3070_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections(v_e_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_);
lean_dec(v_a_3068_);
lean_dec_ref(v_a_3067_);
lean_dec(v_a_3066_);
lean_dec_ref(v_a_3065_);
return v_res_3070_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_x_3071_, lean_object* v_x_3072_, lean_object* v_x_3073_, lean_object* v_x_3074_){
_start:
{
lean_object* v_ks_3075_; lean_object* v_vs_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3100_; 
v_ks_3075_ = lean_ctor_get(v_x_3071_, 0);
v_vs_3076_ = lean_ctor_get(v_x_3071_, 1);
v_isSharedCheck_3100_ = !lean_is_exclusive(v_x_3071_);
if (v_isSharedCheck_3100_ == 0)
{
v___x_3078_ = v_x_3071_;
v_isShared_3079_ = v_isSharedCheck_3100_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_vs_3076_);
lean_inc(v_ks_3075_);
lean_dec(v_x_3071_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3100_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___x_3080_; uint8_t v___x_3081_; 
v___x_3080_ = lean_array_get_size(v_ks_3075_);
v___x_3081_ = lean_nat_dec_lt(v_x_3072_, v___x_3080_);
if (v___x_3081_ == 0)
{
lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3085_; 
lean_dec(v_x_3072_);
v___x_3082_ = lean_array_push(v_ks_3075_, v_x_3073_);
v___x_3083_ = lean_array_push(v_vs_3076_, v_x_3074_);
if (v_isShared_3079_ == 0)
{
lean_ctor_set(v___x_3078_, 1, v___x_3083_);
lean_ctor_set(v___x_3078_, 0, v___x_3082_);
v___x_3085_ = v___x_3078_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v___x_3082_);
lean_ctor_set(v_reuseFailAlloc_3086_, 1, v___x_3083_);
v___x_3085_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
return v___x_3085_;
}
}
else
{
lean_object* v_k_x27_3087_; uint8_t v___x_3088_; 
v_k_x27_3087_ = lean_array_fget_borrowed(v_ks_3075_, v_x_3072_);
v___x_3088_ = l_Lean_instBEqMVarId_beq(v_x_3073_, v_k_x27_3087_);
if (v___x_3088_ == 0)
{
lean_object* v___x_3090_; 
if (v_isShared_3079_ == 0)
{
v___x_3090_ = v___x_3078_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v_ks_3075_);
lean_ctor_set(v_reuseFailAlloc_3094_, 1, v_vs_3076_);
v___x_3090_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
lean_object* v___x_3091_; lean_object* v___x_3092_; 
v___x_3091_ = lean_unsigned_to_nat(1u);
v___x_3092_ = lean_nat_add(v_x_3072_, v___x_3091_);
lean_dec(v_x_3072_);
v_x_3071_ = v___x_3090_;
v_x_3072_ = v___x_3092_;
goto _start;
}
}
else
{
lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3098_; 
v___x_3095_ = lean_array_fset(v_ks_3075_, v_x_3072_, v_x_3073_);
v___x_3096_ = lean_array_fset(v_vs_3076_, v_x_3072_, v_x_3074_);
lean_dec(v_x_3072_);
if (v_isShared_3079_ == 0)
{
lean_ctor_set(v___x_3078_, 1, v___x_3096_);
lean_ctor_set(v___x_3078_, 0, v___x_3095_);
v___x_3098_ = v___x_3078_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v___x_3095_);
lean_ctor_set(v_reuseFailAlloc_3099_, 1, v___x_3096_);
v___x_3098_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
return v___x_3098_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_n_3101_, lean_object* v_k_3102_, lean_object* v_v_3103_){
_start:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___x_3104_ = lean_unsigned_to_nat(0u);
v___x_3105_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_n_3101_, v___x_3104_, v_k_3102_, v_v_3103_);
return v___x_3105_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_3106_; 
v___x_3106_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_3106_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(lean_object* v_x_3107_, size_t v_x_3108_, size_t v_x_3109_, lean_object* v_x_3110_, lean_object* v_x_3111_){
_start:
{
if (lean_obj_tag(v_x_3107_) == 0)
{
lean_object* v_es_3112_; size_t v___x_3113_; size_t v___x_3114_; lean_object* v_j_3115_; lean_object* v___x_3116_; uint8_t v___x_3117_; 
v_es_3112_ = lean_ctor_get(v_x_3107_, 0);
v___x_3113_ = ((size_t)31ULL);
v___x_3114_ = lean_usize_land(v_x_3108_, v___x_3113_);
v_j_3115_ = lean_usize_to_nat(v___x_3114_);
v___x_3116_ = lean_array_get_size(v_es_3112_);
v___x_3117_ = lean_nat_dec_lt(v_j_3115_, v___x_3116_);
if (v___x_3117_ == 0)
{
lean_dec(v_j_3115_);
lean_dec(v_x_3111_);
lean_dec(v_x_3110_);
return v_x_3107_;
}
else
{
lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3156_; 
lean_inc_ref(v_es_3112_);
v_isSharedCheck_3156_ = !lean_is_exclusive(v_x_3107_);
if (v_isSharedCheck_3156_ == 0)
{
lean_object* v_unused_3157_; 
v_unused_3157_ = lean_ctor_get(v_x_3107_, 0);
lean_dec(v_unused_3157_);
v___x_3119_ = v_x_3107_;
v_isShared_3120_ = v_isSharedCheck_3156_;
goto v_resetjp_3118_;
}
else
{
lean_dec(v_x_3107_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3156_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
lean_object* v_v_3121_; lean_object* v___x_3122_; lean_object* v_xs_x27_3123_; lean_object* v___y_3125_; 
v_v_3121_ = lean_array_fget(v_es_3112_, v_j_3115_);
v___x_3122_ = lean_box(0);
v_xs_x27_3123_ = lean_array_fset(v_es_3112_, v_j_3115_, v___x_3122_);
switch(lean_obj_tag(v_v_3121_))
{
case 0:
{
lean_object* v_key_3130_; lean_object* v_val_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3141_; 
v_key_3130_ = lean_ctor_get(v_v_3121_, 0);
v_val_3131_ = lean_ctor_get(v_v_3121_, 1);
v_isSharedCheck_3141_ = !lean_is_exclusive(v_v_3121_);
if (v_isSharedCheck_3141_ == 0)
{
v___x_3133_ = v_v_3121_;
v_isShared_3134_ = v_isSharedCheck_3141_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_val_3131_);
lean_inc(v_key_3130_);
lean_dec(v_v_3121_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3141_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
uint8_t v___x_3135_; 
v___x_3135_ = l_Lean_instBEqMVarId_beq(v_x_3110_, v_key_3130_);
if (v___x_3135_ == 0)
{
lean_object* v___x_3136_; lean_object* v___x_3137_; 
lean_del_object(v___x_3133_);
v___x_3136_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3130_, v_val_3131_, v_x_3110_, v_x_3111_);
v___x_3137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3137_, 0, v___x_3136_);
v___y_3125_ = v___x_3137_;
goto v___jp_3124_;
}
else
{
lean_object* v___x_3139_; 
lean_dec(v_val_3131_);
lean_dec(v_key_3130_);
if (v_isShared_3134_ == 0)
{
lean_ctor_set(v___x_3133_, 1, v_x_3111_);
lean_ctor_set(v___x_3133_, 0, v_x_3110_);
v___x_3139_ = v___x_3133_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v_x_3110_);
lean_ctor_set(v_reuseFailAlloc_3140_, 1, v_x_3111_);
v___x_3139_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
v___y_3125_ = v___x_3139_;
goto v___jp_3124_;
}
}
}
}
case 1:
{
lean_object* v_node_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3154_; 
v_node_3142_ = lean_ctor_get(v_v_3121_, 0);
v_isSharedCheck_3154_ = !lean_is_exclusive(v_v_3121_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3144_ = v_v_3121_;
v_isShared_3145_ = v_isSharedCheck_3154_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_node_3142_);
lean_dec(v_v_3121_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3154_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
size_t v___x_3146_; size_t v___x_3147_; size_t v___x_3148_; size_t v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3152_; 
v___x_3146_ = ((size_t)5ULL);
v___x_3147_ = lean_usize_shift_right(v_x_3108_, v___x_3146_);
v___x_3148_ = ((size_t)1ULL);
v___x_3149_ = lean_usize_add(v_x_3109_, v___x_3148_);
v___x_3150_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_node_3142_, v___x_3147_, v___x_3149_, v_x_3110_, v_x_3111_);
if (v_isShared_3145_ == 0)
{
lean_ctor_set(v___x_3144_, 0, v___x_3150_);
v___x_3152_ = v___x_3144_;
goto v_reusejp_3151_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v___x_3150_);
v___x_3152_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3151_;
}
v_reusejp_3151_:
{
v___y_3125_ = v___x_3152_;
goto v___jp_3124_;
}
}
}
default: 
{
lean_object* v___x_3155_; 
v___x_3155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3155_, 0, v_x_3110_);
lean_ctor_set(v___x_3155_, 1, v_x_3111_);
v___y_3125_ = v___x_3155_;
goto v___jp_3124_;
}
}
v___jp_3124_:
{
lean_object* v___x_3126_; lean_object* v___x_3128_; 
v___x_3126_ = lean_array_fset(v_xs_x27_3123_, v_j_3115_, v___y_3125_);
lean_dec(v_j_3115_);
if (v_isShared_3120_ == 0)
{
lean_ctor_set(v___x_3119_, 0, v___x_3126_);
v___x_3128_ = v___x_3119_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v___x_3126_);
v___x_3128_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
return v___x_3128_;
}
}
}
}
}
else
{
lean_object* v_ks_3158_; lean_object* v_vs_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3179_; 
v_ks_3158_ = lean_ctor_get(v_x_3107_, 0);
v_vs_3159_ = lean_ctor_get(v_x_3107_, 1);
v_isSharedCheck_3179_ = !lean_is_exclusive(v_x_3107_);
if (v_isSharedCheck_3179_ == 0)
{
v___x_3161_ = v_x_3107_;
v_isShared_3162_ = v_isSharedCheck_3179_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_vs_3159_);
lean_inc(v_ks_3158_);
lean_dec(v_x_3107_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3179_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
lean_object* v___x_3164_; 
if (v_isShared_3162_ == 0)
{
v___x_3164_ = v___x_3161_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v_ks_3158_);
lean_ctor_set(v_reuseFailAlloc_3178_, 1, v_vs_3159_);
v___x_3164_ = v_reuseFailAlloc_3178_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
lean_object* v_newNode_3165_; uint8_t v___y_3167_; size_t v___x_3173_; uint8_t v___x_3174_; 
v_newNode_3165_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(v___x_3164_, v_x_3110_, v_x_3111_);
v___x_3173_ = ((size_t)7ULL);
v___x_3174_ = lean_usize_dec_le(v___x_3173_, v_x_3109_);
if (v___x_3174_ == 0)
{
lean_object* v___x_3175_; lean_object* v___x_3176_; uint8_t v___x_3177_; 
v___x_3175_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3165_);
v___x_3176_ = lean_unsigned_to_nat(4u);
v___x_3177_ = lean_nat_dec_lt(v___x_3175_, v___x_3176_);
lean_dec(v___x_3175_);
v___y_3167_ = v___x_3177_;
goto v___jp_3166_;
}
else
{
v___y_3167_ = v___x_3174_;
goto v___jp_3166_;
}
v___jp_3166_:
{
if (v___y_3167_ == 0)
{
lean_object* v_ks_3168_; lean_object* v_vs_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; 
v_ks_3168_ = lean_ctor_get(v_newNode_3165_, 0);
lean_inc_ref(v_ks_3168_);
v_vs_3169_ = lean_ctor_get(v_newNode_3165_, 1);
lean_inc_ref(v_vs_3169_);
lean_dec_ref(v_newNode_3165_);
v___x_3170_ = lean_unsigned_to_nat(0u);
v___x_3171_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_3172_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(v_x_3109_, v_ks_3168_, v_vs_3169_, v___x_3170_, v___x_3171_);
lean_dec_ref(v_vs_3169_);
lean_dec_ref(v_ks_3168_);
return v___x_3172_;
}
else
{
return v_newNode_3165_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(size_t v_depth_3180_, lean_object* v_keys_3181_, lean_object* v_vals_3182_, lean_object* v_i_3183_, lean_object* v_entries_3184_){
_start:
{
lean_object* v___x_3185_; uint8_t v___x_3186_; 
v___x_3185_ = lean_array_get_size(v_keys_3181_);
v___x_3186_ = lean_nat_dec_lt(v_i_3183_, v___x_3185_);
if (v___x_3186_ == 0)
{
lean_dec(v_i_3183_);
return v_entries_3184_;
}
else
{
lean_object* v_k_3187_; lean_object* v_v_3188_; uint64_t v___x_3189_; size_t v_h_3190_; size_t v___x_3191_; lean_object* v___x_3192_; size_t v___x_3193_; size_t v___x_3194_; size_t v___x_3195_; size_t v_h_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; 
v_k_3187_ = lean_array_fget_borrowed(v_keys_3181_, v_i_3183_);
v_v_3188_ = lean_array_fget_borrowed(v_vals_3182_, v_i_3183_);
v___x_3189_ = l_Lean_instHashableMVarId_hash(v_k_3187_);
v_h_3190_ = lean_uint64_to_usize(v___x_3189_);
v___x_3191_ = ((size_t)5ULL);
v___x_3192_ = lean_unsigned_to_nat(1u);
v___x_3193_ = ((size_t)1ULL);
v___x_3194_ = lean_usize_sub(v_depth_3180_, v___x_3193_);
v___x_3195_ = lean_usize_mul(v___x_3191_, v___x_3194_);
v_h_3196_ = lean_usize_shift_right(v_h_3190_, v___x_3195_);
v___x_3197_ = lean_nat_add(v_i_3183_, v___x_3192_);
lean_dec(v_i_3183_);
lean_inc(v_v_3188_);
lean_inc(v_k_3187_);
v___x_3198_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_entries_3184_, v_h_3196_, v_depth_3180_, v_k_3187_, v_v_3188_);
v_i_3183_ = v___x_3197_;
v_entries_3184_ = v___x_3198_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_depth_3200_, lean_object* v_keys_3201_, lean_object* v_vals_3202_, lean_object* v_i_3203_, lean_object* v_entries_3204_){
_start:
{
size_t v_depth_boxed_3205_; lean_object* v_res_3206_; 
v_depth_boxed_3205_ = lean_unbox_usize(v_depth_3200_);
lean_dec(v_depth_3200_);
v_res_3206_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_boxed_3205_, v_keys_3201_, v_vals_3202_, v_i_3203_, v_entries_3204_);
lean_dec_ref(v_vals_3202_);
lean_dec_ref(v_keys_3201_);
return v_res_3206_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_3207_, lean_object* v_x_3208_, lean_object* v_x_3209_, lean_object* v_x_3210_, lean_object* v_x_3211_){
_start:
{
size_t v_x_5645__boxed_3212_; size_t v_x_5646__boxed_3213_; lean_object* v_res_3214_; 
v_x_5645__boxed_3212_ = lean_unbox_usize(v_x_3208_);
lean_dec(v_x_3208_);
v_x_5646__boxed_3213_ = lean_unbox_usize(v_x_3209_);
lean_dec(v_x_3209_);
v_res_3214_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_x_3207_, v_x_5645__boxed_3212_, v_x_5646__boxed_3213_, v_x_3210_, v_x_3211_);
return v_res_3214_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(lean_object* v_x_3215_, lean_object* v_x_3216_, lean_object* v_x_3217_){
_start:
{
uint64_t v___x_3218_; size_t v___x_3219_; size_t v___x_3220_; lean_object* v___x_3221_; 
v___x_3218_ = l_Lean_instHashableMVarId_hash(v_x_3216_);
v___x_3219_ = lean_uint64_to_usize(v___x_3218_);
v___x_3220_ = ((size_t)1ULL);
v___x_3221_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_x_3215_, v___x_3219_, v___x_3220_, v_x_3216_, v_x_3217_);
return v___x_3221_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(lean_object* v_mvarId_3222_, lean_object* v_val_3223_, lean_object* v___y_3224_){
_start:
{
lean_object* v___x_3226_; lean_object* v_mctx_3227_; lean_object* v_cache_3228_; lean_object* v_zetaDeltaFVarIds_3229_; lean_object* v_postponed_3230_; lean_object* v_diag_3231_; lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3259_; 
v___x_3226_ = lean_st_ref_take(v___y_3224_);
v_mctx_3227_ = lean_ctor_get(v___x_3226_, 0);
v_cache_3228_ = lean_ctor_get(v___x_3226_, 1);
v_zetaDeltaFVarIds_3229_ = lean_ctor_get(v___x_3226_, 2);
v_postponed_3230_ = lean_ctor_get(v___x_3226_, 3);
v_diag_3231_ = lean_ctor_get(v___x_3226_, 4);
v_isSharedCheck_3259_ = !lean_is_exclusive(v___x_3226_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3233_ = v___x_3226_;
v_isShared_3234_ = v_isSharedCheck_3259_;
goto v_resetjp_3232_;
}
else
{
lean_inc(v_diag_3231_);
lean_inc(v_postponed_3230_);
lean_inc(v_zetaDeltaFVarIds_3229_);
lean_inc(v_cache_3228_);
lean_inc(v_mctx_3227_);
lean_dec(v___x_3226_);
v___x_3233_ = lean_box(0);
v_isShared_3234_ = v_isSharedCheck_3259_;
goto v_resetjp_3232_;
}
v_resetjp_3232_:
{
lean_object* v_depth_3235_; lean_object* v_levelAssignDepth_3236_; lean_object* v_lmvarCounter_3237_; lean_object* v_mvarCounter_3238_; lean_object* v_lDecls_3239_; lean_object* v_decls_3240_; lean_object* v_userNames_3241_; lean_object* v_lAssignment_3242_; lean_object* v_eAssignment_3243_; lean_object* v_dAssignment_3244_; lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3258_; 
v_depth_3235_ = lean_ctor_get(v_mctx_3227_, 0);
v_levelAssignDepth_3236_ = lean_ctor_get(v_mctx_3227_, 1);
v_lmvarCounter_3237_ = lean_ctor_get(v_mctx_3227_, 2);
v_mvarCounter_3238_ = lean_ctor_get(v_mctx_3227_, 3);
v_lDecls_3239_ = lean_ctor_get(v_mctx_3227_, 4);
v_decls_3240_ = lean_ctor_get(v_mctx_3227_, 5);
v_userNames_3241_ = lean_ctor_get(v_mctx_3227_, 6);
v_lAssignment_3242_ = lean_ctor_get(v_mctx_3227_, 7);
v_eAssignment_3243_ = lean_ctor_get(v_mctx_3227_, 8);
v_dAssignment_3244_ = lean_ctor_get(v_mctx_3227_, 9);
v_isSharedCheck_3258_ = !lean_is_exclusive(v_mctx_3227_);
if (v_isSharedCheck_3258_ == 0)
{
v___x_3246_ = v_mctx_3227_;
v_isShared_3247_ = v_isSharedCheck_3258_;
goto v_resetjp_3245_;
}
else
{
lean_inc(v_dAssignment_3244_);
lean_inc(v_eAssignment_3243_);
lean_inc(v_lAssignment_3242_);
lean_inc(v_userNames_3241_);
lean_inc(v_decls_3240_);
lean_inc(v_lDecls_3239_);
lean_inc(v_mvarCounter_3238_);
lean_inc(v_lmvarCounter_3237_);
lean_inc(v_levelAssignDepth_3236_);
lean_inc(v_depth_3235_);
lean_dec(v_mctx_3227_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3258_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
lean_object* v___x_3248_; lean_object* v___x_3250_; 
v___x_3248_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(v_eAssignment_3243_, v_mvarId_3222_, v_val_3223_);
if (v_isShared_3247_ == 0)
{
lean_ctor_set(v___x_3246_, 8, v___x_3248_);
v___x_3250_ = v___x_3246_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v_depth_3235_);
lean_ctor_set(v_reuseFailAlloc_3257_, 1, v_levelAssignDepth_3236_);
lean_ctor_set(v_reuseFailAlloc_3257_, 2, v_lmvarCounter_3237_);
lean_ctor_set(v_reuseFailAlloc_3257_, 3, v_mvarCounter_3238_);
lean_ctor_set(v_reuseFailAlloc_3257_, 4, v_lDecls_3239_);
lean_ctor_set(v_reuseFailAlloc_3257_, 5, v_decls_3240_);
lean_ctor_set(v_reuseFailAlloc_3257_, 6, v_userNames_3241_);
lean_ctor_set(v_reuseFailAlloc_3257_, 7, v_lAssignment_3242_);
lean_ctor_set(v_reuseFailAlloc_3257_, 8, v___x_3248_);
lean_ctor_set(v_reuseFailAlloc_3257_, 9, v_dAssignment_3244_);
v___x_3250_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
lean_object* v___x_3252_; 
if (v_isShared_3234_ == 0)
{
lean_ctor_set(v___x_3233_, 0, v___x_3250_);
v___x_3252_ = v___x_3233_;
goto v_reusejp_3251_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v___x_3250_);
lean_ctor_set(v_reuseFailAlloc_3256_, 1, v_cache_3228_);
lean_ctor_set(v_reuseFailAlloc_3256_, 2, v_zetaDeltaFVarIds_3229_);
lean_ctor_set(v_reuseFailAlloc_3256_, 3, v_postponed_3230_);
lean_ctor_set(v_reuseFailAlloc_3256_, 4, v_diag_3231_);
v___x_3252_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3251_;
}
v_reusejp_3251_:
{
lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; 
v___x_3253_ = lean_st_ref_set(v___y_3224_, v___x_3252_);
v___x_3254_ = lean_box(0);
v___x_3255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3255_, 0, v___x_3254_);
return v___x_3255_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg___boxed(lean_object* v_mvarId_3260_, lean_object* v_val_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_){
_start:
{
lean_object* v_res_3264_; 
v_res_3264_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(v_mvarId_3260_, v_val_3261_, v___y_3262_);
lean_dec(v___y_3262_);
return v_res_3264_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(lean_object* v___f_3265_, lean_object* v_a_3266_, lean_object* v_x_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_){
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1___boxed(lean_object* v___f_3275_, lean_object* v_a_3276_, lean_object* v_x_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_){
_start:
{
lean_object* v_res_3283_; 
v_res_3283_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(v___f_3275_, v_a_3276_, v_x_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_);
lean_dec(v___y_3281_);
lean_dec_ref(v___y_3280_);
lean_dec(v___y_3279_);
lean_dec_ref(v___y_3278_);
return v_res_3283_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3285_; lean_object* v___x_3286_; 
v___x_3285_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___closed__0));
v___x_3286_ = l_Lean_stringToMessageData(v___x_3285_);
return v___x_3286_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(lean_object* v___f_3287_, lean_object* v_a_3288_, lean_object* v_x_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_){
_start:
{
lean_object* v___x_3295_; lean_object* v___x_3296_; 
v___x_3295_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___closed__1, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___closed__1);
v___x_3296_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_3295_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_);
if (lean_obj_tag(v___x_3296_) == 0)
{
lean_object* v_a_3297_; lean_object* v___x_3298_; 
v_a_3297_ = lean_ctor_get(v___x_3296_, 0);
lean_inc(v_a_3297_);
lean_dec_ref_known(v___x_3296_, 1);
lean_inc(v___y_3293_);
lean_inc_ref(v___y_3292_);
lean_inc(v___y_3291_);
lean_inc_ref(v___y_3290_);
v___x_3298_ = lean_apply_7(v___f_3287_, v_a_3297_, v_a_3288_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_, lean_box(0));
return v___x_3298_;
}
else
{
lean_object* v_a_3299_; lean_object* v___x_3301_; uint8_t v_isShared_3302_; uint8_t v_isSharedCheck_3306_; 
lean_dec(v_a_3288_);
lean_dec_ref(v___f_3287_);
v_a_3299_ = lean_ctor_get(v___x_3296_, 0);
v_isSharedCheck_3306_ = !lean_is_exclusive(v___x_3296_);
if (v_isSharedCheck_3306_ == 0)
{
v___x_3301_ = v___x_3296_;
v_isShared_3302_ = v_isSharedCheck_3306_;
goto v_resetjp_3300_;
}
else
{
lean_inc(v_a_3299_);
lean_dec(v___x_3296_);
v___x_3301_ = lean_box(0);
v_isShared_3302_ = v_isSharedCheck_3306_;
goto v_resetjp_3300_;
}
v_resetjp_3300_:
{
lean_object* v___x_3304_; 
if (v_isShared_3302_ == 0)
{
v___x_3304_ = v___x_3301_;
goto v_reusejp_3303_;
}
else
{
lean_object* v_reuseFailAlloc_3305_; 
v_reuseFailAlloc_3305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3305_, 0, v_a_3299_);
v___x_3304_ = v_reuseFailAlloc_3305_;
goto v_reusejp_3303_;
}
v_reusejp_3303_:
{
return v___x_3304_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___boxed(lean_object* v___f_3307_, lean_object* v_a_3308_, lean_object* v_x_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_){
_start:
{
lean_object* v_res_3315_; 
v_res_3315_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(v___f_3307_, v_a_3308_, v_x_3309_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_);
lean_dec(v___y_3313_);
lean_dec_ref(v___y_3312_);
lean_dec(v___y_3311_);
lean_dec_ref(v___y_3310_);
lean_dec(v_x_3309_);
return v_res_3315_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0(uint8_t v___x_3316_, lean_object* v_____r_3317_, lean_object* v_mvarId_u2082_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_){
_start:
{
lean_object* v___x_3324_; 
v___x_3324_ = l_Lean_Meta_introSubstEq(v_mvarId_u2082_3318_, v___x_3316_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_);
if (lean_obj_tag(v___x_3324_) == 0)
{
lean_object* v_a_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3334_; 
v_a_3325_ = lean_ctor_get(v___x_3324_, 0);
v_isSharedCheck_3334_ = !lean_is_exclusive(v___x_3324_);
if (v_isSharedCheck_3334_ == 0)
{
v___x_3327_ = v___x_3324_;
v_isShared_3328_ = v_isSharedCheck_3334_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_a_3325_);
lean_dec(v___x_3324_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3334_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v_snd_3329_; lean_object* v___x_3330_; lean_object* v___x_3332_; 
v_snd_3329_ = lean_ctor_get(v_a_3325_, 1);
lean_inc(v_snd_3329_);
lean_dec(v_a_3325_);
v___x_3330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3330_, 0, v_snd_3329_);
if (v_isShared_3328_ == 0)
{
lean_ctor_set(v___x_3327_, 0, v___x_3330_);
v___x_3332_ = v___x_3327_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3333_; 
v_reuseFailAlloc_3333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3333_, 0, v___x_3330_);
v___x_3332_ = v_reuseFailAlloc_3333_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
return v___x_3332_;
}
}
}
else
{
lean_object* v_a_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3342_; 
v_a_3335_ = lean_ctor_get(v___x_3324_, 0);
v_isSharedCheck_3342_ = !lean_is_exclusive(v___x_3324_);
if (v_isSharedCheck_3342_ == 0)
{
v___x_3337_ = v___x_3324_;
v_isShared_3338_ = v_isSharedCheck_3342_;
goto v_resetjp_3336_;
}
else
{
lean_inc(v_a_3335_);
lean_dec(v___x_3324_);
v___x_3337_ = lean_box(0);
v_isShared_3338_ = v_isSharedCheck_3342_;
goto v_resetjp_3336_;
}
v_resetjp_3336_:
{
lean_object* v___x_3340_; 
if (v_isShared_3338_ == 0)
{
v___x_3340_ = v___x_3337_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v_a_3335_);
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
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0___boxed(lean_object* v___x_3343_, lean_object* v_____r_3344_, lean_object* v_mvarId_u2082_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_){
_start:
{
uint8_t v___x_5937__boxed_3351_; lean_object* v_res_3352_; 
v___x_5937__boxed_3351_ = lean_unbox(v___x_3343_);
v_res_3352_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0(v___x_5937__boxed_3351_, v_____r_3344_, v_mvarId_u2082_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
lean_dec(v___y_3349_);
lean_dec_ref(v___y_3348_);
lean_dec(v___y_3347_);
lean_dec_ref(v___y_3346_);
return v_res_3352_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; 
v___x_3358_ = lean_box(0);
v___x_3359_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__2));
v___x_3360_ = l_Lean_mkConst(v___x_3359_, v___x_3358_);
return v___x_3360_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg(lean_object* v_a_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_){
_start:
{
lean_object* v___y_3368_; lean_object* v___x_3388_; 
lean_inc(v_a_3361_);
v___x_3388_ = l_Lean_MVarId_getType(v_a_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
if (lean_obj_tag(v___x_3388_) == 0)
{
lean_object* v_a_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3448_; 
v_a_3389_ = lean_ctor_get(v___x_3388_, 0);
v_isSharedCheck_3448_ = !lean_is_exclusive(v___x_3388_);
if (v_isSharedCheck_3448_ == 0)
{
v___x_3391_ = v___x_3388_;
v_isShared_3392_ = v_isSharedCheck_3448_;
goto v_resetjp_3390_;
}
else
{
lean_inc(v_a_3389_);
lean_dec(v___x_3388_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3448_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
if (lean_obj_tag(v_a_3389_) == 7)
{
lean_object* v_binderType_3393_; lean_object* v_body_3394_; uint8_t v___x_3395_; 
v_binderType_3393_ = lean_ctor_get(v_a_3389_, 1);
lean_inc_ref(v_binderType_3393_);
v_body_3394_ = lean_ctor_get(v_a_3389_, 2);
lean_inc_ref(v_body_3394_);
lean_dec_ref_known(v_a_3389_, 3);
v___x_3395_ = l_Lean_Expr_hasLooseBVars(v_body_3394_);
if (v___x_3395_ == 0)
{
lean_object* v___x_3396_; 
lean_del_object(v___x_3391_);
v___x_3396_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_3393_, v___y_3363_);
if (lean_obj_tag(v___x_3396_) == 0)
{
lean_object* v_a_3397_; lean_object* v___x_3398_; lean_object* v___f_3399_; lean_object* v___x_3400_; uint8_t v___x_3401_; 
v_a_3397_ = lean_ctor_get(v___x_3396_, 0);
lean_inc(v_a_3397_);
lean_dec_ref_known(v___x_3396_, 1);
v___x_3398_ = lean_box(v___x_3395_);
v___f_3399_ = lean_alloc_closure((void*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3399_, 0, v___x_3398_);
v___x_3400_ = l_Lean_Expr_cleanupAnnotations(v_a_3397_);
v___x_3401_ = l_Lean_Expr_isApp(v___x_3400_);
if (v___x_3401_ == 0)
{
lean_object* v___x_3402_; lean_object* v___x_3403_; 
lean_dec_ref(v___x_3400_);
lean_dec_ref(v_body_3394_);
v___x_3402_ = lean_box(0);
v___x_3403_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(v___f_3399_, v_a_3361_, v___x_3402_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
v___y_3368_ = v___x_3403_;
goto v___jp_3367_;
}
else
{
lean_object* v_arg_3404_; lean_object* v___x_3405_; uint8_t v___x_3406_; 
v_arg_3404_ = lean_ctor_get(v___x_3400_, 1);
lean_inc_ref(v_arg_3404_);
v___x_3405_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3400_);
v___x_3406_ = l_Lean_Expr_isApp(v___x_3405_);
if (v___x_3406_ == 0)
{
lean_object* v___x_3407_; lean_object* v___x_3408_; 
lean_dec_ref(v___x_3405_);
lean_dec_ref(v_arg_3404_);
lean_dec_ref(v_body_3394_);
v___x_3407_ = lean_box(0);
v___x_3408_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(v___f_3399_, v_a_3361_, v___x_3407_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
v___y_3368_ = v___x_3408_;
goto v___jp_3367_;
}
else
{
lean_object* v_arg_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; uint8_t v___x_3412_; 
v_arg_3409_ = lean_ctor_get(v___x_3405_, 1);
lean_inc_ref(v_arg_3409_);
v___x_3410_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3405_);
v___x_3411_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__1));
v___x_3412_ = l_Lean_Expr_isConstOf(v___x_3410_, v___x_3411_);
lean_dec_ref(v___x_3410_);
if (v___x_3412_ == 0)
{
lean_object* v___x_3413_; lean_object* v___x_3414_; 
lean_dec_ref(v_arg_3409_);
lean_dec_ref(v_arg_3404_);
lean_dec_ref(v_body_3394_);
v___x_3413_ = lean_box(0);
v___x_3414_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(v___f_3399_, v_a_3361_, v___x_3413_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
v___y_3368_ = v___x_3414_;
goto v___jp_3367_;
}
else
{
lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; 
v___x_3415_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__3, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__3_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__3);
v___x_3416_ = l_Lean_mkApp3(v___x_3415_, v_arg_3409_, v_arg_3404_, v_body_3394_);
v___x_3417_ = lean_unsigned_to_nat(1u);
lean_inc(v_a_3361_);
v___x_3418_ = l_Lean_MVarId_applyN(v_a_3361_, v___x_3416_, v___x_3417_, v___x_3412_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
if (lean_obj_tag(v___x_3418_) == 0)
{
lean_object* v_a_3419_; 
v_a_3419_ = lean_ctor_get(v___x_3418_, 0);
lean_inc(v_a_3419_);
lean_dec_ref_known(v___x_3418_, 1);
if (lean_obj_tag(v_a_3419_) == 1)
{
lean_object* v_tail_3420_; 
v_tail_3420_ = lean_ctor_get(v_a_3419_, 1);
if (lean_obj_tag(v_tail_3420_) == 0)
{
lean_object* v_head_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; 
lean_dec_ref(v___f_3399_);
lean_dec(v_a_3361_);
v_head_3421_ = lean_ctor_get(v_a_3419_, 0);
lean_inc(v_head_3421_);
lean_dec_ref_known(v_a_3419_, 2);
v___x_3422_ = lean_box(0);
v___x_3423_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0(v___x_3395_, v___x_3422_, v_head_3421_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
v___y_3368_ = v___x_3423_;
goto v___jp_3367_;
}
else
{
lean_object* v___x_3424_; 
v___x_3424_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(v___f_3399_, v_a_3361_, v_a_3419_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
lean_dec_ref_known(v_a_3419_, 2);
v___y_3368_ = v___x_3424_;
goto v___jp_3367_;
}
}
else
{
lean_object* v___x_3425_; 
v___x_3425_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(v___f_3399_, v_a_3361_, v_a_3419_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
lean_dec(v_a_3419_);
v___y_3368_ = v___x_3425_;
goto v___jp_3367_;
}
}
else
{
lean_object* v_a_3426_; lean_object* v___x_3428_; uint8_t v_isShared_3429_; uint8_t v_isSharedCheck_3433_; 
lean_dec_ref(v___f_3399_);
lean_dec(v_a_3361_);
v_a_3426_ = lean_ctor_get(v___x_3418_, 0);
v_isSharedCheck_3433_ = !lean_is_exclusive(v___x_3418_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3428_ = v___x_3418_;
v_isShared_3429_ = v_isSharedCheck_3433_;
goto v_resetjp_3427_;
}
else
{
lean_inc(v_a_3426_);
lean_dec(v___x_3418_);
v___x_3428_ = lean_box(0);
v_isShared_3429_ = v_isSharedCheck_3433_;
goto v_resetjp_3427_;
}
v_resetjp_3427_:
{
lean_object* v___x_3431_; 
if (v_isShared_3429_ == 0)
{
v___x_3431_ = v___x_3428_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v_a_3426_);
v___x_3431_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
return v___x_3431_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3441_; 
lean_dec_ref(v_body_3394_);
lean_dec(v_a_3361_);
v_a_3434_ = lean_ctor_get(v___x_3396_, 0);
v_isSharedCheck_3441_ = !lean_is_exclusive(v___x_3396_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3436_ = v___x_3396_;
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_a_3434_);
lean_dec(v___x_3396_);
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
}
else
{
lean_object* v___x_3443_; 
lean_dec_ref(v_body_3394_);
lean_dec_ref(v_binderType_3393_);
if (v_isShared_3392_ == 0)
{
lean_ctor_set(v___x_3391_, 0, v_a_3361_);
v___x_3443_ = v___x_3391_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v_a_3361_);
v___x_3443_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
return v___x_3443_;
}
}
}
else
{
lean_object* v___x_3446_; 
lean_dec(v_a_3389_);
if (v_isShared_3392_ == 0)
{
lean_ctor_set(v___x_3391_, 0, v_a_3361_);
v___x_3446_ = v___x_3391_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v_a_3361_);
v___x_3446_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
return v___x_3446_;
}
}
}
}
else
{
lean_object* v_a_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3456_; 
lean_dec(v_a_3361_);
v_a_3449_ = lean_ctor_get(v___x_3388_, 0);
v_isSharedCheck_3456_ = !lean_is_exclusive(v___x_3388_);
if (v_isSharedCheck_3456_ == 0)
{
v___x_3451_ = v___x_3388_;
v_isShared_3452_ = v_isSharedCheck_3456_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_a_3449_);
lean_dec(v___x_3388_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3456_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
lean_object* v___x_3454_; 
if (v_isShared_3452_ == 0)
{
v___x_3454_ = v___x_3451_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v_a_3449_);
v___x_3454_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
return v___x_3454_;
}
}
}
v___jp_3367_:
{
if (lean_obj_tag(v___y_3368_) == 0)
{
lean_object* v_a_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3379_; 
v_a_3369_ = lean_ctor_get(v___y_3368_, 0);
v_isSharedCheck_3379_ = !lean_is_exclusive(v___y_3368_);
if (v_isSharedCheck_3379_ == 0)
{
v___x_3371_ = v___y_3368_;
v_isShared_3372_ = v_isSharedCheck_3379_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_a_3369_);
lean_dec(v___y_3368_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3379_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
if (lean_obj_tag(v_a_3369_) == 0)
{
lean_object* v_a_3373_; lean_object* v___x_3375_; 
v_a_3373_ = lean_ctor_get(v_a_3369_, 0);
lean_inc(v_a_3373_);
lean_dec_ref_known(v_a_3369_, 1);
if (v_isShared_3372_ == 0)
{
lean_ctor_set(v___x_3371_, 0, v_a_3373_);
v___x_3375_ = v___x_3371_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3376_, 0, v_a_3373_);
v___x_3375_ = v_reuseFailAlloc_3376_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
return v___x_3375_;
}
}
else
{
lean_object* v_a_3377_; 
lean_del_object(v___x_3371_);
v_a_3377_ = lean_ctor_get(v_a_3369_, 0);
lean_inc(v_a_3377_);
lean_dec_ref_known(v_a_3369_, 1);
v_a_3361_ = v_a_3377_;
goto _start;
}
}
}
else
{
lean_object* v_a_3380_; lean_object* v___x_3382_; uint8_t v_isShared_3383_; uint8_t v_isSharedCheck_3387_; 
v_a_3380_ = lean_ctor_get(v___y_3368_, 0);
v_isSharedCheck_3387_ = !lean_is_exclusive(v___y_3368_);
if (v_isSharedCheck_3387_ == 0)
{
v___x_3382_ = v___y_3368_;
v_isShared_3383_ = v_isSharedCheck_3387_;
goto v_resetjp_3381_;
}
else
{
lean_inc(v_a_3380_);
lean_dec(v___y_3368_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___boxed(lean_object* v_a_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_){
_start:
{
lean_object* v_res_3463_; 
v_res_3463_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg(v_a_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_);
lean_dec(v___y_3461_);
lean_dec_ref(v___y_3460_);
lean_dec(v___y_3459_);
lean_dec_ref(v___y_3458_);
return v_res_3463_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; 
v___x_3469_ = lean_box(0);
v___x_3470_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__2));
v___x_3471_ = l_Lean_mkConst(v___x_3470_, v___x_3469_);
return v___x_3471_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6(void){
_start:
{
lean_object* v___x_3477_; lean_object* v___x_3478_; 
v___x_3477_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__5));
v___x_3478_ = l_Lean_stringToMessageData(v___x_3477_);
return v___x_3478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0(lean_object* v_ctorVal_3479_, lean_object* v_xs_3480_, lean_object* v_type_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_){
_start:
{
lean_object* v___x_3487_; lean_object* v___x_3488_; 
v___x_3487_ = lean_box(0);
v___x_3488_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_3481_, v___x_3487_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_);
if (lean_obj_tag(v___x_3488_) == 0)
{
lean_object* v_a_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; uint8_t v___x_3493_; uint8_t v___x_3494_; lean_object* v___y_3496_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; 
v_a_3489_ = lean_ctor_get(v___x_3488_, 0);
lean_inc(v_a_3489_);
lean_dec_ref_known(v___x_3488_, 1);
v___x_3490_ = l_Lean_Expr_mvarId_x21(v_a_3489_);
v___x_3491_ = lean_box(0);
v___x_3492_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3);
v___x_3493_ = 1;
v___x_3494_ = 0;
v___x_3507_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__4));
v___x_3508_ = lean_box(0);
v___x_3509_ = l_Lean_MVarId_apply(v___x_3490_, v___x_3492_, v___x_3507_, v___x_3508_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_);
if (lean_obj_tag(v___x_3509_) == 0)
{
lean_object* v_a_3510_; lean_object* v___y_3512_; lean_object* v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3515_; 
v_a_3510_ = lean_ctor_get(v___x_3509_, 0);
lean_inc(v_a_3510_);
lean_dec_ref_known(v___x_3509_, 1);
if (lean_obj_tag(v_a_3510_) == 1)
{
lean_object* v_tail_3524_; 
v_tail_3524_ = lean_ctor_get(v_a_3510_, 1);
lean_inc(v_tail_3524_);
if (lean_obj_tag(v_tail_3524_) == 1)
{
lean_object* v_tail_3525_; 
v_tail_3525_ = lean_ctor_get(v_tail_3524_, 1);
if (lean_obj_tag(v_tail_3525_) == 0)
{
lean_object* v_toConstantVal_3526_; lean_object* v_head_3527_; lean_object* v_head_3528_; lean_object* v_name_3529_; lean_object* v_levelParams_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; 
v_toConstantVal_3526_ = lean_ctor_get(v_ctorVal_3479_, 0);
lean_inc_ref(v_toConstantVal_3526_);
lean_dec_ref(v_ctorVal_3479_);
v_head_3527_ = lean_ctor_get(v_a_3510_, 0);
lean_inc(v_head_3527_);
lean_dec_ref_known(v_a_3510_, 2);
v_head_3528_ = lean_ctor_get(v_tail_3524_, 0);
lean_inc(v_head_3528_);
lean_dec_ref_known(v_tail_3524_, 2);
v_name_3529_ = lean_ctor_get(v_toConstantVal_3526_, 0);
lean_inc_n(v_name_3529_, 2);
v_levelParams_3530_ = lean_ctor_get(v_toConstantVal_3526_, 1);
lean_inc(v_levelParams_3530_);
lean_dec_ref(v_toConstantVal_3526_);
v___x_3531_ = l_Lean_Meta_mkInjectiveTheoremNameFor(v_name_3529_);
v___x_3532_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(v_levelParams_3530_, v___x_3491_);
v___x_3533_ = l_Lean_mkConst(v___x_3531_, v___x_3532_);
v___x_3534_ = l_Lean_mkAppN(v___x_3533_, v_xs_3480_);
v___x_3535_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(v_head_3527_, v___x_3534_, v___y_3483_);
lean_dec_ref(v___x_3535_);
v___x_3536_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg(v_head_3528_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_);
if (lean_obj_tag(v___x_3536_) == 0)
{
lean_object* v_a_3537_; lean_object* v___x_3538_; 
v_a_3537_ = lean_ctor_get(v___x_3536_, 0);
lean_inc(v_a_3537_);
lean_dec_ref_known(v___x_3536_, 1);
v___x_3538_ = l_Lean_MVarId_refl(v_a_3537_, v___x_3493_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_);
if (lean_obj_tag(v___x_3538_) == 0)
{
lean_dec(v_name_3529_);
v___y_3496_ = v___x_3538_;
goto v___jp_3495_;
}
else
{
lean_object* v_a_3539_; uint8_t v___y_3541_; uint8_t v___x_3544_; 
v_a_3539_ = lean_ctor_get(v___x_3538_, 0);
lean_inc(v_a_3539_);
v___x_3544_ = l_Lean_Exception_isInterrupt(v_a_3539_);
if (v___x_3544_ == 0)
{
uint8_t v___x_3545_; 
v___x_3545_ = l_Lean_Exception_isRuntime(v_a_3539_);
v___y_3541_ = v___x_3545_;
goto v___jp_3540_;
}
else
{
lean_dec(v_a_3539_);
v___y_3541_ = v___x_3544_;
goto v___jp_3540_;
}
v___jp_3540_:
{
if (v___y_3541_ == 0)
{
lean_object* v___x_3542_; lean_object* v___x_3543_; 
lean_dec_ref_known(v___x_3538_, 1);
v___x_3542_ = l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(v_name_3529_);
v___x_3543_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_3542_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_);
v___y_3496_ = v___x_3543_;
goto v___jp_3495_;
}
else
{
lean_dec(v_name_3529_);
v___y_3496_ = v___x_3538_;
goto v___jp_3495_;
}
}
}
}
else
{
lean_object* v_a_3546_; lean_object* v___x_3548_; uint8_t v_isShared_3549_; uint8_t v_isSharedCheck_3553_; 
lean_dec(v_name_3529_);
lean_dec(v_a_3489_);
v_a_3546_ = lean_ctor_get(v___x_3536_, 0);
v_isSharedCheck_3553_ = !lean_is_exclusive(v___x_3536_);
if (v_isSharedCheck_3553_ == 0)
{
v___x_3548_ = v___x_3536_;
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
else
{
lean_inc(v_a_3546_);
lean_dec(v___x_3536_);
v___x_3548_ = lean_box(0);
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
v_resetjp_3547_:
{
lean_object* v___x_3551_; 
if (v_isShared_3549_ == 0)
{
v___x_3551_ = v___x_3548_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v_a_3546_);
v___x_3551_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
return v___x_3551_;
}
}
}
}
else
{
lean_dec_ref_known(v_tail_3524_, 2);
lean_dec_ref_known(v_a_3510_, 2);
lean_dec(v_a_3489_);
v___y_3512_ = v___y_3482_;
v___y_3513_ = v___y_3483_;
v___y_3514_ = v___y_3484_;
v___y_3515_ = v___y_3485_;
goto v___jp_3511_;
}
}
else
{
lean_dec_ref_known(v_a_3510_, 2);
lean_dec(v_tail_3524_);
lean_dec(v_a_3489_);
v___y_3512_ = v___y_3482_;
v___y_3513_ = v___y_3483_;
v___y_3514_ = v___y_3484_;
v___y_3515_ = v___y_3485_;
goto v___jp_3511_;
}
}
else
{
lean_dec(v_a_3510_);
lean_dec(v_a_3489_);
v___y_3512_ = v___y_3482_;
v___y_3513_ = v___y_3483_;
v___y_3514_ = v___y_3484_;
v___y_3515_ = v___y_3485_;
goto v___jp_3511_;
}
v___jp_3511_:
{
lean_object* v_toConstantVal_3516_; lean_object* v_name_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; 
v_toConstantVal_3516_ = lean_ctor_get(v_ctorVal_3479_, 0);
lean_inc_ref(v_toConstantVal_3516_);
lean_dec_ref(v_ctorVal_3479_);
v_name_3517_ = lean_ctor_get(v_toConstantVal_3516_, 0);
lean_inc(v_name_3517_);
lean_dec_ref(v_toConstantVal_3516_);
v___x_3518_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6);
v___x_3519_ = l_Lean_MessageData_ofName(v_name_3517_);
v___x_3520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3520_, 0, v___x_3518_);
lean_ctor_set(v___x_3520_, 1, v___x_3519_);
v___x_3521_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_3522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3522_, 0, v___x_3520_);
lean_ctor_set(v___x_3522_, 1, v___x_3521_);
v___x_3523_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_3522_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_);
return v___x_3523_;
}
}
else
{
lean_object* v_a_3554_; lean_object* v___x_3556_; uint8_t v_isShared_3557_; uint8_t v_isSharedCheck_3561_; 
lean_dec(v_a_3489_);
lean_dec_ref(v_ctorVal_3479_);
v_a_3554_ = lean_ctor_get(v___x_3509_, 0);
v_isSharedCheck_3561_ = !lean_is_exclusive(v___x_3509_);
if (v_isSharedCheck_3561_ == 0)
{
v___x_3556_ = v___x_3509_;
v_isShared_3557_ = v_isSharedCheck_3561_;
goto v_resetjp_3555_;
}
else
{
lean_inc(v_a_3554_);
lean_dec(v___x_3509_);
v___x_3556_ = lean_box(0);
v_isShared_3557_ = v_isSharedCheck_3561_;
goto v_resetjp_3555_;
}
v_resetjp_3555_:
{
lean_object* v___x_3559_; 
if (v_isShared_3557_ == 0)
{
v___x_3559_ = v___x_3556_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v_a_3554_);
v___x_3559_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
return v___x_3559_;
}
}
}
v___jp_3495_:
{
if (lean_obj_tag(v___y_3496_) == 0)
{
uint8_t v___x_3497_; lean_object* v___x_3498_; 
lean_dec_ref_known(v___y_3496_, 1);
v___x_3497_ = 1;
v___x_3498_ = l_Lean_Meta_mkLambdaFVars(v_xs_3480_, v_a_3489_, v___x_3494_, v___x_3493_, v___x_3494_, v___x_3493_, v___x_3497_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_);
return v___x_3498_;
}
else
{
lean_object* v_a_3499_; lean_object* v___x_3501_; uint8_t v_isShared_3502_; uint8_t v_isSharedCheck_3506_; 
lean_dec(v_a_3489_);
v_a_3499_ = lean_ctor_get(v___y_3496_, 0);
v_isSharedCheck_3506_ = !lean_is_exclusive(v___y_3496_);
if (v_isSharedCheck_3506_ == 0)
{
v___x_3501_ = v___y_3496_;
v_isShared_3502_ = v_isSharedCheck_3506_;
goto v_resetjp_3500_;
}
else
{
lean_inc(v_a_3499_);
lean_dec(v___y_3496_);
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
else
{
lean_dec_ref(v_ctorVal_3479_);
return v___x_3488_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___boxed(lean_object* v_ctorVal_3562_, lean_object* v_xs_3563_, lean_object* v_type_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_){
_start:
{
lean_object* v_res_3570_; 
v_res_3570_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0(v_ctorVal_3562_, v_xs_3563_, v_type_3564_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_);
lean_dec(v___y_3568_);
lean_dec_ref(v___y_3567_);
lean_dec(v___y_3566_);
lean_dec_ref(v___y_3565_);
lean_dec_ref(v_xs_3563_);
return v_res_3570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(lean_object* v_ctorVal_3571_, lean_object* v_targetType_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_){
_start:
{
lean_object* v___f_3578_; uint8_t v___x_3579_; lean_object* v___x_3580_; 
v___f_3578_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3578_, 0, v_ctorVal_3571_);
v___x_3579_ = 0;
v___x_3580_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_targetType_3572_, v___f_3578_, v___x_3579_, v___x_3579_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_);
return v___x_3580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___boxed(lean_object* v_ctorVal_3581_, lean_object* v_targetType_3582_, lean_object* v_a_3583_, lean_object* v_a_3584_, lean_object* v_a_3585_, lean_object* v_a_3586_, lean_object* v_a_3587_){
_start:
{
lean_object* v_res_3588_; 
v_res_3588_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3581_, v_targetType_3582_, v_a_3583_, v_a_3584_, v_a_3585_, v_a_3586_);
lean_dec(v_a_3586_);
lean_dec_ref(v_a_3585_);
lean_dec(v_a_3584_);
lean_dec_ref(v_a_3583_);
return v_res_3588_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0(lean_object* v_mvarId_3589_, lean_object* v_val_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_){
_start:
{
lean_object* v___x_3596_; 
v___x_3596_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(v_mvarId_3589_, v_val_3590_, v___y_3592_);
return v___x_3596_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___boxed(lean_object* v_mvarId_3597_, lean_object* v_val_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_){
_start:
{
lean_object* v_res_3604_; 
v_res_3604_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0(v_mvarId_3597_, v_val_3598_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_);
lean_dec(v___y_3602_);
lean_dec_ref(v___y_3601_);
lean_dec(v___y_3600_);
lean_dec_ref(v___y_3599_);
return v_res_3604_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1(lean_object* v_inst_3605_, lean_object* v_a_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_){
_start:
{
lean_object* v___x_3612_; 
v___x_3612_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg(v_a_3606_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_);
return v___x_3612_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___boxed(lean_object* v_inst_3613_, lean_object* v_a_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_){
_start:
{
lean_object* v_res_3620_; 
v_res_3620_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1(v_inst_3613_, v_a_3614_, v___y_3615_, v___y_3616_, v___y_3617_, v___y_3618_);
lean_dec(v___y_3618_);
lean_dec_ref(v___y_3617_);
lean_dec(v___y_3616_);
lean_dec_ref(v___y_3615_);
return v_res_3620_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0(lean_object* v_00_u03b2_3621_, lean_object* v_x_3622_, lean_object* v_x_3623_, lean_object* v_x_3624_){
_start:
{
lean_object* v___x_3625_; 
v___x_3625_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(v_x_3622_, v_x_3623_, v_x_3624_);
return v___x_3625_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3626_, lean_object* v_x_3627_, size_t v_x_3628_, size_t v_x_3629_, lean_object* v_x_3630_, lean_object* v_x_3631_){
_start:
{
lean_object* v___x_3632_; 
v___x_3632_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_x_3627_, v_x_3628_, v_x_3629_, v_x_3630_, v_x_3631_);
return v___x_3632_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3633_, lean_object* v_x_3634_, lean_object* v_x_3635_, lean_object* v_x_3636_, lean_object* v_x_3637_, lean_object* v_x_3638_){
_start:
{
size_t v_x_6488__boxed_3639_; size_t v_x_6489__boxed_3640_; lean_object* v_res_3641_; 
v_x_6488__boxed_3639_ = lean_unbox_usize(v_x_3635_);
lean_dec(v_x_3635_);
v_x_6489__boxed_3640_ = lean_unbox_usize(v_x_3636_);
lean_dec(v_x_3636_);
v_res_3641_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1(v_00_u03b2_3633_, v_x_3634_, v_x_6488__boxed_3639_, v_x_6489__boxed_3640_, v_x_3637_, v_x_3638_);
return v_res_3641_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_3642_, lean_object* v_n_3643_, lean_object* v_k_3644_, lean_object* v_v_3645_){
_start:
{
lean_object* v___x_3646_; 
v___x_3646_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(v_n_3643_, v_k_3644_, v_v_3645_);
return v___x_3646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_3647_, size_t v_depth_3648_, lean_object* v_keys_3649_, lean_object* v_vals_3650_, lean_object* v_heq_3651_, lean_object* v_i_3652_, lean_object* v_entries_3653_){
_start:
{
lean_object* v___x_3654_; 
v___x_3654_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_3648_, v_keys_3649_, v_vals_3650_, v_i_3652_, v_entries_3653_);
return v___x_3654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_3655_, lean_object* v_depth_3656_, lean_object* v_keys_3657_, lean_object* v_vals_3658_, lean_object* v_heq_3659_, lean_object* v_i_3660_, lean_object* v_entries_3661_){
_start:
{
size_t v_depth_boxed_3662_; lean_object* v_res_3663_; 
v_depth_boxed_3662_ = lean_unbox_usize(v_depth_3656_);
lean_dec(v_depth_3656_);
v_res_3663_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_3655_, v_depth_boxed_3662_, v_keys_3657_, v_vals_3658_, v_heq_3659_, v_i_3660_, v_entries_3661_);
lean_dec_ref(v_vals_3658_);
lean_dec_ref(v_keys_3657_);
return v_res_3663_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_3664_, lean_object* v_x_3665_, lean_object* v_x_3666_, lean_object* v_x_3667_, lean_object* v_x_3668_){
_start:
{
lean_object* v___x_3669_; 
v___x_3669_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_x_3665_, v_x_3666_, v_x_3667_, v_x_3668_);
return v___x_3669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(lean_object* v_ctorVal_3670_, lean_object* v_val_3671_, lean_object* v_name_3672_, lean_object* v_levelParams_3673_, uint8_t v___x_3674_, uint8_t v___x_3675_, lean_object* v_____r_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_){
_start:
{
lean_object* v___x_3682_; 
lean_inc_ref(v_val_3671_);
v___x_3682_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3670_, v_val_3671_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_);
if (lean_obj_tag(v___x_3682_) == 0)
{
lean_object* v_a_3683_; lean_object* v___x_3684_; lean_object* v_a_3685_; lean_object* v___x_3686_; lean_object* v_a_3687_; lean_object* v___x_3689_; uint8_t v_isShared_3690_; uint8_t v_isSharedCheck_3703_; 
v_a_3683_ = lean_ctor_get(v___x_3682_, 0);
lean_inc(v_a_3683_);
lean_dec_ref_known(v___x_3682_, 1);
v___x_3684_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___redArg(v_val_3671_, v___y_3678_);
v_a_3685_ = lean_ctor_get(v___x_3684_, 0);
lean_inc(v_a_3685_);
lean_dec_ref(v___x_3684_);
v___x_3686_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___redArg(v_a_3683_, v___y_3678_);
v_a_3687_ = lean_ctor_get(v___x_3686_, 0);
v_isSharedCheck_3703_ = !lean_is_exclusive(v___x_3686_);
if (v_isSharedCheck_3703_ == 0)
{
v___x_3689_ = v___x_3686_;
v_isShared_3690_ = v_isSharedCheck_3703_;
goto v_resetjp_3688_;
}
else
{
lean_inc(v_a_3687_);
lean_dec(v___x_3686_);
v___x_3689_ = lean_box(0);
v_isShared_3690_ = v_isSharedCheck_3703_;
goto v_resetjp_3688_;
}
v_resetjp_3688_:
{
lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3696_; 
lean_inc_n(v_name_3672_, 2);
v___x_3691_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3691_, 0, v_name_3672_);
lean_ctor_set(v___x_3691_, 1, v_levelParams_3673_);
lean_ctor_set(v___x_3691_, 2, v_a_3685_);
v___x_3692_ = lean_box(0);
v___x_3693_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3693_, 0, v_name_3672_);
lean_ctor_set(v___x_3693_, 1, v___x_3692_);
v___x_3694_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3694_, 0, v___x_3691_);
lean_ctor_set(v___x_3694_, 1, v_a_3687_);
lean_ctor_set(v___x_3694_, 2, v___x_3693_);
if (v_isShared_3690_ == 0)
{
lean_ctor_set_tag(v___x_3689_, 2);
lean_ctor_set(v___x_3689_, 0, v___x_3694_);
v___x_3696_ = v___x_3689_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v___x_3694_);
v___x_3696_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
lean_object* v___x_3697_; 
v___x_3697_ = l_Lean_addDecl(v___x_3696_, v___x_3674_, v___y_3679_, v___y_3680_);
if (lean_obj_tag(v___x_3697_) == 0)
{
lean_object* v___x_3698_; uint8_t v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; 
lean_dec_ref_known(v___x_3697_, 1);
v___x_3698_ = l_Lean_Meta_simpExtension;
v___x_3699_ = 0;
v___x_3700_ = lean_unsigned_to_nat(1000u);
v___x_3701_ = l_Lean_Meta_addSimpTheorem(v___x_3698_, v_name_3672_, v___x_3675_, v___x_3674_, v___x_3699_, v___x_3700_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_);
return v___x_3701_;
}
else
{
lean_dec(v_name_3672_);
return v___x_3697_;
}
}
}
}
else
{
lean_object* v_a_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3711_; 
lean_dec(v_levelParams_3673_);
lean_dec(v_name_3672_);
lean_dec_ref(v_val_3671_);
v_a_3704_ = lean_ctor_get(v___x_3682_, 0);
v_isSharedCheck_3711_ = !lean_is_exclusive(v___x_3682_);
if (v_isSharedCheck_3711_ == 0)
{
v___x_3706_ = v___x_3682_;
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_a_3704_);
lean_dec(v___x_3682_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
lean_object* v___x_3709_; 
if (v_isShared_3707_ == 0)
{
v___x_3709_ = v___x_3706_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v_a_3704_);
v___x_3709_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
return v___x_3709_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1___boxed(lean_object* v_ctorVal_3712_, lean_object* v_val_3713_, lean_object* v_name_3714_, lean_object* v_levelParams_3715_, lean_object* v___x_3716_, lean_object* v___x_3717_, lean_object* v_____r_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_){
_start:
{
uint8_t v___x_8847__boxed_3724_; uint8_t v___x_8848__boxed_3725_; lean_object* v_res_3726_; 
v___x_8847__boxed_3724_ = lean_unbox(v___x_3716_);
v___x_8848__boxed_3725_ = lean_unbox(v___x_3717_);
v_res_3726_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(v_ctorVal_3712_, v_val_3713_, v_name_3714_, v_levelParams_3715_, v___x_8847__boxed_3724_, v___x_8848__boxed_3725_, v_____r_3718_, v___y_3719_, v___y_3720_, v___y_3721_, v___y_3722_);
lean_dec(v___y_3722_);
lean_dec_ref(v___y_3721_);
lean_dec(v___y_3720_);
lean_dec_ref(v___y_3719_);
return v_res_3726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(lean_object* v_ctorVal_3727_, lean_object* v_a_3728_, lean_object* v_a_3729_, lean_object* v_a_3730_, lean_object* v_a_3731_){
_start:
{
lean_object* v_toConstantVal_3733_; lean_object* v_options_3734_; lean_object* v_name_3735_; lean_object* v_levelParams_3736_; lean_object* v___x_3738_; uint8_t v_isShared_3739_; uint8_t v_isSharedCheck_4003_; 
v_toConstantVal_3733_ = lean_ctor_get(v_ctorVal_3727_, 0);
lean_inc_ref(v_toConstantVal_3733_);
v_options_3734_ = lean_ctor_get(v_a_3730_, 2);
v_name_3735_ = lean_ctor_get(v_toConstantVal_3733_, 0);
v_levelParams_3736_ = lean_ctor_get(v_toConstantVal_3733_, 1);
v_isSharedCheck_4003_ = !lean_is_exclusive(v_toConstantVal_3733_);
if (v_isSharedCheck_4003_ == 0)
{
lean_object* v_unused_4004_; 
v_unused_4004_ = lean_ctor_get(v_toConstantVal_3733_, 2);
lean_dec(v_unused_4004_);
v___x_3738_ = v_toConstantVal_3733_;
v_isShared_3739_ = v_isSharedCheck_4003_;
goto v_resetjp_3737_;
}
else
{
lean_inc(v_levelParams_3736_);
lean_inc(v_name_3735_);
lean_dec(v_toConstantVal_3733_);
v___x_3738_ = lean_box(0);
v_isShared_3739_ = v_isSharedCheck_4003_;
goto v_resetjp_3737_;
}
v_resetjp_3737_:
{
lean_object* v_inheritedTraceOptions_3740_; uint8_t v_hasTrace_3741_; lean_object* v_name_3742_; lean_object* v_cls_3743_; uint8_t v___x_3744_; 
v_inheritedTraceOptions_3740_ = lean_ctor_get(v_a_3730_, 13);
v_hasTrace_3741_ = lean_ctor_get_uint8(v_options_3734_, sizeof(void*)*1);
v_name_3742_ = l_Lean_Meta_mkInjectiveEqTheoremNameFor(v_name_3735_);
v_cls_3743_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_3744_ = lean_bool_not(v_hasTrace_3741_);
if (v___x_3744_ == 0)
{
lean_object* v___f_3745_; uint8_t v___x_3746_; lean_object* v___y_3748_; uint8_t v___y_3749_; lean_object* v___y_3750_; lean_object* v___y_3751_; lean_object* v___y_3752_; lean_object* v___y_3753_; lean_object* v___x_3786_; uint8_t v___y_3788_; lean_object* v___y_3789_; lean_object* v___y_3790_; lean_object* v_a_3791_; uint8_t v___y_3801_; lean_object* v___y_3802_; lean_object* v___y_3803_; lean_object* v_a_3804_; uint8_t v___y_3807_; lean_object* v___y_3808_; lean_object* v___y_3809_; lean_object* v_a_3810_; uint8_t v___y_3813_; lean_object* v___y_3814_; lean_object* v___y_3815_; lean_object* v___y_3816_; uint8_t v___y_3820_; lean_object* v___y_3821_; lean_object* v___y_3822_; lean_object* v___y_3823_; uint8_t v___y_3827_; lean_object* v___y_3828_; lean_object* v___y_3829_; lean_object* v_a_3830_; uint8_t v___y_3843_; lean_object* v___y_3844_; lean_object* v___y_3845_; lean_object* v_a_3846_; uint8_t v___y_3849_; lean_object* v___y_3850_; lean_object* v___y_3851_; lean_object* v_a_3852_; uint8_t v___y_3855_; lean_object* v___y_3856_; lean_object* v___y_3857_; lean_object* v___y_3858_; uint8_t v___y_3862_; lean_object* v___y_3863_; lean_object* v___y_3864_; lean_object* v___y_3865_; uint8_t v___y_3869_; uint8_t v_a_3909_; 
lean_inc(v_name_3742_);
v___f_3745_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3745_, 0, v_name_3742_);
v___x_3746_ = 1;
v___x_3786_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
if (v_hasTrace_3741_ == 0)
{
v_a_3909_ = v_hasTrace_3741_;
goto v___jp_3908_;
}
else
{
lean_object* v___x_3938_; uint8_t v___x_3939_; 
v___x_3938_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_3939_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3740_, v_options_3734_, v___x_3938_);
if (v___x_3939_ == 0)
{
v_a_3909_ = v___x_3939_;
goto v___jp_3908_;
}
else
{
lean_del_object(v___x_3738_);
v___y_3869_ = v___x_3939_;
goto v___jp_3868_;
}
}
v___jp_3747_:
{
lean_object* v___x_3754_; 
lean_inc_ref(v___y_3748_);
v___x_3754_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3727_, v___y_3748_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_);
if (lean_obj_tag(v___x_3754_) == 0)
{
lean_object* v_a_3755_; lean_object* v___x_3756_; lean_object* v_a_3757_; lean_object* v___x_3758_; lean_object* v_a_3759_; lean_object* v___x_3761_; uint8_t v_isShared_3762_; uint8_t v_isSharedCheck_3777_; 
v_a_3755_ = lean_ctor_get(v___x_3754_, 0);
lean_inc(v_a_3755_);
lean_dec_ref_known(v___x_3754_, 1);
v___x_3756_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___redArg(v___y_3748_, v___y_3751_);
v_a_3757_ = lean_ctor_get(v___x_3756_, 0);
lean_inc(v_a_3757_);
lean_dec_ref(v___x_3756_);
v___x_3758_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___redArg(v_a_3755_, v___y_3751_);
v_a_3759_ = lean_ctor_get(v___x_3758_, 0);
v_isSharedCheck_3777_ = !lean_is_exclusive(v___x_3758_);
if (v_isSharedCheck_3777_ == 0)
{
v___x_3761_ = v___x_3758_;
v_isShared_3762_ = v_isSharedCheck_3777_;
goto v_resetjp_3760_;
}
else
{
lean_inc(v_a_3759_);
lean_dec(v___x_3758_);
v___x_3761_ = lean_box(0);
v_isShared_3762_ = v_isSharedCheck_3777_;
goto v_resetjp_3760_;
}
v_resetjp_3760_:
{
lean_object* v___x_3764_; 
lean_inc(v_name_3742_);
if (v_isShared_3739_ == 0)
{
lean_ctor_set(v___x_3738_, 2, v_a_3757_);
lean_ctor_set(v___x_3738_, 0, v_name_3742_);
v___x_3764_ = v___x_3738_;
goto v_reusejp_3763_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v_name_3742_);
lean_ctor_set(v_reuseFailAlloc_3776_, 1, v_levelParams_3736_);
lean_ctor_set(v_reuseFailAlloc_3776_, 2, v_a_3757_);
v___x_3764_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3763_;
}
v_reusejp_3763_:
{
lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3769_; 
v___x_3765_ = lean_box(0);
lean_inc(v_name_3742_);
v___x_3766_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3766_, 0, v_name_3742_);
lean_ctor_set(v___x_3766_, 1, v___x_3765_);
v___x_3767_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3767_, 0, v___x_3764_);
lean_ctor_set(v___x_3767_, 1, v_a_3759_);
lean_ctor_set(v___x_3767_, 2, v___x_3766_);
if (v_isShared_3762_ == 0)
{
lean_ctor_set_tag(v___x_3761_, 2);
lean_ctor_set(v___x_3761_, 0, v___x_3767_);
v___x_3769_ = v___x_3761_;
goto v_reusejp_3768_;
}
else
{
lean_object* v_reuseFailAlloc_3775_; 
v_reuseFailAlloc_3775_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3775_, 0, v___x_3767_);
v___x_3769_ = v_reuseFailAlloc_3775_;
goto v_reusejp_3768_;
}
v_reusejp_3768_:
{
lean_object* v___x_3770_; 
v___x_3770_ = l_Lean_addDecl(v___x_3769_, v___y_3749_, v___y_3752_, v___y_3753_);
if (lean_obj_tag(v___x_3770_) == 0)
{
lean_object* v___x_3771_; uint8_t v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; 
lean_dec_ref_known(v___x_3770_, 1);
v___x_3771_ = l_Lean_Meta_simpExtension;
v___x_3772_ = 0;
v___x_3773_ = lean_unsigned_to_nat(1000u);
v___x_3774_ = l_Lean_Meta_addSimpTheorem(v___x_3771_, v_name_3742_, v___x_3746_, v___y_3749_, v___x_3772_, v___x_3773_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_);
return v___x_3774_;
}
else
{
lean_dec(v_name_3742_);
return v___x_3770_;
}
}
}
}
}
else
{
lean_object* v_a_3778_; lean_object* v___x_3780_; uint8_t v_isShared_3781_; uint8_t v_isSharedCheck_3785_; 
lean_dec_ref(v___y_3748_);
lean_dec(v_name_3742_);
lean_del_object(v___x_3738_);
lean_dec(v_levelParams_3736_);
v_a_3778_ = lean_ctor_get(v___x_3754_, 0);
v_isSharedCheck_3785_ = !lean_is_exclusive(v___x_3754_);
if (v_isSharedCheck_3785_ == 0)
{
v___x_3780_ = v___x_3754_;
v_isShared_3781_ = v_isSharedCheck_3785_;
goto v_resetjp_3779_;
}
else
{
lean_inc(v_a_3778_);
lean_dec(v___x_3754_);
v___x_3780_ = lean_box(0);
v_isShared_3781_ = v_isSharedCheck_3785_;
goto v_resetjp_3779_;
}
v_resetjp_3779_:
{
lean_object* v___x_3783_; 
if (v_isShared_3781_ == 0)
{
v___x_3783_ = v___x_3780_;
goto v_reusejp_3782_;
}
else
{
lean_object* v_reuseFailAlloc_3784_; 
v_reuseFailAlloc_3784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3784_, 0, v_a_3778_);
v___x_3783_ = v_reuseFailAlloc_3784_;
goto v_reusejp_3782_;
}
v_reusejp_3782_:
{
return v___x_3783_;
}
}
}
}
v___jp_3787_:
{
lean_object* v___x_3792_; double v___x_3793_; double v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; 
v___x_3792_ = lean_io_get_num_heartbeats();
v___x_3793_ = lean_float_of_nat(v___y_3789_);
v___x_3794_ = lean_float_of_nat(v___x_3792_);
v___x_3795_ = lean_box_float(v___x_3793_);
v___x_3796_ = lean_box_float(v___x_3794_);
v___x_3797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3797_, 0, v___x_3795_);
lean_ctor_set(v___x_3797_, 1, v___x_3796_);
v___x_3798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3798_, 0, v_a_3791_);
lean_ctor_set(v___x_3798_, 1, v___x_3797_);
v___x_3799_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_cls_3743_, v___x_3746_, v___x_3786_, v_options_3734_, v___y_3788_, v___y_3790_, v___f_3745_, v___x_3798_, v_a_3728_, v_a_3729_, v_a_3730_, v_a_3731_);
return v___x_3799_;
}
v___jp_3800_:
{
lean_object* v___x_3805_; 
v___x_3805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3805_, 0, v_a_3804_);
v___y_3788_ = v___y_3801_;
v___y_3789_ = v___y_3802_;
v___y_3790_ = v___y_3803_;
v_a_3791_ = v___x_3805_;
goto v___jp_3787_;
}
v___jp_3806_:
{
lean_object* v___x_3811_; 
v___x_3811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3811_, 0, v_a_3810_);
v___y_3788_ = v___y_3807_;
v___y_3789_ = v___y_3808_;
v___y_3790_ = v___y_3809_;
v_a_3791_ = v___x_3811_;
goto v___jp_3787_;
}
v___jp_3812_:
{
if (lean_obj_tag(v___y_3816_) == 0)
{
lean_object* v_a_3817_; 
v_a_3817_ = lean_ctor_get(v___y_3816_, 0);
lean_inc(v_a_3817_);
lean_dec_ref_known(v___y_3816_, 1);
v___y_3807_ = v___y_3813_;
v___y_3808_ = v___y_3814_;
v___y_3809_ = v___y_3815_;
v_a_3810_ = v_a_3817_;
goto v___jp_3806_;
}
else
{
lean_object* v_a_3818_; 
v_a_3818_ = lean_ctor_get(v___y_3816_, 0);
lean_inc(v_a_3818_);
lean_dec_ref_known(v___y_3816_, 1);
v___y_3801_ = v___y_3813_;
v___y_3802_ = v___y_3814_;
v___y_3803_ = v___y_3815_;
v_a_3804_ = v_a_3818_;
goto v___jp_3800_;
}
}
v___jp_3819_:
{
lean_object* v___x_3824_; lean_object* v___x_3825_; 
v___x_3824_ = lean_box(0);
lean_inc(v_a_3731_);
lean_inc_ref(v_a_3730_);
lean_inc(v_a_3729_);
lean_inc_ref(v_a_3728_);
v___x_3825_ = lean_apply_6(v___y_3823_, v___x_3824_, v_a_3728_, v_a_3729_, v_a_3730_, v_a_3731_, lean_box(0));
v___y_3813_ = v___y_3820_;
v___y_3814_ = v___y_3821_;
v___y_3815_ = v___y_3822_;
v___y_3816_ = v___x_3825_;
goto v___jp_3812_;
}
v___jp_3826_:
{
lean_object* v___x_3831_; double v___x_3832_; double v___x_3833_; double v___x_3834_; double v___x_3835_; double v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; 
v___x_3831_ = lean_io_mono_nanos_now();
v___x_3832_ = lean_float_of_nat(v___y_3829_);
v___x_3833_ = lean_float_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0);
v___x_3834_ = lean_float_div(v___x_3832_, v___x_3833_);
v___x_3835_ = lean_float_of_nat(v___x_3831_);
v___x_3836_ = lean_float_div(v___x_3835_, v___x_3833_);
v___x_3837_ = lean_box_float(v___x_3834_);
v___x_3838_ = lean_box_float(v___x_3836_);
v___x_3839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3839_, 0, v___x_3837_);
lean_ctor_set(v___x_3839_, 1, v___x_3838_);
v___x_3840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3840_, 0, v_a_3830_);
lean_ctor_set(v___x_3840_, 1, v___x_3839_);
v___x_3841_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_cls_3743_, v___x_3746_, v___x_3786_, v_options_3734_, v___y_3827_, v___y_3828_, v___f_3745_, v___x_3840_, v_a_3728_, v_a_3729_, v_a_3730_, v_a_3731_);
return v___x_3841_;
}
v___jp_3842_:
{
lean_object* v___x_3847_; 
v___x_3847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3847_, 0, v_a_3846_);
v___y_3827_ = v___y_3843_;
v___y_3828_ = v___y_3844_;
v___y_3829_ = v___y_3845_;
v_a_3830_ = v___x_3847_;
goto v___jp_3826_;
}
v___jp_3848_:
{
lean_object* v___x_3853_; 
v___x_3853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3853_, 0, v_a_3852_);
v___y_3827_ = v___y_3849_;
v___y_3828_ = v___y_3850_;
v___y_3829_ = v___y_3851_;
v_a_3830_ = v___x_3853_;
goto v___jp_3826_;
}
v___jp_3854_:
{
if (lean_obj_tag(v___y_3858_) == 0)
{
lean_object* v_a_3859_; 
v_a_3859_ = lean_ctor_get(v___y_3858_, 0);
lean_inc(v_a_3859_);
lean_dec_ref_known(v___y_3858_, 1);
v___y_3843_ = v___y_3855_;
v___y_3844_ = v___y_3856_;
v___y_3845_ = v___y_3857_;
v_a_3846_ = v_a_3859_;
goto v___jp_3842_;
}
else
{
lean_object* v_a_3860_; 
v_a_3860_ = lean_ctor_get(v___y_3858_, 0);
lean_inc(v_a_3860_);
lean_dec_ref_known(v___y_3858_, 1);
v___y_3849_ = v___y_3855_;
v___y_3850_ = v___y_3856_;
v___y_3851_ = v___y_3857_;
v_a_3852_ = v_a_3860_;
goto v___jp_3848_;
}
}
v___jp_3861_:
{
lean_object* v___x_3866_; lean_object* v___x_3867_; 
v___x_3866_ = lean_box(0);
lean_inc(v_a_3731_);
lean_inc_ref(v_a_3730_);
lean_inc(v_a_3729_);
lean_inc_ref(v_a_3728_);
v___x_3867_ = lean_apply_6(v___y_3863_, v___x_3866_, v_a_3728_, v_a_3729_, v_a_3730_, v_a_3731_, lean_box(0));
v___y_3855_ = v___y_3862_;
v___y_3856_ = v___y_3864_;
v___y_3857_ = v___y_3865_;
v___y_3858_ = v___x_3867_;
goto v___jp_3854_;
}
v___jp_3868_:
{
lean_object* v___x_3870_; lean_object* v_a_3871_; lean_object* v___x_3872_; uint8_t v___x_3873_; 
v___x_3870_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3731_);
v_a_3871_ = lean_ctor_get(v___x_3870_, 0);
lean_inc(v_a_3871_);
lean_dec_ref(v___x_3870_);
v___x_3872_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3873_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1(v_options_3734_, v___x_3872_);
if (v___x_3873_ == 0)
{
lean_object* v___x_3874_; lean_object* v___x_3875_; 
v___x_3874_ = lean_io_mono_nanos_now();
lean_inc_ref(v_ctorVal_3727_);
v___x_3875_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3727_, v_a_3728_, v_a_3729_, v_a_3730_, v_a_3731_);
if (lean_obj_tag(v___x_3875_) == 0)
{
lean_object* v_a_3876_; 
v_a_3876_ = lean_ctor_get(v___x_3875_, 0);
lean_inc(v_a_3876_);
lean_dec_ref_known(v___x_3875_, 1);
if (lean_obj_tag(v_a_3876_) == 1)
{
lean_object* v_val_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___f_3880_; 
v_val_3877_ = lean_ctor_get(v_a_3876_, 0);
lean_inc_n(v_val_3877_, 2);
lean_dec_ref_known(v_a_3876_, 1);
v___x_3878_ = lean_box(v___x_3873_);
v___x_3879_ = lean_box(v___x_3746_);
lean_inc(v_levelParams_3736_);
lean_inc(v_name_3742_);
lean_inc_ref(v_ctorVal_3727_);
v___f_3880_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1___boxed), 12, 6);
lean_closure_set(v___f_3880_, 0, v_ctorVal_3727_);
lean_closure_set(v___f_3880_, 1, v_val_3877_);
lean_closure_set(v___f_3880_, 2, v_name_3742_);
lean_closure_set(v___f_3880_, 3, v_levelParams_3736_);
lean_closure_set(v___f_3880_, 4, v___x_3878_);
lean_closure_set(v___f_3880_, 5, v___x_3879_);
if (v_hasTrace_3741_ == 0)
{
lean_dec(v_val_3877_);
lean_dec(v_name_3742_);
lean_dec(v_levelParams_3736_);
lean_dec_ref(v_ctorVal_3727_);
v___y_3862_ = v___y_3869_;
v___y_3863_ = v___f_3880_;
v___y_3864_ = v_a_3871_;
v___y_3865_ = v___x_3874_;
goto v___jp_3861_;
}
else
{
lean_object* v___x_3881_; uint8_t v___x_3882_; 
v___x_3881_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_3882_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3740_, v_options_3734_, v___x_3881_);
if (v___x_3882_ == 0)
{
lean_dec(v_val_3877_);
lean_dec(v_name_3742_);
lean_dec(v_levelParams_3736_);
lean_dec_ref(v_ctorVal_3727_);
v___y_3862_ = v___y_3869_;
v___y_3863_ = v___f_3880_;
v___y_3864_ = v_a_3871_;
v___y_3865_ = v___x_3874_;
goto v___jp_3861_;
}
else
{
lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; 
lean_dec_ref(v___f_3880_);
v___x_3883_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
lean_inc(v_val_3877_);
v___x_3884_ = l_Lean_MessageData_ofExpr(v_val_3877_);
v___x_3885_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3885_, 0, v___x_3883_);
lean_ctor_set(v___x_3885_, 1, v___x_3884_);
v___x_3886_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_3743_, v___x_3885_, v_a_3728_, v_a_3729_, v_a_3730_, v_a_3731_);
if (lean_obj_tag(v___x_3886_) == 0)
{
lean_object* v_a_3887_; lean_object* v___x_3888_; 
v_a_3887_ = lean_ctor_get(v___x_3886_, 0);
lean_inc(v_a_3887_);
lean_dec_ref_known(v___x_3886_, 1);
v___x_3888_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(v_ctorVal_3727_, v_val_3877_, v_name_3742_, v_levelParams_3736_, v___x_3873_, v___x_3746_, v_a_3887_, v_a_3728_, v_a_3729_, v_a_3730_, v_a_3731_);
v___y_3855_ = v___y_3869_;
v___y_3856_ = v_a_3871_;
v___y_3857_ = v___x_3874_;
v___y_3858_ = v___x_3888_;
goto v___jp_3854_;
}
else
{
lean_dec(v_val_3877_);
lean_dec(v_name_3742_);
lean_dec(v_levelParams_3736_);
lean_dec_ref(v_ctorVal_3727_);
v___y_3855_ = v___y_3869_;
v___y_3856_ = v_a_3871_;
v___y_3857_ = v___x_3874_;
v___y_3858_ = v___x_3886_;
goto v___jp_3854_;
}
}
}
}
else
{
lean_object* v___x_3889_; 
lean_dec(v_a_3876_);
lean_dec(v_name_3742_);
lean_dec(v_levelParams_3736_);
lean_dec_ref(v_ctorVal_3727_);
v___x_3889_ = lean_box(0);
v___y_3843_ = v___y_3869_;
v___y_3844_ = v_a_3871_;
v___y_3845_ = v___x_3874_;
v_a_3846_ = v___x_3889_;
goto v___jp_3842_;
}
}
else
{
lean_object* v_a_3890_; 
lean_dec(v_name_3742_);
lean_dec(v_levelParams_3736_);
lean_dec_ref(v_ctorVal_3727_);
v_a_3890_ = lean_ctor_get(v___x_3875_, 0);
lean_inc(v_a_3890_);
lean_dec_ref_known(v___x_3875_, 1);
v___y_3849_ = v___y_3869_;
v___y_3850_ = v_a_3871_;
v___y_3851_ = v___x_3874_;
v_a_3852_ = v_a_3890_;
goto v___jp_3848_;
}
}
else
{
lean_object* v___x_3891_; lean_object* v___x_3892_; 
v___x_3891_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_ctorVal_3727_);
v___x_3892_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3727_, v_a_3728_, v_a_3729_, v_a_3730_, v_a_3731_);
if (lean_obj_tag(v___x_3892_) == 0)
{
lean_object* v_a_3893_; 
v_a_3893_ = lean_ctor_get(v___x_3892_, 0);
lean_inc(v_a_3893_);
lean_dec_ref_known(v___x_3892_, 1);
if (lean_obj_tag(v_a_3893_) == 1)
{
lean_object* v_val_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___f_3897_; 
v_val_3894_ = lean_ctor_get(v_a_3893_, 0);
lean_inc_n(v_val_3894_, 2);
lean_dec_ref_known(v_a_3893_, 1);
v___x_3895_ = lean_box(v___x_3744_);
v___x_3896_ = lean_box(v___x_3873_);
lean_inc(v_levelParams_3736_);
lean_inc(v_name_3742_);
lean_inc_ref(v_ctorVal_3727_);
v___f_3897_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1___boxed), 12, 6);
lean_closure_set(v___f_3897_, 0, v_ctorVal_3727_);
lean_closure_set(v___f_3897_, 1, v_val_3894_);
lean_closure_set(v___f_3897_, 2, v_name_3742_);
lean_closure_set(v___f_3897_, 3, v_levelParams_3736_);
lean_closure_set(v___f_3897_, 4, v___x_3895_);
lean_closure_set(v___f_3897_, 5, v___x_3896_);
if (v_hasTrace_3741_ == 0)
{
lean_dec(v_val_3894_);
lean_dec(v_name_3742_);
lean_dec(v_levelParams_3736_);
lean_dec_ref(v_ctorVal_3727_);
v___y_3820_ = v___y_3869_;
v___y_3821_ = v___x_3891_;
v___y_3822_ = v_a_3871_;
v___y_3823_ = v___f_3897_;
goto v___jp_3819_;
}
else
{
lean_object* v___x_3898_; uint8_t v___x_3899_; 
v___x_3898_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_3899_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3740_, v_options_3734_, v___x_3898_);
if (v___x_3899_ == 0)
{
lean_dec(v_val_3894_);
lean_dec(v_name_3742_);
lean_dec(v_levelParams_3736_);
lean_dec_ref(v_ctorVal_3727_);
v___y_3820_ = v___y_3869_;
v___y_3821_ = v___x_3891_;
v___y_3822_ = v_a_3871_;
v___y_3823_ = v___f_3897_;
goto v___jp_3819_;
}
else
{
lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; 
lean_dec_ref(v___f_3897_);
v___x_3900_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
lean_inc(v_val_3894_);
v___x_3901_ = l_Lean_MessageData_ofExpr(v_val_3894_);
v___x_3902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3902_, 0, v___x_3900_);
lean_ctor_set(v___x_3902_, 1, v___x_3901_);
v___x_3903_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_3743_, v___x_3902_, v_a_3728_, v_a_3729_, v_a_3730_, v_a_3731_);
if (lean_obj_tag(v___x_3903_) == 0)
{
lean_object* v_a_3904_; lean_object* v___x_3905_; 
v_a_3904_ = lean_ctor_get(v___x_3903_, 0);
lean_inc(v_a_3904_);
lean_dec_ref_known(v___x_3903_, 1);
v___x_3905_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(v_ctorVal_3727_, v_val_3894_, v_name_3742_, v_levelParams_3736_, v___x_3744_, v___x_3873_, v_a_3904_, v_a_3728_, v_a_3729_, v_a_3730_, v_a_3731_);
v___y_3813_ = v___y_3869_;
v___y_3814_ = v___x_3891_;
v___y_3815_ = v_a_3871_;
v___y_3816_ = v___x_3905_;
goto v___jp_3812_;
}
else
{
lean_dec(v_val_3894_);
lean_dec(v_name_3742_);
lean_dec(v_levelParams_3736_);
lean_dec_ref(v_ctorVal_3727_);
v___y_3813_ = v___y_3869_;
v___y_3814_ = v___x_3891_;
v___y_3815_ = v_a_3871_;
v___y_3816_ = v___x_3903_;
goto v___jp_3812_;
}
}
}
}
else
{
lean_object* v___x_3906_; 
lean_dec(v_a_3893_);
lean_dec(v_name_3742_);
lean_dec(v_levelParams_3736_);
lean_dec_ref(v_ctorVal_3727_);
v___x_3906_ = lean_box(0);
v___y_3807_ = v___y_3869_;
v___y_3808_ = v___x_3891_;
v___y_3809_ = v_a_3871_;
v_a_3810_ = v___x_3906_;
goto v___jp_3806_;
}
}
else
{
lean_object* v_a_3907_; 
lean_dec(v_name_3742_);
lean_dec(v_levelParams_3736_);
lean_dec_ref(v_ctorVal_3727_);
v_a_3907_ = lean_ctor_get(v___x_3892_, 0);
lean_inc(v_a_3907_);
lean_dec_ref_known(v___x_3892_, 1);
v___y_3801_ = v___y_3869_;
v___y_3802_ = v___x_3891_;
v___y_3803_ = v_a_3871_;
v_a_3804_ = v_a_3907_;
goto v___jp_3800_;
}
}
}
v___jp_3908_:
{
lean_object* v___x_3910_; uint8_t v___x_3911_; 
v___x_3910_ = l_Lean_trace_profiler;
v___x_3911_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1(v_options_3734_, v___x_3910_);
if (v___x_3911_ == 0)
{
lean_object* v___x_3912_; 
lean_dec_ref(v___f_3745_);
lean_inc_ref(v_ctorVal_3727_);
v___x_3912_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3727_, v_a_3728_, v_a_3729_, v_a_3730_, v_a_3731_);
if (lean_obj_tag(v___x_3912_) == 0)
{
lean_object* v_a_3913_; lean_object* v___x_3915_; uint8_t v_isShared_3916_; uint8_t v_isSharedCheck_3929_; 
v_a_3913_ = lean_ctor_get(v___x_3912_, 0);
v_isSharedCheck_3929_ = !lean_is_exclusive(v___x_3912_);
if (v_isSharedCheck_3929_ == 0)
{
v___x_3915_ = v___x_3912_;
v_isShared_3916_ = v_isSharedCheck_3929_;
goto v_resetjp_3914_;
}
else
{
lean_inc(v_a_3913_);
lean_dec(v___x_3912_);
v___x_3915_ = lean_box(0);
v_isShared_3916_ = v_isSharedCheck_3929_;
goto v_resetjp_3914_;
}
v_resetjp_3914_:
{
if (lean_obj_tag(v_a_3913_) == 1)
{
lean_del_object(v___x_3915_);
if (v_hasTrace_3741_ == 0)
{
lean_object* v_val_3917_; 
v_val_3917_ = lean_ctor_get(v_a_3913_, 0);
lean_inc(v_val_3917_);
lean_dec_ref_known(v_a_3913_, 1);
v___y_3748_ = v_val_3917_;
v___y_3749_ = v___x_3911_;
v___y_3750_ = v_a_3728_;
v___y_3751_ = v_a_3729_;
v___y_3752_ = v_a_3730_;
v___y_3753_ = v_a_3731_;
goto v___jp_3747_;
}
else
{
lean_object* v_val_3918_; lean_object* v___x_3919_; uint8_t v___x_3920_; 
v_val_3918_ = lean_ctor_get(v_a_3913_, 0);
lean_inc(v_val_3918_);
lean_dec_ref_known(v_a_3913_, 1);
v___x_3919_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_3920_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3740_, v_options_3734_, v___x_3919_);
if (v___x_3920_ == 0)
{
v___y_3748_ = v_val_3918_;
v___y_3749_ = v___x_3911_;
v___y_3750_ = v_a_3728_;
v___y_3751_ = v_a_3729_;
v___y_3752_ = v_a_3730_;
v___y_3753_ = v_a_3731_;
goto v___jp_3747_;
}
else
{
lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; 
v___x_3921_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
lean_inc(v_val_3918_);
v___x_3922_ = l_Lean_MessageData_ofExpr(v_val_3918_);
v___x_3923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3923_, 0, v___x_3921_);
lean_ctor_set(v___x_3923_, 1, v___x_3922_);
v___x_3924_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_3743_, v___x_3923_, v_a_3728_, v_a_3729_, v_a_3730_, v_a_3731_);
if (lean_obj_tag(v___x_3924_) == 0)
{
lean_dec_ref_known(v___x_3924_, 1);
v___y_3748_ = v_val_3918_;
v___y_3749_ = v___x_3911_;
v___y_3750_ = v_a_3728_;
v___y_3751_ = v_a_3729_;
v___y_3752_ = v_a_3730_;
v___y_3753_ = v_a_3731_;
goto v___jp_3747_;
}
else
{
lean_dec(v_val_3918_);
lean_dec(v_name_3742_);
lean_del_object(v___x_3738_);
lean_dec(v_levelParams_3736_);
lean_dec_ref(v_ctorVal_3727_);
return v___x_3924_;
}
}
}
}
else
{
lean_object* v___x_3925_; lean_object* v___x_3927_; 
lean_dec(v_a_3913_);
lean_dec(v_name_3742_);
lean_del_object(v___x_3738_);
lean_dec(v_levelParams_3736_);
lean_dec_ref(v_ctorVal_3727_);
v___x_3925_ = lean_box(0);
if (v_isShared_3916_ == 0)
{
lean_ctor_set(v___x_3915_, 0, v___x_3925_);
v___x_3927_ = v___x_3915_;
goto v_reusejp_3926_;
}
else
{
lean_object* v_reuseFailAlloc_3928_; 
v_reuseFailAlloc_3928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3928_, 0, v___x_3925_);
v___x_3927_ = v_reuseFailAlloc_3928_;
goto v_reusejp_3926_;
}
v_reusejp_3926_:
{
return v___x_3927_;
}
}
}
}
else
{
lean_object* v_a_3930_; lean_object* v___x_3932_; uint8_t v_isShared_3933_; uint8_t v_isSharedCheck_3937_; 
lean_dec(v_name_3742_);
lean_del_object(v___x_3738_);
lean_dec(v_levelParams_3736_);
lean_dec_ref(v_ctorVal_3727_);
v_a_3930_ = lean_ctor_get(v___x_3912_, 0);
v_isSharedCheck_3937_ = !lean_is_exclusive(v___x_3912_);
if (v_isSharedCheck_3937_ == 0)
{
v___x_3932_ = v___x_3912_;
v_isShared_3933_ = v_isSharedCheck_3937_;
goto v_resetjp_3931_;
}
else
{
lean_inc(v_a_3930_);
lean_dec(v___x_3912_);
v___x_3932_ = lean_box(0);
v_isShared_3933_ = v_isSharedCheck_3937_;
goto v_resetjp_3931_;
}
v_resetjp_3931_:
{
lean_object* v___x_3935_; 
if (v_isShared_3933_ == 0)
{
v___x_3935_ = v___x_3932_;
goto v_reusejp_3934_;
}
else
{
lean_object* v_reuseFailAlloc_3936_; 
v_reuseFailAlloc_3936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3936_, 0, v_a_3930_);
v___x_3935_ = v_reuseFailAlloc_3936_;
goto v_reusejp_3934_;
}
v_reusejp_3934_:
{
return v___x_3935_;
}
}
}
}
else
{
lean_del_object(v___x_3738_);
v___y_3869_ = v_a_3909_;
goto v___jp_3868_;
}
}
}
else
{
lean_object* v___x_3940_; 
lean_inc_ref(v_ctorVal_3727_);
v___x_3940_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3727_, v_a_3728_, v_a_3729_, v_a_3730_, v_a_3731_);
if (lean_obj_tag(v___x_3940_) == 0)
{
lean_object* v_a_3941_; lean_object* v___x_3943_; uint8_t v_isShared_3944_; uint8_t v_isSharedCheck_3994_; 
v_a_3941_ = lean_ctor_get(v___x_3940_, 0);
v_isSharedCheck_3994_ = !lean_is_exclusive(v___x_3940_);
if (v_isSharedCheck_3994_ == 0)
{
v___x_3943_ = v___x_3940_;
v_isShared_3944_ = v_isSharedCheck_3994_;
goto v_resetjp_3942_;
}
else
{
lean_inc(v_a_3941_);
lean_dec(v___x_3940_);
v___x_3943_ = lean_box(0);
v_isShared_3944_ = v_isSharedCheck_3994_;
goto v_resetjp_3942_;
}
v_resetjp_3942_:
{
if (lean_obj_tag(v_a_3941_) == 1)
{
lean_object* v_val_3945_; lean_object* v___y_3947_; lean_object* v___y_3948_; lean_object* v___y_3949_; lean_object* v___y_3950_; 
lean_del_object(v___x_3943_);
v_val_3945_ = lean_ctor_get(v_a_3941_, 0);
lean_inc(v_val_3945_);
lean_dec_ref_known(v_a_3941_, 1);
if (v_hasTrace_3741_ == 0)
{
v___y_3947_ = v_a_3728_;
v___y_3948_ = v_a_3729_;
v___y_3949_ = v_a_3730_;
v___y_3950_ = v_a_3731_;
goto v___jp_3946_;
}
else
{
lean_object* v___x_3984_; uint8_t v___x_3985_; 
v___x_3984_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_3985_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3740_, v_options_3734_, v___x_3984_);
if (v___x_3985_ == 0)
{
v___y_3947_ = v_a_3728_;
v___y_3948_ = v_a_3729_;
v___y_3949_ = v_a_3730_;
v___y_3950_ = v_a_3731_;
goto v___jp_3946_;
}
else
{
lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; 
v___x_3986_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
lean_inc(v_val_3945_);
v___x_3987_ = l_Lean_MessageData_ofExpr(v_val_3945_);
v___x_3988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3988_, 0, v___x_3986_);
lean_ctor_set(v___x_3988_, 1, v___x_3987_);
v___x_3989_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_3743_, v___x_3988_, v_a_3728_, v_a_3729_, v_a_3730_, v_a_3731_);
if (lean_obj_tag(v___x_3989_) == 0)
{
lean_dec_ref_known(v___x_3989_, 1);
v___y_3947_ = v_a_3728_;
v___y_3948_ = v_a_3729_;
v___y_3949_ = v_a_3730_;
v___y_3950_ = v_a_3731_;
goto v___jp_3946_;
}
else
{
lean_dec(v_val_3945_);
lean_dec(v_name_3742_);
lean_del_object(v___x_3738_);
lean_dec(v_levelParams_3736_);
lean_dec_ref(v_ctorVal_3727_);
return v___x_3989_;
}
}
}
v___jp_3946_:
{
lean_object* v___x_3951_; 
lean_inc(v_val_3945_);
v___x_3951_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3727_, v_val_3945_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_);
if (lean_obj_tag(v___x_3951_) == 0)
{
lean_object* v_a_3952_; lean_object* v___x_3953_; lean_object* v_a_3954_; lean_object* v___x_3955_; lean_object* v_a_3956_; lean_object* v___x_3958_; uint8_t v_isShared_3959_; uint8_t v_isSharedCheck_3975_; 
v_a_3952_ = lean_ctor_get(v___x_3951_, 0);
lean_inc(v_a_3952_);
lean_dec_ref_known(v___x_3951_, 1);
v___x_3953_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___redArg(v_val_3945_, v___y_3948_);
v_a_3954_ = lean_ctor_get(v___x_3953_, 0);
lean_inc(v_a_3954_);
lean_dec_ref(v___x_3953_);
v___x_3955_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___redArg(v_a_3952_, v___y_3948_);
v_a_3956_ = lean_ctor_get(v___x_3955_, 0);
v_isSharedCheck_3975_ = !lean_is_exclusive(v___x_3955_);
if (v_isSharedCheck_3975_ == 0)
{
v___x_3958_ = v___x_3955_;
v_isShared_3959_ = v_isSharedCheck_3975_;
goto v_resetjp_3957_;
}
else
{
lean_inc(v_a_3956_);
lean_dec(v___x_3955_);
v___x_3958_ = lean_box(0);
v_isShared_3959_ = v_isSharedCheck_3975_;
goto v_resetjp_3957_;
}
v_resetjp_3957_:
{
lean_object* v___x_3961_; 
lean_inc(v_name_3742_);
if (v_isShared_3739_ == 0)
{
lean_ctor_set(v___x_3738_, 2, v_a_3954_);
lean_ctor_set(v___x_3738_, 0, v_name_3742_);
v___x_3961_ = v___x_3738_;
goto v_reusejp_3960_;
}
else
{
lean_object* v_reuseFailAlloc_3974_; 
v_reuseFailAlloc_3974_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3974_, 0, v_name_3742_);
lean_ctor_set(v_reuseFailAlloc_3974_, 1, v_levelParams_3736_);
lean_ctor_set(v_reuseFailAlloc_3974_, 2, v_a_3954_);
v___x_3961_ = v_reuseFailAlloc_3974_;
goto v_reusejp_3960_;
}
v_reusejp_3960_:
{
lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3966_; 
v___x_3962_ = lean_box(0);
lean_inc(v_name_3742_);
v___x_3963_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3963_, 0, v_name_3742_);
lean_ctor_set(v___x_3963_, 1, v___x_3962_);
v___x_3964_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3964_, 0, v___x_3961_);
lean_ctor_set(v___x_3964_, 1, v_a_3956_);
lean_ctor_set(v___x_3964_, 2, v___x_3963_);
if (v_isShared_3959_ == 0)
{
lean_ctor_set_tag(v___x_3958_, 2);
lean_ctor_set(v___x_3958_, 0, v___x_3964_);
v___x_3966_ = v___x_3958_;
goto v_reusejp_3965_;
}
else
{
lean_object* v_reuseFailAlloc_3973_; 
v_reuseFailAlloc_3973_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3973_, 0, v___x_3964_);
v___x_3966_ = v_reuseFailAlloc_3973_;
goto v_reusejp_3965_;
}
v_reusejp_3965_:
{
uint8_t v___x_3967_; lean_object* v___x_3968_; 
v___x_3967_ = 0;
v___x_3968_ = l_Lean_addDecl(v___x_3966_, v___x_3967_, v___y_3949_, v___y_3950_);
if (lean_obj_tag(v___x_3968_) == 0)
{
lean_object* v___x_3969_; uint8_t v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; 
lean_dec_ref_known(v___x_3968_, 1);
v___x_3969_ = l_Lean_Meta_simpExtension;
v___x_3970_ = 0;
v___x_3971_ = lean_unsigned_to_nat(1000u);
v___x_3972_ = l_Lean_Meta_addSimpTheorem(v___x_3969_, v_name_3742_, v___x_3744_, v___x_3967_, v___x_3970_, v___x_3971_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_);
return v___x_3972_;
}
else
{
lean_dec(v_name_3742_);
return v___x_3968_;
}
}
}
}
}
else
{
lean_object* v_a_3976_; lean_object* v___x_3978_; uint8_t v_isShared_3979_; uint8_t v_isSharedCheck_3983_; 
lean_dec(v_val_3945_);
lean_dec(v_name_3742_);
lean_del_object(v___x_3738_);
lean_dec(v_levelParams_3736_);
v_a_3976_ = lean_ctor_get(v___x_3951_, 0);
v_isSharedCheck_3983_ = !lean_is_exclusive(v___x_3951_);
if (v_isSharedCheck_3983_ == 0)
{
v___x_3978_ = v___x_3951_;
v_isShared_3979_ = v_isSharedCheck_3983_;
goto v_resetjp_3977_;
}
else
{
lean_inc(v_a_3976_);
lean_dec(v___x_3951_);
v___x_3978_ = lean_box(0);
v_isShared_3979_ = v_isSharedCheck_3983_;
goto v_resetjp_3977_;
}
v_resetjp_3977_:
{
lean_object* v___x_3981_; 
if (v_isShared_3979_ == 0)
{
v___x_3981_ = v___x_3978_;
goto v_reusejp_3980_;
}
else
{
lean_object* v_reuseFailAlloc_3982_; 
v_reuseFailAlloc_3982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3982_, 0, v_a_3976_);
v___x_3981_ = v_reuseFailAlloc_3982_;
goto v_reusejp_3980_;
}
v_reusejp_3980_:
{
return v___x_3981_;
}
}
}
}
}
else
{
lean_object* v___x_3990_; lean_object* v___x_3992_; 
lean_dec(v_a_3941_);
lean_dec(v_name_3742_);
lean_del_object(v___x_3738_);
lean_dec(v_levelParams_3736_);
lean_dec_ref(v_ctorVal_3727_);
v___x_3990_ = lean_box(0);
if (v_isShared_3944_ == 0)
{
lean_ctor_set(v___x_3943_, 0, v___x_3990_);
v___x_3992_ = v___x_3943_;
goto v_reusejp_3991_;
}
else
{
lean_object* v_reuseFailAlloc_3993_; 
v_reuseFailAlloc_3993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3993_, 0, v___x_3990_);
v___x_3992_ = v_reuseFailAlloc_3993_;
goto v_reusejp_3991_;
}
v_reusejp_3991_:
{
return v___x_3992_;
}
}
}
}
else
{
lean_object* v_a_3995_; lean_object* v___x_3997_; uint8_t v_isShared_3998_; uint8_t v_isSharedCheck_4002_; 
lean_dec(v_name_3742_);
lean_del_object(v___x_3738_);
lean_dec(v_levelParams_3736_);
lean_dec_ref(v_ctorVal_3727_);
v_a_3995_ = lean_ctor_get(v___x_3940_, 0);
v_isSharedCheck_4002_ = !lean_is_exclusive(v___x_3940_);
if (v_isSharedCheck_4002_ == 0)
{
v___x_3997_ = v___x_3940_;
v_isShared_3998_ = v_isSharedCheck_4002_;
goto v_resetjp_3996_;
}
else
{
lean_inc(v_a_3995_);
lean_dec(v___x_3940_);
v___x_3997_ = lean_box(0);
v_isShared_3998_ = v_isSharedCheck_4002_;
goto v_resetjp_3996_;
}
v_resetjp_3996_:
{
lean_object* v___x_4000_; 
if (v_isShared_3998_ == 0)
{
v___x_4000_ = v___x_3997_;
goto v_reusejp_3999_;
}
else
{
lean_object* v_reuseFailAlloc_4001_; 
v_reuseFailAlloc_4001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4001_, 0, v_a_3995_);
v___x_4000_ = v_reuseFailAlloc_4001_;
goto v_reusejp_3999_;
}
v_reusejp_3999_:
{
return v___x_4000_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___boxed(lean_object* v_ctorVal_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_, lean_object* v_a_4009_, lean_object* v_a_4010_){
_start:
{
lean_object* v_res_4011_; 
v_res_4011_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(v_ctorVal_4005_, v_a_4006_, v_a_4007_, v_a_4008_, v_a_4009_);
lean_dec(v_a_4009_);
lean_dec_ref(v_a_4008_);
lean_dec(v_a_4007_);
lean_dec_ref(v_a_4006_);
return v_res_4011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(lean_object* v_name_4012_, lean_object* v_decl_4013_, lean_object* v_ref_4014_){
_start:
{
lean_object* v_defValue_4016_; lean_object* v_descr_4017_; lean_object* v_deprecation_x3f_4018_; lean_object* v___x_4019_; uint8_t v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; 
v_defValue_4016_ = lean_ctor_get(v_decl_4013_, 0);
v_descr_4017_ = lean_ctor_get(v_decl_4013_, 1);
v_deprecation_x3f_4018_ = lean_ctor_get(v_decl_4013_, 2);
v___x_4019_ = lean_alloc_ctor(1, 0, 1);
v___x_4020_ = lean_unbox(v_defValue_4016_);
lean_ctor_set_uint8(v___x_4019_, 0, v___x_4020_);
lean_inc(v_deprecation_x3f_4018_);
lean_inc_ref(v_descr_4017_);
lean_inc_n(v_name_4012_, 2);
v___x_4021_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4021_, 0, v_name_4012_);
lean_ctor_set(v___x_4021_, 1, v_ref_4014_);
lean_ctor_set(v___x_4021_, 2, v___x_4019_);
lean_ctor_set(v___x_4021_, 3, v_descr_4017_);
lean_ctor_set(v___x_4021_, 4, v_deprecation_x3f_4018_);
v___x_4022_ = lean_register_option(v_name_4012_, v___x_4021_);
if (lean_obj_tag(v___x_4022_) == 0)
{
lean_object* v___x_4024_; uint8_t v_isShared_4025_; uint8_t v_isSharedCheck_4030_; 
v_isSharedCheck_4030_ = !lean_is_exclusive(v___x_4022_);
if (v_isSharedCheck_4030_ == 0)
{
lean_object* v_unused_4031_; 
v_unused_4031_ = lean_ctor_get(v___x_4022_, 0);
lean_dec(v_unused_4031_);
v___x_4024_ = v___x_4022_;
v_isShared_4025_ = v_isSharedCheck_4030_;
goto v_resetjp_4023_;
}
else
{
lean_dec(v___x_4022_);
v___x_4024_ = lean_box(0);
v_isShared_4025_ = v_isSharedCheck_4030_;
goto v_resetjp_4023_;
}
v_resetjp_4023_:
{
lean_object* v___x_4026_; lean_object* v___x_4028_; 
lean_inc(v_defValue_4016_);
v___x_4026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4026_, 0, v_name_4012_);
lean_ctor_set(v___x_4026_, 1, v_defValue_4016_);
if (v_isShared_4025_ == 0)
{
lean_ctor_set(v___x_4024_, 0, v___x_4026_);
v___x_4028_ = v___x_4024_;
goto v_reusejp_4027_;
}
else
{
lean_object* v_reuseFailAlloc_4029_; 
v_reuseFailAlloc_4029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4029_, 0, v___x_4026_);
v___x_4028_ = v_reuseFailAlloc_4029_;
goto v_reusejp_4027_;
}
v_reusejp_4027_:
{
return v___x_4028_;
}
}
}
else
{
lean_object* v_a_4032_; lean_object* v___x_4034_; uint8_t v_isShared_4035_; uint8_t v_isSharedCheck_4039_; 
lean_dec(v_name_4012_);
v_a_4032_ = lean_ctor_get(v___x_4022_, 0);
v_isSharedCheck_4039_ = !lean_is_exclusive(v___x_4022_);
if (v_isSharedCheck_4039_ == 0)
{
v___x_4034_ = v___x_4022_;
v_isShared_4035_ = v_isSharedCheck_4039_;
goto v_resetjp_4033_;
}
else
{
lean_inc(v_a_4032_);
lean_dec(v___x_4022_);
v___x_4034_ = lean_box(0);
v_isShared_4035_ = v_isSharedCheck_4039_;
goto v_resetjp_4033_;
}
v_resetjp_4033_:
{
lean_object* v___x_4037_; 
if (v_isShared_4035_ == 0)
{
v___x_4037_ = v___x_4034_;
goto v_reusejp_4036_;
}
else
{
lean_object* v_reuseFailAlloc_4038_; 
v_reuseFailAlloc_4038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4038_, 0, v_a_4032_);
v___x_4037_ = v_reuseFailAlloc_4038_;
goto v_reusejp_4036_;
}
v_reusejp_4036_:
{
return v___x_4037_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_4040_, lean_object* v_decl_4041_, lean_object* v_ref_4042_, lean_object* v_a_4043_){
_start:
{
lean_object* v_res_4044_; 
v_res_4044_ = l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(v_name_4040_, v_decl_4041_, v_ref_4042_);
lean_dec_ref(v_decl_4041_);
return v_res_4044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; 
v___x_4059_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_));
v___x_4060_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_));
v___x_4061_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_));
v___x_4062_ = l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(v___x_4059_, v___x_4060_, v___x_4061_);
return v___x_4062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4____boxed(lean_object* v_a_4063_){
_start:
{
lean_object* v_res_4064_; 
v_res_4064_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_();
return v_res_4064_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(lean_object* v___y_4065_, uint8_t v_isExporting_4066_, lean_object* v___x_4067_, lean_object* v___y_4068_, lean_object* v___x_4069_, lean_object* v_a_x3f_4070_){
_start:
{
lean_object* v___x_4072_; lean_object* v_env_4073_; lean_object* v_nextMacroScope_4074_; lean_object* v_ngen_4075_; lean_object* v_auxDeclNGen_4076_; lean_object* v_traceState_4077_; lean_object* v_messages_4078_; lean_object* v_infoState_4079_; lean_object* v_snapshotTasks_4080_; lean_object* v___x_4082_; uint8_t v_isShared_4083_; uint8_t v_isSharedCheck_4105_; 
v___x_4072_ = lean_st_ref_take(v___y_4065_);
v_env_4073_ = lean_ctor_get(v___x_4072_, 0);
v_nextMacroScope_4074_ = lean_ctor_get(v___x_4072_, 1);
v_ngen_4075_ = lean_ctor_get(v___x_4072_, 2);
v_auxDeclNGen_4076_ = lean_ctor_get(v___x_4072_, 3);
v_traceState_4077_ = lean_ctor_get(v___x_4072_, 4);
v_messages_4078_ = lean_ctor_get(v___x_4072_, 6);
v_infoState_4079_ = lean_ctor_get(v___x_4072_, 7);
v_snapshotTasks_4080_ = lean_ctor_get(v___x_4072_, 8);
v_isSharedCheck_4105_ = !lean_is_exclusive(v___x_4072_);
if (v_isSharedCheck_4105_ == 0)
{
lean_object* v_unused_4106_; 
v_unused_4106_ = lean_ctor_get(v___x_4072_, 5);
lean_dec(v_unused_4106_);
v___x_4082_ = v___x_4072_;
v_isShared_4083_ = v_isSharedCheck_4105_;
goto v_resetjp_4081_;
}
else
{
lean_inc(v_snapshotTasks_4080_);
lean_inc(v_infoState_4079_);
lean_inc(v_messages_4078_);
lean_inc(v_traceState_4077_);
lean_inc(v_auxDeclNGen_4076_);
lean_inc(v_ngen_4075_);
lean_inc(v_nextMacroScope_4074_);
lean_inc(v_env_4073_);
lean_dec(v___x_4072_);
v___x_4082_ = lean_box(0);
v_isShared_4083_ = v_isSharedCheck_4105_;
goto v_resetjp_4081_;
}
v_resetjp_4081_:
{
lean_object* v___x_4084_; lean_object* v___x_4086_; 
v___x_4084_ = l_Lean_Environment_setExporting(v_env_4073_, v_isExporting_4066_);
if (v_isShared_4083_ == 0)
{
lean_ctor_set(v___x_4082_, 5, v___x_4067_);
lean_ctor_set(v___x_4082_, 0, v___x_4084_);
v___x_4086_ = v___x_4082_;
goto v_reusejp_4085_;
}
else
{
lean_object* v_reuseFailAlloc_4104_; 
v_reuseFailAlloc_4104_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4104_, 0, v___x_4084_);
lean_ctor_set(v_reuseFailAlloc_4104_, 1, v_nextMacroScope_4074_);
lean_ctor_set(v_reuseFailAlloc_4104_, 2, v_ngen_4075_);
lean_ctor_set(v_reuseFailAlloc_4104_, 3, v_auxDeclNGen_4076_);
lean_ctor_set(v_reuseFailAlloc_4104_, 4, v_traceState_4077_);
lean_ctor_set(v_reuseFailAlloc_4104_, 5, v___x_4067_);
lean_ctor_set(v_reuseFailAlloc_4104_, 6, v_messages_4078_);
lean_ctor_set(v_reuseFailAlloc_4104_, 7, v_infoState_4079_);
lean_ctor_set(v_reuseFailAlloc_4104_, 8, v_snapshotTasks_4080_);
v___x_4086_ = v_reuseFailAlloc_4104_;
goto v_reusejp_4085_;
}
v_reusejp_4085_:
{
lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v_mctx_4089_; lean_object* v_zetaDeltaFVarIds_4090_; lean_object* v_postponed_4091_; lean_object* v_diag_4092_; lean_object* v___x_4094_; uint8_t v_isShared_4095_; uint8_t v_isSharedCheck_4102_; 
v___x_4087_ = lean_st_ref_set(v___y_4065_, v___x_4086_);
v___x_4088_ = lean_st_ref_take(v___y_4068_);
v_mctx_4089_ = lean_ctor_get(v___x_4088_, 0);
v_zetaDeltaFVarIds_4090_ = lean_ctor_get(v___x_4088_, 2);
v_postponed_4091_ = lean_ctor_get(v___x_4088_, 3);
v_diag_4092_ = lean_ctor_get(v___x_4088_, 4);
v_isSharedCheck_4102_ = !lean_is_exclusive(v___x_4088_);
if (v_isSharedCheck_4102_ == 0)
{
lean_object* v_unused_4103_; 
v_unused_4103_ = lean_ctor_get(v___x_4088_, 1);
lean_dec(v_unused_4103_);
v___x_4094_ = v___x_4088_;
v_isShared_4095_ = v_isSharedCheck_4102_;
goto v_resetjp_4093_;
}
else
{
lean_inc(v_diag_4092_);
lean_inc(v_postponed_4091_);
lean_inc(v_zetaDeltaFVarIds_4090_);
lean_inc(v_mctx_4089_);
lean_dec(v___x_4088_);
v___x_4094_ = lean_box(0);
v_isShared_4095_ = v_isSharedCheck_4102_;
goto v_resetjp_4093_;
}
v_resetjp_4093_:
{
lean_object* v___x_4097_; 
if (v_isShared_4095_ == 0)
{
lean_ctor_set(v___x_4094_, 1, v___x_4069_);
v___x_4097_ = v___x_4094_;
goto v_reusejp_4096_;
}
else
{
lean_object* v_reuseFailAlloc_4101_; 
v_reuseFailAlloc_4101_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4101_, 0, v_mctx_4089_);
lean_ctor_set(v_reuseFailAlloc_4101_, 1, v___x_4069_);
lean_ctor_set(v_reuseFailAlloc_4101_, 2, v_zetaDeltaFVarIds_4090_);
lean_ctor_set(v_reuseFailAlloc_4101_, 3, v_postponed_4091_);
lean_ctor_set(v_reuseFailAlloc_4101_, 4, v_diag_4092_);
v___x_4097_ = v_reuseFailAlloc_4101_;
goto v_reusejp_4096_;
}
v_reusejp_4096_:
{
lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; 
v___x_4098_ = lean_st_ref_set(v___y_4068_, v___x_4097_);
v___x_4099_ = lean_box(0);
v___x_4100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4100_, 0, v___x_4099_);
return v___x_4100_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0___boxed(lean_object* v___y_4107_, lean_object* v_isExporting_4108_, lean_object* v___x_4109_, lean_object* v___y_4110_, lean_object* v___x_4111_, lean_object* v_a_x3f_4112_, lean_object* v___y_4113_){
_start:
{
uint8_t v_isExporting_boxed_4114_; lean_object* v_res_4115_; 
v_isExporting_boxed_4114_ = lean_unbox(v_isExporting_4108_);
v_res_4115_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(v___y_4107_, v_isExporting_boxed_4114_, v___x_4109_, v___y_4110_, v___x_4111_, v_a_x3f_4112_);
lean_dec(v_a_x3f_4112_);
lean_dec(v___y_4110_);
lean_dec(v___y_4107_);
return v_res_4115_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_4116_; 
v___x_4116_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4116_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4117_; lean_object* v___x_4118_; 
v___x_4117_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0);
v___x_4118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4118_, 0, v___x_4117_);
return v___x_4118_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_4119_; lean_object* v___x_4120_; 
v___x_4119_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1);
v___x_4120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4120_, 0, v___x_4119_);
lean_ctor_set(v___x_4120_, 1, v___x_4119_);
return v___x_4120_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_4121_; lean_object* v___x_4122_; 
v___x_4121_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1);
v___x_4122_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4122_, 0, v___x_4121_);
lean_ctor_set(v___x_4122_, 1, v___x_4121_);
lean_ctor_set(v___x_4122_, 2, v___x_4121_);
lean_ctor_set(v___x_4122_, 3, v___x_4121_);
lean_ctor_set(v___x_4122_, 4, v___x_4121_);
lean_ctor_set(v___x_4122_, 5, v___x_4121_);
return v___x_4122_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(lean_object* v_x_4123_, uint8_t v_isExporting_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_){
_start:
{
lean_object* v___x_4130_; lean_object* v_env_4131_; uint8_t v_isExporting_4132_; uint8_t v___y_4199_; lean_object* v___x_4201_; uint8_t v_isModule_4202_; uint8_t v___x_4203_; 
v___x_4130_ = lean_st_ref_get(v___y_4128_);
v_env_4131_ = lean_ctor_get(v___x_4130_, 0);
lean_inc_ref(v_env_4131_);
lean_dec(v___x_4130_);
v_isExporting_4132_ = lean_ctor_get_uint8(v_env_4131_, sizeof(void*)*8);
v___x_4201_ = l_Lean_Environment_header(v_env_4131_);
lean_dec_ref(v_env_4131_);
v_isModule_4202_ = lean_ctor_get_uint8(v___x_4201_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4201_);
v___x_4203_ = lean_bool_not(v_isModule_4202_);
if (v___x_4203_ == 0)
{
if (v_isExporting_4132_ == 0)
{
if (v_isExporting_4124_ == 0)
{
lean_object* v___x_4204_; 
lean_inc(v___y_4128_);
lean_inc_ref(v___y_4127_);
lean_inc(v___y_4126_);
lean_inc_ref(v___y_4125_);
v___x_4204_ = lean_apply_5(v_x_4123_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, lean_box(0));
return v___x_4204_;
}
else
{
goto v___jp_4133_;
}
}
else
{
v___y_4199_ = v_isExporting_4124_;
goto v___jp_4198_;
}
}
else
{
v___y_4199_ = v___x_4203_;
goto v___jp_4198_;
}
v___jp_4133_:
{
lean_object* v___x_4134_; lean_object* v_env_4135_; lean_object* v_nextMacroScope_4136_; lean_object* v_ngen_4137_; lean_object* v_auxDeclNGen_4138_; lean_object* v_traceState_4139_; lean_object* v_messages_4140_; lean_object* v_infoState_4141_; lean_object* v_snapshotTasks_4142_; lean_object* v___x_4144_; uint8_t v_isShared_4145_; uint8_t v_isSharedCheck_4196_; 
v___x_4134_ = lean_st_ref_take(v___y_4128_);
v_env_4135_ = lean_ctor_get(v___x_4134_, 0);
v_nextMacroScope_4136_ = lean_ctor_get(v___x_4134_, 1);
v_ngen_4137_ = lean_ctor_get(v___x_4134_, 2);
v_auxDeclNGen_4138_ = lean_ctor_get(v___x_4134_, 3);
v_traceState_4139_ = lean_ctor_get(v___x_4134_, 4);
v_messages_4140_ = lean_ctor_get(v___x_4134_, 6);
v_infoState_4141_ = lean_ctor_get(v___x_4134_, 7);
v_snapshotTasks_4142_ = lean_ctor_get(v___x_4134_, 8);
v_isSharedCheck_4196_ = !lean_is_exclusive(v___x_4134_);
if (v_isSharedCheck_4196_ == 0)
{
lean_object* v_unused_4197_; 
v_unused_4197_ = lean_ctor_get(v___x_4134_, 5);
lean_dec(v_unused_4197_);
v___x_4144_ = v___x_4134_;
v_isShared_4145_ = v_isSharedCheck_4196_;
goto v_resetjp_4143_;
}
else
{
lean_inc(v_snapshotTasks_4142_);
lean_inc(v_infoState_4141_);
lean_inc(v_messages_4140_);
lean_inc(v_traceState_4139_);
lean_inc(v_auxDeclNGen_4138_);
lean_inc(v_ngen_4137_);
lean_inc(v_nextMacroScope_4136_);
lean_inc(v_env_4135_);
lean_dec(v___x_4134_);
v___x_4144_ = lean_box(0);
v_isShared_4145_ = v_isSharedCheck_4196_;
goto v_resetjp_4143_;
}
v_resetjp_4143_:
{
lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4149_; 
v___x_4146_ = l_Lean_Environment_setExporting(v_env_4135_, v_isExporting_4124_);
v___x_4147_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2);
if (v_isShared_4145_ == 0)
{
lean_ctor_set(v___x_4144_, 5, v___x_4147_);
lean_ctor_set(v___x_4144_, 0, v___x_4146_);
v___x_4149_ = v___x_4144_;
goto v_reusejp_4148_;
}
else
{
lean_object* v_reuseFailAlloc_4195_; 
v_reuseFailAlloc_4195_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4195_, 0, v___x_4146_);
lean_ctor_set(v_reuseFailAlloc_4195_, 1, v_nextMacroScope_4136_);
lean_ctor_set(v_reuseFailAlloc_4195_, 2, v_ngen_4137_);
lean_ctor_set(v_reuseFailAlloc_4195_, 3, v_auxDeclNGen_4138_);
lean_ctor_set(v_reuseFailAlloc_4195_, 4, v_traceState_4139_);
lean_ctor_set(v_reuseFailAlloc_4195_, 5, v___x_4147_);
lean_ctor_set(v_reuseFailAlloc_4195_, 6, v_messages_4140_);
lean_ctor_set(v_reuseFailAlloc_4195_, 7, v_infoState_4141_);
lean_ctor_set(v_reuseFailAlloc_4195_, 8, v_snapshotTasks_4142_);
v___x_4149_ = v_reuseFailAlloc_4195_;
goto v_reusejp_4148_;
}
v_reusejp_4148_:
{
lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v_mctx_4152_; lean_object* v_zetaDeltaFVarIds_4153_; lean_object* v_postponed_4154_; lean_object* v_diag_4155_; lean_object* v___x_4157_; uint8_t v_isShared_4158_; uint8_t v_isSharedCheck_4193_; 
v___x_4150_ = lean_st_ref_set(v___y_4128_, v___x_4149_);
v___x_4151_ = lean_st_ref_take(v___y_4126_);
v_mctx_4152_ = lean_ctor_get(v___x_4151_, 0);
v_zetaDeltaFVarIds_4153_ = lean_ctor_get(v___x_4151_, 2);
v_postponed_4154_ = lean_ctor_get(v___x_4151_, 3);
v_diag_4155_ = lean_ctor_get(v___x_4151_, 4);
v_isSharedCheck_4193_ = !lean_is_exclusive(v___x_4151_);
if (v_isSharedCheck_4193_ == 0)
{
lean_object* v_unused_4194_; 
v_unused_4194_ = lean_ctor_get(v___x_4151_, 1);
lean_dec(v_unused_4194_);
v___x_4157_ = v___x_4151_;
v_isShared_4158_ = v_isSharedCheck_4193_;
goto v_resetjp_4156_;
}
else
{
lean_inc(v_diag_4155_);
lean_inc(v_postponed_4154_);
lean_inc(v_zetaDeltaFVarIds_4153_);
lean_inc(v_mctx_4152_);
lean_dec(v___x_4151_);
v___x_4157_ = lean_box(0);
v_isShared_4158_ = v_isSharedCheck_4193_;
goto v_resetjp_4156_;
}
v_resetjp_4156_:
{
lean_object* v___x_4159_; lean_object* v___x_4161_; 
v___x_4159_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3);
if (v_isShared_4158_ == 0)
{
lean_ctor_set(v___x_4157_, 1, v___x_4159_);
v___x_4161_ = v___x_4157_;
goto v_reusejp_4160_;
}
else
{
lean_object* v_reuseFailAlloc_4192_; 
v_reuseFailAlloc_4192_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4192_, 0, v_mctx_4152_);
lean_ctor_set(v_reuseFailAlloc_4192_, 1, v___x_4159_);
lean_ctor_set(v_reuseFailAlloc_4192_, 2, v_zetaDeltaFVarIds_4153_);
lean_ctor_set(v_reuseFailAlloc_4192_, 3, v_postponed_4154_);
lean_ctor_set(v_reuseFailAlloc_4192_, 4, v_diag_4155_);
v___x_4161_ = v_reuseFailAlloc_4192_;
goto v_reusejp_4160_;
}
v_reusejp_4160_:
{
lean_object* v___x_4162_; lean_object* v_r_4163_; 
v___x_4162_ = lean_st_ref_set(v___y_4126_, v___x_4161_);
lean_inc(v___y_4128_);
lean_inc_ref(v___y_4127_);
lean_inc(v___y_4126_);
lean_inc_ref(v___y_4125_);
v_r_4163_ = lean_apply_5(v_x_4123_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, lean_box(0));
if (lean_obj_tag(v_r_4163_) == 0)
{
lean_object* v_a_4164_; lean_object* v___x_4166_; uint8_t v_isShared_4167_; uint8_t v_isSharedCheck_4180_; 
v_a_4164_ = lean_ctor_get(v_r_4163_, 0);
v_isSharedCheck_4180_ = !lean_is_exclusive(v_r_4163_);
if (v_isSharedCheck_4180_ == 0)
{
v___x_4166_ = v_r_4163_;
v_isShared_4167_ = v_isSharedCheck_4180_;
goto v_resetjp_4165_;
}
else
{
lean_inc(v_a_4164_);
lean_dec(v_r_4163_);
v___x_4166_ = lean_box(0);
v_isShared_4167_ = v_isSharedCheck_4180_;
goto v_resetjp_4165_;
}
v_resetjp_4165_:
{
lean_object* v___x_4169_; 
lean_inc(v_a_4164_);
if (v_isShared_4167_ == 0)
{
lean_ctor_set_tag(v___x_4166_, 1);
v___x_4169_ = v___x_4166_;
goto v_reusejp_4168_;
}
else
{
lean_object* v_reuseFailAlloc_4179_; 
v_reuseFailAlloc_4179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4179_, 0, v_a_4164_);
v___x_4169_ = v_reuseFailAlloc_4179_;
goto v_reusejp_4168_;
}
v_reusejp_4168_:
{
lean_object* v___x_4170_; lean_object* v___x_4172_; uint8_t v_isShared_4173_; uint8_t v_isSharedCheck_4177_; 
v___x_4170_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(v___y_4128_, v_isExporting_4132_, v___x_4147_, v___y_4126_, v___x_4159_, v___x_4169_);
lean_dec_ref(v___x_4169_);
v_isSharedCheck_4177_ = !lean_is_exclusive(v___x_4170_);
if (v_isSharedCheck_4177_ == 0)
{
lean_object* v_unused_4178_; 
v_unused_4178_ = lean_ctor_get(v___x_4170_, 0);
lean_dec(v_unused_4178_);
v___x_4172_ = v___x_4170_;
v_isShared_4173_ = v_isSharedCheck_4177_;
goto v_resetjp_4171_;
}
else
{
lean_dec(v___x_4170_);
v___x_4172_ = lean_box(0);
v_isShared_4173_ = v_isSharedCheck_4177_;
goto v_resetjp_4171_;
}
v_resetjp_4171_:
{
lean_object* v___x_4175_; 
if (v_isShared_4173_ == 0)
{
lean_ctor_set(v___x_4172_, 0, v_a_4164_);
v___x_4175_ = v___x_4172_;
goto v_reusejp_4174_;
}
else
{
lean_object* v_reuseFailAlloc_4176_; 
v_reuseFailAlloc_4176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4176_, 0, v_a_4164_);
v___x_4175_ = v_reuseFailAlloc_4176_;
goto v_reusejp_4174_;
}
v_reusejp_4174_:
{
return v___x_4175_;
}
}
}
}
}
else
{
lean_object* v_a_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4185_; uint8_t v_isShared_4186_; uint8_t v_isSharedCheck_4190_; 
v_a_4181_ = lean_ctor_get(v_r_4163_, 0);
lean_inc(v_a_4181_);
lean_dec_ref_known(v_r_4163_, 1);
v___x_4182_ = lean_box(0);
v___x_4183_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(v___y_4128_, v_isExporting_4132_, v___x_4147_, v___y_4126_, v___x_4159_, v___x_4182_);
v_isSharedCheck_4190_ = !lean_is_exclusive(v___x_4183_);
if (v_isSharedCheck_4190_ == 0)
{
lean_object* v_unused_4191_; 
v_unused_4191_ = lean_ctor_get(v___x_4183_, 0);
lean_dec(v_unused_4191_);
v___x_4185_ = v___x_4183_;
v_isShared_4186_ = v_isSharedCheck_4190_;
goto v_resetjp_4184_;
}
else
{
lean_dec(v___x_4183_);
v___x_4185_ = lean_box(0);
v_isShared_4186_ = v_isSharedCheck_4190_;
goto v_resetjp_4184_;
}
v_resetjp_4184_:
{
lean_object* v___x_4188_; 
if (v_isShared_4186_ == 0)
{
lean_ctor_set_tag(v___x_4185_, 1);
lean_ctor_set(v___x_4185_, 0, v_a_4181_);
v___x_4188_ = v___x_4185_;
goto v_reusejp_4187_;
}
else
{
lean_object* v_reuseFailAlloc_4189_; 
v_reuseFailAlloc_4189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4189_, 0, v_a_4181_);
v___x_4188_ = v_reuseFailAlloc_4189_;
goto v_reusejp_4187_;
}
v_reusejp_4187_:
{
return v___x_4188_;
}
}
}
}
}
}
}
}
v___jp_4198_:
{
if (v___y_4199_ == 0)
{
goto v___jp_4133_;
}
else
{
lean_object* v___x_4200_; 
lean_inc(v___y_4128_);
lean_inc_ref(v___y_4127_);
lean_inc(v___y_4126_);
lean_inc_ref(v___y_4125_);
v___x_4200_ = lean_apply_5(v_x_4123_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, lean_box(0));
return v___x_4200_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___boxed(lean_object* v_x_4205_, lean_object* v_isExporting_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_){
_start:
{
uint8_t v_isExporting_boxed_4212_; lean_object* v_res_4213_; 
v_isExporting_boxed_4212_ = lean_unbox(v_isExporting_4206_);
v_res_4213_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(v_x_4205_, v_isExporting_boxed_4212_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_);
lean_dec(v___y_4210_);
lean_dec_ref(v___y_4209_);
lean_dec(v___y_4208_);
lean_dec_ref(v___y_4207_);
return v_res_4213_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2(lean_object* v_00_u03b1_4214_, lean_object* v_x_4215_, uint8_t v_isExporting_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_){
_start:
{
lean_object* v___x_4222_; 
v___x_4222_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(v_x_4215_, v_isExporting_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_);
return v___x_4222_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___boxed(lean_object* v_00_u03b1_4223_, lean_object* v_x_4224_, lean_object* v_isExporting_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_){
_start:
{
uint8_t v_isExporting_boxed_4231_; lean_object* v_res_4232_; 
v_isExporting_boxed_4231_ = lean_unbox(v_isExporting_4225_);
v_res_4232_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2(v_00_u03b1_4223_, v_x_4224_, v_isExporting_boxed_4231_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_);
lean_dec(v___y_4229_);
lean_dec_ref(v___y_4228_);
lean_dec(v___y_4227_);
lean_dec_ref(v___y_4226_);
return v_res_4232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(lean_object* v_lctx_4233_, lean_object* v_localInsts_4234_, lean_object* v_x_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_){
_start:
{
lean_object* v___x_4241_; 
v___x_4241_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_4233_, v_localInsts_4234_, v_x_4235_, v___y_4236_, v___y_4237_, v___y_4238_, v___y_4239_);
if (lean_obj_tag(v___x_4241_) == 0)
{
lean_object* v_a_4242_; lean_object* v___x_4244_; uint8_t v_isShared_4245_; uint8_t v_isSharedCheck_4249_; 
v_a_4242_ = lean_ctor_get(v___x_4241_, 0);
v_isSharedCheck_4249_ = !lean_is_exclusive(v___x_4241_);
if (v_isSharedCheck_4249_ == 0)
{
v___x_4244_ = v___x_4241_;
v_isShared_4245_ = v_isSharedCheck_4249_;
goto v_resetjp_4243_;
}
else
{
lean_inc(v_a_4242_);
lean_dec(v___x_4241_);
v___x_4244_ = lean_box(0);
v_isShared_4245_ = v_isSharedCheck_4249_;
goto v_resetjp_4243_;
}
v_resetjp_4243_:
{
lean_object* v___x_4247_; 
if (v_isShared_4245_ == 0)
{
v___x_4247_ = v___x_4244_;
goto v_reusejp_4246_;
}
else
{
lean_object* v_reuseFailAlloc_4248_; 
v_reuseFailAlloc_4248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4248_, 0, v_a_4242_);
v___x_4247_ = v_reuseFailAlloc_4248_;
goto v_reusejp_4246_;
}
v_reusejp_4246_:
{
return v___x_4247_;
}
}
}
else
{
lean_object* v_a_4250_; lean_object* v___x_4252_; uint8_t v_isShared_4253_; uint8_t v_isSharedCheck_4257_; 
v_a_4250_ = lean_ctor_get(v___x_4241_, 0);
v_isSharedCheck_4257_ = !lean_is_exclusive(v___x_4241_);
if (v_isSharedCheck_4257_ == 0)
{
v___x_4252_ = v___x_4241_;
v_isShared_4253_ = v_isSharedCheck_4257_;
goto v_resetjp_4251_;
}
else
{
lean_inc(v_a_4250_);
lean_dec(v___x_4241_);
v___x_4252_ = lean_box(0);
v_isShared_4253_ = v_isSharedCheck_4257_;
goto v_resetjp_4251_;
}
v_resetjp_4251_:
{
lean_object* v___x_4255_; 
if (v_isShared_4253_ == 0)
{
v___x_4255_ = v___x_4252_;
goto v_reusejp_4254_;
}
else
{
lean_object* v_reuseFailAlloc_4256_; 
v_reuseFailAlloc_4256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4256_, 0, v_a_4250_);
v___x_4255_ = v_reuseFailAlloc_4256_;
goto v_reusejp_4254_;
}
v_reusejp_4254_:
{
return v___x_4255_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg___boxed(lean_object* v_lctx_4258_, lean_object* v_localInsts_4259_, lean_object* v_x_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_){
_start:
{
lean_object* v_res_4266_; 
v_res_4266_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v_lctx_4258_, v_localInsts_4259_, v_x_4260_, v___y_4261_, v___y_4262_, v___y_4263_, v___y_4264_);
lean_dec(v___y_4264_);
lean_dec_ref(v___y_4263_);
lean_dec(v___y_4262_);
lean_dec_ref(v___y_4261_);
return v_res_4266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4(lean_object* v_00_u03b1_4267_, lean_object* v_lctx_4268_, lean_object* v_localInsts_4269_, lean_object* v_x_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_){
_start:
{
lean_object* v___x_4276_; 
v___x_4276_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v_lctx_4268_, v_localInsts_4269_, v_x_4270_, v___y_4271_, v___y_4272_, v___y_4273_, v___y_4274_);
return v___x_4276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___boxed(lean_object* v_00_u03b1_4277_, lean_object* v_lctx_4278_, lean_object* v_localInsts_4279_, lean_object* v_x_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_){
_start:
{
lean_object* v_res_4286_; 
v_res_4286_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4(v_00_u03b1_4277_, v_lctx_4278_, v_localInsts_4279_, v_x_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_);
lean_dec(v___y_4284_);
lean_dec_ref(v___y_4283_);
lean_dec(v___y_4282_);
lean_dec_ref(v___y_4281_);
return v_res_4286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__0(lean_object* v_declName_4287_, lean_object* v_x_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_){
_start:
{
lean_object* v___x_4294_; lean_object* v___x_4295_; 
v___x_4294_ = l_Lean_MessageData_ofName(v_declName_4287_);
v___x_4295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4295_, 0, v___x_4294_);
return v___x_4295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__0___boxed(lean_object* v_declName_4296_, lean_object* v_x_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_){
_start:
{
lean_object* v_res_4303_; 
v_res_4303_ = l_Lean_Meta_mkInjectiveTheorems___lam__0(v_declName_4296_, v_x_4297_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_);
lean_dec(v___y_4301_);
lean_dec_ref(v___y_4300_);
lean_dec(v___y_4299_);
lean_dec_ref(v___y_4298_);
lean_dec_ref(v_x_4297_);
return v_res_4303_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_4304_; 
v___x_4304_ = l_instMonadEIO(lean_box(0));
return v___x_4304_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(lean_object* v_msg_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_){
_start:
{
lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v_toApplicative_4317_; lean_object* v___x_4319_; uint8_t v_isShared_4320_; uint8_t v_isSharedCheck_4378_; 
v___x_4315_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0);
v___x_4316_ = l_StateRefT_x27_instMonad___redArg(v___x_4315_);
v_toApplicative_4317_ = lean_ctor_get(v___x_4316_, 0);
v_isSharedCheck_4378_ = !lean_is_exclusive(v___x_4316_);
if (v_isSharedCheck_4378_ == 0)
{
lean_object* v_unused_4379_; 
v_unused_4379_ = lean_ctor_get(v___x_4316_, 1);
lean_dec(v_unused_4379_);
v___x_4319_ = v___x_4316_;
v_isShared_4320_ = v_isSharedCheck_4378_;
goto v_resetjp_4318_;
}
else
{
lean_inc(v_toApplicative_4317_);
lean_dec(v___x_4316_);
v___x_4319_ = lean_box(0);
v_isShared_4320_ = v_isSharedCheck_4378_;
goto v_resetjp_4318_;
}
v_resetjp_4318_:
{
lean_object* v_toFunctor_4321_; lean_object* v_toSeq_4322_; lean_object* v_toSeqLeft_4323_; lean_object* v_toSeqRight_4324_; lean_object* v___x_4326_; uint8_t v_isShared_4327_; uint8_t v_isSharedCheck_4376_; 
v_toFunctor_4321_ = lean_ctor_get(v_toApplicative_4317_, 0);
v_toSeq_4322_ = lean_ctor_get(v_toApplicative_4317_, 2);
v_toSeqLeft_4323_ = lean_ctor_get(v_toApplicative_4317_, 3);
v_toSeqRight_4324_ = lean_ctor_get(v_toApplicative_4317_, 4);
v_isSharedCheck_4376_ = !lean_is_exclusive(v_toApplicative_4317_);
if (v_isSharedCheck_4376_ == 0)
{
lean_object* v_unused_4377_; 
v_unused_4377_ = lean_ctor_get(v_toApplicative_4317_, 1);
lean_dec(v_unused_4377_);
v___x_4326_ = v_toApplicative_4317_;
v_isShared_4327_ = v_isSharedCheck_4376_;
goto v_resetjp_4325_;
}
else
{
lean_inc(v_toSeqRight_4324_);
lean_inc(v_toSeqLeft_4323_);
lean_inc(v_toSeq_4322_);
lean_inc(v_toFunctor_4321_);
lean_dec(v_toApplicative_4317_);
v___x_4326_ = lean_box(0);
v_isShared_4327_ = v_isSharedCheck_4376_;
goto v_resetjp_4325_;
}
v_resetjp_4325_:
{
lean_object* v___f_4328_; lean_object* v___f_4329_; lean_object* v___f_4330_; lean_object* v___f_4331_; lean_object* v___x_4332_; lean_object* v___f_4333_; lean_object* v___f_4334_; lean_object* v___f_4335_; lean_object* v___x_4337_; 
v___f_4328_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__1));
v___f_4329_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__2));
lean_inc_ref(v_toFunctor_4321_);
v___f_4330_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4330_, 0, v_toFunctor_4321_);
v___f_4331_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4331_, 0, v_toFunctor_4321_);
v___x_4332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4332_, 0, v___f_4330_);
lean_ctor_set(v___x_4332_, 1, v___f_4331_);
v___f_4333_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4333_, 0, v_toSeqRight_4324_);
v___f_4334_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4334_, 0, v_toSeqLeft_4323_);
v___f_4335_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4335_, 0, v_toSeq_4322_);
if (v_isShared_4327_ == 0)
{
lean_ctor_set(v___x_4326_, 4, v___f_4333_);
lean_ctor_set(v___x_4326_, 3, v___f_4334_);
lean_ctor_set(v___x_4326_, 2, v___f_4335_);
lean_ctor_set(v___x_4326_, 1, v___f_4328_);
lean_ctor_set(v___x_4326_, 0, v___x_4332_);
v___x_4337_ = v___x_4326_;
goto v_reusejp_4336_;
}
else
{
lean_object* v_reuseFailAlloc_4375_; 
v_reuseFailAlloc_4375_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4375_, 0, v___x_4332_);
lean_ctor_set(v_reuseFailAlloc_4375_, 1, v___f_4328_);
lean_ctor_set(v_reuseFailAlloc_4375_, 2, v___f_4335_);
lean_ctor_set(v_reuseFailAlloc_4375_, 3, v___f_4334_);
lean_ctor_set(v_reuseFailAlloc_4375_, 4, v___f_4333_);
v___x_4337_ = v_reuseFailAlloc_4375_;
goto v_reusejp_4336_;
}
v_reusejp_4336_:
{
lean_object* v___x_4339_; 
if (v_isShared_4320_ == 0)
{
lean_ctor_set(v___x_4319_, 1, v___f_4329_);
lean_ctor_set(v___x_4319_, 0, v___x_4337_);
v___x_4339_ = v___x_4319_;
goto v_reusejp_4338_;
}
else
{
lean_object* v_reuseFailAlloc_4374_; 
v_reuseFailAlloc_4374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4374_, 0, v___x_4337_);
lean_ctor_set(v_reuseFailAlloc_4374_, 1, v___f_4329_);
v___x_4339_ = v_reuseFailAlloc_4374_;
goto v_reusejp_4338_;
}
v_reusejp_4338_:
{
lean_object* v___x_4340_; lean_object* v_toApplicative_4341_; lean_object* v___x_4343_; uint8_t v_isShared_4344_; uint8_t v_isSharedCheck_4372_; 
v___x_4340_ = l_StateRefT_x27_instMonad___redArg(v___x_4339_);
v_toApplicative_4341_ = lean_ctor_get(v___x_4340_, 0);
v_isSharedCheck_4372_ = !lean_is_exclusive(v___x_4340_);
if (v_isSharedCheck_4372_ == 0)
{
lean_object* v_unused_4373_; 
v_unused_4373_ = lean_ctor_get(v___x_4340_, 1);
lean_dec(v_unused_4373_);
v___x_4343_ = v___x_4340_;
v_isShared_4344_ = v_isSharedCheck_4372_;
goto v_resetjp_4342_;
}
else
{
lean_inc(v_toApplicative_4341_);
lean_dec(v___x_4340_);
v___x_4343_ = lean_box(0);
v_isShared_4344_ = v_isSharedCheck_4372_;
goto v_resetjp_4342_;
}
v_resetjp_4342_:
{
lean_object* v_toFunctor_4345_; lean_object* v_toSeq_4346_; lean_object* v_toSeqLeft_4347_; lean_object* v_toSeqRight_4348_; lean_object* v___x_4350_; uint8_t v_isShared_4351_; uint8_t v_isSharedCheck_4370_; 
v_toFunctor_4345_ = lean_ctor_get(v_toApplicative_4341_, 0);
v_toSeq_4346_ = lean_ctor_get(v_toApplicative_4341_, 2);
v_toSeqLeft_4347_ = lean_ctor_get(v_toApplicative_4341_, 3);
v_toSeqRight_4348_ = lean_ctor_get(v_toApplicative_4341_, 4);
v_isSharedCheck_4370_ = !lean_is_exclusive(v_toApplicative_4341_);
if (v_isSharedCheck_4370_ == 0)
{
lean_object* v_unused_4371_; 
v_unused_4371_ = lean_ctor_get(v_toApplicative_4341_, 1);
lean_dec(v_unused_4371_);
v___x_4350_ = v_toApplicative_4341_;
v_isShared_4351_ = v_isSharedCheck_4370_;
goto v_resetjp_4349_;
}
else
{
lean_inc(v_toSeqRight_4348_);
lean_inc(v_toSeqLeft_4347_);
lean_inc(v_toSeq_4346_);
lean_inc(v_toFunctor_4345_);
lean_dec(v_toApplicative_4341_);
v___x_4350_ = lean_box(0);
v_isShared_4351_ = v_isSharedCheck_4370_;
goto v_resetjp_4349_;
}
v_resetjp_4349_:
{
lean_object* v___f_4352_; lean_object* v___f_4353_; lean_object* v___f_4354_; lean_object* v___f_4355_; lean_object* v___x_4356_; lean_object* v___f_4357_; lean_object* v___f_4358_; lean_object* v___f_4359_; lean_object* v___x_4361_; 
v___f_4352_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__3));
v___f_4353_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__4));
lean_inc_ref(v_toFunctor_4345_);
v___f_4354_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4354_, 0, v_toFunctor_4345_);
v___f_4355_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4355_, 0, v_toFunctor_4345_);
v___x_4356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4356_, 0, v___f_4354_);
lean_ctor_set(v___x_4356_, 1, v___f_4355_);
v___f_4357_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4357_, 0, v_toSeqRight_4348_);
v___f_4358_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4358_, 0, v_toSeqLeft_4347_);
v___f_4359_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4359_, 0, v_toSeq_4346_);
if (v_isShared_4351_ == 0)
{
lean_ctor_set(v___x_4350_, 4, v___f_4357_);
lean_ctor_set(v___x_4350_, 3, v___f_4358_);
lean_ctor_set(v___x_4350_, 2, v___f_4359_);
lean_ctor_set(v___x_4350_, 1, v___f_4352_);
lean_ctor_set(v___x_4350_, 0, v___x_4356_);
v___x_4361_ = v___x_4350_;
goto v_reusejp_4360_;
}
else
{
lean_object* v_reuseFailAlloc_4369_; 
v_reuseFailAlloc_4369_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4369_, 0, v___x_4356_);
lean_ctor_set(v_reuseFailAlloc_4369_, 1, v___f_4352_);
lean_ctor_set(v_reuseFailAlloc_4369_, 2, v___f_4359_);
lean_ctor_set(v_reuseFailAlloc_4369_, 3, v___f_4358_);
lean_ctor_set(v_reuseFailAlloc_4369_, 4, v___f_4357_);
v___x_4361_ = v_reuseFailAlloc_4369_;
goto v_reusejp_4360_;
}
v_reusejp_4360_:
{
lean_object* v___x_4363_; 
if (v_isShared_4344_ == 0)
{
lean_ctor_set(v___x_4343_, 1, v___f_4353_);
lean_ctor_set(v___x_4343_, 0, v___x_4361_);
v___x_4363_ = v___x_4343_;
goto v_reusejp_4362_;
}
else
{
lean_object* v_reuseFailAlloc_4368_; 
v_reuseFailAlloc_4368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4368_, 0, v___x_4361_);
lean_ctor_set(v_reuseFailAlloc_4368_, 1, v___f_4353_);
v___x_4363_ = v_reuseFailAlloc_4368_;
goto v_reusejp_4362_;
}
v_reusejp_4362_:
{
lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_18440__overap_4366_; lean_object* v___x_4367_; 
v___x_4364_ = lean_box(0);
v___x_4365_ = l_instInhabitedOfMonad___redArg(v___x_4363_, v___x_4364_);
v___x_18440__overap_4366_ = lean_panic_fn_borrowed(v___x_4365_, v_msg_4309_);
lean_dec(v___x_4365_);
lean_inc(v___y_4313_);
lean_inc_ref(v___y_4312_);
lean_inc(v___y_4311_);
lean_inc_ref(v___y_4310_);
v___x_4367_ = lean_apply_5(v___x_18440__overap_4366_, v___y_4310_, v___y_4311_, v___y_4312_, v___y_4313_, lean_box(0));
return v___x_4367_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___boxed(lean_object* v_msg_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_){
_start:
{
lean_object* v_res_4386_; 
v_res_4386_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(v_msg_4380_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_);
lean_dec(v___y_4384_);
lean_dec_ref(v___y_4383_);
lean_dec(v___y_4382_);
lean_dec_ref(v___y_4381_);
return v_res_4386_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1(void){
_start:
{
lean_object* v___x_4388_; lean_object* v___x_4389_; 
v___x_4388_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__0));
v___x_4389_ = l_Lean_stringToMessageData(v___x_4388_);
return v___x_4389_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4(void){
_start:
{
lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; 
v___x_4392_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__2));
v___x_4393_ = lean_unsigned_to_nat(11u);
v___x_4394_ = lean_unsigned_to_nat(122u);
v___x_4395_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__3));
v___x_4396_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__2));
v___x_4397_ = l_mkPanicMessageWithDecl(v___x_4396_, v___x_4395_, v___x_4394_, v___x_4393_, v___x_4392_);
return v___x_4397_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(lean_object* v_constName_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_){
_start:
{
lean_object* v___x_4412_; lean_object* v_env_4413_; uint8_t v___x_4414_; lean_object* v___x_4415_; 
v___x_4412_ = lean_st_ref_get(v___y_4402_);
v_env_4413_ = lean_ctor_get(v___x_4412_, 0);
lean_inc_ref(v_env_4413_);
lean_dec(v___x_4412_);
v___x_4414_ = 0;
lean_inc(v_constName_4398_);
v___x_4415_ = l_Lean_Environment_findAsync_x3f(v_env_4413_, v_constName_4398_, v___x_4414_);
if (lean_obj_tag(v___x_4415_) == 1)
{
lean_object* v_val_4416_; uint8_t v_kind_4417_; 
v_val_4416_ = lean_ctor_get(v___x_4415_, 0);
lean_inc(v_val_4416_);
lean_dec_ref_known(v___x_4415_, 1);
v_kind_4417_ = lean_ctor_get_uint8(v_val_4416_, sizeof(void*)*3);
if (v_kind_4417_ == 6)
{
lean_object* v___x_4418_; 
v___x_4418_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_4416_);
if (lean_obj_tag(v___x_4418_) == 6)
{
lean_object* v_val_4419_; lean_object* v___x_4421_; uint8_t v_isShared_4422_; uint8_t v_isSharedCheck_4426_; 
lean_dec(v_constName_4398_);
v_val_4419_ = lean_ctor_get(v___x_4418_, 0);
v_isSharedCheck_4426_ = !lean_is_exclusive(v___x_4418_);
if (v_isSharedCheck_4426_ == 0)
{
v___x_4421_ = v___x_4418_;
v_isShared_4422_ = v_isSharedCheck_4426_;
goto v_resetjp_4420_;
}
else
{
lean_inc(v_val_4419_);
lean_dec(v___x_4418_);
v___x_4421_ = lean_box(0);
v_isShared_4422_ = v_isSharedCheck_4426_;
goto v_resetjp_4420_;
}
v_resetjp_4420_:
{
lean_object* v___x_4424_; 
if (v_isShared_4422_ == 0)
{
lean_ctor_set_tag(v___x_4421_, 0);
v___x_4424_ = v___x_4421_;
goto v_reusejp_4423_;
}
else
{
lean_object* v_reuseFailAlloc_4425_; 
v_reuseFailAlloc_4425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4425_, 0, v_val_4419_);
v___x_4424_ = v_reuseFailAlloc_4425_;
goto v_reusejp_4423_;
}
v_reusejp_4423_:
{
return v___x_4424_;
}
}
}
else
{
lean_object* v___x_4427_; lean_object* v___x_4428_; 
lean_dec_ref(v___x_4418_);
v___x_4427_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4);
v___x_4428_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(v___x_4427_, v___y_4399_, v___y_4400_, v___y_4401_, v___y_4402_);
if (lean_obj_tag(v___x_4428_) == 0)
{
lean_object* v_a_4429_; lean_object* v___x_4431_; uint8_t v_isShared_4432_; uint8_t v_isSharedCheck_4437_; 
v_a_4429_ = lean_ctor_get(v___x_4428_, 0);
v_isSharedCheck_4437_ = !lean_is_exclusive(v___x_4428_);
if (v_isSharedCheck_4437_ == 0)
{
v___x_4431_ = v___x_4428_;
v_isShared_4432_ = v_isSharedCheck_4437_;
goto v_resetjp_4430_;
}
else
{
lean_inc(v_a_4429_);
lean_dec(v___x_4428_);
v___x_4431_ = lean_box(0);
v_isShared_4432_ = v_isSharedCheck_4437_;
goto v_resetjp_4430_;
}
v_resetjp_4430_:
{
if (lean_obj_tag(v_a_4429_) == 0)
{
lean_del_object(v___x_4431_);
goto v___jp_4404_;
}
else
{
lean_object* v_val_4433_; lean_object* v___x_4435_; 
lean_dec(v_constName_4398_);
v_val_4433_ = lean_ctor_get(v_a_4429_, 0);
lean_inc(v_val_4433_);
lean_dec_ref_known(v_a_4429_, 1);
if (v_isShared_4432_ == 0)
{
lean_ctor_set(v___x_4431_, 0, v_val_4433_);
v___x_4435_ = v___x_4431_;
goto v_reusejp_4434_;
}
else
{
lean_object* v_reuseFailAlloc_4436_; 
v_reuseFailAlloc_4436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4436_, 0, v_val_4433_);
v___x_4435_ = v_reuseFailAlloc_4436_;
goto v_reusejp_4434_;
}
v_reusejp_4434_:
{
return v___x_4435_;
}
}
}
}
else
{
lean_object* v_a_4438_; lean_object* v___x_4440_; uint8_t v_isShared_4441_; uint8_t v_isSharedCheck_4445_; 
lean_dec(v_constName_4398_);
v_a_4438_ = lean_ctor_get(v___x_4428_, 0);
v_isSharedCheck_4445_ = !lean_is_exclusive(v___x_4428_);
if (v_isSharedCheck_4445_ == 0)
{
v___x_4440_ = v___x_4428_;
v_isShared_4441_ = v_isSharedCheck_4445_;
goto v_resetjp_4439_;
}
else
{
lean_inc(v_a_4438_);
lean_dec(v___x_4428_);
v___x_4440_ = lean_box(0);
v_isShared_4441_ = v_isSharedCheck_4445_;
goto v_resetjp_4439_;
}
v_resetjp_4439_:
{
lean_object* v___x_4443_; 
if (v_isShared_4441_ == 0)
{
v___x_4443_ = v___x_4440_;
goto v_reusejp_4442_;
}
else
{
lean_object* v_reuseFailAlloc_4444_; 
v_reuseFailAlloc_4444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4444_, 0, v_a_4438_);
v___x_4443_ = v_reuseFailAlloc_4444_;
goto v_reusejp_4442_;
}
v_reusejp_4442_:
{
return v___x_4443_;
}
}
}
}
}
else
{
lean_dec(v_val_4416_);
goto v___jp_4404_;
}
}
else
{
lean_dec(v___x_4415_);
goto v___jp_4404_;
}
v___jp_4404_:
{
lean_object* v___x_4405_; uint8_t v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; 
v___x_4405_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_4406_ = 0;
v___x_4407_ = l_Lean_MessageData_ofConstName(v_constName_4398_, v___x_4406_);
v___x_4408_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4408_, 0, v___x_4405_);
lean_ctor_set(v___x_4408_, 1, v___x_4407_);
v___x_4409_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1);
v___x_4410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4410_, 0, v___x_4408_);
lean_ctor_set(v___x_4410_, 1, v___x_4409_);
v___x_4411_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_4410_, v___y_4399_, v___y_4400_, v___y_4401_, v___y_4402_);
return v___x_4411_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___boxed(lean_object* v_constName_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_){
_start:
{
lean_object* v_res_4452_; 
v_res_4452_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(v_constName_4446_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_);
lean_dec(v___y_4450_);
lean_dec_ref(v___y_4449_);
lean_dec(v___y_4448_);
lean_dec_ref(v___y_4447_);
return v_res_4452_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0(lean_object* v_head_4453_, lean_object* v___x_4454_, lean_object* v___x_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_){
_start:
{
lean_object* v___x_4461_; 
v___x_4461_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(v_head_4453_, v___y_4456_, v___y_4457_, v___y_4458_, v___y_4459_);
if (lean_obj_tag(v___x_4461_) == 0)
{
lean_object* v_a_4462_; lean_object* v___x_4464_; uint8_t v_isShared_4465_; uint8_t v_isSharedCheck_4473_; 
v_a_4462_ = lean_ctor_get(v___x_4461_, 0);
v_isSharedCheck_4473_ = !lean_is_exclusive(v___x_4461_);
if (v_isSharedCheck_4473_ == 0)
{
v___x_4464_ = v___x_4461_;
v_isShared_4465_ = v_isSharedCheck_4473_;
goto v_resetjp_4463_;
}
else
{
lean_inc(v_a_4462_);
lean_dec(v___x_4461_);
v___x_4464_ = lean_box(0);
v_isShared_4465_ = v_isSharedCheck_4473_;
goto v_resetjp_4463_;
}
v_resetjp_4463_:
{
lean_object* v_numFields_4466_; uint8_t v___x_4467_; 
v_numFields_4466_ = lean_ctor_get(v_a_4462_, 4);
v___x_4467_ = lean_nat_dec_lt(v___x_4454_, v_numFields_4466_);
if (v___x_4467_ == 0)
{
lean_object* v___x_4469_; 
lean_dec(v_a_4462_);
if (v_isShared_4465_ == 0)
{
lean_ctor_set(v___x_4464_, 0, v___x_4455_);
v___x_4469_ = v___x_4464_;
goto v_reusejp_4468_;
}
else
{
lean_object* v_reuseFailAlloc_4470_; 
v_reuseFailAlloc_4470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4470_, 0, v___x_4455_);
v___x_4469_ = v_reuseFailAlloc_4470_;
goto v_reusejp_4468_;
}
v_reusejp_4468_:
{
return v___x_4469_;
}
}
else
{
lean_object* v___x_4471_; 
lean_del_object(v___x_4464_);
lean_inc(v_a_4462_);
v___x_4471_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(v_a_4462_, v___y_4456_, v___y_4457_, v___y_4458_, v___y_4459_);
if (lean_obj_tag(v___x_4471_) == 0)
{
lean_object* v___x_4472_; 
lean_dec_ref_known(v___x_4471_, 1);
v___x_4472_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(v_a_4462_, v___y_4456_, v___y_4457_, v___y_4458_, v___y_4459_);
return v___x_4472_;
}
else
{
lean_dec(v_a_4462_);
return v___x_4471_;
}
}
}
}
else
{
lean_object* v_a_4474_; lean_object* v___x_4476_; uint8_t v_isShared_4477_; uint8_t v_isSharedCheck_4481_; 
v_a_4474_ = lean_ctor_get(v___x_4461_, 0);
v_isSharedCheck_4481_ = !lean_is_exclusive(v___x_4461_);
if (v_isSharedCheck_4481_ == 0)
{
v___x_4476_ = v___x_4461_;
v_isShared_4477_ = v_isSharedCheck_4481_;
goto v_resetjp_4475_;
}
else
{
lean_inc(v_a_4474_);
lean_dec(v___x_4461_);
v___x_4476_ = lean_box(0);
v_isShared_4477_ = v_isSharedCheck_4481_;
goto v_resetjp_4475_;
}
v_resetjp_4475_:
{
lean_object* v___x_4479_; 
if (v_isShared_4477_ == 0)
{
v___x_4479_ = v___x_4476_;
goto v_reusejp_4478_;
}
else
{
lean_object* v_reuseFailAlloc_4480_; 
v_reuseFailAlloc_4480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4480_, 0, v_a_4474_);
v___x_4479_ = v_reuseFailAlloc_4480_;
goto v_reusejp_4478_;
}
v_reusejp_4478_:
{
return v___x_4479_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0___boxed(lean_object* v_head_4482_, lean_object* v___x_4483_, lean_object* v___x_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_){
_start:
{
lean_object* v_res_4490_; 
v_res_4490_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0(v_head_4482_, v___x_4483_, v___x_4484_, v___y_4485_, v___y_4486_, v___y_4487_, v___y_4488_);
lean_dec(v___y_4488_);
lean_dec_ref(v___y_4487_);
lean_dec(v___y_4486_);
lean_dec_ref(v___y_4485_);
lean_dec(v___x_4483_);
return v_res_4490_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(lean_object* v_as_x27_4491_, lean_object* v_b_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_){
_start:
{
if (lean_obj_tag(v_as_x27_4491_) == 0)
{
lean_object* v___x_4498_; 
v___x_4498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4498_, 0, v_b_4492_);
return v___x_4498_;
}
else
{
lean_object* v_head_4499_; lean_object* v_tail_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; lean_object* v___f_4503_; uint8_t v___x_4504_; uint8_t v___x_4505_; lean_object* v___x_4506_; 
v_head_4499_ = lean_ctor_get(v_as_x27_4491_, 0);
v_tail_4500_ = lean_ctor_get(v_as_x27_4491_, 1);
v___x_4501_ = lean_unsigned_to_nat(0u);
v___x_4502_ = lean_box(0);
lean_inc(v_head_4499_);
v___f_4503_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4503_, 0, v_head_4499_);
lean_closure_set(v___f_4503_, 1, v___x_4501_);
lean_closure_set(v___f_4503_, 2, v___x_4502_);
v___x_4504_ = l_Lean_isPrivateName(v_head_4499_);
v___x_4505_ = lean_bool_not(v___x_4504_);
v___x_4506_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(v___f_4503_, v___x_4505_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_);
if (lean_obj_tag(v___x_4506_) == 0)
{
lean_dec_ref_known(v___x_4506_, 1);
v_as_x27_4491_ = v_tail_4500_;
v_b_4492_ = v___x_4502_;
goto _start;
}
else
{
return v___x_4506_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___boxed(lean_object* v_as_x27_4508_, lean_object* v_b_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_){
_start:
{
lean_object* v_res_4515_; 
v_res_4515_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v_as_x27_4508_, v_b_4509_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_);
lean_dec(v___y_4513_);
lean_dec_ref(v___y_4512_);
lean_dec(v___y_4511_);
lean_dec_ref(v___y_4510_);
lean_dec(v_as_x27_4508_);
return v_res_4515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__1(lean_object* v_ctors_4516_, lean_object* v___x_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_){
_start:
{
lean_object* v___x_4523_; 
v___x_4523_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v_ctors_4516_, v___x_4517_, v___y_4518_, v___y_4519_, v___y_4520_, v___y_4521_);
if (lean_obj_tag(v___x_4523_) == 0)
{
lean_object* v___x_4525_; uint8_t v_isShared_4526_; uint8_t v_isSharedCheck_4530_; 
v_isSharedCheck_4530_ = !lean_is_exclusive(v___x_4523_);
if (v_isSharedCheck_4530_ == 0)
{
lean_object* v_unused_4531_; 
v_unused_4531_ = lean_ctor_get(v___x_4523_, 0);
lean_dec(v_unused_4531_);
v___x_4525_ = v___x_4523_;
v_isShared_4526_ = v_isSharedCheck_4530_;
goto v_resetjp_4524_;
}
else
{
lean_dec(v___x_4523_);
v___x_4525_ = lean_box(0);
v_isShared_4526_ = v_isSharedCheck_4530_;
goto v_resetjp_4524_;
}
v_resetjp_4524_:
{
lean_object* v___x_4528_; 
if (v_isShared_4526_ == 0)
{
lean_ctor_set(v___x_4525_, 0, v___x_4517_);
v___x_4528_ = v___x_4525_;
goto v_reusejp_4527_;
}
else
{
lean_object* v_reuseFailAlloc_4529_; 
v_reuseFailAlloc_4529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4529_, 0, v___x_4517_);
v___x_4528_ = v_reuseFailAlloc_4529_;
goto v_reusejp_4527_;
}
v_reusejp_4527_:
{
return v___x_4528_;
}
}
}
else
{
return v___x_4523_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed(lean_object* v_ctors_4532_, lean_object* v___x_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_){
_start:
{
lean_object* v_res_4539_; 
v_res_4539_ = l_Lean_Meta_mkInjectiveTheorems___lam__1(v_ctors_4532_, v___x_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_);
lean_dec(v___y_4537_);
lean_dec_ref(v___y_4536_);
lean_dec(v___y_4535_);
lean_dec_ref(v___y_4534_);
lean_dec(v_ctors_4532_);
return v_res_4539_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4541_; lean_object* v___x_4542_; 
v___x_4541_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__0));
v___x_4542_ = l_Lean_stringToMessageData(v___x_4541_);
return v___x_4542_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(lean_object* v_constName_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_){
_start:
{
lean_object* v___x_4549_; lean_object* v_env_4550_; lean_object* v___x_4551_; 
v___x_4549_ = lean_st_ref_get(v___y_4547_);
v_env_4550_ = lean_ctor_get(v___x_4549_, 0);
lean_inc_ref(v_env_4550_);
lean_dec(v___x_4549_);
lean_inc(v_constName_4543_);
v___x_4551_ = l_Lean_isInductiveCore_x3f(v_env_4550_, v_constName_4543_);
if (lean_obj_tag(v___x_4551_) == 0)
{
lean_object* v___x_4552_; uint8_t v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; 
v___x_4552_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_4553_ = 0;
v___x_4554_ = l_Lean_MessageData_ofConstName(v_constName_4543_, v___x_4553_);
v___x_4555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4555_, 0, v___x_4552_);
lean_ctor_set(v___x_4555_, 1, v___x_4554_);
v___x_4556_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1);
v___x_4557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4557_, 0, v___x_4555_);
lean_ctor_set(v___x_4557_, 1, v___x_4556_);
v___x_4558_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_4557_, v___y_4544_, v___y_4545_, v___y_4546_, v___y_4547_);
return v___x_4558_;
}
else
{
lean_object* v_val_4559_; lean_object* v___x_4561_; uint8_t v_isShared_4562_; uint8_t v_isSharedCheck_4566_; 
lean_dec(v_constName_4543_);
v_val_4559_ = lean_ctor_get(v___x_4551_, 0);
v_isSharedCheck_4566_ = !lean_is_exclusive(v___x_4551_);
if (v_isSharedCheck_4566_ == 0)
{
v___x_4561_ = v___x_4551_;
v_isShared_4562_ = v_isSharedCheck_4566_;
goto v_resetjp_4560_;
}
else
{
lean_inc(v_val_4559_);
lean_dec(v___x_4551_);
v___x_4561_ = lean_box(0);
v_isShared_4562_ = v_isSharedCheck_4566_;
goto v_resetjp_4560_;
}
v_resetjp_4560_:
{
lean_object* v___x_4564_; 
if (v_isShared_4562_ == 0)
{
lean_ctor_set_tag(v___x_4561_, 0);
v___x_4564_ = v___x_4561_;
goto v_reusejp_4563_;
}
else
{
lean_object* v_reuseFailAlloc_4565_; 
v_reuseFailAlloc_4565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4565_, 0, v_val_4559_);
v___x_4564_ = v_reuseFailAlloc_4565_;
goto v_reusejp_4563_;
}
v_reusejp_4563_:
{
return v___x_4564_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___boxed(lean_object* v_constName_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_){
_start:
{
lean_object* v_res_4573_; 
v_res_4573_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_constName_4567_, v___y_4568_, v___y_4569_, v___y_4570_, v___y_4571_);
lean_dec(v___y_4571_);
lean_dec_ref(v___y_4570_);
lean_dec(v___y_4569_);
lean_dec_ref(v___y_4568_);
return v_res_4573_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__0(void){
_start:
{
lean_object* v___x_4574_; 
v___x_4574_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4574_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__1(void){
_start:
{
lean_object* v___x_4575_; lean_object* v___x_4576_; 
v___x_4575_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__0, &l_Lean_Meta_mkInjectiveTheorems___closed__0_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__0);
v___x_4576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4576_, 0, v___x_4575_);
return v___x_4576_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__2(void){
_start:
{
lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; 
v___x_4577_ = lean_unsigned_to_nat(32u);
v___x_4578_ = lean_mk_empty_array_with_capacity(v___x_4577_);
v___x_4579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4579_, 0, v___x_4578_);
return v___x_4579_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__3(void){
_start:
{
size_t v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; 
v___x_4580_ = ((size_t)5ULL);
v___x_4581_ = lean_unsigned_to_nat(0u);
v___x_4582_ = lean_unsigned_to_nat(32u);
v___x_4583_ = lean_mk_empty_array_with_capacity(v___x_4582_);
v___x_4584_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__2, &l_Lean_Meta_mkInjectiveTheorems___closed__2_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__2);
v___x_4585_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4585_, 0, v___x_4584_);
lean_ctor_set(v___x_4585_, 1, v___x_4583_);
lean_ctor_set(v___x_4585_, 2, v___x_4581_);
lean_ctor_set(v___x_4585_, 3, v___x_4581_);
lean_ctor_set_usize(v___x_4585_, 4, v___x_4580_);
return v___x_4585_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__4(void){
_start:
{
lean_object* v___x_4586_; lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; 
v___x_4586_ = lean_box(1);
v___x_4587_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_4588_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_4589_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4589_, 0, v___x_4588_);
lean_ctor_set(v___x_4589_, 1, v___x_4587_);
lean_ctor_set(v___x_4589_, 2, v___x_4586_);
return v___x_4589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems(lean_object* v_declName_4592_, lean_object* v_a_4593_, lean_object* v_a_4594_, lean_object* v_a_4595_, lean_object* v_a_4596_){
_start:
{
lean_object* v___x_4598_; lean_object* v___x_4599_; 
v___x_4598_ = lean_st_ref_get(v_a_4596_);
lean_inc(v_declName_4592_);
v___x_4599_ = l_Lean_Meta_isInductivePredicate(v_declName_4592_, v_a_4593_, v_a_4594_, v_a_4595_, v_a_4596_);
if (lean_obj_tag(v___x_4599_) == 0)
{
lean_object* v_a_4600_; lean_object* v___x_4602_; uint8_t v_isShared_4603_; uint8_t v_isSharedCheck_4794_; 
v_a_4600_ = lean_ctor_get(v___x_4599_, 0);
v_isSharedCheck_4794_ = !lean_is_exclusive(v___x_4599_);
if (v_isSharedCheck_4794_ == 0)
{
v___x_4602_ = v___x_4599_;
v_isShared_4603_ = v_isSharedCheck_4794_;
goto v_resetjp_4601_;
}
else
{
lean_inc(v_a_4600_);
lean_dec(v___x_4599_);
v___x_4602_ = lean_box(0);
v_isShared_4603_ = v_isSharedCheck_4794_;
goto v_resetjp_4601_;
}
v_resetjp_4601_:
{
lean_object* v_env_4609_; lean_object* v___f_4610_; lean_object* v___x_4611_; uint8_t v___x_4612_; lean_object* v___y_4614_; lean_object* v___y_4615_; lean_object* v___y_4616_; lean_object* v___y_4617_; uint8_t v___y_4618_; lean_object* v___y_4619_; lean_object* v_a_4620_; lean_object* v___y_4630_; lean_object* v___y_4631_; lean_object* v___y_4632_; lean_object* v___y_4633_; uint8_t v___y_4634_; lean_object* v___y_4635_; lean_object* v_a_4636_; lean_object* v___y_4639_; lean_object* v___y_4640_; lean_object* v___y_4641_; lean_object* v___y_4642_; uint8_t v___y_4643_; lean_object* v___y_4644_; lean_object* v_a_4645_; lean_object* v___y_4648_; lean_object* v___y_4649_; lean_object* v___y_4650_; lean_object* v___y_4651_; uint8_t v___y_4652_; lean_object* v___y_4653_; lean_object* v_a_4654_; lean_object* v___y_4667_; lean_object* v___y_4668_; lean_object* v___y_4669_; lean_object* v___y_4670_; uint8_t v___y_4671_; lean_object* v___y_4672_; lean_object* v_a_4673_; lean_object* v___y_4676_; lean_object* v___y_4677_; lean_object* v___y_4678_; lean_object* v___y_4679_; uint8_t v___y_4680_; lean_object* v___y_4681_; lean_object* v_a_4682_; lean_object* v___y_4685_; lean_object* v___y_4686_; lean_object* v___y_4687_; uint8_t v___y_4688_; lean_object* v___y_4722_; lean_object* v___y_4723_; lean_object* v___y_4724_; uint8_t v_a_4725_; uint8_t v___y_4754_; uint8_t v___x_4790_; 
v_env_4609_ = lean_ctor_get(v___x_4598_, 0);
lean_inc_ref(v_env_4609_);
lean_dec(v___x_4598_);
lean_inc(v_declName_4592_);
v___f_4610_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4610_, 0, v_declName_4592_);
v___x_4611_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__2));
v___x_4612_ = 1;
v___x_4790_ = l_Lean_Environment_contains(v_env_4609_, v___x_4611_, v___x_4612_);
if (v___x_4790_ == 0)
{
v___y_4754_ = v___x_4790_;
goto v___jp_4753_;
}
else
{
lean_object* v_options_4791_; lean_object* v___x_4792_; uint8_t v___x_4793_; 
v_options_4791_ = lean_ctor_get(v_a_4595_, 2);
v___x_4792_ = l_Lean_Meta_genInjectivity;
v___x_4793_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1(v_options_4791_, v___x_4792_);
v___y_4754_ = v___x_4793_;
goto v___jp_4753_;
}
v___jp_4604_:
{
lean_object* v___x_4605_; lean_object* v___x_4607_; 
v___x_4605_ = lean_box(0);
if (v_isShared_4603_ == 0)
{
lean_ctor_set(v___x_4602_, 0, v___x_4605_);
v___x_4607_ = v___x_4602_;
goto v_reusejp_4606_;
}
else
{
lean_object* v_reuseFailAlloc_4608_; 
v_reuseFailAlloc_4608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4608_, 0, v___x_4605_);
v___x_4607_ = v_reuseFailAlloc_4608_;
goto v_reusejp_4606_;
}
v_reusejp_4606_:
{
return v___x_4607_;
}
}
v___jp_4613_:
{
lean_object* v___x_4621_; double v___x_4622_; double v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; 
v___x_4621_ = lean_io_get_num_heartbeats();
v___x_4622_ = lean_float_of_nat(v___y_4619_);
v___x_4623_ = lean_float_of_nat(v___x_4621_);
v___x_4624_ = lean_box_float(v___x_4622_);
v___x_4625_ = lean_box_float(v___x_4623_);
v___x_4626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4626_, 0, v___x_4624_);
lean_ctor_set(v___x_4626_, 1, v___x_4625_);
v___x_4627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4627_, 0, v_a_4620_);
lean_ctor_set(v___x_4627_, 1, v___x_4626_);
lean_inc_ref(v___y_4614_);
lean_inc(v___y_4617_);
v___x_4628_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v___y_4617_, v___x_4612_, v___y_4614_, v___y_4615_, v___y_4618_, v___y_4616_, v___f_4610_, v___x_4627_, v_a_4593_, v_a_4594_, v_a_4595_, v_a_4596_);
return v___x_4628_;
}
v___jp_4629_:
{
lean_object* v___x_4637_; 
v___x_4637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4637_, 0, v_a_4636_);
v___y_4614_ = v___y_4630_;
v___y_4615_ = v___y_4631_;
v___y_4616_ = v___y_4632_;
v___y_4617_ = v___y_4633_;
v___y_4618_ = v___y_4634_;
v___y_4619_ = v___y_4635_;
v_a_4620_ = v___x_4637_;
goto v___jp_4613_;
}
v___jp_4638_:
{
lean_object* v___x_4646_; 
v___x_4646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4646_, 0, v_a_4645_);
v___y_4614_ = v___y_4639_;
v___y_4615_ = v___y_4640_;
v___y_4616_ = v___y_4641_;
v___y_4617_ = v___y_4642_;
v___y_4618_ = v___y_4643_;
v___y_4619_ = v___y_4644_;
v_a_4620_ = v___x_4646_;
goto v___jp_4613_;
}
v___jp_4647_:
{
lean_object* v___x_4655_; double v___x_4656_; double v___x_4657_; double v___x_4658_; double v___x_4659_; double v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; 
v___x_4655_ = lean_io_mono_nanos_now();
v___x_4656_ = lean_float_of_nat(v___y_4653_);
v___x_4657_ = lean_float_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0);
v___x_4658_ = lean_float_div(v___x_4656_, v___x_4657_);
v___x_4659_ = lean_float_of_nat(v___x_4655_);
v___x_4660_ = lean_float_div(v___x_4659_, v___x_4657_);
v___x_4661_ = lean_box_float(v___x_4658_);
v___x_4662_ = lean_box_float(v___x_4660_);
v___x_4663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4663_, 0, v___x_4661_);
lean_ctor_set(v___x_4663_, 1, v___x_4662_);
v___x_4664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4664_, 0, v_a_4654_);
lean_ctor_set(v___x_4664_, 1, v___x_4663_);
lean_inc_ref(v___y_4648_);
lean_inc(v___y_4651_);
v___x_4665_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v___y_4651_, v___x_4612_, v___y_4648_, v___y_4649_, v___y_4652_, v___y_4650_, v___f_4610_, v___x_4664_, v_a_4593_, v_a_4594_, v_a_4595_, v_a_4596_);
return v___x_4665_;
}
v___jp_4666_:
{
lean_object* v___x_4674_; 
v___x_4674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4674_, 0, v_a_4673_);
v___y_4648_ = v___y_4667_;
v___y_4649_ = v___y_4668_;
v___y_4650_ = v___y_4669_;
v___y_4651_ = v___y_4670_;
v___y_4652_ = v___y_4671_;
v___y_4653_ = v___y_4672_;
v_a_4654_ = v___x_4674_;
goto v___jp_4647_;
}
v___jp_4675_:
{
lean_object* v___x_4683_; 
v___x_4683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4683_, 0, v_a_4682_);
v___y_4648_ = v___y_4676_;
v___y_4649_ = v___y_4677_;
v___y_4650_ = v___y_4678_;
v___y_4651_ = v___y_4679_;
v___y_4652_ = v___y_4680_;
v___y_4653_ = v___y_4681_;
v_a_4654_ = v___x_4683_;
goto v___jp_4647_;
}
v___jp_4684_:
{
lean_object* v___x_4689_; lean_object* v_a_4690_; lean_object* v___x_4691_; uint8_t v___x_4692_; 
v___x_4689_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_4596_);
v_a_4690_ = lean_ctor_get(v___x_4689_, 0);
lean_inc(v_a_4690_);
lean_dec_ref(v___x_4689_);
v___x_4691_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4692_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1(v___y_4686_, v___x_4691_);
if (v___x_4692_ == 0)
{
lean_object* v___x_4693_; lean_object* v___x_4694_; 
v___x_4693_ = lean_io_mono_nanos_now();
v___x_4694_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4592_, v_a_4593_, v_a_4594_, v_a_4595_, v_a_4596_);
if (lean_obj_tag(v___x_4694_) == 0)
{
lean_object* v_a_4695_; uint8_t v_isUnsafe_4696_; 
v_a_4695_ = lean_ctor_get(v___x_4694_, 0);
lean_inc(v_a_4695_);
lean_dec_ref_known(v___x_4694_, 1);
v_isUnsafe_4696_ = lean_ctor_get_uint8(v_a_4695_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4696_ == 0)
{
lean_object* v_ctors_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___f_4701_; lean_object* v___x_4702_; 
v_ctors_4697_ = lean_ctor_get(v_a_4695_, 4);
lean_inc(v_ctors_4697_);
lean_dec(v_a_4695_);
v___x_4698_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4699_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4700_ = lean_box(0);
v___f_4701_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed), 7, 2);
lean_closure_set(v___f_4701_, 0, v_ctors_4697_);
lean_closure_set(v___f_4701_, 1, v___x_4700_);
v___x_4702_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4698_, v___x_4699_, v___f_4701_, v_a_4593_, v_a_4594_, v_a_4595_, v_a_4596_);
if (lean_obj_tag(v___x_4702_) == 0)
{
lean_object* v_a_4703_; 
v_a_4703_ = lean_ctor_get(v___x_4702_, 0);
lean_inc(v_a_4703_);
lean_dec_ref_known(v___x_4702_, 1);
v___y_4667_ = v___y_4685_;
v___y_4668_ = v___y_4686_;
v___y_4669_ = v_a_4690_;
v___y_4670_ = v___y_4687_;
v___y_4671_ = v___y_4688_;
v___y_4672_ = v___x_4693_;
v_a_4673_ = v_a_4703_;
goto v___jp_4666_;
}
else
{
lean_object* v_a_4704_; 
v_a_4704_ = lean_ctor_get(v___x_4702_, 0);
lean_inc(v_a_4704_);
lean_dec_ref_known(v___x_4702_, 1);
v___y_4676_ = v___y_4685_;
v___y_4677_ = v___y_4686_;
v___y_4678_ = v_a_4690_;
v___y_4679_ = v___y_4687_;
v___y_4680_ = v___y_4688_;
v___y_4681_ = v___x_4693_;
v_a_4682_ = v_a_4704_;
goto v___jp_4675_;
}
}
else
{
lean_object* v___x_4705_; 
lean_dec(v_a_4695_);
v___x_4705_ = lean_box(0);
v___y_4667_ = v___y_4685_;
v___y_4668_ = v___y_4686_;
v___y_4669_ = v_a_4690_;
v___y_4670_ = v___y_4687_;
v___y_4671_ = v___y_4688_;
v___y_4672_ = v___x_4693_;
v_a_4673_ = v___x_4705_;
goto v___jp_4666_;
}
}
else
{
lean_object* v_a_4706_; 
v_a_4706_ = lean_ctor_get(v___x_4694_, 0);
lean_inc(v_a_4706_);
lean_dec_ref_known(v___x_4694_, 1);
v___y_4676_ = v___y_4685_;
v___y_4677_ = v___y_4686_;
v___y_4678_ = v_a_4690_;
v___y_4679_ = v___y_4687_;
v___y_4680_ = v___y_4688_;
v___y_4681_ = v___x_4693_;
v_a_4682_ = v_a_4706_;
goto v___jp_4675_;
}
}
else
{
lean_object* v___x_4707_; lean_object* v___x_4708_; 
v___x_4707_ = lean_io_get_num_heartbeats();
v___x_4708_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4592_, v_a_4593_, v_a_4594_, v_a_4595_, v_a_4596_);
if (lean_obj_tag(v___x_4708_) == 0)
{
lean_object* v_a_4709_; uint8_t v_isUnsafe_4710_; 
v_a_4709_ = lean_ctor_get(v___x_4708_, 0);
lean_inc(v_a_4709_);
lean_dec_ref_known(v___x_4708_, 1);
v_isUnsafe_4710_ = lean_ctor_get_uint8(v_a_4709_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4710_ == 0)
{
lean_object* v_ctors_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___f_4715_; lean_object* v___x_4716_; 
v_ctors_4711_ = lean_ctor_get(v_a_4709_, 4);
lean_inc(v_ctors_4711_);
lean_dec(v_a_4709_);
v___x_4712_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4713_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4714_ = lean_box(0);
v___f_4715_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed), 7, 2);
lean_closure_set(v___f_4715_, 0, v_ctors_4711_);
lean_closure_set(v___f_4715_, 1, v___x_4714_);
v___x_4716_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4712_, v___x_4713_, v___f_4715_, v_a_4593_, v_a_4594_, v_a_4595_, v_a_4596_);
if (lean_obj_tag(v___x_4716_) == 0)
{
lean_object* v_a_4717_; 
v_a_4717_ = lean_ctor_get(v___x_4716_, 0);
lean_inc(v_a_4717_);
lean_dec_ref_known(v___x_4716_, 1);
v___y_4630_ = v___y_4685_;
v___y_4631_ = v___y_4686_;
v___y_4632_ = v_a_4690_;
v___y_4633_ = v___y_4687_;
v___y_4634_ = v___y_4688_;
v___y_4635_ = v___x_4707_;
v_a_4636_ = v_a_4717_;
goto v___jp_4629_;
}
else
{
lean_object* v_a_4718_; 
v_a_4718_ = lean_ctor_get(v___x_4716_, 0);
lean_inc(v_a_4718_);
lean_dec_ref_known(v___x_4716_, 1);
v___y_4639_ = v___y_4685_;
v___y_4640_ = v___y_4686_;
v___y_4641_ = v_a_4690_;
v___y_4642_ = v___y_4687_;
v___y_4643_ = v___y_4688_;
v___y_4644_ = v___x_4707_;
v_a_4645_ = v_a_4718_;
goto v___jp_4638_;
}
}
else
{
lean_object* v___x_4719_; 
lean_dec(v_a_4709_);
v___x_4719_ = lean_box(0);
v___y_4630_ = v___y_4685_;
v___y_4631_ = v___y_4686_;
v___y_4632_ = v_a_4690_;
v___y_4633_ = v___y_4687_;
v___y_4634_ = v___y_4688_;
v___y_4635_ = v___x_4707_;
v_a_4636_ = v___x_4719_;
goto v___jp_4629_;
}
}
else
{
lean_object* v_a_4720_; 
v_a_4720_ = lean_ctor_get(v___x_4708_, 0);
lean_inc(v_a_4720_);
lean_dec_ref_known(v___x_4708_, 1);
v___y_4639_ = v___y_4685_;
v___y_4640_ = v___y_4686_;
v___y_4641_ = v_a_4690_;
v___y_4642_ = v___y_4687_;
v___y_4643_ = v___y_4688_;
v___y_4644_ = v___x_4707_;
v_a_4645_ = v_a_4720_;
goto v___jp_4638_;
}
}
}
v___jp_4721_:
{
lean_object* v___x_4726_; uint8_t v___x_4727_; 
v___x_4726_ = l_Lean_trace_profiler;
v___x_4727_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1(v___y_4723_, v___x_4726_);
if (v___x_4727_ == 0)
{
lean_object* v___x_4728_; 
lean_dec_ref(v___f_4610_);
v___x_4728_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4592_, v_a_4593_, v_a_4594_, v_a_4595_, v_a_4596_);
if (lean_obj_tag(v___x_4728_) == 0)
{
lean_object* v_a_4729_; lean_object* v___x_4731_; uint8_t v_isShared_4732_; uint8_t v_isSharedCheck_4744_; 
v_a_4729_ = lean_ctor_get(v___x_4728_, 0);
v_isSharedCheck_4744_ = !lean_is_exclusive(v___x_4728_);
if (v_isSharedCheck_4744_ == 0)
{
v___x_4731_ = v___x_4728_;
v_isShared_4732_ = v_isSharedCheck_4744_;
goto v_resetjp_4730_;
}
else
{
lean_inc(v_a_4729_);
lean_dec(v___x_4728_);
v___x_4731_ = lean_box(0);
v_isShared_4732_ = v_isSharedCheck_4744_;
goto v_resetjp_4730_;
}
v_resetjp_4730_:
{
uint8_t v_isUnsafe_4733_; 
v_isUnsafe_4733_ = lean_ctor_get_uint8(v_a_4729_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4733_ == 0)
{
lean_object* v_ctors_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v___f_4738_; lean_object* v___x_4739_; 
lean_del_object(v___x_4731_);
v_ctors_4734_ = lean_ctor_get(v_a_4729_, 4);
lean_inc(v_ctors_4734_);
lean_dec(v_a_4729_);
v___x_4735_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4736_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4737_ = lean_box(0);
v___f_4738_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed), 7, 2);
lean_closure_set(v___f_4738_, 0, v_ctors_4734_);
lean_closure_set(v___f_4738_, 1, v___x_4737_);
v___x_4739_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4735_, v___x_4736_, v___f_4738_, v_a_4593_, v_a_4594_, v_a_4595_, v_a_4596_);
return v___x_4739_;
}
else
{
lean_object* v___x_4740_; lean_object* v___x_4742_; 
lean_dec(v_a_4729_);
v___x_4740_ = lean_box(0);
if (v_isShared_4732_ == 0)
{
lean_ctor_set(v___x_4731_, 0, v___x_4740_);
v___x_4742_ = v___x_4731_;
goto v_reusejp_4741_;
}
else
{
lean_object* v_reuseFailAlloc_4743_; 
v_reuseFailAlloc_4743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4743_, 0, v___x_4740_);
v___x_4742_ = v_reuseFailAlloc_4743_;
goto v_reusejp_4741_;
}
v_reusejp_4741_:
{
return v___x_4742_;
}
}
}
}
else
{
lean_object* v_a_4745_; lean_object* v___x_4747_; uint8_t v_isShared_4748_; uint8_t v_isSharedCheck_4752_; 
v_a_4745_ = lean_ctor_get(v___x_4728_, 0);
v_isSharedCheck_4752_ = !lean_is_exclusive(v___x_4728_);
if (v_isSharedCheck_4752_ == 0)
{
v___x_4747_ = v___x_4728_;
v_isShared_4748_ = v_isSharedCheck_4752_;
goto v_resetjp_4746_;
}
else
{
lean_inc(v_a_4745_);
lean_dec(v___x_4728_);
v___x_4747_ = lean_box(0);
v_isShared_4748_ = v_isSharedCheck_4752_;
goto v_resetjp_4746_;
}
v_resetjp_4746_:
{
lean_object* v___x_4750_; 
if (v_isShared_4748_ == 0)
{
v___x_4750_ = v___x_4747_;
goto v_reusejp_4749_;
}
else
{
lean_object* v_reuseFailAlloc_4751_; 
v_reuseFailAlloc_4751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4751_, 0, v_a_4745_);
v___x_4750_ = v_reuseFailAlloc_4751_;
goto v_reusejp_4749_;
}
v_reusejp_4749_:
{
return v___x_4750_;
}
}
}
}
else
{
v___y_4685_ = v___y_4722_;
v___y_4686_ = v___y_4723_;
v___y_4687_ = v___y_4724_;
v___y_4688_ = v_a_4725_;
goto v___jp_4684_;
}
}
v___jp_4753_:
{
if (v___y_4754_ == 0)
{
lean_dec_ref(v___f_4610_);
lean_dec(v_a_4600_);
lean_dec(v_declName_4592_);
goto v___jp_4604_;
}
else
{
uint8_t v___x_4755_; uint8_t v___x_4756_; 
v___x_4755_ = lean_unbox(v_a_4600_);
lean_dec(v_a_4600_);
v___x_4756_ = lean_bool_not(v___x_4755_);
if (v___x_4756_ == 0)
{
lean_dec_ref(v___f_4610_);
lean_dec(v_declName_4592_);
goto v___jp_4604_;
}
else
{
lean_object* v_options_4757_; lean_object* v_inheritedTraceOptions_4758_; uint8_t v_hasTrace_4759_; uint8_t v___x_4760_; 
lean_del_object(v___x_4602_);
v_options_4757_ = lean_ctor_get(v_a_4595_, 2);
v_inheritedTraceOptions_4758_ = lean_ctor_get(v_a_4595_, 13);
v_hasTrace_4759_ = lean_ctor_get_uint8(v_options_4757_, sizeof(void*)*1);
v___x_4760_ = lean_bool_not(v_hasTrace_4759_);
if (v___x_4760_ == 0)
{
lean_object* v___x_4761_; lean_object* v___x_4762_; 
v___x_4761_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_4762_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
if (v_hasTrace_4759_ == 0)
{
v___y_4722_ = v___x_4762_;
v___y_4723_ = v_options_4757_;
v___y_4724_ = v___x_4761_;
v_a_4725_ = v_hasTrace_4759_;
goto v___jp_4721_;
}
else
{
lean_object* v___x_4763_; uint8_t v___x_4764_; 
v___x_4763_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_4764_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4758_, v_options_4757_, v___x_4763_);
if (v___x_4764_ == 0)
{
v___y_4722_ = v___x_4762_;
v___y_4723_ = v_options_4757_;
v___y_4724_ = v___x_4761_;
v_a_4725_ = v___x_4764_;
goto v___jp_4721_;
}
else
{
v___y_4685_ = v___x_4762_;
v___y_4686_ = v_options_4757_;
v___y_4687_ = v___x_4761_;
v___y_4688_ = v___x_4764_;
goto v___jp_4684_;
}
}
}
else
{
lean_object* v___x_4765_; 
lean_dec_ref(v___f_4610_);
v___x_4765_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4592_, v_a_4593_, v_a_4594_, v_a_4595_, v_a_4596_);
if (lean_obj_tag(v___x_4765_) == 0)
{
lean_object* v_a_4766_; lean_object* v___x_4768_; uint8_t v_isShared_4769_; uint8_t v_isSharedCheck_4781_; 
v_a_4766_ = lean_ctor_get(v___x_4765_, 0);
v_isSharedCheck_4781_ = !lean_is_exclusive(v___x_4765_);
if (v_isSharedCheck_4781_ == 0)
{
v___x_4768_ = v___x_4765_;
v_isShared_4769_ = v_isSharedCheck_4781_;
goto v_resetjp_4767_;
}
else
{
lean_inc(v_a_4766_);
lean_dec(v___x_4765_);
v___x_4768_ = lean_box(0);
v_isShared_4769_ = v_isSharedCheck_4781_;
goto v_resetjp_4767_;
}
v_resetjp_4767_:
{
uint8_t v_isUnsafe_4770_; 
v_isUnsafe_4770_ = lean_ctor_get_uint8(v_a_4766_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4770_ == 0)
{
lean_object* v_ctors_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v___f_4775_; lean_object* v___x_4776_; 
lean_del_object(v___x_4768_);
v_ctors_4771_ = lean_ctor_get(v_a_4766_, 4);
lean_inc(v_ctors_4771_);
lean_dec(v_a_4766_);
v___x_4772_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4773_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4774_ = lean_box(0);
v___f_4775_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed), 7, 2);
lean_closure_set(v___f_4775_, 0, v_ctors_4771_);
lean_closure_set(v___f_4775_, 1, v___x_4774_);
v___x_4776_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4772_, v___x_4773_, v___f_4775_, v_a_4593_, v_a_4594_, v_a_4595_, v_a_4596_);
return v___x_4776_;
}
else
{
lean_object* v___x_4777_; lean_object* v___x_4779_; 
lean_dec(v_a_4766_);
v___x_4777_ = lean_box(0);
if (v_isShared_4769_ == 0)
{
lean_ctor_set(v___x_4768_, 0, v___x_4777_);
v___x_4779_ = v___x_4768_;
goto v_reusejp_4778_;
}
else
{
lean_object* v_reuseFailAlloc_4780_; 
v_reuseFailAlloc_4780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4780_, 0, v___x_4777_);
v___x_4779_ = v_reuseFailAlloc_4780_;
goto v_reusejp_4778_;
}
v_reusejp_4778_:
{
return v___x_4779_;
}
}
}
}
else
{
lean_object* v_a_4782_; lean_object* v___x_4784_; uint8_t v_isShared_4785_; uint8_t v_isSharedCheck_4789_; 
v_a_4782_ = lean_ctor_get(v___x_4765_, 0);
v_isSharedCheck_4789_ = !lean_is_exclusive(v___x_4765_);
if (v_isSharedCheck_4789_ == 0)
{
v___x_4784_ = v___x_4765_;
v_isShared_4785_ = v_isSharedCheck_4789_;
goto v_resetjp_4783_;
}
else
{
lean_inc(v_a_4782_);
lean_dec(v___x_4765_);
v___x_4784_ = lean_box(0);
v_isShared_4785_ = v_isSharedCheck_4789_;
goto v_resetjp_4783_;
}
v_resetjp_4783_:
{
lean_object* v___x_4787_; 
if (v_isShared_4785_ == 0)
{
v___x_4787_ = v___x_4784_;
goto v_reusejp_4786_;
}
else
{
lean_object* v_reuseFailAlloc_4788_; 
v_reuseFailAlloc_4788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4788_, 0, v_a_4782_);
v___x_4787_ = v_reuseFailAlloc_4788_;
goto v_reusejp_4786_;
}
v_reusejp_4786_:
{
return v___x_4787_;
}
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
lean_object* v_a_4795_; lean_object* v___x_4797_; uint8_t v_isShared_4798_; uint8_t v_isSharedCheck_4802_; 
lean_dec(v___x_4598_);
lean_dec(v_declName_4592_);
v_a_4795_ = lean_ctor_get(v___x_4599_, 0);
v_isSharedCheck_4802_ = !lean_is_exclusive(v___x_4599_);
if (v_isSharedCheck_4802_ == 0)
{
v___x_4797_ = v___x_4599_;
v_isShared_4798_ = v_isSharedCheck_4802_;
goto v_resetjp_4796_;
}
else
{
lean_inc(v_a_4795_);
lean_dec(v___x_4599_);
v___x_4797_ = lean_box(0);
v_isShared_4798_ = v_isSharedCheck_4802_;
goto v_resetjp_4796_;
}
v_resetjp_4796_:
{
lean_object* v___x_4800_; 
if (v_isShared_4798_ == 0)
{
v___x_4800_ = v___x_4797_;
goto v_reusejp_4799_;
}
else
{
lean_object* v_reuseFailAlloc_4801_; 
v_reuseFailAlloc_4801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4801_, 0, v_a_4795_);
v___x_4800_ = v_reuseFailAlloc_4801_;
goto v_reusejp_4799_;
}
v_reusejp_4799_:
{
return v___x_4800_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___boxed(lean_object* v_declName_4803_, lean_object* v_a_4804_, lean_object* v_a_4805_, lean_object* v_a_4806_, lean_object* v_a_4807_, lean_object* v_a_4808_){
_start:
{
lean_object* v_res_4809_; 
v_res_4809_ = l_Lean_Meta_mkInjectiveTheorems(v_declName_4803_, v_a_4804_, v_a_4805_, v_a_4806_, v_a_4807_);
lean_dec(v_a_4807_);
lean_dec_ref(v_a_4806_);
lean_dec(v_a_4805_);
lean_dec_ref(v_a_4804_);
return v_res_4809_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3(lean_object* v_as_4810_, lean_object* v_as_x27_4811_, lean_object* v_b_4812_, lean_object* v_a_4813_, lean_object* v___y_4814_, lean_object* v___y_4815_, lean_object* v___y_4816_, lean_object* v___y_4817_){
_start:
{
lean_object* v___x_4819_; 
v___x_4819_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v_as_x27_4811_, v_b_4812_, v___y_4814_, v___y_4815_, v___y_4816_, v___y_4817_);
return v___x_4819_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___boxed(lean_object* v_as_4820_, lean_object* v_as_x27_4821_, lean_object* v_b_4822_, lean_object* v_a_4823_, lean_object* v___y_4824_, lean_object* v___y_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_, lean_object* v___y_4828_){
_start:
{
lean_object* v_res_4829_; 
v_res_4829_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3(v_as_4820_, v_as_x27_4821_, v_b_4822_, v_a_4823_, v___y_4824_, v___y_4825_, v___y_4826_, v___y_4827_);
lean_dec(v___y_4827_);
lean_dec_ref(v___y_4826_);
lean_dec(v___y_4825_);
lean_dec_ref(v___y_4824_);
lean_dec(v_as_x27_4821_);
lean_dec(v_as_4820_);
return v_res_4829_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4870_; lean_object* v___x_4871_; lean_object* v___x_4872_; 
v___x_4870_ = lean_unsigned_to_nat(4172903888u);
v___x_4871_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_));
v___x_4872_ = l_Lean_Name_num___override(v___x_4871_, v___x_4870_);
return v___x_4872_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4874_; lean_object* v___x_4875_; lean_object* v___x_4876_; 
v___x_4874_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_));
v___x_4875_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4876_ = l_Lean_Name_str___override(v___x_4875_, v___x_4874_);
return v___x_4876_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; 
v___x_4878_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_));
v___x_4879_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4880_ = l_Lean_Name_str___override(v___x_4879_, v___x_4878_);
return v___x_4880_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4881_; lean_object* v___x_4882_; lean_object* v___x_4883_; 
v___x_4881_ = lean_unsigned_to_nat(2u);
v___x_4882_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4883_ = l_Lean_Name_num___override(v___x_4882_, v___x_4881_);
return v___x_4883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4885_; uint8_t v___x_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; 
v___x_4885_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_4886_ = 0;
v___x_4887_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4888_ = l_Lean_registerTraceClass(v___x_4885_, v___x_4886_, v___x_4887_);
return v___x_4888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2____boxed(lean_object* v_a_4889_){
_start:
{
lean_object* v_res_4890_; 
v_res_4890_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_();
return v_res_4890_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(lean_object* v_a_4891_, lean_object* v_b_4892_){
_start:
{
lean_object* v_array_4893_; lean_object* v_start_4894_; lean_object* v_stop_4895_; lean_object* v___x_4897_; uint8_t v_isShared_4898_; uint8_t v_isSharedCheck_4908_; 
v_array_4893_ = lean_ctor_get(v_a_4891_, 0);
v_start_4894_ = lean_ctor_get(v_a_4891_, 1);
v_stop_4895_ = lean_ctor_get(v_a_4891_, 2);
v_isSharedCheck_4908_ = !lean_is_exclusive(v_a_4891_);
if (v_isSharedCheck_4908_ == 0)
{
v___x_4897_ = v_a_4891_;
v_isShared_4898_ = v_isSharedCheck_4908_;
goto v_resetjp_4896_;
}
else
{
lean_inc(v_stop_4895_);
lean_inc(v_start_4894_);
lean_inc(v_array_4893_);
lean_dec(v_a_4891_);
v___x_4897_ = lean_box(0);
v_isShared_4898_ = v_isSharedCheck_4908_;
goto v_resetjp_4896_;
}
v_resetjp_4896_:
{
uint8_t v___x_4899_; 
v___x_4899_ = lean_nat_dec_lt(v_start_4894_, v_stop_4895_);
if (v___x_4899_ == 0)
{
lean_del_object(v___x_4897_);
lean_dec(v_stop_4895_);
lean_dec(v_start_4894_);
lean_dec_ref(v_array_4893_);
return v_b_4892_;
}
else
{
lean_object* v___x_4900_; lean_object* v___x_4901_; lean_object* v___x_4903_; 
v___x_4900_ = lean_unsigned_to_nat(1u);
v___x_4901_ = lean_nat_add(v_start_4894_, v___x_4900_);
lean_inc_ref(v_array_4893_);
if (v_isShared_4898_ == 0)
{
lean_ctor_set(v___x_4897_, 1, v___x_4901_);
v___x_4903_ = v___x_4897_;
goto v_reusejp_4902_;
}
else
{
lean_object* v_reuseFailAlloc_4907_; 
v_reuseFailAlloc_4907_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4907_, 0, v_array_4893_);
lean_ctor_set(v_reuseFailAlloc_4907_, 1, v___x_4901_);
lean_ctor_set(v_reuseFailAlloc_4907_, 2, v_stop_4895_);
v___x_4903_ = v_reuseFailAlloc_4907_;
goto v_reusejp_4902_;
}
v_reusejp_4902_:
{
lean_object* v___x_4904_; lean_object* v___x_4905_; 
v___x_4904_ = lean_array_fget(v_array_4893_, v_start_4894_);
lean_dec(v_start_4894_);
lean_dec_ref(v_array_4893_);
v___x_4905_ = lean_array_push(v_b_4892_, v___x_4904_);
v_a_4891_ = v___x_4903_;
v_b_4892_ = v___x_4905_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_4909_; 
v___x_4909_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4909_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_4910_; lean_object* v___x_4911_; 
v___x_4910_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_4911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4911_, 0, v___x_4910_);
return v___x_4911_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4914_; 
v___x_4912_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_4913_ = lean_unsigned_to_nat(0u);
v___x_4914_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4914_, 0, v___x_4913_);
lean_ctor_set(v___x_4914_, 1, v___x_4913_);
lean_ctor_set(v___x_4914_, 2, v___x_4913_);
lean_ctor_set(v___x_4914_, 3, v___x_4913_);
lean_ctor_set(v___x_4914_, 4, v___x_4912_);
lean_ctor_set(v___x_4914_, 5, v___x_4912_);
lean_ctor_set(v___x_4914_, 6, v___x_4912_);
lean_ctor_set(v___x_4914_, 7, v___x_4912_);
lean_ctor_set(v___x_4914_, 8, v___x_4912_);
lean_ctor_set(v___x_4914_, 9, v___x_4912_);
return v___x_4914_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; 
v___x_4915_ = lean_box(1);
v___x_4916_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_4917_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_4918_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4918_, 0, v___x_4917_);
lean_ctor_set(v___x_4918_, 1, v___x_4916_);
lean_ctor_set(v___x_4918_, 2, v___x_4915_);
return v___x_4918_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_4920_; lean_object* v___x_4921_; 
v___x_4920_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4));
v___x_4921_ = l_Lean_stringToMessageData(v___x_4920_);
return v___x_4921_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_4923_; lean_object* v___x_4924_; 
v___x_4923_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_4924_ = l_Lean_stringToMessageData(v___x_4923_);
return v___x_4924_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_4926_; lean_object* v___x_4927_; 
v___x_4926_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_4927_ = l_Lean_stringToMessageData(v___x_4926_);
return v___x_4927_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_4929_; lean_object* v___x_4930_; 
v___x_4929_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_4930_ = l_Lean_stringToMessageData(v___x_4929_);
return v___x_4930_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_4932_; lean_object* v___x_4933_; 
v___x_4932_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_4933_ = l_Lean_stringToMessageData(v___x_4932_);
return v___x_4933_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15(void){
_start:
{
lean_object* v___x_4935_; lean_object* v___x_4936_; 
v___x_4935_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14));
v___x_4936_ = l_Lean_stringToMessageData(v___x_4935_);
return v___x_4936_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17(void){
_start:
{
lean_object* v___x_4938_; lean_object* v___x_4939_; 
v___x_4938_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16));
v___x_4939_ = l_Lean_stringToMessageData(v___x_4938_);
return v___x_4939_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_4940_, lean_object* v_declHint_4941_, lean_object* v___y_4942_){
_start:
{
lean_object* v___x_4944_; lean_object* v_env_4945_; uint8_t v___y_4947_; uint8_t v___x_5003_; uint8_t v___x_5004_; 
v___x_4944_ = lean_st_ref_get(v___y_4942_);
v_env_4945_ = lean_ctor_get(v___x_4944_, 0);
lean_inc_ref(v_env_4945_);
lean_dec(v___x_4944_);
v___x_5003_ = l_Lean_Name_isAnonymous(v_declHint_4941_);
v___x_5004_ = lean_bool_not(v___x_5003_);
if (v___x_5004_ == 0)
{
v___y_4947_ = v___x_5004_;
goto v___jp_4946_;
}
else
{
uint8_t v_isExporting_5005_; 
v_isExporting_5005_ = lean_ctor_get_uint8(v_env_4945_, sizeof(void*)*8);
v___y_4947_ = v_isExporting_5005_;
goto v___jp_4946_;
}
v___jp_4946_:
{
if (v___y_4947_ == 0)
{
lean_object* v___x_4948_; 
lean_dec_ref(v_env_4945_);
lean_dec(v_declHint_4941_);
v___x_4948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4948_, 0, v_msg_4940_);
return v___x_4948_;
}
else
{
uint8_t v___x_4949_; lean_object* v___x_4950_; uint8_t v___x_4951_; 
v___x_4949_ = 0;
lean_inc_ref(v_env_4945_);
v___x_4950_ = l_Lean_Environment_setExporting(v_env_4945_, v___x_4949_);
lean_inc(v_declHint_4941_);
lean_inc_ref(v___x_4950_);
v___x_4951_ = l_Lean_Environment_contains(v___x_4950_, v_declHint_4941_, v___y_4947_);
if (v___x_4951_ == 0)
{
lean_object* v___x_4952_; 
lean_dec_ref(v___x_4950_);
lean_dec_ref(v_env_4945_);
lean_dec(v_declHint_4941_);
v___x_4952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4952_, 0, v_msg_4940_);
return v___x_4952_;
}
else
{
lean_object* v___x_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v_c_4958_; lean_object* v___x_4959_; 
v___x_4953_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_4954_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_4955_ = l_Lean_Options_empty;
v___x_4956_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4956_, 0, v___x_4950_);
lean_ctor_set(v___x_4956_, 1, v___x_4953_);
lean_ctor_set(v___x_4956_, 2, v___x_4954_);
lean_ctor_set(v___x_4956_, 3, v___x_4955_);
lean_inc(v_declHint_4941_);
v___x_4957_ = l_Lean_MessageData_ofConstName(v_declHint_4941_, v___x_4949_);
v_c_4958_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_4958_, 0, v___x_4956_);
lean_ctor_set(v_c_4958_, 1, v___x_4957_);
v___x_4959_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4945_, v_declHint_4941_);
if (lean_obj_tag(v___x_4959_) == 0)
{
lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; lean_object* v___x_4963_; lean_object* v___x_4964_; lean_object* v___x_4965_; lean_object* v___x_4966_; 
lean_dec_ref(v_env_4945_);
lean_dec(v_declHint_4941_);
v___x_4960_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_4961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4961_, 0, v___x_4960_);
lean_ctor_set(v___x_4961_, 1, v_c_4958_);
v___x_4962_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_4963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4963_, 0, v___x_4961_);
lean_ctor_set(v___x_4963_, 1, v___x_4962_);
v___x_4964_ = l_Lean_MessageData_note(v___x_4963_);
v___x_4965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4965_, 0, v_msg_4940_);
lean_ctor_set(v___x_4965_, 1, v___x_4964_);
v___x_4966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4966_, 0, v___x_4965_);
return v___x_4966_;
}
else
{
lean_object* v_val_4967_; lean_object* v___x_4969_; uint8_t v_isShared_4970_; uint8_t v_isSharedCheck_5002_; 
v_val_4967_ = lean_ctor_get(v___x_4959_, 0);
v_isSharedCheck_5002_ = !lean_is_exclusive(v___x_4959_);
if (v_isSharedCheck_5002_ == 0)
{
v___x_4969_ = v___x_4959_;
v_isShared_4970_ = v_isSharedCheck_5002_;
goto v_resetjp_4968_;
}
else
{
lean_inc(v_val_4967_);
lean_dec(v___x_4959_);
v___x_4969_ = lean_box(0);
v_isShared_4970_ = v_isSharedCheck_5002_;
goto v_resetjp_4968_;
}
v_resetjp_4968_:
{
lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v_mod_4974_; uint8_t v___x_4975_; 
v___x_4971_ = lean_box(0);
v___x_4972_ = l_Lean_Environment_header(v_env_4945_);
lean_dec_ref(v_env_4945_);
v___x_4973_ = l_Lean_EnvironmentHeader_moduleNames(v___x_4972_);
v_mod_4974_ = lean_array_get(v___x_4971_, v___x_4973_, v_val_4967_);
lean_dec(v_val_4967_);
lean_dec_ref(v___x_4973_);
v___x_4975_ = l_Lean_isPrivateName(v_declHint_4941_);
lean_dec(v_declHint_4941_);
if (v___x_4975_ == 0)
{
lean_object* v___x_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; lean_object* v___x_4985_; lean_object* v___x_4987_; 
v___x_4976_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_4977_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4977_, 0, v___x_4976_);
lean_ctor_set(v___x_4977_, 1, v_c_4958_);
v___x_4978_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_4979_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4979_, 0, v___x_4977_);
lean_ctor_set(v___x_4979_, 1, v___x_4978_);
v___x_4980_ = l_Lean_MessageData_ofName(v_mod_4974_);
v___x_4981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4981_, 0, v___x_4979_);
lean_ctor_set(v___x_4981_, 1, v___x_4980_);
v___x_4982_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_4983_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4983_, 0, v___x_4981_);
lean_ctor_set(v___x_4983_, 1, v___x_4982_);
v___x_4984_ = l_Lean_MessageData_note(v___x_4983_);
v___x_4985_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4985_, 0, v_msg_4940_);
lean_ctor_set(v___x_4985_, 1, v___x_4984_);
if (v_isShared_4970_ == 0)
{
lean_ctor_set_tag(v___x_4969_, 0);
lean_ctor_set(v___x_4969_, 0, v___x_4985_);
v___x_4987_ = v___x_4969_;
goto v_reusejp_4986_;
}
else
{
lean_object* v_reuseFailAlloc_4988_; 
v_reuseFailAlloc_4988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4988_, 0, v___x_4985_);
v___x_4987_ = v_reuseFailAlloc_4988_;
goto v_reusejp_4986_;
}
v_reusejp_4986_:
{
return v___x_4987_;
}
}
else
{
lean_object* v___x_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; lean_object* v___x_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; lean_object* v___x_5000_; 
v___x_4989_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_4990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4990_, 0, v___x_4989_);
lean_ctor_set(v___x_4990_, 1, v_c_4958_);
v___x_4991_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_4992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4992_, 0, v___x_4990_);
lean_ctor_set(v___x_4992_, 1, v___x_4991_);
v___x_4993_ = l_Lean_MessageData_ofName(v_mod_4974_);
v___x_4994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4994_, 0, v___x_4992_);
lean_ctor_set(v___x_4994_, 1, v___x_4993_);
v___x_4995_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_4996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4996_, 0, v___x_4994_);
lean_ctor_set(v___x_4996_, 1, v___x_4995_);
v___x_4997_ = l_Lean_MessageData_note(v___x_4996_);
v___x_4998_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4998_, 0, v_msg_4940_);
lean_ctor_set(v___x_4998_, 1, v___x_4997_);
if (v_isShared_4970_ == 0)
{
lean_ctor_set_tag(v___x_4969_, 0);
lean_ctor_set(v___x_4969_, 0, v___x_4998_);
v___x_5000_ = v___x_4969_;
goto v_reusejp_4999_;
}
else
{
lean_object* v_reuseFailAlloc_5001_; 
v_reuseFailAlloc_5001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5001_, 0, v___x_4998_);
v___x_5000_ = v_reuseFailAlloc_5001_;
goto v_reusejp_4999_;
}
v_reusejp_4999_:
{
return v___x_5000_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_5006_, lean_object* v_declHint_5007_, lean_object* v___y_5008_, lean_object* v___y_5009_){
_start:
{
lean_object* v_res_5010_; 
v_res_5010_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_5006_, v_declHint_5007_, v___y_5008_);
lean_dec(v___y_5008_);
return v_res_5010_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_msg_5011_, lean_object* v_declHint_5012_, lean_object* v___y_5013_, lean_object* v___y_5014_, lean_object* v___y_5015_, lean_object* v___y_5016_){
_start:
{
lean_object* v___x_5018_; lean_object* v_a_5019_; lean_object* v___x_5021_; uint8_t v_isShared_5022_; uint8_t v_isSharedCheck_5028_; 
v___x_5018_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_5011_, v_declHint_5012_, v___y_5016_);
v_a_5019_ = lean_ctor_get(v___x_5018_, 0);
v_isSharedCheck_5028_ = !lean_is_exclusive(v___x_5018_);
if (v_isSharedCheck_5028_ == 0)
{
v___x_5021_ = v___x_5018_;
v_isShared_5022_ = v_isSharedCheck_5028_;
goto v_resetjp_5020_;
}
else
{
lean_inc(v_a_5019_);
lean_dec(v___x_5018_);
v___x_5021_ = lean_box(0);
v_isShared_5022_ = v_isSharedCheck_5028_;
goto v_resetjp_5020_;
}
v_resetjp_5020_:
{
lean_object* v___x_5023_; lean_object* v___x_5024_; lean_object* v___x_5026_; 
v___x_5023_ = l_Lean_unknownIdentifierMessageTag;
v___x_5024_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_5024_, 0, v___x_5023_);
lean_ctor_set(v___x_5024_, 1, v_a_5019_);
if (v_isShared_5022_ == 0)
{
lean_ctor_set(v___x_5021_, 0, v___x_5024_);
v___x_5026_ = v___x_5021_;
goto v_reusejp_5025_;
}
else
{
lean_object* v_reuseFailAlloc_5027_; 
v_reuseFailAlloc_5027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5027_, 0, v___x_5024_);
v___x_5026_ = v_reuseFailAlloc_5027_;
goto v_reusejp_5025_;
}
v_reusejp_5025_:
{
return v___x_5026_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v_msg_5029_, lean_object* v_declHint_5030_, lean_object* v___y_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_, lean_object* v___y_5034_, lean_object* v___y_5035_){
_start:
{
lean_object* v_res_5036_; 
v_res_5036_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_5029_, v_declHint_5030_, v___y_5031_, v___y_5032_, v___y_5033_, v___y_5034_);
lean_dec(v___y_5034_);
lean_dec_ref(v___y_5033_);
lean_dec(v___y_5032_);
lean_dec_ref(v___y_5031_);
return v_res_5036_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_5037_, lean_object* v_msg_5038_, lean_object* v___y_5039_, lean_object* v___y_5040_, lean_object* v___y_5041_, lean_object* v___y_5042_){
_start:
{
lean_object* v_fileName_5044_; lean_object* v_fileMap_5045_; lean_object* v_options_5046_; lean_object* v_currRecDepth_5047_; lean_object* v_maxRecDepth_5048_; lean_object* v_ref_5049_; lean_object* v_currNamespace_5050_; lean_object* v_openDecls_5051_; lean_object* v_initHeartbeats_5052_; lean_object* v_maxHeartbeats_5053_; lean_object* v_quotContext_5054_; lean_object* v_currMacroScope_5055_; uint8_t v_diag_5056_; lean_object* v_cancelTk_x3f_5057_; uint8_t v_suppressElabErrors_5058_; lean_object* v_inheritedTraceOptions_5059_; lean_object* v_ref_5060_; lean_object* v___x_5061_; lean_object* v___x_5062_; 
v_fileName_5044_ = lean_ctor_get(v___y_5041_, 0);
v_fileMap_5045_ = lean_ctor_get(v___y_5041_, 1);
v_options_5046_ = lean_ctor_get(v___y_5041_, 2);
v_currRecDepth_5047_ = lean_ctor_get(v___y_5041_, 3);
v_maxRecDepth_5048_ = lean_ctor_get(v___y_5041_, 4);
v_ref_5049_ = lean_ctor_get(v___y_5041_, 5);
v_currNamespace_5050_ = lean_ctor_get(v___y_5041_, 6);
v_openDecls_5051_ = lean_ctor_get(v___y_5041_, 7);
v_initHeartbeats_5052_ = lean_ctor_get(v___y_5041_, 8);
v_maxHeartbeats_5053_ = lean_ctor_get(v___y_5041_, 9);
v_quotContext_5054_ = lean_ctor_get(v___y_5041_, 10);
v_currMacroScope_5055_ = lean_ctor_get(v___y_5041_, 11);
v_diag_5056_ = lean_ctor_get_uint8(v___y_5041_, sizeof(void*)*14);
v_cancelTk_x3f_5057_ = lean_ctor_get(v___y_5041_, 12);
v_suppressElabErrors_5058_ = lean_ctor_get_uint8(v___y_5041_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_5059_ = lean_ctor_get(v___y_5041_, 13);
v_ref_5060_ = l_Lean_replaceRef(v_ref_5037_, v_ref_5049_);
lean_inc_ref(v_inheritedTraceOptions_5059_);
lean_inc(v_cancelTk_x3f_5057_);
lean_inc(v_currMacroScope_5055_);
lean_inc(v_quotContext_5054_);
lean_inc(v_maxHeartbeats_5053_);
lean_inc(v_initHeartbeats_5052_);
lean_inc(v_openDecls_5051_);
lean_inc(v_currNamespace_5050_);
lean_inc(v_maxRecDepth_5048_);
lean_inc(v_currRecDepth_5047_);
lean_inc_ref(v_options_5046_);
lean_inc_ref(v_fileMap_5045_);
lean_inc_ref(v_fileName_5044_);
v___x_5061_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_5061_, 0, v_fileName_5044_);
lean_ctor_set(v___x_5061_, 1, v_fileMap_5045_);
lean_ctor_set(v___x_5061_, 2, v_options_5046_);
lean_ctor_set(v___x_5061_, 3, v_currRecDepth_5047_);
lean_ctor_set(v___x_5061_, 4, v_maxRecDepth_5048_);
lean_ctor_set(v___x_5061_, 5, v_ref_5060_);
lean_ctor_set(v___x_5061_, 6, v_currNamespace_5050_);
lean_ctor_set(v___x_5061_, 7, v_openDecls_5051_);
lean_ctor_set(v___x_5061_, 8, v_initHeartbeats_5052_);
lean_ctor_set(v___x_5061_, 9, v_maxHeartbeats_5053_);
lean_ctor_set(v___x_5061_, 10, v_quotContext_5054_);
lean_ctor_set(v___x_5061_, 11, v_currMacroScope_5055_);
lean_ctor_set(v___x_5061_, 12, v_cancelTk_x3f_5057_);
lean_ctor_set(v___x_5061_, 13, v_inheritedTraceOptions_5059_);
lean_ctor_set_uint8(v___x_5061_, sizeof(void*)*14, v_diag_5056_);
lean_ctor_set_uint8(v___x_5061_, sizeof(void*)*14 + 1, v_suppressElabErrors_5058_);
v___x_5062_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v_msg_5038_, v___y_5039_, v___y_5040_, v___x_5061_, v___y_5042_);
lean_dec_ref_known(v___x_5061_, 14);
return v___x_5062_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_5063_, lean_object* v_msg_5064_, lean_object* v___y_5065_, lean_object* v___y_5066_, lean_object* v___y_5067_, lean_object* v___y_5068_, lean_object* v___y_5069_){
_start:
{
lean_object* v_res_5070_; 
v_res_5070_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5063_, v_msg_5064_, v___y_5065_, v___y_5066_, v___y_5067_, v___y_5068_);
lean_dec(v___y_5068_);
lean_dec_ref(v___y_5067_);
lean_dec(v___y_5066_);
lean_dec_ref(v___y_5065_);
lean_dec(v_ref_5063_);
return v_res_5070_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_5071_, lean_object* v_msg_5072_, lean_object* v_declHint_5073_, lean_object* v___y_5074_, lean_object* v___y_5075_, lean_object* v___y_5076_, lean_object* v___y_5077_){
_start:
{
lean_object* v___x_5079_; lean_object* v_a_5080_; lean_object* v___x_5081_; 
v___x_5079_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_5072_, v_declHint_5073_, v___y_5074_, v___y_5075_, v___y_5076_, v___y_5077_);
v_a_5080_ = lean_ctor_get(v___x_5079_, 0);
lean_inc(v_a_5080_);
lean_dec_ref(v___x_5079_);
v___x_5081_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5071_, v_a_5080_, v___y_5074_, v___y_5075_, v___y_5076_, v___y_5077_);
return v___x_5081_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_5082_, lean_object* v_msg_5083_, lean_object* v_declHint_5084_, lean_object* v___y_5085_, lean_object* v___y_5086_, lean_object* v___y_5087_, lean_object* v___y_5088_, lean_object* v___y_5089_){
_start:
{
lean_object* v_res_5090_; 
v_res_5090_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5082_, v_msg_5083_, v_declHint_5084_, v___y_5085_, v___y_5086_, v___y_5087_, v___y_5088_);
lean_dec(v___y_5088_);
lean_dec_ref(v___y_5087_);
lean_dec(v___y_5086_);
lean_dec_ref(v___y_5085_);
lean_dec(v_ref_5082_);
return v_res_5090_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_5092_; lean_object* v___x_5093_; 
v___x_5092_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_5093_ = l_Lean_stringToMessageData(v___x_5092_);
return v___x_5093_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_5094_, lean_object* v_constName_5095_, lean_object* v___y_5096_, lean_object* v___y_5097_, lean_object* v___y_5098_, lean_object* v___y_5099_){
_start:
{
lean_object* v___x_5101_; uint8_t v___x_5102_; lean_object* v___x_5103_; lean_object* v___x_5104_; lean_object* v___x_5105_; lean_object* v___x_5106_; lean_object* v___x_5107_; 
v___x_5101_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_5102_ = 0;
lean_inc(v_constName_5095_);
v___x_5103_ = l_Lean_MessageData_ofConstName(v_constName_5095_, v___x_5102_);
v___x_5104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5104_, 0, v___x_5101_);
lean_ctor_set(v___x_5104_, 1, v___x_5103_);
v___x_5105_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_5106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5106_, 0, v___x_5104_);
lean_ctor_set(v___x_5106_, 1, v___x_5105_);
v___x_5107_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5094_, v___x_5106_, v_constName_5095_, v___y_5096_, v___y_5097_, v___y_5098_, v___y_5099_);
return v___x_5107_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_5108_, lean_object* v_constName_5109_, lean_object* v___y_5110_, lean_object* v___y_5111_, lean_object* v___y_5112_, lean_object* v___y_5113_, lean_object* v___y_5114_){
_start:
{
lean_object* v_res_5115_; 
v_res_5115_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(v_ref_5108_, v_constName_5109_, v___y_5110_, v___y_5111_, v___y_5112_, v___y_5113_);
lean_dec(v___y_5113_);
lean_dec_ref(v___y_5112_);
lean_dec(v___y_5111_);
lean_dec_ref(v___y_5110_);
lean_dec(v_ref_5108_);
return v_res_5115_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(lean_object* v_constName_5116_, lean_object* v___y_5117_, lean_object* v___y_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_){
_start:
{
lean_object* v_ref_5122_; lean_object* v___x_5123_; 
v_ref_5122_ = lean_ctor_get(v___y_5119_, 5);
v___x_5123_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(v_ref_5122_, v_constName_5116_, v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_);
return v___x_5123_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_constName_5124_, lean_object* v___y_5125_, lean_object* v___y_5126_, lean_object* v___y_5127_, lean_object* v___y_5128_, lean_object* v___y_5129_){
_start:
{
lean_object* v_res_5130_; 
v_res_5130_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(v_constName_5124_, v___y_5125_, v___y_5126_, v___y_5127_, v___y_5128_);
lean_dec(v___y_5128_);
lean_dec_ref(v___y_5127_);
lean_dec(v___y_5126_);
lean_dec_ref(v___y_5125_);
return v_res_5130_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(lean_object* v_constName_5131_, lean_object* v___y_5132_, lean_object* v___y_5133_, lean_object* v___y_5134_, lean_object* v___y_5135_){
_start:
{
lean_object* v___x_5137_; lean_object* v_env_5138_; uint8_t v___x_5139_; lean_object* v___x_5140_; 
v___x_5137_ = lean_st_ref_get(v___y_5135_);
v_env_5138_ = lean_ctor_get(v___x_5137_, 0);
lean_inc_ref(v_env_5138_);
lean_dec(v___x_5137_);
v___x_5139_ = 0;
lean_inc(v_constName_5131_);
v___x_5140_ = l_Lean_Environment_find_x3f(v_env_5138_, v_constName_5131_, v___x_5139_);
if (lean_obj_tag(v___x_5140_) == 0)
{
lean_object* v___x_5141_; 
v___x_5141_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(v_constName_5131_, v___y_5132_, v___y_5133_, v___y_5134_, v___y_5135_);
return v___x_5141_;
}
else
{
lean_object* v_val_5142_; lean_object* v___x_5144_; uint8_t v_isShared_5145_; uint8_t v_isSharedCheck_5149_; 
lean_dec(v_constName_5131_);
v_val_5142_ = lean_ctor_get(v___x_5140_, 0);
v_isSharedCheck_5149_ = !lean_is_exclusive(v___x_5140_);
if (v_isSharedCheck_5149_ == 0)
{
v___x_5144_ = v___x_5140_;
v_isShared_5145_ = v_isSharedCheck_5149_;
goto v_resetjp_5143_;
}
else
{
lean_inc(v_val_5142_);
lean_dec(v___x_5140_);
v___x_5144_ = lean_box(0);
v_isShared_5145_ = v_isSharedCheck_5149_;
goto v_resetjp_5143_;
}
v_resetjp_5143_:
{
lean_object* v___x_5147_; 
if (v_isShared_5145_ == 0)
{
lean_ctor_set_tag(v___x_5144_, 0);
v___x_5147_ = v___x_5144_;
goto v_reusejp_5146_;
}
else
{
lean_object* v_reuseFailAlloc_5148_; 
v_reuseFailAlloc_5148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5148_, 0, v_val_5142_);
v___x_5147_ = v_reuseFailAlloc_5148_;
goto v_reusejp_5146_;
}
v_reusejp_5146_:
{
return v___x_5147_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0___boxed(lean_object* v_constName_5150_, lean_object* v___y_5151_, lean_object* v___y_5152_, lean_object* v___y_5153_, lean_object* v___y_5154_, lean_object* v___y_5155_){
_start:
{
lean_object* v_res_5156_; 
v_res_5156_ = l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(v_constName_5150_, v___y_5151_, v___y_5152_, v___y_5153_, v___y_5154_);
lean_dec(v___y_5154_);
lean_dec_ref(v___y_5153_);
lean_dec(v___y_5152_);
lean_dec_ref(v___y_5151_);
return v_res_5156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(lean_object* v_x_5159_, lean_object* v_x_5160_, lean_object* v_x_5161_, lean_object* v___y_5162_, lean_object* v___y_5163_, lean_object* v___y_5164_, lean_object* v___y_5165_){
_start:
{
if (lean_obj_tag(v_x_5159_) == 5)
{
lean_object* v_fn_5167_; lean_object* v_arg_5168_; lean_object* v___x_5169_; lean_object* v___x_5170_; lean_object* v___x_5171_; 
v_fn_5167_ = lean_ctor_get(v_x_5159_, 0);
lean_inc_ref(v_fn_5167_);
v_arg_5168_ = lean_ctor_get(v_x_5159_, 1);
lean_inc_ref(v_arg_5168_);
lean_dec_ref_known(v_x_5159_, 2);
v___x_5169_ = lean_array_set(v_x_5160_, v_x_5161_, v_arg_5168_);
v___x_5170_ = lean_unsigned_to_nat(1u);
v___x_5171_ = lean_nat_sub(v_x_5161_, v___x_5170_);
lean_dec(v_x_5161_);
v_x_5159_ = v_fn_5167_;
v_x_5160_ = v___x_5169_;
v_x_5161_ = v___x_5171_;
goto _start;
}
else
{
lean_dec(v_x_5161_);
if (lean_obj_tag(v_x_5159_) == 4)
{
lean_object* v_declName_5173_; lean_object* v___x_5174_; 
v_declName_5173_ = lean_ctor_get(v_x_5159_, 0);
lean_inc(v_declName_5173_);
lean_dec_ref_known(v_x_5159_, 2);
v___x_5174_ = l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(v_declName_5173_, v___y_5162_, v___y_5163_, v___y_5164_, v___y_5165_);
if (lean_obj_tag(v___x_5174_) == 0)
{
lean_object* v_a_5175_; lean_object* v___x_5177_; uint8_t v_isShared_5178_; uint8_t v_isSharedCheck_5206_; 
v_a_5175_ = lean_ctor_get(v___x_5174_, 0);
v_isSharedCheck_5206_ = !lean_is_exclusive(v___x_5174_);
if (v_isSharedCheck_5206_ == 0)
{
v___x_5177_ = v___x_5174_;
v_isShared_5178_ = v_isSharedCheck_5206_;
goto v_resetjp_5176_;
}
else
{
lean_inc(v_a_5175_);
lean_dec(v___x_5174_);
v___x_5177_ = lean_box(0);
v_isShared_5178_ = v_isSharedCheck_5206_;
goto v_resetjp_5176_;
}
v_resetjp_5176_:
{
lean_object* v_lower_5180_; lean_object* v_upper_5181_; 
if (lean_obj_tag(v_a_5175_) == 5)
{
lean_object* v_val_5189_; lean_object* v___x_5191_; uint8_t v_isShared_5192_; uint8_t v_isSharedCheck_5203_; 
v_val_5189_ = lean_ctor_get(v_a_5175_, 0);
v_isSharedCheck_5203_ = !lean_is_exclusive(v_a_5175_);
if (v_isSharedCheck_5203_ == 0)
{
v___x_5191_ = v_a_5175_;
v_isShared_5192_ = v_isSharedCheck_5203_;
goto v_resetjp_5190_;
}
else
{
lean_inc(v_val_5189_);
lean_dec(v_a_5175_);
v___x_5191_ = lean_box(0);
v_isShared_5192_ = v_isSharedCheck_5203_;
goto v_resetjp_5190_;
}
v_resetjp_5190_:
{
lean_object* v_numParams_5193_; lean_object* v_numIndices_5194_; lean_object* v___x_5195_; uint8_t v___x_5196_; 
v_numParams_5193_ = lean_ctor_get(v_val_5189_, 1);
lean_inc(v_numParams_5193_);
v_numIndices_5194_ = lean_ctor_get(v_val_5189_, 2);
lean_inc(v_numIndices_5194_);
lean_dec_ref(v_val_5189_);
v___x_5195_ = lean_unsigned_to_nat(0u);
v___x_5196_ = lean_nat_dec_eq(v_numIndices_5194_, v___x_5195_);
lean_dec(v_numIndices_5194_);
if (v___x_5196_ == 0)
{
lean_object* v___x_5197_; uint8_t v___x_5198_; 
lean_del_object(v___x_5191_);
v___x_5197_ = lean_array_get_size(v_x_5160_);
v___x_5198_ = lean_nat_dec_le(v_numParams_5193_, v___x_5195_);
if (v___x_5198_ == 0)
{
v_lower_5180_ = v_numParams_5193_;
v_upper_5181_ = v___x_5197_;
goto v___jp_5179_;
}
else
{
lean_dec(v_numParams_5193_);
v_lower_5180_ = v___x_5195_;
v_upper_5181_ = v___x_5197_;
goto v___jp_5179_;
}
}
else
{
lean_object* v___x_5199_; lean_object* v___x_5201_; 
lean_dec(v_numParams_5193_);
lean_del_object(v___x_5177_);
lean_dec_ref(v_x_5160_);
v___x_5199_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2___closed__0));
if (v_isShared_5192_ == 0)
{
lean_ctor_set_tag(v___x_5191_, 0);
lean_ctor_set(v___x_5191_, 0, v___x_5199_);
v___x_5201_ = v___x_5191_;
goto v_reusejp_5200_;
}
else
{
lean_object* v_reuseFailAlloc_5202_; 
v_reuseFailAlloc_5202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5202_, 0, v___x_5199_);
v___x_5201_ = v_reuseFailAlloc_5202_;
goto v_reusejp_5200_;
}
v_reusejp_5200_:
{
return v___x_5201_;
}
}
}
}
else
{
lean_object* v___x_5204_; lean_object* v___x_5205_; 
lean_del_object(v___x_5177_);
lean_dec(v_a_5175_);
lean_dec_ref(v_x_5160_);
v___x_5204_ = lean_box(0);
v___x_5205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5205_, 0, v___x_5204_);
return v___x_5205_;
}
v___jp_5179_:
{
lean_object* v___x_5182_; lean_object* v___x_5183_; lean_object* v___x_5184_; lean_object* v___x_5185_; lean_object* v___x_5187_; 
v___x_5182_ = l_Array_toSubarray___redArg(v_x_5160_, v_lower_5180_, v_upper_5181_);
v___x_5183_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_5184_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(v___x_5182_, v___x_5183_);
v___x_5185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5185_, 0, v___x_5184_);
if (v_isShared_5178_ == 0)
{
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
lean_object* v_a_5207_; lean_object* v___x_5209_; uint8_t v_isShared_5210_; uint8_t v_isSharedCheck_5214_; 
lean_dec_ref(v_x_5160_);
v_a_5207_ = lean_ctor_get(v___x_5174_, 0);
v_isSharedCheck_5214_ = !lean_is_exclusive(v___x_5174_);
if (v_isSharedCheck_5214_ == 0)
{
v___x_5209_ = v___x_5174_;
v_isShared_5210_ = v_isSharedCheck_5214_;
goto v_resetjp_5208_;
}
else
{
lean_inc(v_a_5207_);
lean_dec(v___x_5174_);
v___x_5209_ = lean_box(0);
v_isShared_5210_ = v_isSharedCheck_5214_;
goto v_resetjp_5208_;
}
v_resetjp_5208_:
{
lean_object* v___x_5212_; 
if (v_isShared_5210_ == 0)
{
v___x_5212_ = v___x_5209_;
goto v_reusejp_5211_;
}
else
{
lean_object* v_reuseFailAlloc_5213_; 
v_reuseFailAlloc_5213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5213_, 0, v_a_5207_);
v___x_5212_ = v_reuseFailAlloc_5213_;
goto v_reusejp_5211_;
}
v_reusejp_5211_:
{
return v___x_5212_;
}
}
}
}
else
{
lean_object* v___x_5215_; lean_object* v___x_5216_; 
lean_dec_ref(v_x_5160_);
lean_dec_ref(v_x_5159_);
v___x_5215_ = lean_box(0);
v___x_5216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5216_, 0, v___x_5215_);
return v___x_5216_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2___boxed(lean_object* v_x_5217_, lean_object* v_x_5218_, lean_object* v_x_5219_, lean_object* v___y_5220_, lean_object* v___y_5221_, lean_object* v___y_5222_, lean_object* v___y_5223_, lean_object* v___y_5224_){
_start:
{
lean_object* v_res_5225_; 
v_res_5225_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(v_x_5217_, v_x_5218_, v_x_5219_, v___y_5220_, v___y_5221_, v___y_5222_, v___y_5223_);
lean_dec(v___y_5223_);
lean_dec_ref(v___y_5222_);
lean_dec(v___y_5221_);
lean_dec_ref(v___y_5220_);
return v_res_5225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorAppIndices_x3f(lean_object* v_ctorApp_5226_, lean_object* v_a_5227_, lean_object* v_a_5228_, lean_object* v_a_5229_, lean_object* v_a_5230_){
_start:
{
lean_object* v___x_5232_; 
lean_inc(v_a_5230_);
lean_inc_ref(v_a_5229_);
lean_inc(v_a_5228_);
lean_inc_ref(v_a_5227_);
v___x_5232_ = lean_infer_type(v_ctorApp_5226_, v_a_5227_, v_a_5228_, v_a_5229_, v_a_5230_);
if (lean_obj_tag(v___x_5232_) == 0)
{
lean_object* v_a_5233_; lean_object* v___x_5234_; 
v_a_5233_ = lean_ctor_get(v___x_5232_, 0);
lean_inc(v_a_5233_);
lean_dec_ref_known(v___x_5232_, 1);
v___x_5234_ = l_Lean_Meta_whnfD(v_a_5233_, v_a_5227_, v_a_5228_, v_a_5229_, v_a_5230_);
if (lean_obj_tag(v___x_5234_) == 0)
{
lean_object* v_a_5235_; lean_object* v_dummy_5236_; lean_object* v_nargs_5237_; lean_object* v___x_5238_; lean_object* v___x_5239_; lean_object* v___x_5240_; lean_object* v___x_5241_; 
v_a_5235_ = lean_ctor_get(v___x_5234_, 0);
lean_inc(v_a_5235_);
lean_dec_ref_known(v___x_5234_, 1);
v_dummy_5236_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0);
v_nargs_5237_ = l_Lean_Expr_getAppNumArgs(v_a_5235_);
lean_inc(v_nargs_5237_);
v___x_5238_ = lean_mk_array(v_nargs_5237_, v_dummy_5236_);
v___x_5239_ = lean_unsigned_to_nat(1u);
v___x_5240_ = lean_nat_sub(v_nargs_5237_, v___x_5239_);
lean_dec(v_nargs_5237_);
v___x_5241_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(v_a_5235_, v___x_5238_, v___x_5240_, v_a_5227_, v_a_5228_, v_a_5229_, v_a_5230_);
return v___x_5241_;
}
else
{
lean_object* v_a_5242_; lean_object* v___x_5244_; uint8_t v_isShared_5245_; uint8_t v_isSharedCheck_5249_; 
v_a_5242_ = lean_ctor_get(v___x_5234_, 0);
v_isSharedCheck_5249_ = !lean_is_exclusive(v___x_5234_);
if (v_isSharedCheck_5249_ == 0)
{
v___x_5244_ = v___x_5234_;
v_isShared_5245_ = v_isSharedCheck_5249_;
goto v_resetjp_5243_;
}
else
{
lean_inc(v_a_5242_);
lean_dec(v___x_5234_);
v___x_5244_ = lean_box(0);
v_isShared_5245_ = v_isSharedCheck_5249_;
goto v_resetjp_5243_;
}
v_resetjp_5243_:
{
lean_object* v___x_5247_; 
if (v_isShared_5245_ == 0)
{
v___x_5247_ = v___x_5244_;
goto v_reusejp_5246_;
}
else
{
lean_object* v_reuseFailAlloc_5248_; 
v_reuseFailAlloc_5248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5248_, 0, v_a_5242_);
v___x_5247_ = v_reuseFailAlloc_5248_;
goto v_reusejp_5246_;
}
v_reusejp_5246_:
{
return v___x_5247_;
}
}
}
}
else
{
lean_object* v_a_5250_; lean_object* v___x_5252_; uint8_t v_isShared_5253_; uint8_t v_isSharedCheck_5257_; 
v_a_5250_ = lean_ctor_get(v___x_5232_, 0);
v_isSharedCheck_5257_ = !lean_is_exclusive(v___x_5232_);
if (v_isSharedCheck_5257_ == 0)
{
v___x_5252_ = v___x_5232_;
v_isShared_5253_ = v_isSharedCheck_5257_;
goto v_resetjp_5251_;
}
else
{
lean_inc(v_a_5250_);
lean_dec(v___x_5232_);
v___x_5252_ = lean_box(0);
v_isShared_5253_ = v_isSharedCheck_5257_;
goto v_resetjp_5251_;
}
v_resetjp_5251_:
{
lean_object* v___x_5255_; 
if (v_isShared_5253_ == 0)
{
v___x_5255_ = v___x_5252_;
goto v_reusejp_5254_;
}
else
{
lean_object* v_reuseFailAlloc_5256_; 
v_reuseFailAlloc_5256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5256_, 0, v_a_5250_);
v___x_5255_ = v_reuseFailAlloc_5256_;
goto v_reusejp_5254_;
}
v_reusejp_5254_:
{
return v___x_5255_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorAppIndices_x3f___boxed(lean_object* v_ctorApp_5258_, lean_object* v_a_5259_, lean_object* v_a_5260_, lean_object* v_a_5261_, lean_object* v_a_5262_, lean_object* v_a_5263_){
_start:
{
lean_object* v_res_5264_; 
v_res_5264_ = l_Lean_Meta_getCtorAppIndices_x3f(v_ctorApp_5258_, v_a_5259_, v_a_5260_, v_a_5261_, v_a_5262_);
lean_dec(v_a_5262_);
lean_dec_ref(v_a_5261_);
lean_dec(v_a_5260_);
lean_dec_ref(v_a_5259_);
return v_res_5264_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1(lean_object* v_inst_5265_, lean_object* v_R_5266_, lean_object* v_a_5267_, lean_object* v_b_5268_){
_start:
{
lean_object* v___x_5269_; 
v___x_5269_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(v_a_5267_, v_b_5268_);
return v___x_5269_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0(lean_object* v_00_u03b1_5270_, lean_object* v_constName_5271_, lean_object* v___y_5272_, lean_object* v___y_5273_, lean_object* v___y_5274_, lean_object* v___y_5275_){
_start:
{
lean_object* v___x_5277_; 
v___x_5277_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(v_constName_5271_, v___y_5272_, v___y_5273_, v___y_5274_, v___y_5275_);
return v___x_5277_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b1_5278_, lean_object* v_constName_5279_, lean_object* v___y_5280_, lean_object* v___y_5281_, lean_object* v___y_5282_, lean_object* v___y_5283_, lean_object* v___y_5284_){
_start:
{
lean_object* v_res_5285_; 
v_res_5285_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0(v_00_u03b1_5278_, v_constName_5279_, v___y_5280_, v___y_5281_, v___y_5282_, v___y_5283_);
lean_dec(v___y_5283_);
lean_dec_ref(v___y_5282_);
lean_dec(v___y_5281_);
lean_dec_ref(v___y_5280_);
return v_res_5285_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_5286_, lean_object* v_ref_5287_, lean_object* v_constName_5288_, lean_object* v___y_5289_, lean_object* v___y_5290_, lean_object* v___y_5291_, lean_object* v___y_5292_){
_start:
{
lean_object* v___x_5294_; 
v___x_5294_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(v_ref_5287_, v_constName_5288_, v___y_5289_, v___y_5290_, v___y_5291_, v___y_5292_);
return v___x_5294_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_5295_, lean_object* v_ref_5296_, lean_object* v_constName_5297_, lean_object* v___y_5298_, lean_object* v___y_5299_, lean_object* v___y_5300_, lean_object* v___y_5301_, lean_object* v___y_5302_){
_start:
{
lean_object* v_res_5303_; 
v_res_5303_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1(v_00_u03b1_5295_, v_ref_5296_, v_constName_5297_, v___y_5298_, v___y_5299_, v___y_5300_, v___y_5301_);
lean_dec(v___y_5301_);
lean_dec_ref(v___y_5300_);
lean_dec(v___y_5299_);
lean_dec_ref(v___y_5298_);
lean_dec(v_ref_5296_);
return v_res_5303_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_5304_, lean_object* v_ref_5305_, lean_object* v_msg_5306_, lean_object* v_declHint_5307_, lean_object* v___y_5308_, lean_object* v___y_5309_, lean_object* v___y_5310_, lean_object* v___y_5311_){
_start:
{
lean_object* v___x_5313_; 
v___x_5313_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5305_, v_msg_5306_, v_declHint_5307_, v___y_5308_, v___y_5309_, v___y_5310_, v___y_5311_);
return v___x_5313_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_5314_, lean_object* v_ref_5315_, lean_object* v_msg_5316_, lean_object* v_declHint_5317_, lean_object* v___y_5318_, lean_object* v___y_5319_, lean_object* v___y_5320_, lean_object* v___y_5321_, lean_object* v___y_5322_){
_start:
{
lean_object* v_res_5323_; 
v_res_5323_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_5314_, v_ref_5315_, v_msg_5316_, v_declHint_5317_, v___y_5318_, v___y_5319_, v___y_5320_, v___y_5321_);
lean_dec(v___y_5321_);
lean_dec_ref(v___y_5320_);
lean_dec(v___y_5319_);
lean_dec_ref(v___y_5318_);
lean_dec(v_ref_5315_);
return v_res_5323_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_msg_5324_, lean_object* v_declHint_5325_, lean_object* v___y_5326_, lean_object* v___y_5327_, lean_object* v___y_5328_, lean_object* v___y_5329_){
_start:
{
lean_object* v___x_5331_; 
v___x_5331_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_5324_, v_declHint_5325_, v___y_5329_);
return v___x_5331_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_5332_, lean_object* v_declHint_5333_, lean_object* v___y_5334_, lean_object* v___y_5335_, lean_object* v___y_5336_, lean_object* v___y_5337_, lean_object* v___y_5338_){
_start:
{
lean_object* v_res_5339_; 
v_res_5339_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_5332_, v_declHint_5333_, v___y_5334_, v___y_5335_, v___y_5336_, v___y_5337_);
lean_dec(v___y_5337_);
lean_dec_ref(v___y_5336_);
lean_dec(v___y_5335_);
lean_dec_ref(v___y_5334_);
return v_res_5339_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_5340_, lean_object* v_ref_5341_, lean_object* v_msg_5342_, lean_object* v___y_5343_, lean_object* v___y_5344_, lean_object* v___y_5345_, lean_object* v___y_5346_){
_start:
{
lean_object* v___x_5348_; 
v___x_5348_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5341_, v_msg_5342_, v___y_5343_, v___y_5344_, v___y_5345_, v___y_5346_);
return v___x_5348_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_5349_, lean_object* v_ref_5350_, lean_object* v_msg_5351_, lean_object* v___y_5352_, lean_object* v___y_5353_, lean_object* v___y_5354_, lean_object* v___y_5355_, lean_object* v___y_5356_){
_start:
{
lean_object* v_res_5357_; 
v_res_5357_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_5349_, v_ref_5350_, v_msg_5351_, v___y_5352_, v___y_5353_, v___y_5354_, v___y_5355_);
lean_dec(v___y_5355_);
lean_dec_ref(v___y_5354_);
lean_dec(v___y_5353_);
lean_dec_ref(v___y_5352_);
lean_dec(v_ref_5350_);
return v_res_5357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0___boxed(lean_object* v_i_5358_, lean_object* v_body_5359_, lean_object* v_args2_5360_, lean_object* v_ctorVal_5361_, lean_object* v_args1_5362_, lean_object* v_k_5363_, lean_object* v_arg2_5364_, lean_object* v___y_5365_, lean_object* v___y_5366_, lean_object* v___y_5367_, lean_object* v___y_5368_, lean_object* v___y_5369_){
_start:
{
lean_object* v_res_5370_; 
v_res_5370_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0(v_i_5358_, v_body_5359_, v_args2_5360_, v_ctorVal_5361_, v_args1_5362_, v_k_5363_, v_arg2_5364_, v___y_5365_, v___y_5366_, v___y_5367_, v___y_5368_);
lean_dec(v___y_5368_);
lean_dec_ref(v___y_5367_);
lean_dec(v___y_5366_);
lean_dec_ref(v___y_5365_);
lean_dec_ref(v_body_5359_);
lean_dec(v_i_5358_);
return v_res_5370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(lean_object* v_ctorVal_5371_, lean_object* v_args1_5372_, lean_object* v_k_5373_, lean_object* v_i_5374_, lean_object* v_type_5375_, lean_object* v_args2_5376_, lean_object* v_a_5377_, lean_object* v_a_5378_, lean_object* v_a_5379_, lean_object* v_a_5380_){
_start:
{
lean_object* v___x_5382_; uint8_t v___x_5383_; 
v___x_5382_ = lean_array_get_size(v_args1_5372_);
v___x_5383_ = lean_nat_dec_lt(v_i_5374_, v___x_5382_);
if (v___x_5383_ == 0)
{
lean_object* v___x_5384_; 
lean_dec_ref(v_type_5375_);
lean_dec(v_i_5374_);
lean_dec_ref(v_args1_5372_);
lean_dec_ref(v_ctorVal_5371_);
lean_inc(v_a_5380_);
lean_inc_ref(v_a_5379_);
lean_inc(v_a_5378_);
lean_inc_ref(v_a_5377_);
v___x_5384_ = lean_apply_6(v_k_5373_, v_args2_5376_, v_a_5377_, v_a_5378_, v_a_5379_, v_a_5380_, lean_box(0));
return v___x_5384_;
}
else
{
lean_object* v___x_5385_; 
lean_inc(v_a_5380_);
lean_inc_ref(v_a_5379_);
lean_inc(v_a_5378_);
lean_inc_ref(v_a_5377_);
v___x_5385_ = lean_whnf(v_type_5375_, v_a_5377_, v_a_5378_, v_a_5379_, v_a_5380_);
if (lean_obj_tag(v___x_5385_) == 0)
{
lean_object* v_a_5386_; 
v_a_5386_ = lean_ctor_get(v___x_5385_, 0);
lean_inc(v_a_5386_);
lean_dec_ref_known(v___x_5385_, 1);
if (lean_obj_tag(v_a_5386_) == 7)
{
lean_object* v_binderName_5387_; lean_object* v_binderType_5388_; lean_object* v_body_5389_; lean_object* v___f_5390_; uint8_t v___x_5391_; uint8_t v___x_5392_; lean_object* v___x_5393_; 
v_binderName_5387_ = lean_ctor_get(v_a_5386_, 0);
lean_inc(v_binderName_5387_);
v_binderType_5388_ = lean_ctor_get(v_a_5386_, 1);
lean_inc_ref(v_binderType_5388_);
v_body_5389_ = lean_ctor_get(v_a_5386_, 2);
lean_inc_ref(v_body_5389_);
lean_dec_ref_known(v_a_5386_, 3);
v___f_5390_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0___boxed), 12, 6);
lean_closure_set(v___f_5390_, 0, v_i_5374_);
lean_closure_set(v___f_5390_, 1, v_body_5389_);
lean_closure_set(v___f_5390_, 2, v_args2_5376_);
lean_closure_set(v___f_5390_, 3, v_ctorVal_5371_);
lean_closure_set(v___f_5390_, 4, v_args1_5372_);
lean_closure_set(v___f_5390_, 5, v_k_5373_);
v___x_5391_ = 1;
v___x_5392_ = 0;
v___x_5393_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_binderName_5387_, v___x_5391_, v_binderType_5388_, v___f_5390_, v___x_5392_, v_a_5377_, v_a_5378_, v_a_5379_, v_a_5380_);
return v___x_5393_;
}
else
{
lean_object* v_toConstantVal_5394_; lean_object* v_name_5395_; lean_object* v___x_5396_; lean_object* v___x_5397_; lean_object* v___x_5398_; lean_object* v___x_5399_; lean_object* v___x_5400_; lean_object* v___x_5401_; 
lean_dec(v_a_5386_);
lean_dec_ref(v_args2_5376_);
lean_dec(v_i_5374_);
lean_dec_ref(v_k_5373_);
lean_dec_ref(v_args1_5372_);
v_toConstantVal_5394_ = lean_ctor_get(v_ctorVal_5371_, 0);
lean_inc_ref(v_toConstantVal_5394_);
lean_dec_ref(v_ctorVal_5371_);
v_name_5395_ = lean_ctor_get(v_toConstantVal_5394_, 0);
lean_inc(v_name_5395_);
lean_dec_ref(v_toConstantVal_5394_);
v___x_5396_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1);
v___x_5397_ = l_Lean_MessageData_ofName(v_name_5395_);
v___x_5398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5398_, 0, v___x_5396_);
lean_ctor_set(v___x_5398_, 1, v___x_5397_);
v___x_5399_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_5400_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5400_, 0, v___x_5398_);
lean_ctor_set(v___x_5400_, 1, v___x_5399_);
v___x_5401_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_5400_, v_a_5377_, v_a_5378_, v_a_5379_, v_a_5380_);
return v___x_5401_;
}
}
else
{
lean_object* v_a_5402_; lean_object* v___x_5404_; uint8_t v_isShared_5405_; uint8_t v_isSharedCheck_5409_; 
lean_dec_ref(v_args2_5376_);
lean_dec(v_i_5374_);
lean_dec_ref(v_k_5373_);
lean_dec_ref(v_args1_5372_);
lean_dec_ref(v_ctorVal_5371_);
v_a_5402_ = lean_ctor_get(v___x_5385_, 0);
v_isSharedCheck_5409_ = !lean_is_exclusive(v___x_5385_);
if (v_isSharedCheck_5409_ == 0)
{
v___x_5404_ = v___x_5385_;
v_isShared_5405_ = v_isSharedCheck_5409_;
goto v_resetjp_5403_;
}
else
{
lean_inc(v_a_5402_);
lean_dec(v___x_5385_);
v___x_5404_ = lean_box(0);
v_isShared_5405_ = v_isSharedCheck_5409_;
goto v_resetjp_5403_;
}
v_resetjp_5403_:
{
lean_object* v___x_5407_; 
if (v_isShared_5405_ == 0)
{
v___x_5407_ = v___x_5404_;
goto v_reusejp_5406_;
}
else
{
lean_object* v_reuseFailAlloc_5408_; 
v_reuseFailAlloc_5408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5408_, 0, v_a_5402_);
v___x_5407_ = v_reuseFailAlloc_5408_;
goto v_reusejp_5406_;
}
v_reusejp_5406_:
{
return v___x_5407_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0(lean_object* v_i_5410_, lean_object* v_body_5411_, lean_object* v_args2_5412_, lean_object* v_ctorVal_5413_, lean_object* v_args1_5414_, lean_object* v_k_5415_, lean_object* v_arg2_5416_, lean_object* v___y_5417_, lean_object* v___y_5418_, lean_object* v___y_5419_, lean_object* v___y_5420_){
_start:
{
lean_object* v___x_5422_; lean_object* v___x_5423_; lean_object* v___x_5424_; lean_object* v___x_5425_; lean_object* v___x_5426_; 
v___x_5422_ = lean_unsigned_to_nat(1u);
v___x_5423_ = lean_nat_add(v_i_5410_, v___x_5422_);
v___x_5424_ = lean_expr_instantiate1(v_body_5411_, v_arg2_5416_);
v___x_5425_ = lean_array_push(v_args2_5412_, v_arg2_5416_);
v___x_5426_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(v_ctorVal_5413_, v_args1_5414_, v_k_5415_, v___x_5423_, v___x_5424_, v___x_5425_, v___y_5417_, v___y_5418_, v___y_5419_, v___y_5420_);
return v___x_5426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___boxed(lean_object* v_ctorVal_5427_, lean_object* v_args1_5428_, lean_object* v_k_5429_, lean_object* v_i_5430_, lean_object* v_type_5431_, lean_object* v_args2_5432_, lean_object* v_a_5433_, lean_object* v_a_5434_, lean_object* v_a_5435_, lean_object* v_a_5436_, lean_object* v_a_5437_){
_start:
{
lean_object* v_res_5438_; 
v_res_5438_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(v_ctorVal_5427_, v_args1_5428_, v_k_5429_, v_i_5430_, v_type_5431_, v_args2_5432_, v_a_5433_, v_a_5434_, v_a_5435_, v_a_5436_);
lean_dec(v_a_5436_);
lean_dec_ref(v_a_5435_);
lean_dec(v_a_5434_);
lean_dec_ref(v_a_5433_);
return v_res_5438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0(lean_object* v_name_5439_, lean_object* v_us_5440_, lean_object* v_args1_5441_, lean_object* v___x_5442_, lean_object* v_numParams_5443_, lean_object* v___x_5444_, lean_object* v_args2_5445_, lean_object* v___y_5446_, lean_object* v___y_5447_, lean_object* v___y_5448_, lean_object* v___y_5449_){
_start:
{
lean_object* v___x_5451_; lean_object* v___x_5452_; lean_object* v___x_5453_; lean_object* v___x_5454_; 
lean_inc(v_us_5440_);
v___x_5451_ = l_Lean_mkConst(v_name_5439_, v_us_5440_);
lean_inc_ref(v___x_5451_);
v___x_5452_ = l_Lean_mkAppN(v___x_5451_, v_args1_5441_);
v___x_5453_ = l_Lean_mkAppN(v___x_5451_, v_args2_5445_);
lean_inc_ref(v___x_5453_);
lean_inc_ref(v___x_5452_);
v___x_5454_ = l_Lean_Meta_mkEqHEq(v___x_5452_, v___x_5453_, v___y_5446_, v___y_5447_, v___y_5448_, v___y_5449_);
if (lean_obj_tag(v___x_5454_) == 0)
{
lean_object* v_a_5455_; lean_object* v___x_5456_; uint8_t v___x_5457_; lean_object* v___x_5458_; 
v_a_5455_ = lean_ctor_get(v___x_5454_, 0);
lean_inc(v_a_5455_);
lean_dec_ref_known(v___x_5454_, 1);
lean_inc_ref_n(v_args2_5445_, 2);
v___x_5456_ = l_Array_toSubarray___redArg(v_args2_5445_, v___x_5442_, v_numParams_5443_);
v___x_5457_ = 1;
v___x_5458_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v_args1_5441_, v_args2_5445_, v___x_5457_, v___y_5446_, v___y_5447_, v___y_5448_, v___y_5449_);
if (lean_obj_tag(v___x_5458_) == 0)
{
lean_object* v_a_5459_; lean_object* v___x_5461_; uint8_t v_isShared_5462_; uint8_t v_isSharedCheck_5579_; 
v_a_5459_ = lean_ctor_get(v___x_5458_, 0);
v_isSharedCheck_5579_ = !lean_is_exclusive(v___x_5458_);
if (v_isSharedCheck_5579_ == 0)
{
v___x_5461_ = v___x_5458_;
v_isShared_5462_ = v_isSharedCheck_5579_;
goto v_resetjp_5460_;
}
else
{
lean_inc(v_a_5459_);
lean_dec(v___x_5458_);
v___x_5461_ = lean_box(0);
v_isShared_5462_ = v_isSharedCheck_5579_;
goto v_resetjp_5460_;
}
v_resetjp_5460_:
{
lean_object* v___x_5463_; 
v___x_5463_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f(v_a_5459_);
if (lean_obj_tag(v___x_5463_) == 1)
{
lean_object* v_val_5464_; lean_object* v___x_5465_; 
lean_del_object(v___x_5461_);
v_val_5464_ = lean_ctor_get(v___x_5463_, 0);
lean_inc(v_val_5464_);
lean_dec_ref_known(v___x_5463_, 1);
v___x_5465_ = l_Lean_mkArrow(v_a_5455_, v_val_5464_, v___y_5448_, v___y_5449_);
if (lean_obj_tag(v___x_5465_) == 0)
{
lean_object* v_a_5466_; lean_object* v___x_5467_; 
v_a_5466_ = lean_ctor_get(v___x_5465_, 0);
lean_inc(v_a_5466_);
lean_dec_ref_known(v___x_5465_, 1);
v___x_5467_ = l_Lean_Meta_getCtorAppIndices_x3f(v___x_5452_, v___y_5446_, v___y_5447_, v___y_5448_, v___y_5449_);
if (lean_obj_tag(v___x_5467_) == 0)
{
lean_object* v_a_5468_; lean_object* v___x_5470_; uint8_t v_isShared_5471_; uint8_t v_isSharedCheck_5558_; 
v_a_5468_ = lean_ctor_get(v___x_5467_, 0);
v_isSharedCheck_5558_ = !lean_is_exclusive(v___x_5467_);
if (v_isSharedCheck_5558_ == 0)
{
v___x_5470_ = v___x_5467_;
v_isShared_5471_ = v_isSharedCheck_5558_;
goto v_resetjp_5469_;
}
else
{
lean_inc(v_a_5468_);
lean_dec(v___x_5467_);
v___x_5470_ = lean_box(0);
v_isShared_5471_ = v_isSharedCheck_5558_;
goto v_resetjp_5469_;
}
v_resetjp_5469_:
{
if (lean_obj_tag(v_a_5468_) == 1)
{
lean_object* v_val_5472_; lean_object* v___x_5473_; 
lean_del_object(v___x_5470_);
v_val_5472_ = lean_ctor_get(v_a_5468_, 0);
lean_inc(v_val_5472_);
lean_dec_ref_known(v_a_5468_, 1);
v___x_5473_ = l_Lean_Meta_getCtorAppIndices_x3f(v___x_5453_, v___y_5446_, v___y_5447_, v___y_5448_, v___y_5449_);
if (lean_obj_tag(v___x_5473_) == 0)
{
lean_object* v_a_5474_; lean_object* v___x_5476_; uint8_t v_isShared_5477_; uint8_t v_isSharedCheck_5545_; 
v_a_5474_ = lean_ctor_get(v___x_5473_, 0);
v_isSharedCheck_5545_ = !lean_is_exclusive(v___x_5473_);
if (v_isSharedCheck_5545_ == 0)
{
v___x_5476_ = v___x_5473_;
v_isShared_5477_ = v_isSharedCheck_5545_;
goto v_resetjp_5475_;
}
else
{
lean_inc(v_a_5474_);
lean_dec(v___x_5473_);
v___x_5476_ = lean_box(0);
v_isShared_5477_ = v_isSharedCheck_5545_;
goto v_resetjp_5475_;
}
v_resetjp_5475_:
{
if (lean_obj_tag(v_a_5474_) == 1)
{
lean_object* v_val_5478_; lean_object* v___x_5480_; uint8_t v_isShared_5481_; uint8_t v_isSharedCheck_5540_; 
lean_del_object(v___x_5476_);
v_val_5478_ = lean_ctor_get(v_a_5474_, 0);
v_isSharedCheck_5540_ = !lean_is_exclusive(v_a_5474_);
if (v_isSharedCheck_5540_ == 0)
{
v___x_5480_ = v_a_5474_;
v_isShared_5481_ = v_isSharedCheck_5540_;
goto v_resetjp_5479_;
}
else
{
lean_inc(v_val_5478_);
lean_dec(v_a_5474_);
v___x_5480_ = lean_box(0);
v_isShared_5481_ = v_isSharedCheck_5540_;
goto v_resetjp_5479_;
}
v_resetjp_5479_:
{
lean_object* v___x_5482_; lean_object* v___x_5483_; lean_object* v___x_5484_; lean_object* v___x_5485_; uint8_t v___x_5486_; lean_object* v___x_5487_; 
v___x_5482_ = l_Subarray_copy___redArg(v___x_5444_);
v___x_5483_ = l_Array_append___redArg(v___x_5482_, v_val_5472_);
v___x_5484_ = l_Subarray_copy___redArg(v___x_5456_);
v___x_5485_ = l_Array_append___redArg(v___x_5484_, v_val_5478_);
lean_dec(v_val_5478_);
v___x_5486_ = 0;
v___x_5487_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v___x_5483_, v___x_5485_, v___x_5486_, v___y_5446_, v___y_5447_, v___y_5448_, v___y_5449_);
lean_dec_ref(v___x_5483_);
if (lean_obj_tag(v___x_5487_) == 0)
{
lean_object* v_a_5488_; lean_object* v___x_5489_; 
v_a_5488_ = lean_ctor_get(v___x_5487_, 0);
lean_inc(v_a_5488_);
lean_dec_ref_known(v___x_5487_, 1);
v___x_5489_ = l_Lean_mkArrowN(v_a_5488_, v_a_5466_, v___y_5448_, v___y_5449_);
lean_dec(v_a_5488_);
if (lean_obj_tag(v___x_5489_) == 0)
{
lean_object* v_a_5490_; uint8_t v___x_5491_; lean_object* v___x_5492_; 
v_a_5490_ = lean_ctor_get(v___x_5489_, 0);
lean_inc(v_a_5490_);
lean_dec_ref_known(v___x_5489_, 1);
v___x_5491_ = 1;
v___x_5492_ = l_Lean_Meta_mkForallFVars(v_args2_5445_, v_a_5490_, v___x_5486_, v___x_5457_, v___x_5457_, v___x_5491_, v___y_5446_, v___y_5447_, v___y_5448_, v___y_5449_);
lean_dec_ref(v_args2_5445_);
if (lean_obj_tag(v___x_5492_) == 0)
{
lean_object* v_a_5493_; lean_object* v___x_5494_; 
v_a_5493_ = lean_ctor_get(v___x_5492_, 0);
lean_inc(v_a_5493_);
lean_dec_ref_known(v___x_5492_, 1);
v___x_5494_ = l_Lean_Meta_mkForallFVars(v_args1_5441_, v_a_5493_, v___x_5486_, v___x_5457_, v___x_5457_, v___x_5491_, v___y_5446_, v___y_5447_, v___y_5448_, v___y_5449_);
if (lean_obj_tag(v___x_5494_) == 0)
{
lean_object* v_a_5495_; lean_object* v___x_5497_; uint8_t v_isShared_5498_; uint8_t v_isSharedCheck_5507_; 
v_a_5495_ = lean_ctor_get(v___x_5494_, 0);
v_isSharedCheck_5507_ = !lean_is_exclusive(v___x_5494_);
if (v_isSharedCheck_5507_ == 0)
{
v___x_5497_ = v___x_5494_;
v_isShared_5498_ = v_isSharedCheck_5507_;
goto v_resetjp_5496_;
}
else
{
lean_inc(v_a_5495_);
lean_dec(v___x_5494_);
v___x_5497_ = lean_box(0);
v_isShared_5498_ = v_isSharedCheck_5507_;
goto v_resetjp_5496_;
}
v_resetjp_5496_:
{
lean_object* v___x_5499_; lean_object* v___x_5500_; lean_object* v___x_5502_; 
v___x_5499_ = lean_array_get_size(v_val_5472_);
lean_dec(v_val_5472_);
v___x_5500_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5500_, 0, v_a_5495_);
lean_ctor_set(v___x_5500_, 1, v_us_5440_);
lean_ctor_set(v___x_5500_, 2, v___x_5499_);
if (v_isShared_5481_ == 0)
{
lean_ctor_set(v___x_5480_, 0, v___x_5500_);
v___x_5502_ = v___x_5480_;
goto v_reusejp_5501_;
}
else
{
lean_object* v_reuseFailAlloc_5506_; 
v_reuseFailAlloc_5506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5506_, 0, v___x_5500_);
v___x_5502_ = v_reuseFailAlloc_5506_;
goto v_reusejp_5501_;
}
v_reusejp_5501_:
{
lean_object* v___x_5504_; 
if (v_isShared_5498_ == 0)
{
lean_ctor_set(v___x_5497_, 0, v___x_5502_);
v___x_5504_ = v___x_5497_;
goto v_reusejp_5503_;
}
else
{
lean_object* v_reuseFailAlloc_5505_; 
v_reuseFailAlloc_5505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5505_, 0, v___x_5502_);
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
else
{
lean_object* v_a_5508_; lean_object* v___x_5510_; uint8_t v_isShared_5511_; uint8_t v_isSharedCheck_5515_; 
lean_del_object(v___x_5480_);
lean_dec(v_val_5472_);
lean_dec(v_us_5440_);
v_a_5508_ = lean_ctor_get(v___x_5494_, 0);
v_isSharedCheck_5515_ = !lean_is_exclusive(v___x_5494_);
if (v_isSharedCheck_5515_ == 0)
{
v___x_5510_ = v___x_5494_;
v_isShared_5511_ = v_isSharedCheck_5515_;
goto v_resetjp_5509_;
}
else
{
lean_inc(v_a_5508_);
lean_dec(v___x_5494_);
v___x_5510_ = lean_box(0);
v_isShared_5511_ = v_isSharedCheck_5515_;
goto v_resetjp_5509_;
}
v_resetjp_5509_:
{
lean_object* v___x_5513_; 
if (v_isShared_5511_ == 0)
{
v___x_5513_ = v___x_5510_;
goto v_reusejp_5512_;
}
else
{
lean_object* v_reuseFailAlloc_5514_; 
v_reuseFailAlloc_5514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5514_, 0, v_a_5508_);
v___x_5513_ = v_reuseFailAlloc_5514_;
goto v_reusejp_5512_;
}
v_reusejp_5512_:
{
return v___x_5513_;
}
}
}
}
else
{
lean_object* v_a_5516_; lean_object* v___x_5518_; uint8_t v_isShared_5519_; uint8_t v_isSharedCheck_5523_; 
lean_del_object(v___x_5480_);
lean_dec(v_val_5472_);
lean_dec(v_us_5440_);
v_a_5516_ = lean_ctor_get(v___x_5492_, 0);
v_isSharedCheck_5523_ = !lean_is_exclusive(v___x_5492_);
if (v_isSharedCheck_5523_ == 0)
{
v___x_5518_ = v___x_5492_;
v_isShared_5519_ = v_isSharedCheck_5523_;
goto v_resetjp_5517_;
}
else
{
lean_inc(v_a_5516_);
lean_dec(v___x_5492_);
v___x_5518_ = lean_box(0);
v_isShared_5519_ = v_isSharedCheck_5523_;
goto v_resetjp_5517_;
}
v_resetjp_5517_:
{
lean_object* v___x_5521_; 
if (v_isShared_5519_ == 0)
{
v___x_5521_ = v___x_5518_;
goto v_reusejp_5520_;
}
else
{
lean_object* v_reuseFailAlloc_5522_; 
v_reuseFailAlloc_5522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5522_, 0, v_a_5516_);
v___x_5521_ = v_reuseFailAlloc_5522_;
goto v_reusejp_5520_;
}
v_reusejp_5520_:
{
return v___x_5521_;
}
}
}
}
else
{
lean_object* v_a_5524_; lean_object* v___x_5526_; uint8_t v_isShared_5527_; uint8_t v_isSharedCheck_5531_; 
lean_del_object(v___x_5480_);
lean_dec(v_val_5472_);
lean_dec_ref(v_args2_5445_);
lean_dec(v_us_5440_);
v_a_5524_ = lean_ctor_get(v___x_5489_, 0);
v_isSharedCheck_5531_ = !lean_is_exclusive(v___x_5489_);
if (v_isSharedCheck_5531_ == 0)
{
v___x_5526_ = v___x_5489_;
v_isShared_5527_ = v_isSharedCheck_5531_;
goto v_resetjp_5525_;
}
else
{
lean_inc(v_a_5524_);
lean_dec(v___x_5489_);
v___x_5526_ = lean_box(0);
v_isShared_5527_ = v_isSharedCheck_5531_;
goto v_resetjp_5525_;
}
v_resetjp_5525_:
{
lean_object* v___x_5529_; 
if (v_isShared_5527_ == 0)
{
v___x_5529_ = v___x_5526_;
goto v_reusejp_5528_;
}
else
{
lean_object* v_reuseFailAlloc_5530_; 
v_reuseFailAlloc_5530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5530_, 0, v_a_5524_);
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
lean_del_object(v___x_5480_);
lean_dec(v_val_5472_);
lean_dec(v_a_5466_);
lean_dec_ref(v_args2_5445_);
lean_dec(v_us_5440_);
v_a_5532_ = lean_ctor_get(v___x_5487_, 0);
v_isSharedCheck_5539_ = !lean_is_exclusive(v___x_5487_);
if (v_isSharedCheck_5539_ == 0)
{
v___x_5534_ = v___x_5487_;
v_isShared_5535_ = v_isSharedCheck_5539_;
goto v_resetjp_5533_;
}
else
{
lean_inc(v_a_5532_);
lean_dec(v___x_5487_);
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
}
else
{
lean_object* v___x_5541_; lean_object* v___x_5543_; 
lean_dec(v_a_5474_);
lean_dec(v_val_5472_);
lean_dec(v_a_5466_);
lean_dec_ref(v___x_5456_);
lean_dec_ref(v_args2_5445_);
lean_dec_ref(v___x_5444_);
lean_dec(v_us_5440_);
v___x_5541_ = lean_box(0);
if (v_isShared_5477_ == 0)
{
lean_ctor_set(v___x_5476_, 0, v___x_5541_);
v___x_5543_ = v___x_5476_;
goto v_reusejp_5542_;
}
else
{
lean_object* v_reuseFailAlloc_5544_; 
v_reuseFailAlloc_5544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5544_, 0, v___x_5541_);
v___x_5543_ = v_reuseFailAlloc_5544_;
goto v_reusejp_5542_;
}
v_reusejp_5542_:
{
return v___x_5543_;
}
}
}
}
else
{
lean_object* v_a_5546_; lean_object* v___x_5548_; uint8_t v_isShared_5549_; uint8_t v_isSharedCheck_5553_; 
lean_dec(v_val_5472_);
lean_dec(v_a_5466_);
lean_dec_ref(v___x_5456_);
lean_dec_ref(v_args2_5445_);
lean_dec_ref(v___x_5444_);
lean_dec(v_us_5440_);
v_a_5546_ = lean_ctor_get(v___x_5473_, 0);
v_isSharedCheck_5553_ = !lean_is_exclusive(v___x_5473_);
if (v_isSharedCheck_5553_ == 0)
{
v___x_5548_ = v___x_5473_;
v_isShared_5549_ = v_isSharedCheck_5553_;
goto v_resetjp_5547_;
}
else
{
lean_inc(v_a_5546_);
lean_dec(v___x_5473_);
v___x_5548_ = lean_box(0);
v_isShared_5549_ = v_isSharedCheck_5553_;
goto v_resetjp_5547_;
}
v_resetjp_5547_:
{
lean_object* v___x_5551_; 
if (v_isShared_5549_ == 0)
{
v___x_5551_ = v___x_5548_;
goto v_reusejp_5550_;
}
else
{
lean_object* v_reuseFailAlloc_5552_; 
v_reuseFailAlloc_5552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5552_, 0, v_a_5546_);
v___x_5551_ = v_reuseFailAlloc_5552_;
goto v_reusejp_5550_;
}
v_reusejp_5550_:
{
return v___x_5551_;
}
}
}
}
else
{
lean_object* v___x_5554_; lean_object* v___x_5556_; 
lean_dec(v_a_5468_);
lean_dec(v_a_5466_);
lean_dec_ref(v___x_5456_);
lean_dec_ref(v___x_5453_);
lean_dec_ref(v_args2_5445_);
lean_dec_ref(v___x_5444_);
lean_dec(v_us_5440_);
v___x_5554_ = lean_box(0);
if (v_isShared_5471_ == 0)
{
lean_ctor_set(v___x_5470_, 0, v___x_5554_);
v___x_5556_ = v___x_5470_;
goto v_reusejp_5555_;
}
else
{
lean_object* v_reuseFailAlloc_5557_; 
v_reuseFailAlloc_5557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5557_, 0, v___x_5554_);
v___x_5556_ = v_reuseFailAlloc_5557_;
goto v_reusejp_5555_;
}
v_reusejp_5555_:
{
return v___x_5556_;
}
}
}
}
else
{
lean_object* v_a_5559_; lean_object* v___x_5561_; uint8_t v_isShared_5562_; uint8_t v_isSharedCheck_5566_; 
lean_dec(v_a_5466_);
lean_dec_ref(v___x_5456_);
lean_dec_ref(v___x_5453_);
lean_dec_ref(v_args2_5445_);
lean_dec_ref(v___x_5444_);
lean_dec(v_us_5440_);
v_a_5559_ = lean_ctor_get(v___x_5467_, 0);
v_isSharedCheck_5566_ = !lean_is_exclusive(v___x_5467_);
if (v_isSharedCheck_5566_ == 0)
{
v___x_5561_ = v___x_5467_;
v_isShared_5562_ = v_isSharedCheck_5566_;
goto v_resetjp_5560_;
}
else
{
lean_inc(v_a_5559_);
lean_dec(v___x_5467_);
v___x_5561_ = lean_box(0);
v_isShared_5562_ = v_isSharedCheck_5566_;
goto v_resetjp_5560_;
}
v_resetjp_5560_:
{
lean_object* v___x_5564_; 
if (v_isShared_5562_ == 0)
{
v___x_5564_ = v___x_5561_;
goto v_reusejp_5563_;
}
else
{
lean_object* v_reuseFailAlloc_5565_; 
v_reuseFailAlloc_5565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5565_, 0, v_a_5559_);
v___x_5564_ = v_reuseFailAlloc_5565_;
goto v_reusejp_5563_;
}
v_reusejp_5563_:
{
return v___x_5564_;
}
}
}
}
else
{
lean_object* v_a_5567_; lean_object* v___x_5569_; uint8_t v_isShared_5570_; uint8_t v_isSharedCheck_5574_; 
lean_dec_ref(v___x_5456_);
lean_dec_ref(v___x_5453_);
lean_dec_ref(v___x_5452_);
lean_dec_ref(v_args2_5445_);
lean_dec_ref(v___x_5444_);
lean_dec(v_us_5440_);
v_a_5567_ = lean_ctor_get(v___x_5465_, 0);
v_isSharedCheck_5574_ = !lean_is_exclusive(v___x_5465_);
if (v_isSharedCheck_5574_ == 0)
{
v___x_5569_ = v___x_5465_;
v_isShared_5570_ = v_isSharedCheck_5574_;
goto v_resetjp_5568_;
}
else
{
lean_inc(v_a_5567_);
lean_dec(v___x_5465_);
v___x_5569_ = lean_box(0);
v_isShared_5570_ = v_isSharedCheck_5574_;
goto v_resetjp_5568_;
}
v_resetjp_5568_:
{
lean_object* v___x_5572_; 
if (v_isShared_5570_ == 0)
{
v___x_5572_ = v___x_5569_;
goto v_reusejp_5571_;
}
else
{
lean_object* v_reuseFailAlloc_5573_; 
v_reuseFailAlloc_5573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5573_, 0, v_a_5567_);
v___x_5572_ = v_reuseFailAlloc_5573_;
goto v_reusejp_5571_;
}
v_reusejp_5571_:
{
return v___x_5572_;
}
}
}
}
else
{
lean_object* v___x_5575_; lean_object* v___x_5577_; 
lean_dec(v___x_5463_);
lean_dec_ref(v___x_5456_);
lean_dec(v_a_5455_);
lean_dec_ref(v___x_5453_);
lean_dec_ref(v___x_5452_);
lean_dec_ref(v_args2_5445_);
lean_dec_ref(v___x_5444_);
lean_dec(v_us_5440_);
v___x_5575_ = lean_box(0);
if (v_isShared_5462_ == 0)
{
lean_ctor_set(v___x_5461_, 0, v___x_5575_);
v___x_5577_ = v___x_5461_;
goto v_reusejp_5576_;
}
else
{
lean_object* v_reuseFailAlloc_5578_; 
v_reuseFailAlloc_5578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5578_, 0, v___x_5575_);
v___x_5577_ = v_reuseFailAlloc_5578_;
goto v_reusejp_5576_;
}
v_reusejp_5576_:
{
return v___x_5577_;
}
}
}
}
else
{
lean_object* v_a_5580_; lean_object* v___x_5582_; uint8_t v_isShared_5583_; uint8_t v_isSharedCheck_5587_; 
lean_dec_ref(v___x_5456_);
lean_dec(v_a_5455_);
lean_dec_ref(v___x_5453_);
lean_dec_ref(v___x_5452_);
lean_dec_ref(v_args2_5445_);
lean_dec_ref(v___x_5444_);
lean_dec(v_us_5440_);
v_a_5580_ = lean_ctor_get(v___x_5458_, 0);
v_isSharedCheck_5587_ = !lean_is_exclusive(v___x_5458_);
if (v_isSharedCheck_5587_ == 0)
{
v___x_5582_ = v___x_5458_;
v_isShared_5583_ = v_isSharedCheck_5587_;
goto v_resetjp_5581_;
}
else
{
lean_inc(v_a_5580_);
lean_dec(v___x_5458_);
v___x_5582_ = lean_box(0);
v_isShared_5583_ = v_isSharedCheck_5587_;
goto v_resetjp_5581_;
}
v_resetjp_5581_:
{
lean_object* v___x_5585_; 
if (v_isShared_5583_ == 0)
{
v___x_5585_ = v___x_5582_;
goto v_reusejp_5584_;
}
else
{
lean_object* v_reuseFailAlloc_5586_; 
v_reuseFailAlloc_5586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5586_, 0, v_a_5580_);
v___x_5585_ = v_reuseFailAlloc_5586_;
goto v_reusejp_5584_;
}
v_reusejp_5584_:
{
return v___x_5585_;
}
}
}
}
else
{
lean_object* v_a_5588_; lean_object* v___x_5590_; uint8_t v_isShared_5591_; uint8_t v_isSharedCheck_5595_; 
lean_dec_ref(v___x_5453_);
lean_dec_ref(v___x_5452_);
lean_dec_ref(v_args2_5445_);
lean_dec_ref(v___x_5444_);
lean_dec(v_numParams_5443_);
lean_dec(v___x_5442_);
lean_dec(v_us_5440_);
v_a_5588_ = lean_ctor_get(v___x_5454_, 0);
v_isSharedCheck_5595_ = !lean_is_exclusive(v___x_5454_);
if (v_isSharedCheck_5595_ == 0)
{
v___x_5590_ = v___x_5454_;
v_isShared_5591_ = v_isSharedCheck_5595_;
goto v_resetjp_5589_;
}
else
{
lean_inc(v_a_5588_);
lean_dec(v___x_5454_);
v___x_5590_ = lean_box(0);
v_isShared_5591_ = v_isSharedCheck_5595_;
goto v_resetjp_5589_;
}
v_resetjp_5589_:
{
lean_object* v___x_5593_; 
if (v_isShared_5591_ == 0)
{
v___x_5593_ = v___x_5590_;
goto v_reusejp_5592_;
}
else
{
lean_object* v_reuseFailAlloc_5594_; 
v_reuseFailAlloc_5594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5594_, 0, v_a_5588_);
v___x_5593_ = v_reuseFailAlloc_5594_;
goto v_reusejp_5592_;
}
v_reusejp_5592_:
{
return v___x_5593_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0___boxed(lean_object* v_name_5596_, lean_object* v_us_5597_, lean_object* v_args1_5598_, lean_object* v___x_5599_, lean_object* v_numParams_5600_, lean_object* v___x_5601_, lean_object* v_args2_5602_, lean_object* v___y_5603_, lean_object* v___y_5604_, lean_object* v___y_5605_, lean_object* v___y_5606_, lean_object* v___y_5607_){
_start:
{
lean_object* v_res_5608_; 
v_res_5608_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0(v_name_5596_, v_us_5597_, v_args1_5598_, v___x_5599_, v_numParams_5600_, v___x_5601_, v_args2_5602_, v___y_5603_, v___y_5604_, v___y_5605_, v___y_5606_);
lean_dec(v___y_5606_);
lean_dec_ref(v___y_5605_);
lean_dec(v___y_5604_);
lean_dec_ref(v___y_5603_);
lean_dec_ref(v_args1_5598_);
return v_res_5608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1(lean_object* v_numParams_5609_, lean_object* v_name_5610_, lean_object* v_us_5611_, lean_object* v_ctorVal_5612_, lean_object* v_a_5613_, lean_object* v_args1_5614_, lean_object* v_x_5615_, lean_object* v___y_5616_, lean_object* v___y_5617_, lean_object* v___y_5618_, lean_object* v___y_5619_){
_start:
{
lean_object* v___x_5621_; lean_object* v___x_5622_; lean_object* v___f_5623_; lean_object* v___x_5624_; lean_object* v___x_5625_; lean_object* v___x_5626_; 
v___x_5621_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_5609_);
lean_inc_ref_n(v_args1_5614_, 3);
v___x_5622_ = l_Array_toSubarray___redArg(v_args1_5614_, v___x_5621_, v_numParams_5609_);
v___f_5623_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0___boxed), 12, 6);
lean_closure_set(v___f_5623_, 0, v_name_5610_);
lean_closure_set(v___f_5623_, 1, v_us_5611_);
lean_closure_set(v___f_5623_, 2, v_args1_5614_);
lean_closure_set(v___f_5623_, 3, v___x_5621_);
lean_closure_set(v___f_5623_, 4, v_numParams_5609_);
lean_closure_set(v___f_5623_, 5, v___x_5622_);
v___x_5624_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_5625_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___boxed), 11, 6);
lean_closure_set(v___x_5625_, 0, v_ctorVal_5612_);
lean_closure_set(v___x_5625_, 1, v_args1_5614_);
lean_closure_set(v___x_5625_, 2, v___f_5623_);
lean_closure_set(v___x_5625_, 3, v___x_5621_);
lean_closure_set(v___x_5625_, 4, v_a_5613_);
lean_closure_set(v___x_5625_, 5, v___x_5624_);
v___x_5626_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v_args1_5614_, v___x_5625_, v___y_5616_, v___y_5617_, v___y_5618_, v___y_5619_);
return v___x_5626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1___boxed(lean_object* v_numParams_5627_, lean_object* v_name_5628_, lean_object* v_us_5629_, lean_object* v_ctorVal_5630_, lean_object* v_a_5631_, lean_object* v_args1_5632_, lean_object* v_x_5633_, lean_object* v___y_5634_, lean_object* v___y_5635_, lean_object* v___y_5636_, lean_object* v___y_5637_, lean_object* v___y_5638_){
_start:
{
lean_object* v_res_5639_; 
v_res_5639_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1(v_numParams_5627_, v_name_5628_, v_us_5629_, v_ctorVal_5630_, v_a_5631_, v_args1_5632_, v_x_5633_, v___y_5634_, v___y_5635_, v___y_5636_, v___y_5637_);
lean_dec(v___y_5637_);
lean_dec_ref(v___y_5636_);
lean_dec(v___y_5635_);
lean_dec_ref(v___y_5634_);
lean_dec_ref(v_x_5633_);
return v_res_5639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(lean_object* v_ctorVal_5640_, lean_object* v_a_5641_, lean_object* v_a_5642_, lean_object* v_a_5643_, lean_object* v_a_5644_){
_start:
{
lean_object* v_toConstantVal_5646_; lean_object* v_numParams_5647_; lean_object* v_name_5648_; lean_object* v_levelParams_5649_; lean_object* v_type_5650_; lean_object* v___x_5651_; 
v_toConstantVal_5646_ = lean_ctor_get(v_ctorVal_5640_, 0);
v_numParams_5647_ = lean_ctor_get(v_ctorVal_5640_, 3);
lean_inc(v_numParams_5647_);
v_name_5648_ = lean_ctor_get(v_toConstantVal_5646_, 0);
lean_inc(v_name_5648_);
v_levelParams_5649_ = lean_ctor_get(v_toConstantVal_5646_, 1);
v_type_5650_ = lean_ctor_get(v_toConstantVal_5646_, 2);
lean_inc_ref(v_type_5650_);
v___x_5651_ = l_Lean_Meta_elimOptParam(v_type_5650_, v_a_5643_, v_a_5644_);
if (lean_obj_tag(v___x_5651_) == 0)
{
lean_object* v_a_5652_; lean_object* v___x_5653_; lean_object* v_us_5654_; lean_object* v___f_5655_; uint8_t v___x_5656_; lean_object* v___x_5657_; 
v_a_5652_ = lean_ctor_get(v___x_5651_, 0);
lean_inc_n(v_a_5652_, 2);
lean_dec_ref_known(v___x_5651_, 1);
v___x_5653_ = lean_box(0);
lean_inc(v_levelParams_5649_);
v_us_5654_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(v_levelParams_5649_, v___x_5653_);
v___f_5655_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1___boxed), 12, 5);
lean_closure_set(v___f_5655_, 0, v_numParams_5647_);
lean_closure_set(v___f_5655_, 1, v_name_5648_);
lean_closure_set(v___f_5655_, 2, v_us_5654_);
lean_closure_set(v___f_5655_, 3, v_ctorVal_5640_);
lean_closure_set(v___f_5655_, 4, v_a_5652_);
v___x_5656_ = 0;
v___x_5657_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_a_5652_, v___f_5655_, v___x_5656_, v_a_5641_, v_a_5642_, v_a_5643_, v_a_5644_);
return v___x_5657_;
}
else
{
lean_object* v_a_5658_; lean_object* v___x_5660_; uint8_t v_isShared_5661_; uint8_t v_isSharedCheck_5665_; 
lean_dec(v_name_5648_);
lean_dec(v_numParams_5647_);
lean_dec_ref(v_ctorVal_5640_);
v_a_5658_ = lean_ctor_get(v___x_5651_, 0);
v_isSharedCheck_5665_ = !lean_is_exclusive(v___x_5651_);
if (v_isSharedCheck_5665_ == 0)
{
v___x_5660_ = v___x_5651_;
v_isShared_5661_ = v_isSharedCheck_5665_;
goto v_resetjp_5659_;
}
else
{
lean_inc(v_a_5658_);
lean_dec(v___x_5651_);
v___x_5660_ = lean_box(0);
v_isShared_5661_ = v_isSharedCheck_5665_;
goto v_resetjp_5659_;
}
v_resetjp_5659_:
{
lean_object* v___x_5663_; 
if (v_isShared_5661_ == 0)
{
v___x_5663_ = v___x_5660_;
goto v_reusejp_5662_;
}
else
{
lean_object* v_reuseFailAlloc_5664_; 
v_reuseFailAlloc_5664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5664_, 0, v_a_5658_);
v___x_5663_ = v_reuseFailAlloc_5664_;
goto v_reusejp_5662_;
}
v_reusejp_5662_:
{
return v___x_5663_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___boxed(lean_object* v_ctorVal_5666_, lean_object* v_a_5667_, lean_object* v_a_5668_, lean_object* v_a_5669_, lean_object* v_a_5670_, lean_object* v_a_5671_){
_start:
{
lean_object* v_res_5672_; 
v_res_5672_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(v_ctorVal_5666_, v_a_5667_, v_a_5668_, v_a_5669_, v_a_5670_);
lean_dec(v_a_5670_);
lean_dec_ref(v_a_5669_);
lean_dec(v_a_5668_);
lean_dec_ref(v_a_5667_);
return v_res_5672_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1(void){
_start:
{
lean_object* v___x_5674_; lean_object* v___x_5675_; 
v___x_5674_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__0));
v___x_5675_ = l_Lean_stringToMessageData(v___x_5674_);
return v___x_5675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(lean_object* v_ctorVal_5676_, lean_object* v_a_5677_, lean_object* v_a_5678_, lean_object* v_a_5679_, lean_object* v_a_5680_){
_start:
{
lean_object* v_toConstantVal_5682_; lean_object* v_name_5683_; lean_object* v___x_5684_; lean_object* v___x_5685_; lean_object* v___x_5686_; lean_object* v___x_5687_; lean_object* v___x_5688_; lean_object* v___x_5689_; 
v_toConstantVal_5682_ = lean_ctor_get(v_ctorVal_5676_, 0);
lean_inc_ref(v_toConstantVal_5682_);
lean_dec_ref(v_ctorVal_5676_);
v_name_5683_ = lean_ctor_get(v_toConstantVal_5682_, 0);
lean_inc(v_name_5683_);
lean_dec_ref(v_toConstantVal_5682_);
v___x_5684_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1);
v___x_5685_ = l_Lean_MessageData_ofName(v_name_5683_);
v___x_5686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5686_, 0, v___x_5684_);
lean_ctor_set(v___x_5686_, 1, v___x_5685_);
v___x_5687_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_5688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5688_, 0, v___x_5686_);
lean_ctor_set(v___x_5688_, 1, v___x_5687_);
v___x_5689_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_5688_, v_a_5677_, v_a_5678_, v_a_5679_, v_a_5680_);
return v___x_5689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___boxed(lean_object* v_ctorVal_5690_, lean_object* v_a_5691_, lean_object* v_a_5692_, lean_object* v_a_5693_, lean_object* v_a_5694_, lean_object* v_a_5695_){
_start:
{
lean_object* v_res_5696_; 
v_res_5696_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5690_, v_a_5691_, v_a_5692_, v_a_5693_, v_a_5694_);
lean_dec(v_a_5694_);
lean_dec_ref(v_a_5693_);
lean_dec(v_a_5692_);
lean_dec_ref(v_a_5691_);
return v_res_5696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj(lean_object* v_00_u03b1_5697_, lean_object* v_ctorVal_5698_, lean_object* v_a_5699_, lean_object* v_a_5700_, lean_object* v_a_5701_, lean_object* v_a_5702_){
_start:
{
lean_object* v___x_5704_; 
v___x_5704_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5698_, v_a_5699_, v_a_5700_, v_a_5701_, v_a_5702_);
return v___x_5704_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___boxed(lean_object* v_00_u03b1_5705_, lean_object* v_ctorVal_5706_, lean_object* v_a_5707_, lean_object* v_a_5708_, lean_object* v_a_5709_, lean_object* v_a_5710_, lean_object* v_a_5711_){
_start:
{
lean_object* v_res_5712_; 
v_res_5712_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj(v_00_u03b1_5705_, v_ctorVal_5706_, v_a_5707_, v_a_5708_, v_a_5709_, v_a_5710_);
lean_dec(v_a_5710_);
lean_dec_ref(v_a_5709_);
lean_dec(v_a_5708_);
lean_dec_ref(v_a_5707_);
return v_res_5712_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(lean_object* v_ctorVal_5718_, size_t v_sz_5719_, size_t v_i_5720_, lean_object* v_bs_5721_, lean_object* v___y_5722_, lean_object* v___y_5723_, lean_object* v___y_5724_, lean_object* v___y_5725_){
_start:
{
uint8_t v___x_5727_; 
v___x_5727_ = lean_usize_dec_lt(v_i_5720_, v_sz_5719_);
if (v___x_5727_ == 0)
{
lean_object* v___x_5728_; 
lean_dec_ref(v_ctorVal_5718_);
v___x_5728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5728_, 0, v_bs_5721_);
return v___x_5728_;
}
else
{
lean_object* v_v_5729_; lean_object* v___x_5730_; 
v_v_5729_ = lean_array_uget_borrowed(v_bs_5721_, v_i_5720_);
lean_inc(v___y_5725_);
lean_inc_ref(v___y_5724_);
lean_inc(v___y_5723_);
lean_inc_ref(v___y_5722_);
lean_inc(v_v_5729_);
v___x_5730_ = lean_infer_type(v_v_5729_, v___y_5722_, v___y_5723_, v___y_5724_, v___y_5725_);
if (lean_obj_tag(v___x_5730_) == 0)
{
lean_object* v_a_5731_; lean_object* v___x_5732_; 
v_a_5731_ = lean_ctor_get(v___x_5730_, 0);
lean_inc(v_a_5731_);
lean_dec_ref_known(v___x_5730_, 1);
v___x_5732_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_5731_, v___y_5723_);
if (lean_obj_tag(v___x_5732_) == 0)
{
lean_object* v_a_5733_; lean_object* v___x_5734_; lean_object* v_bs_x27_5735_; lean_object* v_a_5737_; lean_object* v___y_5743_; lean_object* v_lhs_5754_; lean_object* v_rhs_5755_; lean_object* v___x_5757_; uint8_t v___x_5758_; 
v_a_5733_ = lean_ctor_get(v___x_5732_, 0);
lean_inc(v_a_5733_);
lean_dec_ref_known(v___x_5732_, 1);
v___x_5734_ = lean_unsigned_to_nat(0u);
v_bs_x27_5735_ = lean_array_uset(v_bs_5721_, v_i_5720_, v___x_5734_);
v___x_5757_ = l_Lean_Expr_cleanupAnnotations(v_a_5733_);
v___x_5758_ = l_Lean_Expr_isApp(v___x_5757_);
if (v___x_5758_ == 0)
{
lean_object* v___x_5759_; 
lean_dec_ref(v___x_5757_);
lean_inc_ref(v_ctorVal_5718_);
v___x_5759_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5718_, v___y_5722_, v___y_5723_, v___y_5724_, v___y_5725_);
v___y_5743_ = v___x_5759_;
goto v___jp_5742_;
}
else
{
lean_object* v_arg_5760_; lean_object* v___x_5761_; uint8_t v___x_5762_; 
v_arg_5760_ = lean_ctor_get(v___x_5757_, 1);
lean_inc_ref(v_arg_5760_);
v___x_5761_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5757_);
v___x_5762_ = l_Lean_Expr_isApp(v___x_5761_);
if (v___x_5762_ == 0)
{
lean_object* v___x_5763_; 
lean_dec_ref(v___x_5761_);
lean_dec_ref(v_arg_5760_);
lean_inc_ref(v_ctorVal_5718_);
v___x_5763_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5718_, v___y_5722_, v___y_5723_, v___y_5724_, v___y_5725_);
v___y_5743_ = v___x_5763_;
goto v___jp_5742_;
}
else
{
lean_object* v_arg_5764_; lean_object* v___x_5765_; uint8_t v___x_5766_; 
v_arg_5764_ = lean_ctor_get(v___x_5761_, 1);
lean_inc_ref(v_arg_5764_);
v___x_5765_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5761_);
v___x_5766_ = l_Lean_Expr_isApp(v___x_5765_);
if (v___x_5766_ == 0)
{
lean_object* v___x_5767_; 
lean_dec_ref(v___x_5765_);
lean_dec_ref(v_arg_5764_);
lean_dec_ref(v_arg_5760_);
lean_inc_ref(v_ctorVal_5718_);
v___x_5767_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5718_, v___y_5722_, v___y_5723_, v___y_5724_, v___y_5725_);
v___y_5743_ = v___x_5767_;
goto v___jp_5742_;
}
else
{
lean_object* v_arg_5768_; lean_object* v___x_5769_; lean_object* v___x_5770_; uint8_t v___x_5771_; 
v_arg_5768_ = lean_ctor_get(v___x_5765_, 1);
lean_inc_ref(v_arg_5768_);
v___x_5769_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5765_);
v___x_5770_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__0));
v___x_5771_ = l_Lean_Expr_isConstOf(v___x_5769_, v___x_5770_);
if (v___x_5771_ == 0)
{
uint8_t v___x_5772_; 
lean_dec_ref(v_arg_5764_);
v___x_5772_ = l_Lean_Expr_isApp(v___x_5769_);
if (v___x_5772_ == 0)
{
lean_object* v___x_5773_; 
lean_dec_ref(v___x_5769_);
lean_dec_ref(v_arg_5768_);
lean_dec_ref(v_arg_5760_);
lean_inc_ref(v_ctorVal_5718_);
v___x_5773_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5718_, v___y_5722_, v___y_5723_, v___y_5724_, v___y_5725_);
v___y_5743_ = v___x_5773_;
goto v___jp_5742_;
}
else
{
lean_object* v___x_5774_; lean_object* v___x_5775_; uint8_t v___x_5776_; 
v___x_5774_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5769_);
v___x_5775_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__2));
v___x_5776_ = l_Lean_Expr_isConstOf(v___x_5774_, v___x_5775_);
lean_dec_ref(v___x_5774_);
if (v___x_5776_ == 0)
{
lean_object* v___x_5777_; 
lean_dec_ref(v_arg_5768_);
lean_dec_ref(v_arg_5760_);
lean_inc_ref(v_ctorVal_5718_);
v___x_5777_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5718_, v___y_5722_, v___y_5723_, v___y_5724_, v___y_5725_);
v___y_5743_ = v___x_5777_;
goto v___jp_5742_;
}
else
{
v_lhs_5754_ = v_arg_5768_;
v_rhs_5755_ = v_arg_5760_;
goto v___jp_5753_;
}
}
}
else
{
lean_dec_ref(v___x_5769_);
lean_dec_ref(v_arg_5768_);
v_lhs_5754_ = v_arg_5764_;
v_rhs_5755_ = v_arg_5760_;
goto v___jp_5753_;
}
}
}
}
v___jp_5736_:
{
size_t v___x_5738_; size_t v___x_5739_; lean_object* v___x_5740_; 
v___x_5738_ = ((size_t)1ULL);
v___x_5739_ = lean_usize_add(v_i_5720_, v___x_5738_);
v___x_5740_ = lean_array_uset(v_bs_x27_5735_, v_i_5720_, v_a_5737_);
v_i_5720_ = v___x_5739_;
v_bs_5721_ = v___x_5740_;
goto _start;
}
v___jp_5742_:
{
if (lean_obj_tag(v___y_5743_) == 0)
{
lean_object* v_a_5744_; 
v_a_5744_ = lean_ctor_get(v___y_5743_, 0);
lean_inc(v_a_5744_);
lean_dec_ref_known(v___y_5743_, 1);
v_a_5737_ = v_a_5744_;
goto v___jp_5736_;
}
else
{
lean_object* v_a_5745_; lean_object* v___x_5747_; uint8_t v_isShared_5748_; uint8_t v_isSharedCheck_5752_; 
lean_dec_ref(v_bs_x27_5735_);
lean_dec_ref(v_ctorVal_5718_);
v_a_5745_ = lean_ctor_get(v___y_5743_, 0);
v_isSharedCheck_5752_ = !lean_is_exclusive(v___y_5743_);
if (v_isSharedCheck_5752_ == 0)
{
v___x_5747_ = v___y_5743_;
v_isShared_5748_ = v_isSharedCheck_5752_;
goto v_resetjp_5746_;
}
else
{
lean_inc(v_a_5745_);
lean_dec(v___y_5743_);
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
v___jp_5753_:
{
lean_object* v___x_5756_; 
v___x_5756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5756_, 0, v_lhs_5754_);
lean_ctor_set(v___x_5756_, 1, v_rhs_5755_);
v_a_5737_ = v___x_5756_;
goto v___jp_5736_;
}
}
else
{
lean_object* v_a_5778_; lean_object* v___x_5780_; uint8_t v_isShared_5781_; uint8_t v_isSharedCheck_5785_; 
lean_dec_ref(v_bs_5721_);
lean_dec_ref(v_ctorVal_5718_);
v_a_5778_ = lean_ctor_get(v___x_5732_, 0);
v_isSharedCheck_5785_ = !lean_is_exclusive(v___x_5732_);
if (v_isSharedCheck_5785_ == 0)
{
v___x_5780_ = v___x_5732_;
v_isShared_5781_ = v_isSharedCheck_5785_;
goto v_resetjp_5779_;
}
else
{
lean_inc(v_a_5778_);
lean_dec(v___x_5732_);
v___x_5780_ = lean_box(0);
v_isShared_5781_ = v_isSharedCheck_5785_;
goto v_resetjp_5779_;
}
v_resetjp_5779_:
{
lean_object* v___x_5783_; 
if (v_isShared_5781_ == 0)
{
v___x_5783_ = v___x_5780_;
goto v_reusejp_5782_;
}
else
{
lean_object* v_reuseFailAlloc_5784_; 
v_reuseFailAlloc_5784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5784_, 0, v_a_5778_);
v___x_5783_ = v_reuseFailAlloc_5784_;
goto v_reusejp_5782_;
}
v_reusejp_5782_:
{
return v___x_5783_;
}
}
}
}
else
{
lean_object* v_a_5786_; lean_object* v___x_5788_; uint8_t v_isShared_5789_; uint8_t v_isSharedCheck_5793_; 
lean_dec_ref(v_bs_5721_);
lean_dec_ref(v_ctorVal_5718_);
v_a_5786_ = lean_ctor_get(v___x_5730_, 0);
v_isSharedCheck_5793_ = !lean_is_exclusive(v___x_5730_);
if (v_isSharedCheck_5793_ == 0)
{
v___x_5788_ = v___x_5730_;
v_isShared_5789_ = v_isSharedCheck_5793_;
goto v_resetjp_5787_;
}
else
{
lean_inc(v_a_5786_);
lean_dec(v___x_5730_);
v___x_5788_ = lean_box(0);
v_isShared_5789_ = v_isSharedCheck_5793_;
goto v_resetjp_5787_;
}
v_resetjp_5787_:
{
lean_object* v___x_5791_; 
if (v_isShared_5789_ == 0)
{
v___x_5791_ = v___x_5788_;
goto v_reusejp_5790_;
}
else
{
lean_object* v_reuseFailAlloc_5792_; 
v_reuseFailAlloc_5792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5792_, 0, v_a_5786_);
v___x_5791_ = v_reuseFailAlloc_5792_;
goto v_reusejp_5790_;
}
v_reusejp_5790_:
{
return v___x_5791_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___boxed(lean_object* v_ctorVal_5794_, lean_object* v_sz_5795_, lean_object* v_i_5796_, lean_object* v_bs_5797_, lean_object* v___y_5798_, lean_object* v___y_5799_, lean_object* v___y_5800_, lean_object* v___y_5801_, lean_object* v___y_5802_){
_start:
{
size_t v_sz_boxed_5803_; size_t v_i_boxed_5804_; lean_object* v_res_5805_; 
v_sz_boxed_5803_ = lean_unbox_usize(v_sz_5795_);
lean_dec(v_sz_5795_);
v_i_boxed_5804_ = lean_unbox_usize(v_i_5796_);
lean_dec(v_i_5796_);
v_res_5805_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(v_ctorVal_5794_, v_sz_boxed_5803_, v_i_boxed_5804_, v_bs_5797_, v___y_5798_, v___y_5799_, v___y_5800_, v___y_5801_);
lean_dec(v___y_5801_);
lean_dec_ref(v___y_5800_);
lean_dec(v___y_5799_);
lean_dec_ref(v___y_5798_);
return v_res_5805_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5807_; lean_object* v___x_5808_; 
v___x_5807_ = lean_unsigned_to_nat(0u);
v___x_5808_ = l_Lean_Level_ofNat(v___x_5807_);
return v___x_5808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0(lean_object* v_ctorVal_5809_, lean_object* v_us_5810_, lean_object* v_numIndices_5811_, lean_object* v_xs_5812_, lean_object* v_type_5813_, lean_object* v___y_5814_, lean_object* v___y_5815_, lean_object* v___y_5816_, lean_object* v___y_5817_){
_start:
{
lean_object* v_toConstantVal_5819_; lean_object* v_induct_5820_; lean_object* v_numParams_5821_; lean_object* v___x_5822_; lean_object* v_noConfusionName_5823_; lean_object* v___x_5824_; lean_object* v___x_5825_; lean_object* v___x_5826_; lean_object* v_noConfusion_5827_; lean_object* v_noConfusion_5828_; lean_object* v_lower_5830_; lean_object* v_upper_5831_; lean_object* v___x_5938_; lean_object* v___x_5939_; lean_object* v___x_5940_; lean_object* v___x_5941_; lean_object* v_n_5942_; uint8_t v___x_5943_; 
v_toConstantVal_5819_ = lean_ctor_get(v_ctorVal_5809_, 0);
v_induct_5820_ = lean_ctor_get(v_ctorVal_5809_, 1);
v_numParams_5821_ = lean_ctor_get(v_ctorVal_5809_, 3);
v___x_5822_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__0));
lean_inc(v_induct_5820_);
v_noConfusionName_5823_ = l_Lean_Name_str___override(v_induct_5820_, v___x_5822_);
v___x_5824_ = lean_unsigned_to_nat(0u);
v___x_5825_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1);
v___x_5826_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5826_, 0, v___x_5825_);
lean_ctor_set(v___x_5826_, 1, v_us_5810_);
v_noConfusion_5827_ = l_Lean_mkConst(v_noConfusionName_5823_, v___x_5826_);
v_noConfusion_5828_ = l_Lean_Expr_app___override(v_noConfusion_5827_, v_type_5813_);
v___x_5938_ = lean_array_get_size(v_xs_5812_);
v___x_5939_ = lean_nat_sub(v___x_5938_, v_numParams_5821_);
v___x_5940_ = lean_nat_sub(v___x_5939_, v_numIndices_5811_);
lean_dec(v___x_5939_);
v___x_5941_ = lean_unsigned_to_nat(1u);
v_n_5942_ = lean_nat_sub(v___x_5940_, v___x_5941_);
lean_dec(v___x_5940_);
v___x_5943_ = lean_nat_dec_le(v_n_5942_, v___x_5824_);
if (v___x_5943_ == 0)
{
v_lower_5830_ = v_n_5942_;
v_upper_5831_ = v___x_5938_;
goto v___jp_5829_;
}
else
{
lean_dec(v_n_5942_);
v_lower_5830_ = v___x_5824_;
v_upper_5831_ = v___x_5938_;
goto v___jp_5829_;
}
v___jp_5829_:
{
lean_object* v___x_5832_; lean_object* v___x_5833_; lean_object* v_eqs_5834_; size_t v_sz_5835_; size_t v___x_5836_; lean_object* v___x_5837_; 
lean_inc_ref(v_xs_5812_);
v___x_5832_ = l_Array_toSubarray___redArg(v_xs_5812_, v_lower_5830_, v_upper_5831_);
v___x_5833_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v_eqs_5834_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(v___x_5832_, v___x_5833_);
v_sz_5835_ = lean_array_size(v_eqs_5834_);
v___x_5836_ = ((size_t)0ULL);
lean_inc_ref(v_eqs_5834_);
lean_inc_ref(v_ctorVal_5809_);
v___x_5837_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(v_ctorVal_5809_, v_sz_5835_, v___x_5836_, v_eqs_5834_, v___y_5814_, v___y_5815_, v___y_5816_, v___y_5817_);
if (lean_obj_tag(v___x_5837_) == 0)
{
lean_object* v_a_5838_; lean_object* v___x_5839_; lean_object* v_fst_5840_; lean_object* v_snd_5841_; lean_object* v___x_5842_; lean_object* v___x_5843_; lean_object* v___x_5844_; lean_object* v___x_5845_; 
v_a_5838_ = lean_ctor_get(v___x_5837_, 0);
lean_inc(v_a_5838_);
lean_dec_ref_known(v___x_5837_, 1);
v___x_5839_ = l_Array_unzip___redArg(v_a_5838_);
lean_dec(v_a_5838_);
v_fst_5840_ = lean_ctor_get(v___x_5839_, 0);
lean_inc(v_fst_5840_);
v_snd_5841_ = lean_ctor_get(v___x_5839_, 1);
lean_inc(v_snd_5841_);
lean_dec_ref(v___x_5839_);
v___x_5842_ = l_Lean_mkAppN(v_noConfusion_5828_, v_fst_5840_);
lean_dec(v_fst_5840_);
v___x_5843_ = l_Lean_mkAppN(v___x_5842_, v_snd_5841_);
lean_dec(v_snd_5841_);
v___x_5844_ = l_Lean_mkAppN(v___x_5843_, v_eqs_5834_);
lean_dec_ref(v_eqs_5834_);
lean_inc(v___y_5817_);
lean_inc_ref(v___y_5816_);
lean_inc(v___y_5815_);
lean_inc_ref(v___y_5814_);
lean_inc_ref(v___x_5844_);
v___x_5845_ = lean_infer_type(v___x_5844_, v___y_5814_, v___y_5815_, v___y_5816_, v___y_5817_);
if (lean_obj_tag(v___x_5845_) == 0)
{
lean_object* v_a_5846_; lean_object* v___x_5847_; 
v_a_5846_ = lean_ctor_get(v___x_5845_, 0);
lean_inc(v_a_5846_);
lean_dec_ref_known(v___x_5845_, 1);
lean_inc(v___y_5817_);
lean_inc_ref(v___y_5816_);
lean_inc(v___y_5815_);
lean_inc_ref(v___y_5814_);
v___x_5847_ = lean_whnf(v_a_5846_, v___y_5814_, v___y_5815_, v___y_5816_, v___y_5817_);
if (lean_obj_tag(v___x_5847_) == 0)
{
lean_object* v_a_5848_; 
v_a_5848_ = lean_ctor_get(v___x_5847_, 0);
lean_inc(v_a_5848_);
lean_dec_ref_known(v___x_5847_, 1);
if (lean_obj_tag(v_a_5848_) == 7)
{
lean_object* v_binderType_5849_; lean_object* v___x_5850_; lean_object* v___x_5851_; 
lean_inc_ref(v_toConstantVal_5819_);
lean_dec_ref(v_ctorVal_5809_);
v_binderType_5849_ = lean_ctor_get(v_a_5848_, 1);
lean_inc_ref(v_binderType_5849_);
lean_dec_ref_known(v_a_5848_, 3);
v___x_5850_ = lean_box(0);
v___x_5851_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_binderType_5849_, v___x_5850_, v___y_5814_, v___y_5815_, v___y_5816_, v___y_5817_);
if (lean_obj_tag(v___x_5851_) == 0)
{
lean_object* v_a_5852_; lean_object* v___x_5853_; lean_object* v___x_5854_; 
v_a_5852_ = lean_ctor_get(v___x_5851_, 0);
lean_inc(v_a_5852_);
lean_dec_ref_known(v___x_5851_, 1);
v___x_5853_ = l_Lean_Expr_mvarId_x21(v_a_5852_);
v___x_5854_ = l_Lean_MVarId_intros(v___x_5853_, v___y_5814_, v___y_5815_, v___y_5816_, v___y_5817_);
if (lean_obj_tag(v___x_5854_) == 0)
{
lean_object* v_a_5855_; lean_object* v_snd_5856_; lean_object* v_name_5857_; lean_object* v___x_5858_; 
v_a_5855_ = lean_ctor_get(v___x_5854_, 0);
lean_inc(v_a_5855_);
lean_dec_ref_known(v___x_5854_, 1);
v_snd_5856_ = lean_ctor_get(v_a_5855_, 1);
lean_inc(v_snd_5856_);
lean_dec(v_a_5855_);
v_name_5857_ = lean_ctor_get(v_toConstantVal_5819_, 0);
lean_inc(v_name_5857_);
lean_dec_ref(v_toConstantVal_5819_);
v___x_5858_ = l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(v_snd_5856_, v_name_5857_, v___y_5814_, v___y_5815_, v___y_5816_, v___y_5817_);
if (lean_obj_tag(v___x_5858_) == 0)
{
lean_object* v___x_5859_; lean_object* v___x_5860_; lean_object* v_a_5861_; lean_object* v___x_5863_; uint8_t v_isShared_5864_; uint8_t v_isSharedCheck_5888_; 
lean_dec_ref_known(v___x_5858_, 1);
v___x_5859_ = l_Lean_Expr_app___override(v___x_5844_, v_a_5852_);
v___x_5860_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___redArg(v___x_5859_, v___y_5815_);
v_a_5861_ = lean_ctor_get(v___x_5860_, 0);
v_isSharedCheck_5888_ = !lean_is_exclusive(v___x_5860_);
if (v_isSharedCheck_5888_ == 0)
{
v___x_5863_ = v___x_5860_;
v_isShared_5864_ = v_isSharedCheck_5888_;
goto v_resetjp_5862_;
}
else
{
lean_inc(v_a_5861_);
lean_dec(v___x_5860_);
v___x_5863_ = lean_box(0);
v_isShared_5864_ = v_isSharedCheck_5888_;
goto v_resetjp_5862_;
}
v_resetjp_5862_:
{
uint8_t v___x_5865_; uint8_t v___x_5866_; uint8_t v___x_5867_; lean_object* v___x_5868_; 
v___x_5865_ = 0;
v___x_5866_ = 1;
v___x_5867_ = 1;
v___x_5868_ = l_Lean_Meta_mkLambdaFVars(v_xs_5812_, v_a_5861_, v___x_5865_, v___x_5866_, v___x_5865_, v___x_5866_, v___x_5867_, v___y_5814_, v___y_5815_, v___y_5816_, v___y_5817_);
lean_dec_ref(v_xs_5812_);
if (lean_obj_tag(v___x_5868_) == 0)
{
lean_object* v_a_5869_; lean_object* v___x_5871_; uint8_t v_isShared_5872_; uint8_t v_isSharedCheck_5879_; 
v_a_5869_ = lean_ctor_get(v___x_5868_, 0);
v_isSharedCheck_5879_ = !lean_is_exclusive(v___x_5868_);
if (v_isSharedCheck_5879_ == 0)
{
v___x_5871_ = v___x_5868_;
v_isShared_5872_ = v_isSharedCheck_5879_;
goto v_resetjp_5870_;
}
else
{
lean_inc(v_a_5869_);
lean_dec(v___x_5868_);
v___x_5871_ = lean_box(0);
v_isShared_5872_ = v_isSharedCheck_5879_;
goto v_resetjp_5870_;
}
v_resetjp_5870_:
{
lean_object* v___x_5874_; 
if (v_isShared_5864_ == 0)
{
lean_ctor_set_tag(v___x_5863_, 1);
lean_ctor_set(v___x_5863_, 0, v_a_5869_);
v___x_5874_ = v___x_5863_;
goto v_reusejp_5873_;
}
else
{
lean_object* v_reuseFailAlloc_5878_; 
v_reuseFailAlloc_5878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5878_, 0, v_a_5869_);
v___x_5874_ = v_reuseFailAlloc_5878_;
goto v_reusejp_5873_;
}
v_reusejp_5873_:
{
lean_object* v___x_5876_; 
if (v_isShared_5872_ == 0)
{
lean_ctor_set(v___x_5871_, 0, v___x_5874_);
v___x_5876_ = v___x_5871_;
goto v_reusejp_5875_;
}
else
{
lean_object* v_reuseFailAlloc_5877_; 
v_reuseFailAlloc_5877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5877_, 0, v___x_5874_);
v___x_5876_ = v_reuseFailAlloc_5877_;
goto v_reusejp_5875_;
}
v_reusejp_5875_:
{
return v___x_5876_;
}
}
}
}
else
{
lean_object* v_a_5880_; lean_object* v___x_5882_; uint8_t v_isShared_5883_; uint8_t v_isSharedCheck_5887_; 
lean_del_object(v___x_5863_);
v_a_5880_ = lean_ctor_get(v___x_5868_, 0);
v_isSharedCheck_5887_ = !lean_is_exclusive(v___x_5868_);
if (v_isSharedCheck_5887_ == 0)
{
v___x_5882_ = v___x_5868_;
v_isShared_5883_ = v_isSharedCheck_5887_;
goto v_resetjp_5881_;
}
else
{
lean_inc(v_a_5880_);
lean_dec(v___x_5868_);
v___x_5882_ = lean_box(0);
v_isShared_5883_ = v_isSharedCheck_5887_;
goto v_resetjp_5881_;
}
v_resetjp_5881_:
{
lean_object* v___x_5885_; 
if (v_isShared_5883_ == 0)
{
v___x_5885_ = v___x_5882_;
goto v_reusejp_5884_;
}
else
{
lean_object* v_reuseFailAlloc_5886_; 
v_reuseFailAlloc_5886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5886_, 0, v_a_5880_);
v___x_5885_ = v_reuseFailAlloc_5886_;
goto v_reusejp_5884_;
}
v_reusejp_5884_:
{
return v___x_5885_;
}
}
}
}
}
else
{
lean_object* v_a_5889_; lean_object* v___x_5891_; uint8_t v_isShared_5892_; uint8_t v_isSharedCheck_5896_; 
lean_dec(v_a_5852_);
lean_dec_ref(v___x_5844_);
lean_dec_ref(v_xs_5812_);
v_a_5889_ = lean_ctor_get(v___x_5858_, 0);
v_isSharedCheck_5896_ = !lean_is_exclusive(v___x_5858_);
if (v_isSharedCheck_5896_ == 0)
{
v___x_5891_ = v___x_5858_;
v_isShared_5892_ = v_isSharedCheck_5896_;
goto v_resetjp_5890_;
}
else
{
lean_inc(v_a_5889_);
lean_dec(v___x_5858_);
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
lean_dec(v_a_5852_);
lean_dec_ref(v___x_5844_);
lean_dec_ref(v_toConstantVal_5819_);
lean_dec_ref(v_xs_5812_);
v_a_5897_ = lean_ctor_get(v___x_5854_, 0);
v_isSharedCheck_5904_ = !lean_is_exclusive(v___x_5854_);
if (v_isSharedCheck_5904_ == 0)
{
v___x_5899_ = v___x_5854_;
v_isShared_5900_ = v_isSharedCheck_5904_;
goto v_resetjp_5898_;
}
else
{
lean_inc(v_a_5897_);
lean_dec(v___x_5854_);
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
else
{
lean_object* v_a_5905_; lean_object* v___x_5907_; uint8_t v_isShared_5908_; uint8_t v_isSharedCheck_5912_; 
lean_dec_ref(v___x_5844_);
lean_dec_ref(v_toConstantVal_5819_);
lean_dec_ref(v_xs_5812_);
v_a_5905_ = lean_ctor_get(v___x_5851_, 0);
v_isSharedCheck_5912_ = !lean_is_exclusive(v___x_5851_);
if (v_isSharedCheck_5912_ == 0)
{
v___x_5907_ = v___x_5851_;
v_isShared_5908_ = v_isSharedCheck_5912_;
goto v_resetjp_5906_;
}
else
{
lean_inc(v_a_5905_);
lean_dec(v___x_5851_);
v___x_5907_ = lean_box(0);
v_isShared_5908_ = v_isSharedCheck_5912_;
goto v_resetjp_5906_;
}
v_resetjp_5906_:
{
lean_object* v___x_5910_; 
if (v_isShared_5908_ == 0)
{
v___x_5910_ = v___x_5907_;
goto v_reusejp_5909_;
}
else
{
lean_object* v_reuseFailAlloc_5911_; 
v_reuseFailAlloc_5911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5911_, 0, v_a_5905_);
v___x_5910_ = v_reuseFailAlloc_5911_;
goto v_reusejp_5909_;
}
v_reusejp_5909_:
{
return v___x_5910_;
}
}
}
}
else
{
lean_object* v___x_5913_; 
lean_dec(v_a_5848_);
lean_dec_ref(v___x_5844_);
lean_dec_ref(v_xs_5812_);
v___x_5913_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5809_, v___y_5814_, v___y_5815_, v___y_5816_, v___y_5817_);
return v___x_5913_;
}
}
else
{
lean_object* v_a_5914_; lean_object* v___x_5916_; uint8_t v_isShared_5917_; uint8_t v_isSharedCheck_5921_; 
lean_dec_ref(v___x_5844_);
lean_dec_ref(v_xs_5812_);
lean_dec_ref(v_ctorVal_5809_);
v_a_5914_ = lean_ctor_get(v___x_5847_, 0);
v_isSharedCheck_5921_ = !lean_is_exclusive(v___x_5847_);
if (v_isSharedCheck_5921_ == 0)
{
v___x_5916_ = v___x_5847_;
v_isShared_5917_ = v_isSharedCheck_5921_;
goto v_resetjp_5915_;
}
else
{
lean_inc(v_a_5914_);
lean_dec(v___x_5847_);
v___x_5916_ = lean_box(0);
v_isShared_5917_ = v_isSharedCheck_5921_;
goto v_resetjp_5915_;
}
v_resetjp_5915_:
{
lean_object* v___x_5919_; 
if (v_isShared_5917_ == 0)
{
v___x_5919_ = v___x_5916_;
goto v_reusejp_5918_;
}
else
{
lean_object* v_reuseFailAlloc_5920_; 
v_reuseFailAlloc_5920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5920_, 0, v_a_5914_);
v___x_5919_ = v_reuseFailAlloc_5920_;
goto v_reusejp_5918_;
}
v_reusejp_5918_:
{
return v___x_5919_;
}
}
}
}
else
{
lean_object* v_a_5922_; lean_object* v___x_5924_; uint8_t v_isShared_5925_; uint8_t v_isSharedCheck_5929_; 
lean_dec_ref(v___x_5844_);
lean_dec_ref(v_xs_5812_);
lean_dec_ref(v_ctorVal_5809_);
v_a_5922_ = lean_ctor_get(v___x_5845_, 0);
v_isSharedCheck_5929_ = !lean_is_exclusive(v___x_5845_);
if (v_isSharedCheck_5929_ == 0)
{
v___x_5924_ = v___x_5845_;
v_isShared_5925_ = v_isSharedCheck_5929_;
goto v_resetjp_5923_;
}
else
{
lean_inc(v_a_5922_);
lean_dec(v___x_5845_);
v___x_5924_ = lean_box(0);
v_isShared_5925_ = v_isSharedCheck_5929_;
goto v_resetjp_5923_;
}
v_resetjp_5923_:
{
lean_object* v___x_5927_; 
if (v_isShared_5925_ == 0)
{
v___x_5927_ = v___x_5924_;
goto v_reusejp_5926_;
}
else
{
lean_object* v_reuseFailAlloc_5928_; 
v_reuseFailAlloc_5928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5928_, 0, v_a_5922_);
v___x_5927_ = v_reuseFailAlloc_5928_;
goto v_reusejp_5926_;
}
v_reusejp_5926_:
{
return v___x_5927_;
}
}
}
}
else
{
lean_object* v_a_5930_; lean_object* v___x_5932_; uint8_t v_isShared_5933_; uint8_t v_isSharedCheck_5937_; 
lean_dec_ref(v_eqs_5834_);
lean_dec_ref(v_noConfusion_5828_);
lean_dec_ref(v_xs_5812_);
lean_dec_ref(v_ctorVal_5809_);
v_a_5930_ = lean_ctor_get(v___x_5837_, 0);
v_isSharedCheck_5937_ = !lean_is_exclusive(v___x_5837_);
if (v_isSharedCheck_5937_ == 0)
{
v___x_5932_ = v___x_5837_;
v_isShared_5933_ = v_isSharedCheck_5937_;
goto v_resetjp_5931_;
}
else
{
lean_inc(v_a_5930_);
lean_dec(v___x_5837_);
v___x_5932_ = lean_box(0);
v_isShared_5933_ = v_isSharedCheck_5937_;
goto v_resetjp_5931_;
}
v_resetjp_5931_:
{
lean_object* v___x_5935_; 
if (v_isShared_5933_ == 0)
{
v___x_5935_ = v___x_5932_;
goto v_reusejp_5934_;
}
else
{
lean_object* v_reuseFailAlloc_5936_; 
v_reuseFailAlloc_5936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5936_, 0, v_a_5930_);
v___x_5935_ = v_reuseFailAlloc_5936_;
goto v_reusejp_5934_;
}
v_reusejp_5934_:
{
return v___x_5935_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___boxed(lean_object* v_ctorVal_5944_, lean_object* v_us_5945_, lean_object* v_numIndices_5946_, lean_object* v_xs_5947_, lean_object* v_type_5948_, lean_object* v___y_5949_, lean_object* v___y_5950_, lean_object* v___y_5951_, lean_object* v___y_5952_, lean_object* v___y_5953_){
_start:
{
lean_object* v_res_5954_; 
v_res_5954_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0(v_ctorVal_5944_, v_us_5945_, v_numIndices_5946_, v_xs_5947_, v_type_5948_, v___y_5949_, v___y_5950_, v___y_5951_, v___y_5952_);
lean_dec(v___y_5952_);
lean_dec_ref(v___y_5951_);
lean_dec(v___y_5950_);
lean_dec_ref(v___y_5949_);
lean_dec(v_numIndices_5946_);
return v_res_5954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(lean_object* v_ctorVal_5955_, lean_object* v_typeInfo_5956_, lean_object* v_a_5957_, lean_object* v_a_5958_, lean_object* v_a_5959_, lean_object* v_a_5960_){
_start:
{
lean_object* v_thmType_5962_; lean_object* v_us_5963_; lean_object* v_numIndices_5964_; lean_object* v___f_5965_; uint8_t v___x_5966_; lean_object* v___x_5967_; 
v_thmType_5962_ = lean_ctor_get(v_typeInfo_5956_, 0);
lean_inc_ref(v_thmType_5962_);
v_us_5963_ = lean_ctor_get(v_typeInfo_5956_, 1);
lean_inc(v_us_5963_);
v_numIndices_5964_ = lean_ctor_get(v_typeInfo_5956_, 2);
lean_inc(v_numIndices_5964_);
lean_dec_ref(v_typeInfo_5956_);
v___f_5965_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___boxed), 10, 3);
lean_closure_set(v___f_5965_, 0, v_ctorVal_5955_);
lean_closure_set(v___f_5965_, 1, v_us_5963_);
lean_closure_set(v___f_5965_, 2, v_numIndices_5964_);
v___x_5966_ = 0;
v___x_5967_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_thmType_5962_, v___f_5965_, v___x_5966_, v___x_5966_, v_a_5957_, v_a_5958_, v_a_5959_, v_a_5960_);
return v___x_5967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___boxed(lean_object* v_ctorVal_5968_, lean_object* v_typeInfo_5969_, lean_object* v_a_5970_, lean_object* v_a_5971_, lean_object* v_a_5972_, lean_object* v_a_5973_, lean_object* v_a_5974_){
_start:
{
lean_object* v_res_5975_; 
v_res_5975_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(v_ctorVal_5968_, v_typeInfo_5969_, v_a_5970_, v_a_5971_, v_a_5972_, v_a_5973_);
lean_dec(v_a_5973_);
lean_dec_ref(v_a_5972_);
lean_dec(v_a_5971_);
lean_dec_ref(v_a_5970_);
return v_res_5975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHInjectiveTheoremNameFor(lean_object* v_ctorName_5978_){
_start:
{
lean_object* v___x_5979_; lean_object* v___x_5980_; 
v___x_5979_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0));
v___x_5980_ = l_Lean_Name_str___override(v_ctorName_5978_, v___x_5979_);
return v___x_5980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(lean_object* v_thmName_5981_, lean_object* v_ctorVal_5982_, lean_object* v_a_5983_, lean_object* v_a_5984_, lean_object* v_a_5985_, lean_object* v_a_5986_){
_start:
{
lean_object* v___x_5988_; 
lean_inc_ref(v_ctorVal_5982_);
v___x_5988_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(v_ctorVal_5982_, v_a_5983_, v_a_5984_, v_a_5985_, v_a_5986_);
if (lean_obj_tag(v___x_5988_) == 0)
{
lean_object* v_a_5989_; lean_object* v___x_5991_; uint8_t v_isShared_5992_; uint8_t v_isSharedCheck_6050_; 
v_a_5989_ = lean_ctor_get(v___x_5988_, 0);
v_isSharedCheck_6050_ = !lean_is_exclusive(v___x_5988_);
if (v_isSharedCheck_6050_ == 0)
{
v___x_5991_ = v___x_5988_;
v_isShared_5992_ = v_isSharedCheck_6050_;
goto v_resetjp_5990_;
}
else
{
lean_inc(v_a_5989_);
lean_dec(v___x_5988_);
v___x_5991_ = lean_box(0);
v_isShared_5992_ = v_isSharedCheck_6050_;
goto v_resetjp_5990_;
}
v_resetjp_5990_:
{
if (lean_obj_tag(v_a_5989_) == 1)
{
lean_object* v_val_5993_; lean_object* v___x_5994_; 
lean_del_object(v___x_5991_);
v_val_5993_ = lean_ctor_get(v_a_5989_, 0);
lean_inc_n(v_val_5993_, 2);
lean_dec_ref_known(v_a_5989_, 1);
lean_inc_ref(v_ctorVal_5982_);
v___x_5994_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(v_ctorVal_5982_, v_val_5993_, v_a_5983_, v_a_5984_, v_a_5985_, v_a_5986_);
if (lean_obj_tag(v___x_5994_) == 0)
{
lean_object* v_a_5995_; lean_object* v___x_5997_; uint8_t v_isShared_5998_; uint8_t v_isSharedCheck_6037_; 
v_a_5995_ = lean_ctor_get(v___x_5994_, 0);
v_isSharedCheck_6037_ = !lean_is_exclusive(v___x_5994_);
if (v_isSharedCheck_6037_ == 0)
{
v___x_5997_ = v___x_5994_;
v_isShared_5998_ = v_isSharedCheck_6037_;
goto v_resetjp_5996_;
}
else
{
lean_inc(v_a_5995_);
lean_dec(v___x_5994_);
v___x_5997_ = lean_box(0);
v_isShared_5998_ = v_isSharedCheck_6037_;
goto v_resetjp_5996_;
}
v_resetjp_5996_:
{
if (lean_obj_tag(v_a_5995_) == 1)
{
lean_object* v_toConstantVal_5999_; lean_object* v_val_6000_; lean_object* v___x_6002_; uint8_t v_isShared_6003_; uint8_t v_isSharedCheck_6032_; 
v_toConstantVal_5999_ = lean_ctor_get(v_ctorVal_5982_, 0);
lean_inc_ref(v_toConstantVal_5999_);
lean_dec_ref(v_ctorVal_5982_);
v_val_6000_ = lean_ctor_get(v_a_5995_, 0);
v_isSharedCheck_6032_ = !lean_is_exclusive(v_a_5995_);
if (v_isSharedCheck_6032_ == 0)
{
v___x_6002_ = v_a_5995_;
v_isShared_6003_ = v_isSharedCheck_6032_;
goto v_resetjp_6001_;
}
else
{
lean_inc(v_val_6000_);
lean_dec(v_a_5995_);
v___x_6002_ = lean_box(0);
v_isShared_6003_ = v_isSharedCheck_6032_;
goto v_resetjp_6001_;
}
v_resetjp_6001_:
{
lean_object* v_levelParams_6004_; lean_object* v___x_6006_; uint8_t v_isShared_6007_; uint8_t v_isSharedCheck_6029_; 
v_levelParams_6004_ = lean_ctor_get(v_toConstantVal_5999_, 1);
v_isSharedCheck_6029_ = !lean_is_exclusive(v_toConstantVal_5999_);
if (v_isSharedCheck_6029_ == 0)
{
lean_object* v_unused_6030_; lean_object* v_unused_6031_; 
v_unused_6030_ = lean_ctor_get(v_toConstantVal_5999_, 2);
lean_dec(v_unused_6030_);
v_unused_6031_ = lean_ctor_get(v_toConstantVal_5999_, 0);
lean_dec(v_unused_6031_);
v___x_6006_ = v_toConstantVal_5999_;
v_isShared_6007_ = v_isSharedCheck_6029_;
goto v_resetjp_6005_;
}
else
{
lean_inc(v_levelParams_6004_);
lean_dec(v_toConstantVal_5999_);
v___x_6006_ = lean_box(0);
v_isShared_6007_ = v_isSharedCheck_6029_;
goto v_resetjp_6005_;
}
v_resetjp_6005_:
{
lean_object* v_thmType_6008_; lean_object* v___x_6010_; uint8_t v_isShared_6011_; uint8_t v_isSharedCheck_6026_; 
v_thmType_6008_ = lean_ctor_get(v_val_5993_, 0);
v_isSharedCheck_6026_ = !lean_is_exclusive(v_val_5993_);
if (v_isSharedCheck_6026_ == 0)
{
lean_object* v_unused_6027_; lean_object* v_unused_6028_; 
v_unused_6027_ = lean_ctor_get(v_val_5993_, 2);
lean_dec(v_unused_6027_);
v_unused_6028_ = lean_ctor_get(v_val_5993_, 1);
lean_dec(v_unused_6028_);
v___x_6010_ = v_val_5993_;
v_isShared_6011_ = v_isSharedCheck_6026_;
goto v_resetjp_6009_;
}
else
{
lean_inc(v_thmType_6008_);
lean_dec(v_val_5993_);
v___x_6010_ = lean_box(0);
v_isShared_6011_ = v_isSharedCheck_6026_;
goto v_resetjp_6009_;
}
v_resetjp_6009_:
{
lean_object* v___x_6013_; 
lean_inc(v_thmName_5981_);
if (v_isShared_6007_ == 0)
{
lean_ctor_set(v___x_6006_, 2, v_thmType_6008_);
lean_ctor_set(v___x_6006_, 0, v_thmName_5981_);
v___x_6013_ = v___x_6006_;
goto v_reusejp_6012_;
}
else
{
lean_object* v_reuseFailAlloc_6025_; 
v_reuseFailAlloc_6025_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6025_, 0, v_thmName_5981_);
lean_ctor_set(v_reuseFailAlloc_6025_, 1, v_levelParams_6004_);
lean_ctor_set(v_reuseFailAlloc_6025_, 2, v_thmType_6008_);
v___x_6013_ = v_reuseFailAlloc_6025_;
goto v_reusejp_6012_;
}
v_reusejp_6012_:
{
lean_object* v___x_6014_; lean_object* v___x_6015_; lean_object* v___x_6017_; 
v___x_6014_ = lean_box(0);
v___x_6015_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6015_, 0, v_thmName_5981_);
lean_ctor_set(v___x_6015_, 1, v___x_6014_);
if (v_isShared_6011_ == 0)
{
lean_ctor_set(v___x_6010_, 2, v___x_6015_);
lean_ctor_set(v___x_6010_, 1, v_val_6000_);
lean_ctor_set(v___x_6010_, 0, v___x_6013_);
v___x_6017_ = v___x_6010_;
goto v_reusejp_6016_;
}
else
{
lean_object* v_reuseFailAlloc_6024_; 
v_reuseFailAlloc_6024_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6024_, 0, v___x_6013_);
lean_ctor_set(v_reuseFailAlloc_6024_, 1, v_val_6000_);
lean_ctor_set(v_reuseFailAlloc_6024_, 2, v___x_6015_);
v___x_6017_ = v_reuseFailAlloc_6024_;
goto v_reusejp_6016_;
}
v_reusejp_6016_:
{
lean_object* v___x_6019_; 
if (v_isShared_6003_ == 0)
{
lean_ctor_set(v___x_6002_, 0, v___x_6017_);
v___x_6019_ = v___x_6002_;
goto v_reusejp_6018_;
}
else
{
lean_object* v_reuseFailAlloc_6023_; 
v_reuseFailAlloc_6023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6023_, 0, v___x_6017_);
v___x_6019_ = v_reuseFailAlloc_6023_;
goto v_reusejp_6018_;
}
v_reusejp_6018_:
{
lean_object* v___x_6021_; 
if (v_isShared_5998_ == 0)
{
lean_ctor_set(v___x_5997_, 0, v___x_6019_);
v___x_6021_ = v___x_5997_;
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
}
}
}
}
else
{
lean_object* v___x_6033_; lean_object* v___x_6035_; 
lean_dec(v_a_5995_);
lean_dec(v_val_5993_);
lean_dec_ref(v_ctorVal_5982_);
lean_dec(v_thmName_5981_);
v___x_6033_ = lean_box(0);
if (v_isShared_5998_ == 0)
{
lean_ctor_set(v___x_5997_, 0, v___x_6033_);
v___x_6035_ = v___x_5997_;
goto v_reusejp_6034_;
}
else
{
lean_object* v_reuseFailAlloc_6036_; 
v_reuseFailAlloc_6036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6036_, 0, v___x_6033_);
v___x_6035_ = v_reuseFailAlloc_6036_;
goto v_reusejp_6034_;
}
v_reusejp_6034_:
{
return v___x_6035_;
}
}
}
}
else
{
lean_object* v_a_6038_; lean_object* v___x_6040_; uint8_t v_isShared_6041_; uint8_t v_isSharedCheck_6045_; 
lean_dec(v_val_5993_);
lean_dec_ref(v_ctorVal_5982_);
lean_dec(v_thmName_5981_);
v_a_6038_ = lean_ctor_get(v___x_5994_, 0);
v_isSharedCheck_6045_ = !lean_is_exclusive(v___x_5994_);
if (v_isSharedCheck_6045_ == 0)
{
v___x_6040_ = v___x_5994_;
v_isShared_6041_ = v_isSharedCheck_6045_;
goto v_resetjp_6039_;
}
else
{
lean_inc(v_a_6038_);
lean_dec(v___x_5994_);
v___x_6040_ = lean_box(0);
v_isShared_6041_ = v_isSharedCheck_6045_;
goto v_resetjp_6039_;
}
v_resetjp_6039_:
{
lean_object* v___x_6043_; 
if (v_isShared_6041_ == 0)
{
v___x_6043_ = v___x_6040_;
goto v_reusejp_6042_;
}
else
{
lean_object* v_reuseFailAlloc_6044_; 
v_reuseFailAlloc_6044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6044_, 0, v_a_6038_);
v___x_6043_ = v_reuseFailAlloc_6044_;
goto v_reusejp_6042_;
}
v_reusejp_6042_:
{
return v___x_6043_;
}
}
}
}
else
{
lean_object* v___x_6046_; lean_object* v___x_6048_; 
lean_dec(v_a_5989_);
lean_dec_ref(v_ctorVal_5982_);
lean_dec(v_thmName_5981_);
v___x_6046_ = lean_box(0);
if (v_isShared_5992_ == 0)
{
lean_ctor_set(v___x_5991_, 0, v___x_6046_);
v___x_6048_ = v___x_5991_;
goto v_reusejp_6047_;
}
else
{
lean_object* v_reuseFailAlloc_6049_; 
v_reuseFailAlloc_6049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6049_, 0, v___x_6046_);
v___x_6048_ = v_reuseFailAlloc_6049_;
goto v_reusejp_6047_;
}
v_reusejp_6047_:
{
return v___x_6048_;
}
}
}
}
else
{
lean_object* v_a_6051_; lean_object* v___x_6053_; uint8_t v_isShared_6054_; uint8_t v_isSharedCheck_6058_; 
lean_dec_ref(v_ctorVal_5982_);
lean_dec(v_thmName_5981_);
v_a_6051_ = lean_ctor_get(v___x_5988_, 0);
v_isSharedCheck_6058_ = !lean_is_exclusive(v___x_5988_);
if (v_isSharedCheck_6058_ == 0)
{
v___x_6053_ = v___x_5988_;
v_isShared_6054_ = v_isSharedCheck_6058_;
goto v_resetjp_6052_;
}
else
{
lean_inc(v_a_6051_);
lean_dec(v___x_5988_);
v___x_6053_ = lean_box(0);
v_isShared_6054_ = v_isSharedCheck_6058_;
goto v_resetjp_6052_;
}
v_resetjp_6052_:
{
lean_object* v___x_6056_; 
if (v_isShared_6054_ == 0)
{
v___x_6056_ = v___x_6053_;
goto v_reusejp_6055_;
}
else
{
lean_object* v_reuseFailAlloc_6057_; 
v_reuseFailAlloc_6057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6057_, 0, v_a_6051_);
v___x_6056_ = v_reuseFailAlloc_6057_;
goto v_reusejp_6055_;
}
v_reusejp_6055_:
{
return v___x_6056_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f___boxed(lean_object* v_thmName_6059_, lean_object* v_ctorVal_6060_, lean_object* v_a_6061_, lean_object* v_a_6062_, lean_object* v_a_6063_, lean_object* v_a_6064_, lean_object* v_a_6065_){
_start:
{
lean_object* v_res_6066_; 
v_res_6066_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(v_thmName_6059_, v_ctorVal_6060_, v_a_6061_, v_a_6062_, v_a_6063_, v_a_6064_);
lean_dec(v_a_6064_);
lean_dec_ref(v_a_6063_);
lean_dec(v_a_6062_);
lean_dec_ref(v_a_6061_);
return v_res_6066_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(lean_object* v_env_6067_, lean_object* v_n_6068_){
_start:
{
if (lean_obj_tag(v_n_6068_) == 1)
{
lean_object* v_pre_6069_; lean_object* v_str_6070_; lean_object* v___x_6071_; uint8_t v___x_6072_; 
v_pre_6069_ = lean_ctor_get(v_n_6068_, 0);
lean_inc(v_pre_6069_);
v_str_6070_ = lean_ctor_get(v_n_6068_, 1);
lean_inc_ref(v_str_6070_);
lean_dec_ref_known(v_n_6068_, 2);
v___x_6071_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0));
v___x_6072_ = lean_string_dec_eq(v_str_6070_, v___x_6071_);
lean_dec_ref(v_str_6070_);
if (v___x_6072_ == 0)
{
lean_dec(v_pre_6069_);
lean_dec_ref(v_env_6067_);
return v___x_6072_;
}
else
{
uint8_t v___x_6073_; lean_object* v___x_6074_; 
v___x_6073_ = 0;
v___x_6074_ = l_Lean_Environment_find_x3f(v_env_6067_, v_pre_6069_, v___x_6073_);
if (lean_obj_tag(v___x_6074_) == 1)
{
lean_object* v_val_6075_; 
v_val_6075_ = lean_ctor_get(v___x_6074_, 0);
lean_inc(v_val_6075_);
lean_dec_ref_known(v___x_6074_, 1);
if (lean_obj_tag(v_val_6075_) == 6)
{
lean_dec_ref_known(v_val_6075_, 1);
return v___x_6072_;
}
else
{
lean_dec(v_val_6075_);
return v___x_6073_;
}
}
else
{
lean_dec(v___x_6074_);
return v___x_6073_;
}
}
}
else
{
uint8_t v___x_6076_; 
lean_dec(v_n_6068_);
lean_dec_ref(v_env_6067_);
v___x_6076_ = 0;
return v___x_6076_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2____boxed(lean_object* v_env_6077_, lean_object* v_n_6078_){
_start:
{
uint8_t v_res_6079_; lean_object* v_r_6080_; 
v_res_6079_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(v_env_6077_, v_n_6078_);
v_r_6080_ = lean_box(v_res_6079_);
return v_r_6080_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_6083_; lean_object* v___x_6084_; 
v___f_6083_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_));
v___x_6084_ = l_Lean_registerReservedNamePredicate(v___f_6083_);
return v___x_6084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2____boxed(lean_object* v_a_6085_){
_start:
{
lean_object* v_res_6086_; 
v_res_6086_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_();
return v_res_6086_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(lean_object* v_thm_6087_, lean_object* v___y_6088_){
_start:
{
lean_object* v___x_6090_; lean_object* v_env_6091_; lean_object* v_toConstantVal_6092_; lean_object* v_value_6093_; lean_object* v_all_6094_; uint8_t v___y_6096_; lean_object* v_type_6104_; uint8_t v___x_6105_; 
v___x_6090_ = lean_st_ref_get(v___y_6088_);
v_env_6091_ = lean_ctor_get(v___x_6090_, 0);
lean_inc_ref_n(v_env_6091_, 2);
lean_dec(v___x_6090_);
v_toConstantVal_6092_ = lean_ctor_get(v_thm_6087_, 0);
v_value_6093_ = lean_ctor_get(v_thm_6087_, 1);
v_all_6094_ = lean_ctor_get(v_thm_6087_, 2);
v_type_6104_ = lean_ctor_get(v_toConstantVal_6092_, 2);
v___x_6105_ = l_Lean_Environment_hasUnsafe(v_env_6091_, v_type_6104_);
if (v___x_6105_ == 0)
{
uint8_t v___x_6106_; 
v___x_6106_ = l_Lean_Environment_hasUnsafe(v_env_6091_, v_value_6093_);
v___y_6096_ = v___x_6106_;
goto v___jp_6095_;
}
else
{
lean_dec_ref(v_env_6091_);
v___y_6096_ = v___x_6105_;
goto v___jp_6095_;
}
v___jp_6095_:
{
if (v___y_6096_ == 0)
{
lean_object* v___x_6097_; lean_object* v___x_6098_; 
v___x_6097_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_6097_, 0, v_thm_6087_);
v___x_6098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6098_, 0, v___x_6097_);
return v___x_6098_;
}
else
{
lean_object* v___x_6099_; uint8_t v___x_6100_; lean_object* v___x_6101_; lean_object* v___x_6102_; lean_object* v___x_6103_; 
lean_inc(v_all_6094_);
lean_inc_ref(v_value_6093_);
lean_inc_ref(v_toConstantVal_6092_);
lean_dec_ref(v_thm_6087_);
v___x_6099_ = lean_box(0);
v___x_6100_ = 0;
v___x_6101_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_6101_, 0, v_toConstantVal_6092_);
lean_ctor_set(v___x_6101_, 1, v_value_6093_);
lean_ctor_set(v___x_6101_, 2, v___x_6099_);
lean_ctor_set(v___x_6101_, 3, v_all_6094_);
lean_ctor_set_uint8(v___x_6101_, sizeof(void*)*4, v___x_6100_);
v___x_6102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6102_, 0, v___x_6101_);
v___x_6103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6103_, 0, v___x_6102_);
return v___x_6103_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_thm_6107_, lean_object* v___y_6108_, lean_object* v___y_6109_){
_start:
{
lean_object* v_res_6110_; 
v_res_6110_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(v_thm_6107_, v___y_6108_);
lean_dec(v___y_6108_);
return v_res_6110_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0(lean_object* v_thm_6111_, lean_object* v___y_6112_, lean_object* v___y_6113_, lean_object* v___y_6114_, lean_object* v___y_6115_){
_start:
{
lean_object* v___x_6117_; 
v___x_6117_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(v_thm_6111_, v___y_6115_);
return v___x_6117_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___boxed(lean_object* v_thm_6118_, lean_object* v___y_6119_, lean_object* v___y_6120_, lean_object* v___y_6121_, lean_object* v___y_6122_, lean_object* v___y_6123_){
_start:
{
lean_object* v_res_6124_; 
v_res_6124_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0(v_thm_6118_, v___y_6119_, v___y_6120_, v___y_6121_, v___y_6122_);
lean_dec(v___y_6122_);
lean_dec_ref(v___y_6121_);
lean_dec(v___y_6120_);
lean_dec_ref(v___y_6119_);
return v_res_6124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(lean_object* v_val_6125_, uint8_t v___x_6126_, lean_object* v___y_6127_, lean_object* v___y_6128_, lean_object* v___y_6129_, lean_object* v___y_6130_){
_start:
{
lean_object* v___x_6132_; lean_object* v_a_6133_; lean_object* v___x_6134_; 
v___x_6132_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(v_val_6125_, v___y_6130_);
v_a_6133_ = lean_ctor_get(v___x_6132_, 0);
lean_inc(v_a_6133_);
lean_dec_ref(v___x_6132_);
v___x_6134_ = l_Lean_addDecl(v_a_6133_, v___x_6126_, v___y_6129_, v___y_6130_);
return v___x_6134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object* v_val_6135_, lean_object* v___x_6136_, lean_object* v___y_6137_, lean_object* v___y_6138_, lean_object* v___y_6139_, lean_object* v___y_6140_, lean_object* v___y_6141_){
_start:
{
uint8_t v___x_2122__boxed_6142_; lean_object* v_res_6143_; 
v___x_2122__boxed_6142_ = lean_unbox(v___x_6136_);
v_res_6143_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(v_val_6135_, v___x_2122__boxed_6142_, v___y_6137_, v___y_6138_, v___y_6139_, v___y_6140_);
lean_dec(v___y_6140_);
lean_dec_ref(v___y_6139_);
lean_dec(v___y_6138_);
lean_dec_ref(v___y_6137_);
return v_res_6143_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6146_; lean_object* v___x_6147_; lean_object* v___x_6148_; 
v___x_6146_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_6147_ = lean_unsigned_to_nat(0u);
v___x_6148_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_6148_, 0, v___x_6147_);
lean_ctor_set(v___x_6148_, 1, v___x_6147_);
lean_ctor_set(v___x_6148_, 2, v___x_6147_);
lean_ctor_set(v___x_6148_, 3, v___x_6147_);
lean_ctor_set(v___x_6148_, 4, v___x_6146_);
lean_ctor_set(v___x_6148_, 5, v___x_6146_);
lean_ctor_set(v___x_6148_, 6, v___x_6146_);
lean_ctor_set(v___x_6148_, 7, v___x_6146_);
lean_ctor_set(v___x_6148_, 8, v___x_6146_);
lean_ctor_set(v___x_6148_, 9, v___x_6146_);
return v___x_6148_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6149_; lean_object* v___x_6150_; 
v___x_6149_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_6150_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6150_, 0, v___x_6149_);
lean_ctor_set(v___x_6150_, 1, v___x_6149_);
lean_ctor_set(v___x_6150_, 2, v___x_6149_);
lean_ctor_set(v___x_6150_, 3, v___x_6149_);
lean_ctor_set(v___x_6150_, 4, v___x_6149_);
lean_ctor_set(v___x_6150_, 5, v___x_6149_);
return v___x_6150_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6151_; lean_object* v___x_6152_; 
v___x_6151_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_6152_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6152_, 0, v___x_6151_);
lean_ctor_set(v___x_6152_, 1, v___x_6151_);
lean_ctor_set(v___x_6152_, 2, v___x_6151_);
lean_ctor_set(v___x_6152_, 3, v___x_6151_);
lean_ctor_set(v___x_6152_, 4, v___x_6151_);
return v___x_6152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(lean_object* v___x_6153_, lean_object* v_name_6154_, lean_object* v___y_6155_, lean_object* v___y_6156_){
_start:
{
if (lean_obj_tag(v_name_6154_) == 1)
{
lean_object* v_pre_6166_; lean_object* v_str_6167_; lean_object* v___x_6168_; uint8_t v___x_6169_; 
v_pre_6166_ = lean_ctor_get(v_name_6154_, 0);
lean_inc(v_pre_6166_);
v_str_6167_ = lean_ctor_get(v_name_6154_, 1);
v___x_6168_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0));
v___x_6169_ = lean_string_dec_eq(v_str_6167_, v___x_6168_);
if (v___x_6169_ == 0)
{
lean_dec(v_pre_6166_);
lean_dec_ref_known(v_name_6154_, 2);
lean_dec(v___x_6153_);
goto v___jp_6162_;
}
else
{
lean_object* v___x_6170_; lean_object* v_env_6171_; uint8_t v___x_6172_; lean_object* v___x_6173_; 
v___x_6170_ = lean_st_ref_get(v___y_6156_);
v_env_6171_ = lean_ctor_get(v___x_6170_, 0);
lean_inc_ref(v_env_6171_);
lean_dec(v___x_6170_);
v___x_6172_ = 0;
lean_inc(v_pre_6166_);
v___x_6173_ = l_Lean_Environment_find_x3f(v_env_6171_, v_pre_6166_, v___x_6172_);
if (lean_obj_tag(v___x_6173_) == 1)
{
lean_object* v_val_6174_; 
v_val_6174_ = lean_ctor_get(v___x_6173_, 0);
lean_inc(v_val_6174_);
lean_dec_ref_known(v___x_6173_, 1);
if (lean_obj_tag(v_val_6174_) == 6)
{
lean_object* v_val_6175_; lean_object* v___x_6177_; uint8_t v_isShared_6178_; uint8_t v_isSharedCheck_6225_; 
v_val_6175_ = lean_ctor_get(v_val_6174_, 0);
v_isSharedCheck_6225_ = !lean_is_exclusive(v_val_6174_);
if (v_isSharedCheck_6225_ == 0)
{
v___x_6177_ = v_val_6174_;
v_isShared_6178_ = v_isSharedCheck_6225_;
goto v_resetjp_6176_;
}
else
{
lean_inc(v_val_6175_);
lean_dec(v_val_6174_);
v___x_6177_ = lean_box(0);
v_isShared_6178_ = v_isSharedCheck_6225_;
goto v_resetjp_6176_;
}
v_resetjp_6176_:
{
uint8_t v___x_6179_; uint8_t v___x_6180_; uint8_t v___x_6181_; lean_object* v___x_6182_; uint64_t v___x_6183_; lean_object* v___x_6184_; lean_object* v___x_6185_; lean_object* v___x_6186_; lean_object* v___x_6187_; lean_object* v___x_6188_; lean_object* v___x_6189_; lean_object* v___x_6190_; lean_object* v___x_6191_; lean_object* v___x_6192_; lean_object* v___x_6193_; lean_object* v___x_6194_; lean_object* v___x_6195_; uint8_t v_a_6197_; lean_object* v___x_6203_; 
v___x_6179_ = 1;
v___x_6180_ = 0;
v___x_6181_ = 2;
v___x_6182_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_6182_, 0, v___x_6172_);
lean_ctor_set_uint8(v___x_6182_, 1, v___x_6172_);
lean_ctor_set_uint8(v___x_6182_, 2, v___x_6172_);
lean_ctor_set_uint8(v___x_6182_, 3, v___x_6172_);
lean_ctor_set_uint8(v___x_6182_, 4, v___x_6172_);
lean_ctor_set_uint8(v___x_6182_, 5, v___x_6169_);
lean_ctor_set_uint8(v___x_6182_, 6, v___x_6169_);
lean_ctor_set_uint8(v___x_6182_, 7, v___x_6172_);
lean_ctor_set_uint8(v___x_6182_, 8, v___x_6169_);
lean_ctor_set_uint8(v___x_6182_, 9, v___x_6179_);
lean_ctor_set_uint8(v___x_6182_, 10, v___x_6180_);
lean_ctor_set_uint8(v___x_6182_, 11, v___x_6169_);
lean_ctor_set_uint8(v___x_6182_, 12, v___x_6169_);
lean_ctor_set_uint8(v___x_6182_, 13, v___x_6169_);
lean_ctor_set_uint8(v___x_6182_, 14, v___x_6181_);
lean_ctor_set_uint8(v___x_6182_, 15, v___x_6169_);
lean_ctor_set_uint8(v___x_6182_, 16, v___x_6169_);
lean_ctor_set_uint8(v___x_6182_, 17, v___x_6169_);
lean_ctor_set_uint8(v___x_6182_, 18, v___x_6169_);
v___x_6183_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_6182_);
v___x_6184_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_6184_, 0, v___x_6182_);
lean_ctor_set_uint64(v___x_6184_, sizeof(void*)*1, v___x_6183_);
v___x_6185_ = lean_unsigned_to_nat(0u);
v___x_6186_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_6187_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_6188_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_));
v___x_6189_ = lean_box(0);
lean_inc(v___x_6153_);
v___x_6190_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_6190_, 0, v___x_6184_);
lean_ctor_set(v___x_6190_, 1, v___x_6153_);
lean_ctor_set(v___x_6190_, 2, v___x_6187_);
lean_ctor_set(v___x_6190_, 3, v___x_6188_);
lean_ctor_set(v___x_6190_, 4, v___x_6189_);
lean_ctor_set(v___x_6190_, 5, v___x_6185_);
lean_ctor_set(v___x_6190_, 6, v___x_6189_);
lean_ctor_set_uint8(v___x_6190_, sizeof(void*)*7, v___x_6172_);
lean_ctor_set_uint8(v___x_6190_, sizeof(void*)*7 + 1, v___x_6172_);
lean_ctor_set_uint8(v___x_6190_, sizeof(void*)*7 + 2, v___x_6172_);
lean_ctor_set_uint8(v___x_6190_, sizeof(void*)*7 + 3, v___x_6169_);
v___x_6191_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6192_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6193_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6194_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6194_, 0, v___x_6191_);
lean_ctor_set(v___x_6194_, 1, v___x_6192_);
lean_ctor_set(v___x_6194_, 2, v___x_6153_);
lean_ctor_set(v___x_6194_, 3, v___x_6186_);
lean_ctor_set(v___x_6194_, 4, v___x_6193_);
v___x_6195_ = lean_st_mk_ref(v___x_6194_);
lean_inc_ref(v_name_6154_);
v___x_6203_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(v_name_6154_, v_val_6175_, v___x_6190_, v___x_6195_, v___y_6155_, v___y_6156_);
if (lean_obj_tag(v___x_6203_) == 0)
{
lean_object* v_a_6204_; 
v_a_6204_ = lean_ctor_get(v___x_6203_, 0);
lean_inc(v_a_6204_);
lean_dec_ref_known(v___x_6203_, 1);
if (lean_obj_tag(v_a_6204_) == 1)
{
lean_object* v_val_6205_; lean_object* v___x_6206_; lean_object* v___f_6207_; lean_object* v___x_6208_; 
v_val_6205_ = lean_ctor_get(v_a_6204_, 0);
lean_inc(v_val_6205_);
lean_dec_ref_known(v_a_6204_, 1);
v___x_6206_ = lean_box(v___x_6172_);
v___f_6207_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed), 7, 2);
lean_closure_set(v___f_6207_, 0, v_val_6205_);
lean_closure_set(v___f_6207_, 1, v___x_6206_);
v___x_6208_ = l_Lean_Meta_realizeConst(v_pre_6166_, v_name_6154_, v___f_6207_, v___x_6190_, v___x_6195_, v___y_6155_, v___y_6156_);
lean_dec_ref_known(v___x_6190_, 7);
if (lean_obj_tag(v___x_6208_) == 0)
{
lean_dec_ref_known(v___x_6208_, 1);
v_a_6197_ = v___x_6169_;
goto v___jp_6196_;
}
else
{
lean_object* v_a_6209_; lean_object* v___x_6211_; uint8_t v_isShared_6212_; uint8_t v_isSharedCheck_6216_; 
lean_dec(v___x_6195_);
lean_del_object(v___x_6177_);
v_a_6209_ = lean_ctor_get(v___x_6208_, 0);
v_isSharedCheck_6216_ = !lean_is_exclusive(v___x_6208_);
if (v_isSharedCheck_6216_ == 0)
{
v___x_6211_ = v___x_6208_;
v_isShared_6212_ = v_isSharedCheck_6216_;
goto v_resetjp_6210_;
}
else
{
lean_inc(v_a_6209_);
lean_dec(v___x_6208_);
v___x_6211_ = lean_box(0);
v_isShared_6212_ = v_isSharedCheck_6216_;
goto v_resetjp_6210_;
}
v_resetjp_6210_:
{
lean_object* v___x_6214_; 
if (v_isShared_6212_ == 0)
{
v___x_6214_ = v___x_6211_;
goto v_reusejp_6213_;
}
else
{
lean_object* v_reuseFailAlloc_6215_; 
v_reuseFailAlloc_6215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6215_, 0, v_a_6209_);
v___x_6214_ = v_reuseFailAlloc_6215_;
goto v_reusejp_6213_;
}
v_reusejp_6213_:
{
return v___x_6214_;
}
}
}
}
else
{
lean_dec(v_a_6204_);
lean_dec_ref_known(v___x_6190_, 7);
lean_dec(v_pre_6166_);
lean_dec_ref_known(v_name_6154_, 2);
v_a_6197_ = v___x_6172_;
goto v___jp_6196_;
}
}
else
{
lean_object* v_a_6217_; lean_object* v___x_6219_; uint8_t v_isShared_6220_; uint8_t v_isSharedCheck_6224_; 
lean_dec(v___x_6195_);
lean_dec_ref_known(v___x_6190_, 7);
lean_del_object(v___x_6177_);
lean_dec(v_pre_6166_);
lean_dec_ref_known(v_name_6154_, 2);
v_a_6217_ = lean_ctor_get(v___x_6203_, 0);
v_isSharedCheck_6224_ = !lean_is_exclusive(v___x_6203_);
if (v_isSharedCheck_6224_ == 0)
{
v___x_6219_ = v___x_6203_;
v_isShared_6220_ = v_isSharedCheck_6224_;
goto v_resetjp_6218_;
}
else
{
lean_inc(v_a_6217_);
lean_dec(v___x_6203_);
v___x_6219_ = lean_box(0);
v_isShared_6220_ = v_isSharedCheck_6224_;
goto v_resetjp_6218_;
}
v_resetjp_6218_:
{
lean_object* v___x_6222_; 
if (v_isShared_6220_ == 0)
{
v___x_6222_ = v___x_6219_;
goto v_reusejp_6221_;
}
else
{
lean_object* v_reuseFailAlloc_6223_; 
v_reuseFailAlloc_6223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6223_, 0, v_a_6217_);
v___x_6222_ = v_reuseFailAlloc_6223_;
goto v_reusejp_6221_;
}
v_reusejp_6221_:
{
return v___x_6222_;
}
}
}
v___jp_6196_:
{
lean_object* v___x_6198_; lean_object* v___x_6199_; lean_object* v___x_6201_; 
v___x_6198_ = lean_st_ref_get(v___x_6195_);
lean_dec(v___x_6195_);
lean_dec(v___x_6198_);
v___x_6199_ = lean_box(v_a_6197_);
if (v_isShared_6178_ == 0)
{
lean_ctor_set_tag(v___x_6177_, 0);
lean_ctor_set(v___x_6177_, 0, v___x_6199_);
v___x_6201_ = v___x_6177_;
goto v_reusejp_6200_;
}
else
{
lean_object* v_reuseFailAlloc_6202_; 
v_reuseFailAlloc_6202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6202_, 0, v___x_6199_);
v___x_6201_ = v_reuseFailAlloc_6202_;
goto v_reusejp_6200_;
}
v_reusejp_6200_:
{
return v___x_6201_;
}
}
}
}
else
{
lean_dec(v_val_6174_);
lean_dec_ref_known(v_name_6154_, 2);
lean_dec(v_pre_6166_);
lean_dec(v___x_6153_);
goto v___jp_6158_;
}
}
else
{
lean_dec(v___x_6173_);
lean_dec_ref_known(v_name_6154_, 2);
lean_dec(v_pre_6166_);
lean_dec(v___x_6153_);
goto v___jp_6158_;
}
}
}
else
{
lean_dec(v_name_6154_);
lean_dec(v___x_6153_);
goto v___jp_6162_;
}
v___jp_6158_:
{
uint8_t v___x_6159_; lean_object* v___x_6160_; lean_object* v___x_6161_; 
v___x_6159_ = 0;
v___x_6160_ = lean_box(v___x_6159_);
v___x_6161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6161_, 0, v___x_6160_);
return v___x_6161_;
}
v___jp_6162_:
{
uint8_t v___x_6163_; lean_object* v___x_6164_; lean_object* v___x_6165_; 
v___x_6163_ = 0;
v___x_6164_ = lean_box(v___x_6163_);
v___x_6165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6165_, 0, v___x_6164_);
return v___x_6165_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object* v___x_6226_, lean_object* v_name_6227_, lean_object* v___y_6228_, lean_object* v___y_6229_, lean_object* v___y_6230_){
_start:
{
lean_object* v_res_6231_; 
v_res_6231_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(v___x_6226_, v_name_6227_, v___y_6228_, v___y_6229_);
lean_dec(v___y_6229_);
lean_dec_ref(v___y_6228_);
return v_res_6231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_6235_; lean_object* v___x_6236_; 
v___f_6235_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_));
v___x_6236_ = l_Lean_registerReservedNameAction(v___f_6235_);
return v___x_6236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object* v_a_6237_){
_start:
{
lean_object* v_res_6238_; 
v_res_6238_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_();
return v_res_6238_;
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
