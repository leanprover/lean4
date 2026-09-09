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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
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
v___x_213_ = lean_st_ref_put(v_a_207_, v___x_212_);
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
lean_object* v___y_254_; lean_object* v___y_264_; lean_object* v___y_265_; uint8_t v___y_266_; lean_object* v___y_267_; uint8_t v___y_268_; lean_object* v_toCold_273_; lean_object* v_currRecDepth_274_; lean_object* v_ref_275_; uint8_t v_diag_276_; uint8_t v_suppressElabErrors_277_; lean_object* v_maxRecDepth_278_; lean_object* v_cancelTk_x3f_279_; 
v_toCold_273_ = lean_ctor_get(v___y_250_, 0);
v_currRecDepth_274_ = lean_ctor_get(v___y_250_, 1);
v_ref_275_ = lean_ctor_get(v___y_250_, 2);
v_diag_276_ = lean_ctor_get_uint8(v___y_250_, sizeof(void*)*3);
v_suppressElabErrors_277_ = lean_ctor_get_uint8(v___y_250_, sizeof(void*)*3 + 1);
v_maxRecDepth_278_ = lean_ctor_get(v_toCold_273_, 3);
v_cancelTk_x3f_279_ = lean_ctor_get(v_toCold_273_, 10);
if (lean_obj_tag(v_cancelTk_x3f_279_) == 1)
{
lean_object* v_val_285_; uint8_t v___x_286_; 
v_val_285_ = lean_ctor_get(v_cancelTk_x3f_279_, 0);
v___x_286_ = l_IO_CancelToken_isSet(v_val_285_);
if (v___x_286_ == 0)
{
goto v___jp_280_;
}
else
{
lean_object* v___x_287_; lean_object* v_a_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_295_; 
lean_dec_ref(v_x_248_);
v___x_287_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg();
v_a_288_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_295_ == 0)
{
v___x_290_ = v___x_287_;
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_a_288_);
lean_dec(v___x_287_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_293_; 
if (v_isShared_291_ == 0)
{
v___x_293_ = v___x_290_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v_a_288_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
}
}
else
{
goto v___jp_280_;
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
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_269_ = lean_unsigned_to_nat(1u);
v___x_270_ = lean_nat_add(v___y_264_, v___x_269_);
lean_inc_ref(v___y_267_);
v___x_271_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_271_, 0, v___y_267_);
lean_ctor_set(v___x_271_, 1, v___x_270_);
lean_ctor_set(v___x_271_, 2, v___y_265_);
lean_ctor_set_uint8(v___x_271_, sizeof(void*)*3, v___y_266_);
lean_ctor_set_uint8(v___x_271_, sizeof(void*)*3 + 1, v___y_268_);
lean_inc(v___y_251_);
lean_inc(v___y_249_);
v___x_272_ = lean_apply_4(v_x_248_, v___y_249_, v___x_271_, v___y_251_, lean_box(0));
v___y_254_ = v___x_272_;
goto v___jp_253_;
}
v___jp_280_:
{
lean_object* v___x_281_; uint8_t v___x_282_; 
v___x_281_ = lean_unsigned_to_nat(0u);
v___x_282_ = lean_nat_dec_eq(v_maxRecDepth_278_, v___x_281_);
if (v___x_282_ == 0)
{
uint8_t v___x_283_; 
v___x_283_ = lean_nat_dec_eq(v_currRecDepth_274_, v_maxRecDepth_278_);
if (v___x_283_ == 0)
{
lean_inc(v_ref_275_);
v___y_264_ = v_currRecDepth_274_;
v___y_265_ = v_ref_275_;
v___y_266_ = v_diag_276_;
v___y_267_ = v_toCold_273_;
v___y_268_ = v_suppressElabErrors_277_;
goto v___jp_263_;
}
else
{
lean_object* v___x_284_; 
lean_dec_ref(v_x_248_);
lean_inc(v_ref_275_);
v___x_284_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_275_);
v___y_254_ = v___x_284_;
goto v___jp_253_;
}
}
else
{
lean_inc(v_ref_275_);
v___y_264_ = v_currRecDepth_274_;
v___y_265_ = v_ref_275_;
v___y_266_ = v_diag_276_;
v___y_267_ = v_toCold_273_;
v___y_268_ = v_suppressElabErrors_277_;
goto v___jp_263_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(v_x_296_, v___y_297_, v___y_298_, v___y_299_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_297_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_302_, lean_object* v_x_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = lean_apply_1(v_x_303_, lean_box(0));
v___x_308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_309_, lean_object* v_x_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(v_00_u03b1_309_, v_x_310_, v___y_311_, v___y_312_);
lean_dec(v___y_312_);
lean_dec_ref(v___y_311_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_a_315_, lean_object* v_x_316_){
_start:
{
if (lean_obj_tag(v_x_316_) == 0)
{
lean_object* v___x_317_; 
v___x_317_ = lean_box(0);
return v___x_317_;
}
else
{
lean_object* v_key_318_; lean_object* v_value_319_; lean_object* v_tail_320_; uint8_t v___x_321_; 
v_key_318_ = lean_ctor_get(v_x_316_, 0);
v_value_319_ = lean_ctor_get(v_x_316_, 1);
v_tail_320_ = lean_ctor_get(v_x_316_, 2);
v___x_321_ = l_Lean_ExprStructEq_beq(v_key_318_, v_a_315_);
if (v___x_321_ == 0)
{
v_x_316_ = v_tail_320_;
goto _start;
}
else
{
lean_object* v___x_323_; 
lean_inc(v_value_319_);
v___x_323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_323_, 0, v_value_319_);
return v___x_323_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_a_324_, lean_object* v_x_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(v_a_324_, v_x_325_);
lean_dec(v_x_325_);
lean_dec_ref(v_a_324_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(lean_object* v_m_327_, lean_object* v_a_328_){
_start:
{
lean_object* v_buckets_329_; lean_object* v___x_330_; uint64_t v___x_331_; uint64_t v___x_332_; uint64_t v___x_333_; uint64_t v_fold_334_; uint64_t v___x_335_; uint64_t v___x_336_; uint64_t v___x_337_; size_t v___x_338_; size_t v___x_339_; size_t v___x_340_; size_t v___x_341_; size_t v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v_buckets_329_ = lean_ctor_get(v_m_327_, 1);
v___x_330_ = lean_array_get_size(v_buckets_329_);
v___x_331_ = l_Lean_ExprStructEq_hash(v_a_328_);
v___x_332_ = 32ULL;
v___x_333_ = lean_uint64_shift_right(v___x_331_, v___x_332_);
v_fold_334_ = lean_uint64_xor(v___x_331_, v___x_333_);
v___x_335_ = 16ULL;
v___x_336_ = lean_uint64_shift_right(v_fold_334_, v___x_335_);
v___x_337_ = lean_uint64_xor(v_fold_334_, v___x_336_);
v___x_338_ = lean_uint64_to_usize(v___x_337_);
v___x_339_ = lean_usize_of_nat(v___x_330_);
v___x_340_ = ((size_t)1ULL);
v___x_341_ = lean_usize_sub(v___x_339_, v___x_340_);
v___x_342_ = lean_usize_land(v___x_338_, v___x_341_);
v___x_343_ = lean_array_uget_borrowed(v_buckets_329_, v___x_342_);
v___x_344_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(v_a_328_, v___x_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_345_, lean_object* v_a_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(v_m_345_, v_a_346_);
lean_dec_ref(v_a_346_);
lean_dec_ref(v_m_345_);
return v_res_347_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0(void){
_start:
{
lean_object* v___x_349_; lean_object* v_dummy_350_; 
v___x_349_ = lean_box(0);
v_dummy_350_ = l_Lean_Expr_sort___override(v___x_349_);
return v_dummy_350_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1(lean_object* v_pre_351_, lean_object* v_post_352_, size_t v_sz_353_, size_t v_i_354_, lean_object* v_bs_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
uint8_t v___x_360_; 
v___x_360_ = lean_usize_dec_lt(v_i_354_, v_sz_353_);
if (v___x_360_ == 0)
{
lean_object* v___x_361_; 
lean_dec_ref(v_post_352_);
lean_dec_ref(v_pre_351_);
v___x_361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_361_, 0, v_bs_355_);
return v___x_361_;
}
else
{
lean_object* v_v_362_; lean_object* v___x_363_; 
v_v_362_ = lean_array_uget_borrowed(v_bs_355_, v_i_354_);
lean_inc(v_v_362_);
lean_inc_ref(v_post_352_);
lean_inc_ref(v_pre_351_);
v___x_363_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_351_, v_post_352_, v_v_362_, v___y_356_, v___y_357_, v___y_358_);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_object* v_a_364_; lean_object* v___x_365_; lean_object* v_bs_x27_366_; size_t v___x_367_; size_t v___x_368_; lean_object* v___x_369_; 
v_a_364_ = lean_ctor_get(v___x_363_, 0);
lean_inc(v_a_364_);
lean_dec_ref_known(v___x_363_, 1);
v___x_365_ = lean_unsigned_to_nat(0u);
v_bs_x27_366_ = lean_array_uset(v_bs_355_, v_i_354_, v___x_365_);
v___x_367_ = ((size_t)1ULL);
v___x_368_ = lean_usize_add(v_i_354_, v___x_367_);
v___x_369_ = lean_array_uset(v_bs_x27_366_, v_i_354_, v_a_364_);
v_i_354_ = v___x_368_;
v_bs_355_ = v___x_369_;
goto _start;
}
else
{
lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_378_; 
lean_dec_ref(v_bs_355_);
lean_dec_ref(v_post_352_);
lean_dec_ref(v_pre_351_);
v_a_371_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_378_ == 0)
{
v___x_373_ = v___x_363_;
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_363_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_376_; 
if (v_isShared_374_ == 0)
{
v___x_376_ = v___x_373_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_a_371_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4(lean_object* v_pre_379_, lean_object* v_post_380_, lean_object* v_x_381_, lean_object* v_x_382_, lean_object* v_x_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
if (lean_obj_tag(v_x_381_) == 5)
{
lean_object* v_fn_388_; lean_object* v_arg_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v_fn_388_ = lean_ctor_get(v_x_381_, 0);
lean_inc_ref(v_fn_388_);
v_arg_389_ = lean_ctor_get(v_x_381_, 1);
lean_inc_ref(v_arg_389_);
lean_dec_ref_known(v_x_381_, 2);
v___x_390_ = lean_array_set(v_x_382_, v_x_383_, v_arg_389_);
v___x_391_ = lean_unsigned_to_nat(1u);
v___x_392_ = lean_nat_sub(v_x_383_, v___x_391_);
lean_dec(v_x_383_);
v_x_381_ = v_fn_388_;
v_x_382_ = v___x_390_;
v_x_383_ = v___x_392_;
goto _start;
}
else
{
lean_object* v___x_394_; 
lean_dec(v_x_383_);
lean_inc_ref(v_post_380_);
lean_inc_ref(v_pre_379_);
v___x_394_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_379_, v_post_380_, v_x_381_, v___y_384_, v___y_385_, v___y_386_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v_a_395_; size_t v_sz_396_; size_t v___x_397_; lean_object* v___x_398_; 
v_a_395_ = lean_ctor_get(v___x_394_, 0);
lean_inc(v_a_395_);
lean_dec_ref_known(v___x_394_, 1);
v_sz_396_ = lean_array_size(v_x_382_);
v___x_397_ = ((size_t)0ULL);
lean_inc_ref(v_post_380_);
lean_inc_ref(v_pre_379_);
v___x_398_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1(v_pre_379_, v_post_380_, v_sz_396_, v___x_397_, v_x_382_, v___y_384_, v___y_385_, v___y_386_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v_a_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v_a_399_ = lean_ctor_get(v___x_398_, 0);
lean_inc(v_a_399_);
lean_dec_ref_known(v___x_398_, 1);
v___x_400_ = l_Lean_mkAppN(v_a_395_, v_a_399_);
lean_dec(v_a_399_);
v___x_401_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_379_, v_post_380_, v___x_400_, v___y_384_, v___y_385_, v___y_386_);
return v___x_401_;
}
else
{
lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_409_; 
lean_dec(v_a_395_);
lean_dec_ref(v_post_380_);
lean_dec_ref(v_pre_379_);
v_a_402_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_409_ == 0)
{
v___x_404_ = v___x_398_;
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v___x_398_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_407_; 
if (v_isShared_405_ == 0)
{
v___x_407_ = v___x_404_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_a_402_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
}
else
{
lean_dec_ref(v_x_382_);
lean_dec_ref(v_post_380_);
lean_dec_ref(v_pre_379_);
return v___x_394_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1(lean_object* v___x_410_, lean_object* v_pre_411_, lean_object* v_e_412_, lean_object* v_post_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Lean_Core_checkSystem(v___x_410_, v___y_415_, v___y_416_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v___x_419_; 
lean_dec_ref_known(v___x_418_, 1);
lean_inc_ref(v_pre_411_);
lean_inc(v___y_416_);
lean_inc_ref(v___y_415_);
lean_inc_ref(v_e_412_);
v___x_419_ = lean_apply_4(v_pre_411_, v_e_412_, v___y_415_, v___y_416_, lean_box(0));
if (lean_obj_tag(v___x_419_) == 0)
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_535_; 
v_a_420_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_535_ == 0)
{
v___x_422_ = v___x_419_;
v_isShared_423_ = v_isSharedCheck_535_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v___x_419_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_535_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___y_425_; 
switch(lean_obj_tag(v_a_420_))
{
case 0:
{
lean_object* v_e_525_; lean_object* v___x_527_; 
lean_dec_ref(v_post_413_);
lean_dec_ref(v_e_412_);
lean_dec_ref(v_pre_411_);
v_e_525_ = lean_ctor_get(v_a_420_, 0);
lean_inc_ref(v_e_525_);
lean_dec_ref_known(v_a_420_, 1);
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 0, v_e_525_);
v___x_527_ = v___x_422_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_e_525_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
case 1:
{
lean_object* v_e_529_; lean_object* v___x_530_; 
lean_del_object(v___x_422_);
lean_dec_ref(v_e_412_);
v_e_529_ = lean_ctor_get(v_a_420_, 0);
lean_inc_ref(v_e_529_);
lean_dec_ref_known(v_a_420_, 1);
lean_inc_ref(v_post_413_);
lean_inc_ref(v_pre_411_);
v___x_530_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_411_, v_post_413_, v_e_529_, v___y_414_, v___y_415_, v___y_416_);
if (lean_obj_tag(v___x_530_) == 0)
{
lean_object* v_a_531_; lean_object* v___x_532_; 
v_a_531_ = lean_ctor_get(v___x_530_, 0);
lean_inc(v_a_531_);
lean_dec_ref_known(v___x_530_, 1);
v___x_532_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_411_, v_post_413_, v_a_531_, v___y_414_, v___y_415_, v___y_416_);
return v___x_532_;
}
else
{
lean_dec_ref(v_post_413_);
lean_dec_ref(v_pre_411_);
return v___x_530_;
}
}
default: 
{
lean_object* v_e_x3f_533_; 
lean_del_object(v___x_422_);
v_e_x3f_533_ = lean_ctor_get(v_a_420_, 0);
lean_inc(v_e_x3f_533_);
lean_dec_ref_known(v_a_420_, 1);
if (lean_obj_tag(v_e_x3f_533_) == 0)
{
v___y_425_ = v_e_412_;
goto v___jp_424_;
}
else
{
lean_object* v_val_534_; 
lean_dec_ref(v_e_412_);
v_val_534_ = lean_ctor_get(v_e_x3f_533_, 0);
lean_inc(v_val_534_);
lean_dec_ref_known(v_e_x3f_533_, 1);
v___y_425_ = v_val_534_;
goto v___jp_424_;
}
}
}
v___jp_424_:
{
switch(lean_obj_tag(v___y_425_))
{
case 7:
{
lean_object* v_binderName_426_; lean_object* v_binderType_427_; lean_object* v_body_428_; uint8_t v_binderInfo_429_; lean_object* v___x_430_; 
v_binderName_426_ = lean_ctor_get(v___y_425_, 0);
v_binderType_427_ = lean_ctor_get(v___y_425_, 1);
v_body_428_ = lean_ctor_get(v___y_425_, 2);
v_binderInfo_429_ = lean_ctor_get_uint8(v___y_425_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_427_);
lean_inc_ref(v_post_413_);
lean_inc_ref(v_pre_411_);
v___x_430_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_411_, v_post_413_, v_binderType_427_, v___y_414_, v___y_415_, v___y_416_);
if (lean_obj_tag(v___x_430_) == 0)
{
lean_object* v_a_431_; lean_object* v___x_432_; 
v_a_431_ = lean_ctor_get(v___x_430_, 0);
lean_inc(v_a_431_);
lean_dec_ref_known(v___x_430_, 1);
lean_inc_ref(v_body_428_);
lean_inc_ref(v_post_413_);
lean_inc_ref(v_pre_411_);
v___x_432_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_411_, v_post_413_, v_body_428_, v___y_414_, v___y_415_, v___y_416_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v_a_433_; size_t v___x_434_; size_t v___x_435_; uint8_t v___x_436_; 
v_a_433_ = lean_ctor_get(v___x_432_, 0);
lean_inc(v_a_433_);
lean_dec_ref_known(v___x_432_, 1);
v___x_434_ = lean_ptr_addr(v_binderType_427_);
v___x_435_ = lean_ptr_addr(v_a_431_);
v___x_436_ = lean_usize_dec_eq(v___x_434_, v___x_435_);
if (v___x_436_ == 0)
{
lean_object* v___x_437_; lean_object* v___x_438_; 
lean_inc(v_binderName_426_);
lean_dec_ref_known(v___y_425_, 3);
v___x_437_ = l_Lean_Expr_forallE___override(v_binderName_426_, v_a_431_, v_a_433_, v_binderInfo_429_);
v___x_438_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_411_, v_post_413_, v___x_437_, v___y_414_, v___y_415_, v___y_416_);
return v___x_438_;
}
else
{
size_t v___x_439_; size_t v___x_440_; uint8_t v___x_441_; 
v___x_439_ = lean_ptr_addr(v_body_428_);
v___x_440_ = lean_ptr_addr(v_a_433_);
v___x_441_ = lean_usize_dec_eq(v___x_439_, v___x_440_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; lean_object* v___x_443_; 
lean_inc(v_binderName_426_);
lean_dec_ref_known(v___y_425_, 3);
v___x_442_ = l_Lean_Expr_forallE___override(v_binderName_426_, v_a_431_, v_a_433_, v_binderInfo_429_);
v___x_443_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_411_, v_post_413_, v___x_442_, v___y_414_, v___y_415_, v___y_416_);
return v___x_443_;
}
else
{
uint8_t v___x_444_; 
v___x_444_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_429_, v_binderInfo_429_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; lean_object* v___x_446_; 
lean_inc(v_binderName_426_);
lean_dec_ref_known(v___y_425_, 3);
v___x_445_ = l_Lean_Expr_forallE___override(v_binderName_426_, v_a_431_, v_a_433_, v_binderInfo_429_);
v___x_446_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_411_, v_post_413_, v___x_445_, v___y_414_, v___y_415_, v___y_416_);
return v___x_446_;
}
else
{
lean_object* v___x_447_; 
lean_dec(v_a_433_);
lean_dec(v_a_431_);
v___x_447_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_411_, v_post_413_, v___y_425_, v___y_414_, v___y_415_, v___y_416_);
return v___x_447_;
}
}
}
}
else
{
lean_dec(v_a_431_);
lean_dec_ref_known(v___y_425_, 3);
lean_dec_ref(v_post_413_);
lean_dec_ref(v_pre_411_);
return v___x_432_;
}
}
else
{
lean_dec_ref_known(v___y_425_, 3);
lean_dec_ref(v_post_413_);
lean_dec_ref(v_pre_411_);
return v___x_430_;
}
}
case 6:
{
lean_object* v_binderName_448_; lean_object* v_binderType_449_; lean_object* v_body_450_; uint8_t v_binderInfo_451_; lean_object* v___x_452_; 
v_binderName_448_ = lean_ctor_get(v___y_425_, 0);
v_binderType_449_ = lean_ctor_get(v___y_425_, 1);
v_body_450_ = lean_ctor_get(v___y_425_, 2);
v_binderInfo_451_ = lean_ctor_get_uint8(v___y_425_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_449_);
lean_inc_ref(v_post_413_);
lean_inc_ref(v_pre_411_);
v___x_452_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_411_, v_post_413_, v_binderType_449_, v___y_414_, v___y_415_, v___y_416_);
if (lean_obj_tag(v___x_452_) == 0)
{
lean_object* v_a_453_; lean_object* v___x_454_; 
v_a_453_ = lean_ctor_get(v___x_452_, 0);
lean_inc(v_a_453_);
lean_dec_ref_known(v___x_452_, 1);
lean_inc_ref(v_body_450_);
lean_inc_ref(v_post_413_);
lean_inc_ref(v_pre_411_);
v___x_454_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_411_, v_post_413_, v_body_450_, v___y_414_, v___y_415_, v___y_416_);
if (lean_obj_tag(v___x_454_) == 0)
{
lean_object* v_a_455_; size_t v___x_456_; size_t v___x_457_; uint8_t v___x_458_; 
v_a_455_ = lean_ctor_get(v___x_454_, 0);
lean_inc(v_a_455_);
lean_dec_ref_known(v___x_454_, 1);
v___x_456_ = lean_ptr_addr(v_binderType_449_);
v___x_457_ = lean_ptr_addr(v_a_453_);
v___x_458_ = lean_usize_dec_eq(v___x_456_, v___x_457_);
if (v___x_458_ == 0)
{
lean_object* v___x_459_; lean_object* v___x_460_; 
lean_inc(v_binderName_448_);
lean_dec_ref_known(v___y_425_, 3);
v___x_459_ = l_Lean_Expr_lam___override(v_binderName_448_, v_a_453_, v_a_455_, v_binderInfo_451_);
v___x_460_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_411_, v_post_413_, v___x_459_, v___y_414_, v___y_415_, v___y_416_);
return v___x_460_;
}
else
{
size_t v___x_461_; size_t v___x_462_; uint8_t v___x_463_; 
v___x_461_ = lean_ptr_addr(v_body_450_);
v___x_462_ = lean_ptr_addr(v_a_455_);
v___x_463_ = lean_usize_dec_eq(v___x_461_, v___x_462_);
if (v___x_463_ == 0)
{
lean_object* v___x_464_; lean_object* v___x_465_; 
lean_inc(v_binderName_448_);
lean_dec_ref_known(v___y_425_, 3);
v___x_464_ = l_Lean_Expr_lam___override(v_binderName_448_, v_a_453_, v_a_455_, v_binderInfo_451_);
v___x_465_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_411_, v_post_413_, v___x_464_, v___y_414_, v___y_415_, v___y_416_);
return v___x_465_;
}
else
{
uint8_t v___x_466_; 
v___x_466_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_451_, v_binderInfo_451_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; lean_object* v___x_468_; 
lean_inc(v_binderName_448_);
lean_dec_ref_known(v___y_425_, 3);
v___x_467_ = l_Lean_Expr_lam___override(v_binderName_448_, v_a_453_, v_a_455_, v_binderInfo_451_);
v___x_468_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_411_, v_post_413_, v___x_467_, v___y_414_, v___y_415_, v___y_416_);
return v___x_468_;
}
else
{
lean_object* v___x_469_; 
lean_dec(v_a_455_);
lean_dec(v_a_453_);
v___x_469_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_411_, v_post_413_, v___y_425_, v___y_414_, v___y_415_, v___y_416_);
return v___x_469_;
}
}
}
}
else
{
lean_dec(v_a_453_);
lean_dec_ref_known(v___y_425_, 3);
lean_dec_ref(v_post_413_);
lean_dec_ref(v_pre_411_);
return v___x_454_;
}
}
else
{
lean_dec_ref_known(v___y_425_, 3);
lean_dec_ref(v_post_413_);
lean_dec_ref(v_pre_411_);
return v___x_452_;
}
}
case 8:
{
lean_object* v_declName_470_; lean_object* v_type_471_; lean_object* v_value_472_; lean_object* v_body_473_; uint8_t v_nondep_474_; lean_object* v___x_475_; 
v_declName_470_ = lean_ctor_get(v___y_425_, 0);
v_type_471_ = lean_ctor_get(v___y_425_, 1);
v_value_472_ = lean_ctor_get(v___y_425_, 2);
v_body_473_ = lean_ctor_get(v___y_425_, 3);
v_nondep_474_ = lean_ctor_get_uint8(v___y_425_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_471_);
lean_inc_ref(v_post_413_);
lean_inc_ref(v_pre_411_);
v___x_475_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_411_, v_post_413_, v_type_471_, v___y_414_, v___y_415_, v___y_416_);
if (lean_obj_tag(v___x_475_) == 0)
{
lean_object* v_a_476_; lean_object* v___x_477_; 
v_a_476_ = lean_ctor_get(v___x_475_, 0);
lean_inc(v_a_476_);
lean_dec_ref_known(v___x_475_, 1);
lean_inc_ref(v_value_472_);
lean_inc_ref(v_post_413_);
lean_inc_ref(v_pre_411_);
v___x_477_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_411_, v_post_413_, v_value_472_, v___y_414_, v___y_415_, v___y_416_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v_a_478_; lean_object* v___x_479_; 
v_a_478_ = lean_ctor_get(v___x_477_, 0);
lean_inc(v_a_478_);
lean_dec_ref_known(v___x_477_, 1);
lean_inc_ref(v_body_473_);
lean_inc_ref(v_post_413_);
lean_inc_ref(v_pre_411_);
v___x_479_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_411_, v_post_413_, v_body_473_, v___y_414_, v___y_415_, v___y_416_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v_a_480_; size_t v___x_481_; size_t v___x_482_; uint8_t v___x_483_; 
v_a_480_ = lean_ctor_get(v___x_479_, 0);
lean_inc(v_a_480_);
lean_dec_ref_known(v___x_479_, 1);
v___x_481_ = lean_ptr_addr(v_type_471_);
v___x_482_ = lean_ptr_addr(v_a_476_);
v___x_483_ = lean_usize_dec_eq(v___x_481_, v___x_482_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; lean_object* v___x_485_; 
lean_inc(v_declName_470_);
lean_dec_ref_known(v___y_425_, 4);
v___x_484_ = l_Lean_Expr_letE___override(v_declName_470_, v_a_476_, v_a_478_, v_a_480_, v_nondep_474_);
v___x_485_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_411_, v_post_413_, v___x_484_, v___y_414_, v___y_415_, v___y_416_);
return v___x_485_;
}
else
{
size_t v___x_486_; size_t v___x_487_; uint8_t v___x_488_; 
v___x_486_ = lean_ptr_addr(v_value_472_);
v___x_487_ = lean_ptr_addr(v_a_478_);
v___x_488_ = lean_usize_dec_eq(v___x_486_, v___x_487_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; lean_object* v___x_490_; 
lean_inc(v_declName_470_);
lean_dec_ref_known(v___y_425_, 4);
v___x_489_ = l_Lean_Expr_letE___override(v_declName_470_, v_a_476_, v_a_478_, v_a_480_, v_nondep_474_);
v___x_490_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_411_, v_post_413_, v___x_489_, v___y_414_, v___y_415_, v___y_416_);
return v___x_490_;
}
else
{
size_t v___x_491_; size_t v___x_492_; uint8_t v___x_493_; 
v___x_491_ = lean_ptr_addr(v_body_473_);
v___x_492_ = lean_ptr_addr(v_a_480_);
v___x_493_ = lean_usize_dec_eq(v___x_491_, v___x_492_);
if (v___x_493_ == 0)
{
lean_object* v___x_494_; lean_object* v___x_495_; 
lean_inc(v_declName_470_);
lean_dec_ref_known(v___y_425_, 4);
v___x_494_ = l_Lean_Expr_letE___override(v_declName_470_, v_a_476_, v_a_478_, v_a_480_, v_nondep_474_);
v___x_495_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_411_, v_post_413_, v___x_494_, v___y_414_, v___y_415_, v___y_416_);
return v___x_495_;
}
else
{
lean_object* v___x_496_; 
lean_dec(v_a_480_);
lean_dec(v_a_478_);
lean_dec(v_a_476_);
v___x_496_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_411_, v_post_413_, v___y_425_, v___y_414_, v___y_415_, v___y_416_);
return v___x_496_;
}
}
}
}
else
{
lean_dec(v_a_478_);
lean_dec(v_a_476_);
lean_dec_ref_known(v___y_425_, 4);
lean_dec_ref(v_post_413_);
lean_dec_ref(v_pre_411_);
return v___x_479_;
}
}
else
{
lean_dec(v_a_476_);
lean_dec_ref_known(v___y_425_, 4);
lean_dec_ref(v_post_413_);
lean_dec_ref(v_pre_411_);
return v___x_477_;
}
}
else
{
lean_dec_ref_known(v___y_425_, 4);
lean_dec_ref(v_post_413_);
lean_dec_ref(v_pre_411_);
return v___x_475_;
}
}
case 5:
{
lean_object* v_dummy_497_; lean_object* v_nargs_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v_dummy_497_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0);
v_nargs_498_ = l_Lean_Expr_getAppNumArgs(v___y_425_);
lean_inc(v_nargs_498_);
v___x_499_ = lean_mk_array(v_nargs_498_, v_dummy_497_);
v___x_500_ = lean_unsigned_to_nat(1u);
v___x_501_ = lean_nat_sub(v_nargs_498_, v___x_500_);
lean_dec(v_nargs_498_);
v___x_502_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4(v_pre_411_, v_post_413_, v___y_425_, v___x_499_, v___x_501_, v___y_414_, v___y_415_, v___y_416_);
return v___x_502_;
}
case 10:
{
lean_object* v_data_503_; lean_object* v_expr_504_; lean_object* v___x_505_; 
v_data_503_ = lean_ctor_get(v___y_425_, 0);
v_expr_504_ = lean_ctor_get(v___y_425_, 1);
lean_inc_ref(v_expr_504_);
lean_inc_ref(v_post_413_);
lean_inc_ref(v_pre_411_);
v___x_505_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_411_, v_post_413_, v_expr_504_, v___y_414_, v___y_415_, v___y_416_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_a_506_; size_t v___x_507_; size_t v___x_508_; uint8_t v___x_509_; 
v_a_506_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_a_506_);
lean_dec_ref_known(v___x_505_, 1);
v___x_507_ = lean_ptr_addr(v_expr_504_);
v___x_508_ = lean_ptr_addr(v_a_506_);
v___x_509_ = lean_usize_dec_eq(v___x_507_, v___x_508_);
if (v___x_509_ == 0)
{
lean_object* v___x_510_; lean_object* v___x_511_; 
lean_inc(v_data_503_);
lean_dec_ref_known(v___y_425_, 2);
v___x_510_ = l_Lean_Expr_mdata___override(v_data_503_, v_a_506_);
v___x_511_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_411_, v_post_413_, v___x_510_, v___y_414_, v___y_415_, v___y_416_);
return v___x_511_;
}
else
{
lean_object* v___x_512_; 
lean_dec(v_a_506_);
v___x_512_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_411_, v_post_413_, v___y_425_, v___y_414_, v___y_415_, v___y_416_);
return v___x_512_;
}
}
else
{
lean_dec_ref_known(v___y_425_, 2);
lean_dec_ref(v_post_413_);
lean_dec_ref(v_pre_411_);
return v___x_505_;
}
}
case 11:
{
lean_object* v_typeName_513_; lean_object* v_idx_514_; lean_object* v_struct_515_; lean_object* v___x_516_; 
v_typeName_513_ = lean_ctor_get(v___y_425_, 0);
v_idx_514_ = lean_ctor_get(v___y_425_, 1);
v_struct_515_ = lean_ctor_get(v___y_425_, 2);
lean_inc_ref(v_struct_515_);
lean_inc_ref(v_post_413_);
lean_inc_ref(v_pre_411_);
v___x_516_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_411_, v_post_413_, v_struct_515_, v___y_414_, v___y_415_, v___y_416_);
if (lean_obj_tag(v___x_516_) == 0)
{
lean_object* v_a_517_; size_t v___x_518_; size_t v___x_519_; uint8_t v___x_520_; 
v_a_517_ = lean_ctor_get(v___x_516_, 0);
lean_inc(v_a_517_);
lean_dec_ref_known(v___x_516_, 1);
v___x_518_ = lean_ptr_addr(v_struct_515_);
v___x_519_ = lean_ptr_addr(v_a_517_);
v___x_520_ = lean_usize_dec_eq(v___x_518_, v___x_519_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; lean_object* v___x_522_; 
lean_inc(v_idx_514_);
lean_inc(v_typeName_513_);
lean_dec_ref_known(v___y_425_, 3);
v___x_521_ = l_Lean_Expr_proj___override(v_typeName_513_, v_idx_514_, v_a_517_);
v___x_522_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_411_, v_post_413_, v___x_521_, v___y_414_, v___y_415_, v___y_416_);
return v___x_522_;
}
else
{
lean_object* v___x_523_; 
lean_dec(v_a_517_);
v___x_523_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_411_, v_post_413_, v___y_425_, v___y_414_, v___y_415_, v___y_416_);
return v___x_523_;
}
}
else
{
lean_dec_ref_known(v___y_425_, 3);
lean_dec_ref(v_post_413_);
lean_dec_ref(v_pre_411_);
return v___x_516_;
}
}
default: 
{
lean_object* v___x_524_; 
v___x_524_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_411_, v_post_413_, v___y_425_, v___y_414_, v___y_415_, v___y_416_);
return v___x_524_;
}
}
}
}
}
else
{
lean_object* v_a_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_543_; 
lean_dec_ref(v_post_413_);
lean_dec_ref(v_e_412_);
lean_dec_ref(v_pre_411_);
v_a_536_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_543_ == 0)
{
v___x_538_ = v___x_419_;
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_a_536_);
lean_dec(v___x_419_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_541_; 
if (v_isShared_539_ == 0)
{
v___x_541_ = v___x_538_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_a_536_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
}
}
else
{
lean_object* v_a_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_551_; 
lean_dec_ref(v_post_413_);
lean_dec_ref(v_e_412_);
lean_dec_ref(v_pre_411_);
v_a_544_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_551_ == 0)
{
v___x_546_ = v___x_418_;
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_a_544_);
lean_dec(v___x_418_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_549_; 
if (v_isShared_547_ == 0)
{
v___x_549_ = v___x_546_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_a_544_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___boxed(lean_object* v___x_552_, lean_object* v_pre_553_, lean_object* v_e_554_, lean_object* v_post_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1(v___x_552_, v_pre_553_, v_e_554_, v_post_555_, v___y_556_, v___y_557_, v___y_558_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec(v___y_556_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(lean_object* v_pre_561_, lean_object* v_post_562_, lean_object* v_e_563_, lean_object* v_a_564_, lean_object* v___y_565_, lean_object* v___y_566_){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
lean_inc(v_a_564_);
v___x_568_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_568_, 0, lean_box(0));
lean_closure_set(v___x_568_, 1, lean_box(0));
lean_closure_set(v___x_568_, 2, v_a_564_);
v___x_569_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(lean_box(0), v___x_568_, v___y_565_, v___y_566_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_601_; 
v_a_570_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_601_ == 0)
{
v___x_572_ = v___x_569_;
v_isShared_573_ = v_isSharedCheck_601_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v___x_569_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_601_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_574_; 
v___x_574_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(v_a_570_, v_e_563_);
lean_dec(v_a_570_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v___x_575_; lean_object* v___f_576_; lean_object* v___x_577_; 
lean_del_object(v___x_572_);
v___x_575_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___closed__0));
lean_inc_ref(v_e_563_);
v___f_576_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___boxed), 8, 4);
lean_closure_set(v___f_576_, 0, v___x_575_);
lean_closure_set(v___f_576_, 1, v_pre_561_);
lean_closure_set(v___f_576_, 2, v_e_563_);
lean_closure_set(v___f_576_, 3, v_post_562_);
v___x_577_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(v___f_576_, v_a_564_, v___y_565_, v___y_566_);
if (lean_obj_tag(v___x_577_) == 0)
{
lean_object* v_a_578_; lean_object* v___f_579_; lean_object* v___x_580_; 
v_a_578_ = lean_ctor_get(v___x_577_, 0);
lean_inc_n(v_a_578_, 2);
lean_dec_ref_known(v___x_577_, 1);
lean_inc(v_a_564_);
v___f_579_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_579_, 0, v_a_564_);
lean_closure_set(v___f_579_, 1, v_e_563_);
lean_closure_set(v___f_579_, 2, v_a_578_);
v___x_580_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(lean_box(0), v___f_579_, v___y_565_, v___y_566_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_587_ == 0)
{
lean_object* v_unused_588_; 
v_unused_588_ = lean_ctor_get(v___x_580_, 0);
lean_dec(v_unused_588_);
v___x_582_ = v___x_580_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_dec(v___x_580_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 0, v_a_578_);
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_a_578_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
else
{
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_596_; 
lean_dec(v_a_578_);
v_a_589_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_596_ == 0)
{
v___x_591_ = v___x_580_;
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v___x_580_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_594_; 
if (v_isShared_592_ == 0)
{
v___x_594_ = v___x_591_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_a_589_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
}
else
{
lean_dec_ref(v_e_563_);
return v___x_577_;
}
}
else
{
lean_object* v_val_597_; lean_object* v___x_599_; 
lean_dec_ref(v_e_563_);
lean_dec_ref(v_post_562_);
lean_dec_ref(v_pre_561_);
v_val_597_ = lean_ctor_get(v___x_574_, 0);
lean_inc(v_val_597_);
lean_dec_ref_known(v___x_574_, 1);
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 0, v_val_597_);
v___x_599_ = v___x_572_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_val_597_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
}
else
{
lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_609_; 
lean_dec_ref(v_e_563_);
lean_dec_ref(v_post_562_);
lean_dec_ref(v_pre_561_);
v_a_602_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_609_ == 0)
{
v___x_604_ = v___x_569_;
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_dec(v___x_569_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(lean_object* v_pre_610_, lean_object* v_post_611_, lean_object* v_e_612_, lean_object* v_a_613_, lean_object* v___y_614_, lean_object* v___y_615_){
_start:
{
lean_object* v___x_617_; 
lean_inc_ref(v_post_611_);
lean_inc(v___y_615_);
lean_inc_ref(v___y_614_);
lean_inc_ref(v_e_612_);
v___x_617_ = lean_apply_4(v_post_611_, v_e_612_, v___y_614_, v___y_615_, lean_box(0));
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_636_; 
v_a_618_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_636_ == 0)
{
v___x_620_ = v___x_617_;
v_isShared_621_ = v_isSharedCheck_636_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_617_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_636_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
switch(lean_obj_tag(v_a_618_))
{
case 0:
{
lean_object* v_e_622_; lean_object* v___x_624_; 
lean_dec_ref(v_e_612_);
lean_dec_ref(v_post_611_);
lean_dec_ref(v_pre_610_);
v_e_622_ = lean_ctor_get(v_a_618_, 0);
lean_inc_ref(v_e_622_);
lean_dec_ref_known(v_a_618_, 1);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 0, v_e_622_);
v___x_624_ = v___x_620_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_e_622_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
case 1:
{
lean_object* v_e_626_; lean_object* v___x_627_; 
lean_del_object(v___x_620_);
lean_dec_ref(v_e_612_);
v_e_626_ = lean_ctor_get(v_a_618_, 0);
lean_inc_ref(v_e_626_);
lean_dec_ref_known(v_a_618_, 1);
v___x_627_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_610_, v_post_611_, v_e_626_, v_a_613_, v___y_614_, v___y_615_);
return v___x_627_;
}
default: 
{
lean_object* v_e_x3f_628_; 
lean_dec_ref(v_post_611_);
lean_dec_ref(v_pre_610_);
v_e_x3f_628_ = lean_ctor_get(v_a_618_, 0);
lean_inc(v_e_x3f_628_);
lean_dec_ref_known(v_a_618_, 1);
if (lean_obj_tag(v_e_x3f_628_) == 0)
{
lean_object* v___x_630_; 
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 0, v_e_612_);
v___x_630_ = v___x_620_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_e_612_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
else
{
lean_object* v_val_632_; lean_object* v___x_634_; 
lean_dec_ref(v_e_612_);
v_val_632_ = lean_ctor_get(v_e_x3f_628_, 0);
lean_inc(v_val_632_);
lean_dec_ref_known(v_e_x3f_628_, 1);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 0, v_val_632_);
v___x_634_ = v___x_620_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_val_632_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
}
}
}
}
else
{
lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_644_; 
lean_dec_ref(v_e_612_);
lean_dec_ref(v_post_611_);
lean_dec_ref(v_pre_610_);
v_a_637_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_644_ == 0)
{
v___x_639_ = v___x_617_;
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v___x_617_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_642_; 
if (v_isShared_640_ == 0)
{
v___x_642_ = v___x_639_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_a_637_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_645_, lean_object* v_post_646_, lean_object* v_e_647_, lean_object* v_a_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_645_, v_post_646_, v_e_647_, v_a_648_, v___y_649_, v___y_650_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
lean_dec(v_a_648_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_653_, lean_object* v_post_654_, lean_object* v_sz_655_, lean_object* v_i_656_, lean_object* v_bs_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
size_t v_sz_boxed_662_; size_t v_i_boxed_663_; lean_object* v_res_664_; 
v_sz_boxed_662_ = lean_unbox_usize(v_sz_655_);
lean_dec(v_sz_655_);
v_i_boxed_663_ = lean_unbox_usize(v_i_656_);
lean_dec(v_i_656_);
v_res_664_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1(v_pre_653_, v_post_654_, v_sz_boxed_662_, v_i_boxed_663_, v_bs_657_, v___y_658_, v___y_659_, v___y_660_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_665_, lean_object* v_post_666_, lean_object* v_x_667_, lean_object* v_x_668_, lean_object* v_x_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4(v_pre_665_, v_post_666_, v_x_667_, v_x_668_, v_x_669_, v___y_670_, v___y_671_, v___y_672_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
lean_dec(v___y_670_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___boxed(lean_object* v_pre_675_, lean_object* v_post_676_, lean_object* v_e_677_, lean_object* v_a_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_675_, v_post_676_, v_e_677_, v_a_678_, v___y_679_, v___y_680_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec(v_a_678_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(lean_object* v_00_u03b1_683_, lean_object* v_x_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_688_ = lean_apply_1(v_x_684_, lean_box(0));
v___x_689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0___boxed(lean_object* v_00_u03b1_690_, lean_object* v_x_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(v_00_u03b1_690_, v_x_691_, v___y_692_, v___y_693_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
return v_res_695_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0(void){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_696_ = lean_box(0);
v___x_697_ = lean_unsigned_to_nat(16u);
v___x_698_ = lean_mk_array(v___x_697_, v___x_696_);
return v___x_698_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1(void){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_699_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0);
v___x_700_ = lean_unsigned_to_nat(0u);
v___x_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_701_, 0, v___x_700_);
lean_ctor_set(v___x_701_, 1, v___x_699_);
return v___x_701_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2(void){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_702_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1, &l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1);
v___x_703_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_703_, 0, lean_box(0));
lean_closure_set(v___x_703_, 1, lean_box(0));
lean_closure_set(v___x_703_, 2, v___x_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0(lean_object* v_input_704_, lean_object* v_pre_705_, lean_object* v_post_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v_a_712_; lean_object* v___x_713_; 
v___x_710_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2);
v___x_711_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(lean_box(0), v___x_710_, v___y_707_, v___y_708_);
v_a_712_ = lean_ctor_get(v___x_711_, 0);
lean_inc(v_a_712_);
lean_dec_ref(v___x_711_);
v___x_713_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_705_, v_post_706_, v_input_704_, v_a_712_, v___y_707_, v___y_708_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_object* v_a_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_723_; 
v_a_714_ = lean_ctor_get(v___x_713_, 0);
lean_inc(v_a_714_);
lean_dec_ref_known(v___x_713_, 1);
v___x_715_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_715_, 0, lean_box(0));
lean_closure_set(v___x_715_, 1, lean_box(0));
lean_closure_set(v___x_715_, 2, v_a_712_);
v___x_716_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(lean_box(0), v___x_715_, v___y_707_, v___y_708_);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_723_ == 0)
{
lean_object* v_unused_724_; 
v_unused_724_ = lean_ctor_get(v___x_716_, 0);
lean_dec(v_unused_724_);
v___x_718_ = v___x_716_;
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
else
{
lean_dec(v___x_716_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_721_; 
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 0, v_a_714_);
v___x_721_ = v___x_718_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_a_714_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
else
{
lean_dec(v_a_712_);
return v___x_713_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___boxed(lean_object* v_input_725_, lean_object* v_pre_726_, lean_object* v_post_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0(v_input_725_, v_pre_726_, v_post_727_, v___y_728_, v___y_729_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam(lean_object* v_type_734_, lean_object* v_a_735_, lean_object* v_a_736_){
_start:
{
lean_object* v___f_738_; lean_object* v___f_739_; lean_object* v___x_740_; 
v___f_738_ = ((lean_object*)(l_Lean_Meta_elimOptParam___closed__0));
v___f_739_ = ((lean_object*)(l_Lean_Meta_elimOptParam___closed__1));
v___x_740_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0(v_type_734_, v___f_738_, v___f_739_, v_a_735_, v_a_736_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam___boxed(lean_object* v_type_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Lean_Meta_elimOptParam(v_type_741_, v_a_742_, v_a_743_);
lean_dec(v_a_743_);
lean_dec_ref(v_a_742_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_746_, lean_object* v_m_747_, lean_object* v_a_748_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(v_m_747_, v_a_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_750_, lean_object* v_m_751_, lean_object* v_a_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(v_00_u03b2_750_, v_m_751_, v_a_752_);
lean_dec_ref(v_a_752_);
lean_dec_ref(v_m_751_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_754_, lean_object* v_ref_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
lean_object* v___x_759_; 
v___x_759_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_755_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_760_, lean_object* v_ref_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_760_, v_ref_761_, v___y_762_, v___y_763_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8(lean_object* v_00_u03b1_766_, lean_object* v___y_767_, lean_object* v___y_768_){
_start:
{
lean_object* v___x_770_; 
v___x_770_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg();
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___boxed(lean_object* v_00_u03b1_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_771_, v___y_772_, v___y_773_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_776_, lean_object* v_x_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_){
_start:
{
lean_object* v___x_782_; 
v___x_782_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(v_x_777_, v___y_778_, v___y_779_, v___y_780_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_783_, lean_object* v_x_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5(v_00_u03b1_783_, v_x_784_, v___y_785_, v___y_786_, v___y_787_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec(v___y_785_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_790_, lean_object* v_m_791_, lean_object* v_a_792_, lean_object* v_b_793_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6___redArg(v_m_791_, v_a_792_, v_b_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_795_, lean_object* v_a_796_, lean_object* v_x_797_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(v_a_796_, v_x_797_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_799_, lean_object* v_a_800_, lean_object* v_x_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_799_, v_a_800_, v_x_801_);
lean_dec(v_x_801_);
lean_dec_ref(v_a_800_);
return v_res_802_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_803_, lean_object* v_a_804_, lean_object* v_x_805_){
_start:
{
uint8_t v___x_806_; 
v___x_806_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___redArg(v_a_804_, v_x_805_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___boxed(lean_object* v_00_u03b2_807_, lean_object* v_a_808_, lean_object* v_x_809_){
_start:
{
uint8_t v_res_810_; lean_object* v_r_811_; 
v_res_810_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_807_, v_a_808_, v_x_809_);
lean_dec(v_x_809_);
lean_dec_ref(v_a_808_);
v_r_811_ = lean_box(v_res_810_);
return v_r_811_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_812_, lean_object* v_data_813_){
_start:
{
lean_object* v___x_814_; 
v___x_814_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11___redArg(v_data_813_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__12(lean_object* v_00_u03b2_815_, lean_object* v_a_816_, lean_object* v_b_817_, lean_object* v_x_818_){
_start:
{
lean_object* v___x_819_; 
v___x_819_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__12___redArg(v_a_816_, v_b_817_, v_x_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12(lean_object* v_00_u03b2_820_, lean_object* v_i_821_, lean_object* v_source_822_, lean_object* v_target_823_){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v_i_821_, v_source_822_, v_target_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_825_, lean_object* v_x_826_, lean_object* v_x_827_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_x_826_, v_x_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0(uint8_t v_skipIfPropOrEq_829_, lean_object* v_as_830_, size_t v_sz_831_, size_t v_i_832_, lean_object* v_b_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v_a_840_; uint8_t v___x_844_; 
v___x_844_ = lean_usize_dec_lt(v_i_832_, v_sz_831_);
if (v___x_844_ == 0)
{
lean_object* v___x_845_; 
v___x_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_845_, 0, v_b_833_);
return v___x_845_;
}
else
{
lean_object* v_snd_846_; lean_object* v_fst_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_925_; 
v_snd_846_ = lean_ctor_get(v_b_833_, 1);
v_fst_847_ = lean_ctor_get(v_b_833_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v_b_833_);
if (v_isSharedCheck_925_ == 0)
{
v___x_849_ = v_b_833_;
v_isShared_850_ = v_isSharedCheck_925_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_snd_846_);
lean_inc(v_fst_847_);
lean_dec(v_b_833_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_925_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v_array_851_; lean_object* v_start_852_; lean_object* v_stop_853_; uint8_t v___x_854_; 
v_array_851_ = lean_ctor_get(v_snd_846_, 0);
v_start_852_ = lean_ctor_get(v_snd_846_, 1);
v_stop_853_ = lean_ctor_get(v_snd_846_, 2);
v___x_854_ = lean_nat_dec_lt(v_start_852_, v_stop_853_);
if (v___x_854_ == 0)
{
lean_object* v___x_856_; 
if (v_isShared_850_ == 0)
{
v___x_856_ = v___x_849_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_fst_847_);
lean_ctor_set(v_reuseFailAlloc_858_, 1, v_snd_846_);
v___x_856_ = v_reuseFailAlloc_858_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
lean_object* v___x_857_; 
v___x_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_857_, 0, v___x_856_);
return v___x_857_;
}
}
else
{
lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_921_; 
lean_inc(v_stop_853_);
lean_inc(v_start_852_);
lean_inc_ref(v_array_851_);
v_isSharedCheck_921_ = !lean_is_exclusive(v_snd_846_);
if (v_isSharedCheck_921_ == 0)
{
lean_object* v_unused_922_; lean_object* v_unused_923_; lean_object* v_unused_924_; 
v_unused_922_ = lean_ctor_get(v_snd_846_, 2);
lean_dec(v_unused_922_);
v_unused_923_ = lean_ctor_get(v_snd_846_, 1);
lean_dec(v_unused_923_);
v_unused_924_ = lean_ctor_get(v_snd_846_, 0);
lean_dec(v_unused_924_);
v___x_860_ = v_snd_846_;
v_isShared_861_ = v_isSharedCheck_921_;
goto v_resetjp_859_;
}
else
{
lean_dec(v_snd_846_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_921_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v_a_862_; lean_object* v___x_863_; 
v_a_862_ = lean_array_uget_borrowed(v_as_830_, v_i_832_);
lean_inc(v___y_837_);
lean_inc_ref(v___y_836_);
lean_inc(v___y_835_);
lean_inc_ref(v___y_834_);
lean_inc(v_a_862_);
v___x_863_ = lean_infer_type(v_a_862_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v_a_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_869_; 
v_a_864_ = lean_ctor_get(v___x_863_, 0);
lean_inc(v_a_864_);
lean_dec_ref_known(v___x_863_, 1);
v___x_865_ = lean_array_fget(v_array_851_, v_start_852_);
v___x_866_ = lean_unsigned_to_nat(1u);
v___x_867_ = lean_nat_add(v_start_852_, v___x_866_);
lean_dec(v_start_852_);
if (v_isShared_861_ == 0)
{
lean_ctor_set(v___x_860_, 1, v___x_867_);
v___x_869_ = v___x_860_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_array_851_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v___x_867_);
lean_ctor_set(v_reuseFailAlloc_912_, 2, v_stop_853_);
v___x_869_ = v_reuseFailAlloc_912_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
if (v_skipIfPropOrEq_829_ == 0)
{
lean_object* v___x_870_; 
lean_dec(v_a_864_);
lean_inc(v_a_862_);
v___x_870_ = l_Lean_Meta_mkEqHEq(v_a_862_, v___x_865_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_871_; lean_object* v___x_872_; lean_object* v___x_874_; 
v_a_871_ = lean_ctor_get(v___x_870_, 0);
lean_inc(v_a_871_);
lean_dec_ref_known(v___x_870_, 1);
v___x_872_ = lean_array_push(v_fst_847_, v_a_871_);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 1, v___x_869_);
lean_ctor_set(v___x_849_, 0, v___x_872_);
v___x_874_ = v___x_849_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_872_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v___x_869_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
v_a_840_ = v___x_874_;
goto v___jp_839_;
}
}
else
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_883_; 
lean_dec_ref(v___x_869_);
lean_del_object(v___x_849_);
lean_dec(v_fst_847_);
v_a_876_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_883_ == 0)
{
v___x_878_ = v___x_870_;
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_870_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_876_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
else
{
lean_object* v___x_884_; 
v___x_884_ = l_Lean_Meta_isProp(v_a_864_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
if (lean_obj_tag(v___x_884_) == 0)
{
lean_object* v_a_885_; uint8_t v___x_890_; 
v_a_885_ = lean_ctor_get(v___x_884_, 0);
lean_inc(v_a_885_);
lean_dec_ref_known(v___x_884_, 1);
v___x_890_ = lean_unbox(v_a_885_);
lean_dec(v_a_885_);
if (v___x_890_ == 0)
{
uint8_t v___x_891_; 
v___x_891_ = lean_expr_eqv(v_a_862_, v___x_865_);
if (v___x_891_ == 0)
{
lean_object* v___x_892_; 
lean_del_object(v___x_849_);
lean_inc(v_a_862_);
v___x_892_ = l_Lean_Meta_mkEqHEq(v_a_862_, v___x_865_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
if (lean_obj_tag(v___x_892_) == 0)
{
lean_object* v_a_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v_a_893_ = lean_ctor_get(v___x_892_, 0);
lean_inc(v_a_893_);
lean_dec_ref_known(v___x_892_, 1);
v___x_894_ = lean_array_push(v_fst_847_, v_a_893_);
v___x_895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_895_, 0, v___x_894_);
lean_ctor_set(v___x_895_, 1, v___x_869_);
v_a_840_ = v___x_895_;
goto v___jp_839_;
}
else
{
lean_object* v_a_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_903_; 
lean_dec_ref(v___x_869_);
lean_dec(v_fst_847_);
v_a_896_ = lean_ctor_get(v___x_892_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_903_ == 0)
{
v___x_898_ = v___x_892_;
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_a_896_);
lean_dec(v___x_892_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_901_; 
if (v_isShared_899_ == 0)
{
v___x_901_ = v___x_898_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_a_896_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
else
{
lean_dec(v___x_865_);
goto v___jp_886_;
}
}
else
{
lean_dec(v___x_865_);
goto v___jp_886_;
}
v___jp_886_:
{
lean_object* v___x_888_; 
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 1, v___x_869_);
v___x_888_ = v___x_849_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_fst_847_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v___x_869_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
v_a_840_ = v___x_888_;
goto v___jp_839_;
}
}
}
else
{
lean_object* v_a_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_911_; 
lean_dec_ref(v___x_869_);
lean_dec(v___x_865_);
lean_del_object(v___x_849_);
lean_dec(v_fst_847_);
v_a_904_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_911_ == 0)
{
v___x_906_ = v___x_884_;
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_a_904_);
lean_dec(v___x_884_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_909_; 
if (v_isShared_907_ == 0)
{
v___x_909_ = v___x_906_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_a_904_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
}
}
else
{
lean_object* v_a_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_920_; 
lean_del_object(v___x_860_);
lean_dec(v_stop_853_);
lean_dec(v_start_852_);
lean_dec_ref(v_array_851_);
lean_del_object(v___x_849_);
lean_dec(v_fst_847_);
v_a_913_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_920_ == 0)
{
v___x_915_ = v___x_863_;
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_a_913_);
lean_dec(v___x_863_);
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
}
}
}
v___jp_839_:
{
size_t v___x_841_; size_t v___x_842_; 
v___x_841_ = ((size_t)1ULL);
v___x_842_ = lean_usize_add(v_i_832_, v___x_841_);
v_i_832_ = v___x_842_;
v_b_833_ = v_a_840_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0___boxed(lean_object* v_skipIfPropOrEq_926_, lean_object* v_as_927_, lean_object* v_sz_928_, lean_object* v_i_929_, lean_object* v_b_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
uint8_t v_skipIfPropOrEq_boxed_936_; size_t v_sz_boxed_937_; size_t v_i_boxed_938_; lean_object* v_res_939_; 
v_skipIfPropOrEq_boxed_936_ = lean_unbox(v_skipIfPropOrEq_926_);
v_sz_boxed_937_ = lean_unbox_usize(v_sz_928_);
lean_dec(v_sz_928_);
v_i_boxed_938_ = lean_unbox_usize(v_i_929_);
lean_dec(v_i_929_);
v_res_939_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0(v_skipIfPropOrEq_boxed_936_, v_as_927_, v_sz_boxed_937_, v_i_boxed_938_, v_b_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec_ref(v_as_927_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(lean_object* v_args1_942_, lean_object* v_args2_943_, uint8_t v_skipIfPropOrEq_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_){
_start:
{
lean_object* v___x_950_; lean_object* v_eqs_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; size_t v_sz_955_; size_t v___x_956_; lean_object* v___x_957_; 
v___x_950_ = lean_unsigned_to_nat(0u);
v_eqs_951_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_952_ = lean_array_get_size(v_args2_943_);
v___x_953_ = l_Array_toSubarray___redArg(v_args2_943_, v___x_950_, v___x_952_);
v___x_954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_954_, 0, v_eqs_951_);
lean_ctor_set(v___x_954_, 1, v___x_953_);
v_sz_955_ = lean_array_size(v_args1_942_);
v___x_956_ = ((size_t)0ULL);
v___x_957_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0(v_skipIfPropOrEq_944_, v_args1_942_, v_sz_955_, v___x_956_, v___x_954_, v_a_945_, v_a_946_, v_a_947_, v_a_948_);
if (lean_obj_tag(v___x_957_) == 0)
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_966_; 
v_a_958_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_966_ == 0)
{
v___x_960_ = v___x_957_;
v_isShared_961_ = v_isSharedCheck_966_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_957_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_966_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v_fst_962_; lean_object* v___x_964_; 
v_fst_962_ = lean_ctor_get(v_a_958_, 0);
lean_inc(v_fst_962_);
lean_dec(v_a_958_);
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 0, v_fst_962_);
v___x_964_ = v___x_960_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_fst_962_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
else
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_974_; 
v_a_967_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_974_ == 0)
{
v___x_969_ = v___x_957_;
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_957_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_972_; 
if (v_isShared_970_ == 0)
{
v___x_972_ = v___x_969_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_a_967_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___boxed(lean_object* v_args1_975_, lean_object* v_args2_976_, lean_object* v_skipIfPropOrEq_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_){
_start:
{
uint8_t v_skipIfPropOrEq_boxed_983_; lean_object* v_res_984_; 
v_skipIfPropOrEq_boxed_983_ = lean_unbox(v_skipIfPropOrEq_977_);
v_res_984_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v_args1_975_, v_args2_976_, v_skipIfPropOrEq_boxed_983_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
lean_dec(v_a_981_);
lean_dec_ref(v_a_980_);
lean_dec(v_a_979_);
lean_dec_ref(v_a_978_);
lean_dec_ref(v_args1_975_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0(lean_object* v_k_985_, lean_object* v_b_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
lean_object* v___x_992_; 
lean_inc(v___y_990_);
lean_inc_ref(v___y_989_);
lean_inc(v___y_988_);
lean_inc_ref(v___y_987_);
v___x_992_ = lean_apply_6(v_k_985_, v_b_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, lean_box(0));
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0___boxed(lean_object* v_k_993_, lean_object* v_b_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0(v_k_993_, v_b_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(lean_object* v_name_1001_, uint8_t v_bi_1002_, lean_object* v_type_1003_, lean_object* v_k_1004_, uint8_t v_kind_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v___f_1011_; lean_object* v___x_1012_; 
v___f_1011_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1011_, 0, v_k_1004_);
v___x_1012_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1001_, v_bi_1002_, v_type_1003_, v___f_1011_, v_kind_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1020_; 
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1015_ = v___x_1012_;
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_1012_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1018_; 
if (v_isShared_1016_ == 0)
{
v___x_1018_ = v___x_1015_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_a_1013_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
else
{
lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1028_; 
v_a_1021_ = lean_ctor_get(v___x_1012_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1023_ = v___x_1012_;
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v___x_1012_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1026_; 
if (v_isShared_1024_ == 0)
{
v___x_1026_ = v___x_1023_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_a_1021_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___boxed(lean_object* v_name_1029_, lean_object* v_bi_1030_, lean_object* v_type_1031_, lean_object* v_k_1032_, lean_object* v_kind_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_){
_start:
{
uint8_t v_bi_boxed_1039_; uint8_t v_kind_boxed_1040_; lean_object* v_res_1041_; 
v_bi_boxed_1039_ = lean_unbox(v_bi_1030_);
v_kind_boxed_1040_ = lean_unbox(v_kind_1033_);
v_res_1041_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_name_1029_, v_bi_boxed_1039_, v_type_1031_, v_k_1032_, v_kind_boxed_1040_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_);
lean_dec(v___y_1037_);
lean_dec_ref(v___y_1036_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0(lean_object* v_00_u03b1_1042_, lean_object* v_name_1043_, uint8_t v_bi_1044_, lean_object* v_type_1045_, lean_object* v_k_1046_, uint8_t v_kind_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_name_1043_, v_bi_1044_, v_type_1045_, v_k_1046_, v_kind_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___boxed(lean_object* v_00_u03b1_1054_, lean_object* v_name_1055_, lean_object* v_bi_1056_, lean_object* v_type_1057_, lean_object* v_k_1058_, lean_object* v_kind_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
uint8_t v_bi_boxed_1065_; uint8_t v_kind_boxed_1066_; lean_object* v_res_1067_; 
v_bi_boxed_1065_ = lean_unbox(v_bi_1056_);
v_kind_boxed_1066_ = lean_unbox(v_kind_1059_);
v_res_1067_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0(v_00_u03b1_1054_, v_name_1055_, v_bi_boxed_1065_, v_type_1057_, v_k_1058_, v_kind_boxed_1066_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(lean_object* v_msgData_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v___x_1074_; lean_object* v_env_1075_; lean_object* v___x_1076_; lean_object* v_toCold_1077_; lean_object* v_mctx_1078_; lean_object* v_lctx_1079_; lean_object* v_options_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1074_ = lean_st_ref_get(v___y_1072_);
v_env_1075_ = lean_ctor_get(v___x_1074_, 0);
lean_inc_ref(v_env_1075_);
lean_dec(v___x_1074_);
v___x_1076_ = lean_st_ref_get(v___y_1070_);
v_toCold_1077_ = lean_ctor_get(v___y_1071_, 0);
v_mctx_1078_ = lean_ctor_get(v___x_1076_, 0);
lean_inc_ref(v_mctx_1078_);
lean_dec(v___x_1076_);
v_lctx_1079_ = lean_ctor_get(v___y_1069_, 2);
v_options_1080_ = lean_ctor_get(v_toCold_1077_, 2);
lean_inc_ref(v_options_1080_);
lean_inc_ref(v_lctx_1079_);
v___x_1081_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1081_, 0, v_env_1075_);
lean_ctor_set(v___x_1081_, 1, v_mctx_1078_);
lean_ctor_set(v___x_1081_, 2, v_lctx_1079_);
lean_ctor_set(v___x_1081_, 3, v_options_1080_);
v___x_1082_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
lean_ctor_set(v___x_1082_, 1, v_msgData_1068_);
v___x_1083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1082_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1___boxed(lean_object* v_msgData_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msgData_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(lean_object* v_msg_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_){
_start:
{
lean_object* v_ref_1097_; lean_object* v___x_1098_; lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1107_; 
v_ref_1097_ = lean_ctor_get(v___y_1094_, 2);
v___x_1098_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msg_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_);
v_a_1099_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1101_ = v___x_1098_;
v_isShared_1102_ = v_isSharedCheck_1107_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1098_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1107_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1103_; lean_object* v___x_1105_; 
lean_inc(v_ref_1097_);
v___x_1103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1103_, 0, v_ref_1097_);
lean_ctor_set(v___x_1103_, 1, v_a_1099_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set_tag(v___x_1101_, 1);
lean_ctor_set(v___x_1101_, 0, v___x_1103_);
v___x_1105_ = v___x_1101_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v___x_1103_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg___boxed(lean_object* v_msg_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v_msg_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
lean_dec(v___y_1112_);
lean_dec_ref(v___y_1111_);
lean_dec(v___y_1110_);
lean_dec_ref(v___y_1109_);
return v_res_1114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0___boxed(lean_object* v_i_1115_, lean_object* v_body_1116_, lean_object* v_args2_1117_, lean_object* v_args2New_1118_, lean_object* v_ctorVal_1119_, lean_object* v_useEq_1120_, lean_object* v_args1_1121_, lean_object* v_resultType_1122_, lean_object* v_k_1123_, lean_object* v_arg2_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
uint8_t v_useEq_boxed_1130_; lean_object* v_res_1131_; 
v_useEq_boxed_1130_ = lean_unbox(v_useEq_1120_);
v_res_1131_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0(v_i_1115_, v_body_1116_, v_args2_1117_, v_args2New_1118_, v_ctorVal_1119_, v_useEq_boxed_1130_, v_args1_1121_, v_resultType_1122_, v_k_1123_, v_arg2_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
lean_dec_ref(v_body_1116_);
lean_dec(v_i_1115_);
return v_res_1131_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1(void){
_start:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1133_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__0));
v___x_1134_ = l_Lean_stringToMessageData(v___x_1133_);
return v___x_1134_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3(void){
_start:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1136_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__2));
v___x_1137_ = l_Lean_stringToMessageData(v___x_1136_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(lean_object* v_ctorVal_1138_, uint8_t v_useEq_1139_, lean_object* v_args1_1140_, lean_object* v_resultType_1141_, lean_object* v_k_1142_, lean_object* v_i_1143_, lean_object* v_type_1144_, lean_object* v_args2_1145_, lean_object* v_args2New_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_){
_start:
{
lean_object* v___x_1152_; uint8_t v___x_1153_; 
v___x_1152_ = lean_array_get_size(v_args1_1140_);
v___x_1153_ = lean_nat_dec_lt(v_i_1143_, v___x_1152_);
if (v___x_1153_ == 0)
{
lean_object* v___x_1154_; 
lean_dec_ref(v_type_1144_);
lean_dec(v_i_1143_);
lean_dec_ref(v_resultType_1141_);
lean_dec_ref(v_args1_1140_);
lean_dec_ref(v_ctorVal_1138_);
lean_inc(v_a_1150_);
lean_inc_ref(v_a_1149_);
lean_inc(v_a_1148_);
lean_inc_ref(v_a_1147_);
v___x_1154_ = lean_apply_7(v_k_1142_, v_args2_1145_, v_args2New_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, lean_box(0));
return v___x_1154_;
}
else
{
lean_object* v___x_1155_; 
lean_inc(v_a_1150_);
lean_inc_ref(v_a_1149_);
lean_inc(v_a_1148_);
lean_inc_ref(v_a_1147_);
v___x_1155_ = lean_whnf(v_type_1144_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_);
if (lean_obj_tag(v___x_1155_) == 0)
{
lean_object* v_a_1156_; 
v_a_1156_ = lean_ctor_get(v___x_1155_, 0);
lean_inc(v_a_1156_);
lean_dec_ref_known(v___x_1155_, 1);
if (lean_obj_tag(v_a_1156_) == 7)
{
lean_object* v_binderName_1157_; lean_object* v_binderType_1158_; lean_object* v_body_1159_; lean_object* v_lctx_1160_; lean_object* v___x_1161_; uint8_t v___x_1162_; 
v_binderName_1157_ = lean_ctor_get(v_a_1156_, 0);
lean_inc(v_binderName_1157_);
v_binderType_1158_ = lean_ctor_get(v_a_1156_, 1);
lean_inc_ref(v_binderType_1158_);
v_body_1159_ = lean_ctor_get(v_a_1156_, 2);
lean_inc_ref(v_body_1159_);
lean_dec_ref_known(v_a_1156_, 3);
v_lctx_1160_ = lean_ctor_get(v_a_1147_, 2);
v___x_1161_ = lean_array_fget_borrowed(v_args1_1140_, v_i_1143_);
lean_inc(v___x_1161_);
lean_inc_ref(v_lctx_1160_);
v___x_1162_ = l_Lean_Meta_occursOrInType(v_lctx_1160_, v___x_1161_, v_resultType_1141_);
if (v___x_1162_ == 0)
{
lean_object* v___x_1163_; lean_object* v___f_1164_; uint8_t v___y_1166_; 
v___x_1163_ = lean_box(v_useEq_1139_);
v___f_1164_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0___boxed), 15, 9);
lean_closure_set(v___f_1164_, 0, v_i_1143_);
lean_closure_set(v___f_1164_, 1, v_body_1159_);
lean_closure_set(v___f_1164_, 2, v_args2_1145_);
lean_closure_set(v___f_1164_, 3, v_args2New_1146_);
lean_closure_set(v___f_1164_, 4, v_ctorVal_1138_);
lean_closure_set(v___f_1164_, 5, v___x_1163_);
lean_closure_set(v___f_1164_, 6, v_args1_1140_);
lean_closure_set(v___f_1164_, 7, v_resultType_1141_);
lean_closure_set(v___f_1164_, 8, v_k_1142_);
if (v_useEq_1139_ == 0)
{
uint8_t v___x_1169_; 
v___x_1169_ = 1;
v___y_1166_ = v___x_1169_;
goto v___jp_1165_;
}
else
{
uint8_t v___x_1170_; 
v___x_1170_ = 0;
v___y_1166_ = v___x_1170_;
goto v___jp_1165_;
}
v___jp_1165_:
{
uint8_t v___x_1167_; lean_object* v___x_1168_; 
v___x_1167_ = 0;
v___x_1168_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_binderName_1157_, v___y_1166_, v_binderType_1158_, v___f_1164_, v___x_1167_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_);
return v___x_1168_;
}
}
else
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
lean_dec_ref(v_binderType_1158_);
lean_dec(v_binderName_1157_);
v___x_1171_ = lean_unsigned_to_nat(1u);
v___x_1172_ = lean_nat_add(v_i_1143_, v___x_1171_);
lean_dec(v_i_1143_);
v___x_1173_ = lean_expr_instantiate1(v_body_1159_, v___x_1161_);
lean_dec_ref(v_body_1159_);
lean_inc(v___x_1161_);
v___x_1174_ = lean_array_push(v_args2_1145_, v___x_1161_);
v_i_1143_ = v___x_1172_;
v_type_1144_ = v___x_1173_;
v_args2_1145_ = v___x_1174_;
goto _start;
}
}
else
{
lean_object* v_toConstantVal_1176_; lean_object* v_name_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
lean_dec(v_a_1156_);
lean_dec_ref(v_args2New_1146_);
lean_dec_ref(v_args2_1145_);
lean_dec(v_i_1143_);
lean_dec_ref(v_k_1142_);
lean_dec_ref(v_resultType_1141_);
lean_dec_ref(v_args1_1140_);
v_toConstantVal_1176_ = lean_ctor_get(v_ctorVal_1138_, 0);
lean_inc_ref(v_toConstantVal_1176_);
lean_dec_ref(v_ctorVal_1138_);
v_name_1177_ = lean_ctor_get(v_toConstantVal_1176_, 0);
lean_inc(v_name_1177_);
lean_dec_ref(v_toConstantVal_1176_);
v___x_1178_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1);
v___x_1179_ = l_Lean_MessageData_ofName(v_name_1177_);
v___x_1180_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1178_);
lean_ctor_set(v___x_1180_, 1, v___x_1179_);
v___x_1181_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_1182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1180_);
lean_ctor_set(v___x_1182_, 1, v___x_1181_);
v___x_1183_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_1182_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_);
return v___x_1183_;
}
}
else
{
lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1191_; 
lean_dec_ref(v_args2New_1146_);
lean_dec_ref(v_args2_1145_);
lean_dec(v_i_1143_);
lean_dec_ref(v_k_1142_);
lean_dec_ref(v_resultType_1141_);
lean_dec_ref(v_args1_1140_);
lean_dec_ref(v_ctorVal_1138_);
v_a_1184_ = lean_ctor_get(v___x_1155_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1155_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1186_ = v___x_1155_;
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_a_1184_);
lean_dec(v___x_1155_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0(lean_object* v_i_1192_, lean_object* v_body_1193_, lean_object* v_args2_1194_, lean_object* v_args2New_1195_, lean_object* v_ctorVal_1196_, uint8_t v_useEq_1197_, lean_object* v_args1_1198_, lean_object* v_resultType_1199_, lean_object* v_k_1200_, lean_object* v_arg2_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1207_ = lean_unsigned_to_nat(1u);
v___x_1208_ = lean_nat_add(v_i_1192_, v___x_1207_);
v___x_1209_ = lean_expr_instantiate1(v_body_1193_, v_arg2_1201_);
lean_inc_ref(v_arg2_1201_);
v___x_1210_ = lean_array_push(v_args2_1194_, v_arg2_1201_);
v___x_1211_ = lean_array_push(v_args2New_1195_, v_arg2_1201_);
v___x_1212_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(v_ctorVal_1196_, v_useEq_1197_, v_args1_1198_, v_resultType_1199_, v_k_1200_, v___x_1208_, v___x_1209_, v___x_1210_, v___x_1211_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___boxed(lean_object* v_ctorVal_1213_, lean_object* v_useEq_1214_, lean_object* v_args1_1215_, lean_object* v_resultType_1216_, lean_object* v_k_1217_, lean_object* v_i_1218_, lean_object* v_type_1219_, lean_object* v_args2_1220_, lean_object* v_args2New_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_){
_start:
{
uint8_t v_useEq_boxed_1227_; lean_object* v_res_1228_; 
v_useEq_boxed_1227_ = lean_unbox(v_useEq_1214_);
v_res_1228_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(v_ctorVal_1213_, v_useEq_boxed_1227_, v_args1_1215_, v_resultType_1216_, v_k_1217_, v_i_1218_, v_type_1219_, v_args2_1220_, v_args2New_1221_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_);
lean_dec(v_a_1225_);
lean_dec_ref(v_a_1224_);
lean_dec(v_a_1223_);
lean_dec_ref(v_a_1222_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1(lean_object* v_00_u03b1_1229_, lean_object* v_msg_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
lean_object* v___x_1236_; 
v___x_1236_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v_msg_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___boxed(lean_object* v_00_u03b1_1237_, lean_object* v_msg_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1(v_00_u03b1_1237_, v_msg_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_match__1_splitter___redArg(lean_object* v_____x_1245_, lean_object* v_h__1_1246_, lean_object* v_h__2_1247_){
_start:
{
if (lean_obj_tag(v_____x_1245_) == 7)
{
lean_object* v_binderName_1248_; lean_object* v_binderType_1249_; lean_object* v_body_1250_; uint8_t v_binderInfo_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
lean_dec(v_h__2_1247_);
v_binderName_1248_ = lean_ctor_get(v_____x_1245_, 0);
lean_inc(v_binderName_1248_);
v_binderType_1249_ = lean_ctor_get(v_____x_1245_, 1);
lean_inc_ref(v_binderType_1249_);
v_body_1250_ = lean_ctor_get(v_____x_1245_, 2);
lean_inc_ref(v_body_1250_);
v_binderInfo_1251_ = lean_ctor_get_uint8(v_____x_1245_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_____x_1245_, 3);
v___x_1252_ = lean_box(v_binderInfo_1251_);
v___x_1253_ = lean_apply_4(v_h__1_1246_, v_binderName_1248_, v_binderType_1249_, v_body_1250_, v___x_1252_);
return v___x_1253_;
}
else
{
lean_object* v___x_1254_; 
lean_dec(v_h__1_1246_);
v___x_1254_ = lean_apply_2(v_h__2_1247_, v_____x_1245_, lean_box(0));
return v___x_1254_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_match__1_splitter(lean_object* v_motive_1255_, lean_object* v_____x_1256_, lean_object* v_h__1_1257_, lean_object* v_h__2_1258_){
_start:
{
if (lean_obj_tag(v_____x_1256_) == 7)
{
lean_object* v_binderName_1259_; lean_object* v_binderType_1260_; lean_object* v_body_1261_; uint8_t v_binderInfo_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
lean_dec(v_h__2_1258_);
v_binderName_1259_ = lean_ctor_get(v_____x_1256_, 0);
lean_inc(v_binderName_1259_);
v_binderType_1260_ = lean_ctor_get(v_____x_1256_, 1);
lean_inc_ref(v_binderType_1260_);
v_body_1261_ = lean_ctor_get(v_____x_1256_, 2);
lean_inc_ref(v_body_1261_);
v_binderInfo_1262_ = lean_ctor_get_uint8(v_____x_1256_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_____x_1256_, 3);
v___x_1263_ = lean_box(v_binderInfo_1262_);
v___x_1264_ = lean_apply_4(v_h__1_1257_, v_binderName_1259_, v_binderType_1260_, v_body_1261_, v___x_1263_);
return v___x_1264_;
}
else
{
lean_object* v___x_1265_; 
lean_dec(v_h__1_1257_);
v___x_1265_ = lean_apply_2(v_h__2_1258_, v_____x_1256_, lean_box(0));
return v___x_1265_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0(lean_object* v_k_1266_, lean_object* v_b_1267_, lean_object* v_c_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v___x_1274_; 
lean_inc(v___y_1272_);
lean_inc_ref(v___y_1271_);
lean_inc(v___y_1270_);
lean_inc_ref(v___y_1269_);
v___x_1274_ = lean_apply_7(v_k_1266_, v_b_1267_, v_c_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, lean_box(0));
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed(lean_object* v_k_1275_, lean_object* v_b_1276_, lean_object* v_c_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0(v_k_1275_, v_b_1276_, v_c_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(lean_object* v_type_1284_, lean_object* v_k_1285_, uint8_t v_cleanupAnnotations_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_){
_start:
{
lean_object* v___f_1292_; uint8_t v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___f_1292_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1292_, 0, v_k_1285_);
v___x_1293_ = 0;
v___x_1294_ = lean_box(0);
v___x_1295_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_1293_, v___x_1294_, v_type_1284_, v___f_1292_, v_cleanupAnnotations_1286_, v___x_1293_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_);
if (lean_obj_tag(v___x_1295_) == 0)
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
v_a_1296_ = lean_ctor_get(v___x_1295_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1295_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1295_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1296_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
else
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
v_a_1304_ = lean_ctor_get(v___x_1295_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1306_ = v___x_1295_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1295_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1304_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___boxed(lean_object* v_type_1312_, lean_object* v_k_1313_, lean_object* v_cleanupAnnotations_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1320_; lean_object* v_res_1321_; 
v_cleanupAnnotations_boxed_1320_ = lean_unbox(v_cleanupAnnotations_1314_);
v_res_1321_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_type_1312_, v_k_1313_, v_cleanupAnnotations_boxed_1320_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_);
lean_dec(v___y_1318_);
lean_dec_ref(v___y_1317_);
lean_dec(v___y_1316_);
lean_dec_ref(v___y_1315_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2(lean_object* v_00_u03b1_1322_, lean_object* v_type_1323_, lean_object* v_k_1324_, uint8_t v_cleanupAnnotations_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
lean_object* v___x_1331_; 
v___x_1331_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_type_1323_, v_k_1324_, v_cleanupAnnotations_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___boxed(lean_object* v_00_u03b1_1332_, lean_object* v_type_1333_, lean_object* v_k_1334_, lean_object* v_cleanupAnnotations_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1341_; lean_object* v_res_1342_; 
v_cleanupAnnotations_boxed_1341_ = lean_unbox(v_cleanupAnnotations_1335_);
v_res_1342_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2(v_00_u03b1_1332_, v_type_1333_, v_k_1334_, v_cleanupAnnotations_boxed_1341_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(lean_object* v_type_1343_, lean_object* v_maxFVars_x3f_1344_, lean_object* v_k_1345_, uint8_t v_cleanupAnnotations_1346_, uint8_t v_whnfType_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
lean_object* v___f_1353_; lean_object* v___x_1354_; 
v___f_1353_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1353_, 0, v_k_1345_);
v___x_1354_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_1343_, v_maxFVars_x3f_1344_, v___f_1353_, v_cleanupAnnotations_1346_, v_whnfType_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1362_; 
v_a_1355_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1357_ = v___x_1354_;
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___x_1354_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1362_;
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
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_a_1355_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
else
{
lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1370_; 
v_a_1363_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1365_ = v___x_1354_;
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v___x_1354_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1368_; 
if (v_isShared_1366_ == 0)
{
v___x_1368_ = v___x_1365_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_a_1363_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg___boxed(lean_object* v_type_1371_, lean_object* v_maxFVars_x3f_1372_, lean_object* v_k_1373_, lean_object* v_cleanupAnnotations_1374_, lean_object* v_whnfType_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1381_; uint8_t v_whnfType_boxed_1382_; lean_object* v_res_1383_; 
v_cleanupAnnotations_boxed_1381_ = lean_unbox(v_cleanupAnnotations_1374_);
v_whnfType_boxed_1382_ = lean_unbox(v_whnfType_1375_);
v_res_1383_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(v_type_1371_, v_maxFVars_x3f_1372_, v_k_1373_, v_cleanupAnnotations_boxed_1381_, v_whnfType_boxed_1382_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3(lean_object* v_00_u03b1_1384_, lean_object* v_type_1385_, lean_object* v_maxFVars_x3f_1386_, lean_object* v_k_1387_, uint8_t v_cleanupAnnotations_1388_, uint8_t v_whnfType_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_){
_start:
{
lean_object* v___x_1395_; 
v___x_1395_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(v_type_1385_, v_maxFVars_x3f_1386_, v_k_1387_, v_cleanupAnnotations_1388_, v_whnfType_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_);
return v___x_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___boxed(lean_object* v_00_u03b1_1396_, lean_object* v_type_1397_, lean_object* v_maxFVars_x3f_1398_, lean_object* v_k_1399_, lean_object* v_cleanupAnnotations_1400_, lean_object* v_whnfType_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1407_; uint8_t v_whnfType_boxed_1408_; lean_object* v_res_1409_; 
v_cleanupAnnotations_boxed_1407_ = lean_unbox(v_cleanupAnnotations_1400_);
v_whnfType_boxed_1408_ = lean_unbox(v_whnfType_1401_);
v_res_1409_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3(v_00_u03b1_1396_, v_type_1397_, v_maxFVars_x3f_1398_, v_k_1399_, v_cleanupAnnotations_boxed_1407_, v_whnfType_boxed_1408_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0(lean_object* v_name_1410_, lean_object* v_us_1411_, lean_object* v_params_1412_, lean_object* v_args1_1413_, uint8_t v_useEq_1414_, lean_object* v_args2_1415_, lean_object* v_args2New_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1422_ = l_Lean_mkConst(v_name_1410_, v_us_1411_);
v___x_1423_ = l_Lean_mkAppN(v___x_1422_, v_params_1412_);
lean_inc_ref(v___x_1423_);
v___x_1424_ = l_Lean_mkAppN(v___x_1423_, v_args1_1413_);
v___x_1425_ = l_Lean_mkAppN(v___x_1423_, v_args2_1415_);
v___x_1426_ = l_Lean_Meta_mkEq(v___x_1424_, v___x_1425_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v_a_1427_; uint8_t v___x_1428_; lean_object* v_result_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___x_1475_; 
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
lean_inc(v_a_1427_);
lean_dec_ref_known(v___x_1426_, 1);
v___x_1428_ = 1;
v___x_1475_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v_args1_1413_, v_args2_1415_, v___x_1428_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1507_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1478_ = v___x_1475_;
v_isShared_1479_ = v_isSharedCheck_1507_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1475_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1507_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1480_; 
v___x_1480_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f(v_a_1476_);
if (lean_obj_tag(v___x_1480_) == 1)
{
lean_del_object(v___x_1478_);
if (v_useEq_1414_ == 0)
{
lean_object* v_val_1481_; lean_object* v___x_1482_; 
v_val_1481_ = lean_ctor_get(v___x_1480_, 0);
lean_inc(v_val_1481_);
lean_dec_ref_known(v___x_1480_, 1);
v___x_1482_ = l_Lean_mkArrow(v_a_1427_, v_val_1481_, v___y_1419_, v___y_1420_);
if (lean_obj_tag(v___x_1482_) == 0)
{
lean_object* v_a_1483_; 
v_a_1483_ = lean_ctor_get(v___x_1482_, 0);
lean_inc(v_a_1483_);
lean_dec_ref_known(v___x_1482_, 1);
v_result_1430_ = v_a_1483_;
v___y_1431_ = v___y_1417_;
v___y_1432_ = v___y_1418_;
v___y_1433_ = v___y_1419_;
v___y_1434_ = v___y_1420_;
goto v___jp_1429_;
}
else
{
lean_object* v_a_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1491_; 
v_a_1484_ = lean_ctor_get(v___x_1482_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1486_ = v___x_1482_;
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_a_1484_);
lean_dec(v___x_1482_);
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
else
{
lean_object* v_val_1492_; lean_object* v___x_1493_; 
v_val_1492_ = lean_ctor_get(v___x_1480_, 0);
lean_inc(v_val_1492_);
lean_dec_ref_known(v___x_1480_, 1);
v___x_1493_ = l_Lean_Meta_mkEq(v_a_1427_, v_val_1492_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_);
if (lean_obj_tag(v___x_1493_) == 0)
{
lean_object* v_a_1494_; 
v_a_1494_ = lean_ctor_get(v___x_1493_, 0);
lean_inc(v_a_1494_);
lean_dec_ref_known(v___x_1493_, 1);
v_result_1430_ = v_a_1494_;
v___y_1431_ = v___y_1417_;
v___y_1432_ = v___y_1418_;
v___y_1433_ = v___y_1419_;
v___y_1434_ = v___y_1420_;
goto v___jp_1429_;
}
else
{
lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1502_; 
v_a_1495_ = lean_ctor_get(v___x_1493_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1497_ = v___x_1493_;
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v___x_1493_);
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
}
else
{
lean_object* v___x_1503_; lean_object* v___x_1505_; 
lean_dec(v___x_1480_);
lean_dec(v_a_1427_);
v___x_1503_ = lean_box(0);
if (v_isShared_1479_ == 0)
{
lean_ctor_set(v___x_1478_, 0, v___x_1503_);
v___x_1505_ = v___x_1478_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___x_1503_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
else
{
lean_object* v_a_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1515_; 
lean_dec(v_a_1427_);
v_a_1508_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1510_ = v___x_1475_;
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_a_1508_);
lean_dec(v___x_1475_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1513_; 
if (v_isShared_1511_ == 0)
{
v___x_1513_ = v___x_1510_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_a_1508_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
}
v___jp_1429_:
{
uint8_t v___x_1435_; uint8_t v___x_1436_; lean_object* v___x_1437_; 
v___x_1435_ = 0;
v___x_1436_ = 1;
v___x_1437_ = l_Lean_Meta_mkForallFVars(v_args2New_1416_, v_result_1430_, v___x_1435_, v___x_1428_, v___x_1428_, v___x_1436_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v_a_1438_; lean_object* v___x_1439_; 
v_a_1438_ = lean_ctor_get(v___x_1437_, 0);
lean_inc(v_a_1438_);
lean_dec_ref_known(v___x_1437_, 1);
v___x_1439_ = l_Lean_Meta_mkForallFVars(v_args1_1413_, v_a_1438_, v___x_1435_, v___x_1428_, v___x_1428_, v___x_1436_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_object* v_a_1440_; lean_object* v___x_1441_; 
v_a_1440_ = lean_ctor_get(v___x_1439_, 0);
lean_inc(v_a_1440_);
lean_dec_ref_known(v___x_1439_, 1);
v___x_1441_ = l_Lean_Meta_mkForallFVars(v_params_1412_, v_a_1440_, v___x_1435_, v___x_1428_, v___x_1428_, v___x_1436_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
if (lean_obj_tag(v___x_1441_) == 0)
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1450_; 
v_a_1442_ = lean_ctor_get(v___x_1441_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1444_ = v___x_1441_;
v_isShared_1445_ = v_isSharedCheck_1450_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1441_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1450_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1446_; lean_object* v___x_1448_; 
v___x_1446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1446_, 0, v_a_1442_);
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 0, v___x_1446_);
v___x_1448_ = v___x_1444_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v___x_1446_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
else
{
lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1458_; 
v_a_1451_ = lean_ctor_get(v___x_1441_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1453_ = v___x_1441_;
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1441_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1456_; 
if (v_isShared_1454_ == 0)
{
v___x_1456_ = v___x_1453_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_a_1451_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
}
else
{
lean_object* v_a_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1466_; 
v_a_1459_ = lean_ctor_get(v___x_1439_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1439_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1461_ = v___x_1439_;
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_a_1459_);
lean_dec(v___x_1439_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1464_; 
if (v_isShared_1462_ == 0)
{
v___x_1464_ = v___x_1461_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_a_1459_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
}
else
{
lean_object* v_a_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1474_; 
v_a_1467_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1469_ = v___x_1437_;
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_a_1467_);
lean_dec(v___x_1437_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1472_; 
if (v_isShared_1470_ == 0)
{
v___x_1472_ = v___x_1469_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_a_1467_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
}
}
else
{
lean_object* v_a_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1523_; 
lean_dec_ref(v_args2_1415_);
v_a_1516_ = lean_ctor_get(v___x_1426_, 0);
v_isSharedCheck_1523_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1518_ = v___x_1426_;
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_a_1516_);
lean_dec(v___x_1426_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1521_; 
if (v_isShared_1519_ == 0)
{
v___x_1521_ = v___x_1518_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v_a_1516_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0___boxed(lean_object* v_name_1524_, lean_object* v_us_1525_, lean_object* v_params_1526_, lean_object* v_args1_1527_, lean_object* v_useEq_1528_, lean_object* v_args2_1529_, lean_object* v_args2New_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_){
_start:
{
uint8_t v_useEq_boxed_1536_; lean_object* v_res_1537_; 
v_useEq_boxed_1536_ = lean_unbox(v_useEq_1528_);
v_res_1537_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0(v_name_1524_, v_us_1525_, v_params_1526_, v_args1_1527_, v_useEq_boxed_1536_, v_args2_1529_, v_args2New_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
lean_dec(v___y_1534_);
lean_dec_ref(v___y_1533_);
lean_dec(v___y_1532_);
lean_dec_ref(v___y_1531_);
lean_dec_ref(v_args2New_1530_);
lean_dec_ref(v_args1_1527_);
lean_dec_ref(v_params_1526_);
return v_res_1537_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1(size_t v_sz_1538_, size_t v_i_1539_, lean_object* v_bs_1540_){
_start:
{
uint8_t v___x_1541_; 
v___x_1541_ = lean_usize_dec_lt(v_i_1539_, v_sz_1538_);
if (v___x_1541_ == 0)
{
return v_bs_1540_;
}
else
{
lean_object* v_v_1542_; lean_object* v___x_1543_; lean_object* v_bs_x27_1544_; lean_object* v___x_1545_; uint8_t v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; size_t v___x_1549_; size_t v___x_1550_; lean_object* v___x_1551_; 
v_v_1542_ = lean_array_uget(v_bs_1540_, v_i_1539_);
v___x_1543_ = lean_unsigned_to_nat(0u);
v_bs_x27_1544_ = lean_array_uset(v_bs_1540_, v_i_1539_, v___x_1543_);
v___x_1545_ = l_Lean_Expr_fvarId_x21(v_v_1542_);
lean_dec(v_v_1542_);
v___x_1546_ = 1;
v___x_1547_ = lean_box(v___x_1546_);
v___x_1548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1545_);
lean_ctor_set(v___x_1548_, 1, v___x_1547_);
v___x_1549_ = ((size_t)1ULL);
v___x_1550_ = lean_usize_add(v_i_1539_, v___x_1549_);
v___x_1551_ = lean_array_uset(v_bs_x27_1544_, v_i_1539_, v___x_1548_);
v_i_1539_ = v___x_1550_;
v_bs_1540_ = v___x_1551_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1___boxed(lean_object* v_sz_1553_, lean_object* v_i_1554_, lean_object* v_bs_1555_){
_start:
{
size_t v_sz_boxed_1556_; size_t v_i_boxed_1557_; lean_object* v_res_1558_; 
v_sz_boxed_1556_ = lean_unbox_usize(v_sz_1553_);
lean_dec(v_sz_1553_);
v_i_boxed_1557_ = lean_unbox_usize(v_i_1554_);
lean_dec(v_i_1554_);
v_res_1558_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1(v_sz_boxed_1556_, v_i_boxed_1557_, v_bs_1555_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(lean_object* v_bs_1559_, lean_object* v_k_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_){
_start:
{
lean_object* v___x_1566_; 
v___x_1566_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_box(0), v_bs_1559_, v_k_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_);
if (lean_obj_tag(v___x_1566_) == 0)
{
lean_object* v_a_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1574_; 
v_a_1567_ = lean_ctor_get(v___x_1566_, 0);
v_isSharedCheck_1574_ = !lean_is_exclusive(v___x_1566_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1569_ = v___x_1566_;
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_a_1567_);
lean_dec(v___x_1566_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1572_; 
if (v_isShared_1570_ == 0)
{
v___x_1572_ = v___x_1569_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_a_1567_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
}
else
{
lean_object* v_a_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1582_; 
v_a_1575_ = lean_ctor_get(v___x_1566_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1566_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1577_ = v___x_1566_;
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_a_1575_);
lean_dec(v___x_1566_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1580_; 
if (v_isShared_1578_ == 0)
{
v___x_1580_ = v___x_1577_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_a_1575_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_bs_1583_, lean_object* v_k_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(v_bs_1583_, v_k_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec_ref(v_bs_1583_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(lean_object* v_bs_1591_, lean_object* v_k_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_){
_start:
{
size_t v_sz_1598_; size_t v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
v_sz_1598_ = lean_array_size(v_bs_1591_);
v___x_1599_ = ((size_t)0ULL);
v___x_1600_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1(v_sz_1598_, v___x_1599_, v_bs_1591_);
v___x_1601_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(v___x_1600_, v_k_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_);
lean_dec_ref(v___x_1600_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg___boxed(lean_object* v_bs_1602_, lean_object* v_k_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v_bs_1602_, v_k_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1(lean_object* v_name_1610_, lean_object* v_us_1611_, lean_object* v_params_1612_, uint8_t v_useEq_1613_, lean_object* v_ctorVal_1614_, lean_object* v_type_1615_, lean_object* v_args1_1616_, lean_object* v_resultType_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_){
_start:
{
lean_object* v___x_1623_; lean_object* v___f_1624_; 
v___x_1623_ = lean_box(v_useEq_1613_);
lean_inc_ref(v_args1_1616_);
lean_inc_ref(v_params_1612_);
v___f_1624_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1624_, 0, v_name_1610_);
lean_closure_set(v___f_1624_, 1, v_us_1611_);
lean_closure_set(v___f_1624_, 2, v_params_1612_);
lean_closure_set(v___f_1624_, 3, v_args1_1616_);
lean_closure_set(v___f_1624_, 4, v___x_1623_);
if (v_useEq_1613_ == 0)
{
lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1625_ = l_Array_append___redArg(v_params_1612_, v_args1_1616_);
v___x_1626_ = lean_unsigned_to_nat(0u);
v___x_1627_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_1628_ = lean_box(v_useEq_1613_);
v___x_1629_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___boxed), 14, 9);
lean_closure_set(v___x_1629_, 0, v_ctorVal_1614_);
lean_closure_set(v___x_1629_, 1, v___x_1628_);
lean_closure_set(v___x_1629_, 2, v_args1_1616_);
lean_closure_set(v___x_1629_, 3, v_resultType_1617_);
lean_closure_set(v___x_1629_, 4, v___f_1624_);
lean_closure_set(v___x_1629_, 5, v___x_1626_);
lean_closure_set(v___x_1629_, 6, v_type_1615_);
lean_closure_set(v___x_1629_, 7, v___x_1627_);
lean_closure_set(v___x_1629_, 8, v___x_1627_);
v___x_1630_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v___x_1625_, v___x_1629_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_);
return v___x_1630_;
}
else
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
lean_dec_ref(v_params_1612_);
v___x_1631_ = lean_unsigned_to_nat(0u);
v___x_1632_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_1633_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(v_ctorVal_1614_, v_useEq_1613_, v_args1_1616_, v_resultType_1617_, v___f_1624_, v___x_1631_, v_type_1615_, v___x_1632_, v___x_1632_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_);
return v___x_1633_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1___boxed(lean_object* v_name_1634_, lean_object* v_us_1635_, lean_object* v_params_1636_, lean_object* v_useEq_1637_, lean_object* v_ctorVal_1638_, lean_object* v_type_1639_, lean_object* v_args1_1640_, lean_object* v_resultType_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
uint8_t v_useEq_boxed_1647_; lean_object* v_res_1648_; 
v_useEq_boxed_1647_ = lean_unbox(v_useEq_1637_);
v_res_1648_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1(v_name_1634_, v_us_1635_, v_params_1636_, v_useEq_boxed_1647_, v_ctorVal_1638_, v_type_1639_, v_args1_1640_, v_resultType_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2(lean_object* v_name_1649_, lean_object* v_us_1650_, uint8_t v_useEq_1651_, lean_object* v_ctorVal_1652_, lean_object* v_params_1653_, lean_object* v_type_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_){
_start:
{
lean_object* v___x_1660_; lean_object* v___f_1661_; uint8_t v___x_1662_; lean_object* v___x_1663_; 
v___x_1660_ = lean_box(v_useEq_1651_);
lean_inc_ref(v_type_1654_);
v___f_1661_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1___boxed), 13, 6);
lean_closure_set(v___f_1661_, 0, v_name_1649_);
lean_closure_set(v___f_1661_, 1, v_us_1650_);
lean_closure_set(v___f_1661_, 2, v_params_1653_);
lean_closure_set(v___f_1661_, 3, v___x_1660_);
lean_closure_set(v___f_1661_, 4, v_ctorVal_1652_);
lean_closure_set(v___f_1661_, 5, v_type_1654_);
v___x_1662_ = 0;
v___x_1663_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_type_1654_, v___f_1661_, v___x_1662_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2___boxed(lean_object* v_name_1664_, lean_object* v_us_1665_, lean_object* v_useEq_1666_, lean_object* v_ctorVal_1667_, lean_object* v_params_1668_, lean_object* v_type_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_){
_start:
{
uint8_t v_useEq_boxed_1675_; lean_object* v_res_1676_; 
v_useEq_boxed_1675_ = lean_unbox(v_useEq_1666_);
v_res_1676_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2(v_name_1664_, v_us_1665_, v_useEq_boxed_1675_, v_ctorVal_1667_, v_params_1668_, v_type_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(lean_object* v_a_1677_, lean_object* v_a_1678_){
_start:
{
if (lean_obj_tag(v_a_1677_) == 0)
{
lean_object* v___x_1679_; 
v___x_1679_ = l_List_reverse___redArg(v_a_1678_);
return v___x_1679_;
}
else
{
lean_object* v_head_1680_; lean_object* v_tail_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1690_; 
v_head_1680_ = lean_ctor_get(v_a_1677_, 0);
v_tail_1681_ = lean_ctor_get(v_a_1677_, 1);
v_isSharedCheck_1690_ = !lean_is_exclusive(v_a_1677_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1683_ = v_a_1677_;
v_isShared_1684_ = v_isSharedCheck_1690_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_tail_1681_);
lean_inc(v_head_1680_);
lean_dec(v_a_1677_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1690_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1685_; lean_object* v___x_1687_; 
v___x_1685_ = l_Lean_mkLevelParam(v_head_1680_);
if (v_isShared_1684_ == 0)
{
lean_ctor_set(v___x_1683_, 1, v_a_1678_);
lean_ctor_set(v___x_1683_, 0, v___x_1685_);
v___x_1687_ = v___x_1683_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v___x_1685_);
lean_ctor_set(v_reuseFailAlloc_1689_, 1, v_a_1678_);
v___x_1687_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
v_a_1677_ = v_tail_1681_;
v_a_1678_ = v___x_1687_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(lean_object* v_ctorVal_1691_, uint8_t v_useEq_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_){
_start:
{
lean_object* v_toConstantVal_1698_; lean_object* v_numParams_1699_; lean_object* v_name_1700_; lean_object* v_levelParams_1701_; lean_object* v_type_1702_; lean_object* v___x_1703_; 
v_toConstantVal_1698_ = lean_ctor_get(v_ctorVal_1691_, 0);
v_numParams_1699_ = lean_ctor_get(v_ctorVal_1691_, 3);
lean_inc(v_numParams_1699_);
v_name_1700_ = lean_ctor_get(v_toConstantVal_1698_, 0);
lean_inc(v_name_1700_);
v_levelParams_1701_ = lean_ctor_get(v_toConstantVal_1698_, 1);
v_type_1702_ = lean_ctor_get(v_toConstantVal_1698_, 2);
lean_inc_ref(v_type_1702_);
v___x_1703_ = l_Lean_Meta_elimOptParam(v_type_1702_, v_a_1695_, v_a_1696_);
if (lean_obj_tag(v___x_1703_) == 0)
{
lean_object* v_a_1704_; lean_object* v___x_1705_; lean_object* v_us_1706_; lean_object* v___x_1707_; lean_object* v___f_1708_; lean_object* v___x_1709_; uint8_t v___x_1710_; lean_object* v___x_1711_; 
v_a_1704_ = lean_ctor_get(v___x_1703_, 0);
lean_inc(v_a_1704_);
lean_dec_ref_known(v___x_1703_, 1);
v___x_1705_ = lean_box(0);
lean_inc(v_levelParams_1701_);
v_us_1706_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(v_levelParams_1701_, v___x_1705_);
v___x_1707_ = lean_box(v_useEq_1692_);
v___f_1708_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2___boxed), 11, 4);
lean_closure_set(v___f_1708_, 0, v_name_1700_);
lean_closure_set(v___f_1708_, 1, v_us_1706_);
lean_closure_set(v___f_1708_, 2, v___x_1707_);
lean_closure_set(v___f_1708_, 3, v_ctorVal_1691_);
v___x_1709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1709_, 0, v_numParams_1699_);
v___x_1710_ = 0;
v___x_1711_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(v_a_1704_, v___x_1709_, v___f_1708_, v___x_1710_, v___x_1710_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_);
return v___x_1711_;
}
else
{
lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1719_; 
lean_dec(v_name_1700_);
lean_dec(v_numParams_1699_);
lean_dec_ref(v_ctorVal_1691_);
v_a_1712_ = lean_ctor_get(v___x_1703_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1703_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1714_ = v___x_1703_;
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_dec(v___x_1703_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1717_; 
if (v_isShared_1715_ == 0)
{
v___x_1717_ = v___x_1714_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_a_1712_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___boxed(lean_object* v_ctorVal_1720_, lean_object* v_useEq_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_){
_start:
{
uint8_t v_useEq_boxed_1727_; lean_object* v_res_1728_; 
v_useEq_boxed_1727_ = lean_unbox(v_useEq_1721_);
v_res_1728_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(v_ctorVal_1720_, v_useEq_boxed_1727_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_);
lean_dec(v_a_1725_);
lean_dec_ref(v_a_1724_);
lean_dec(v_a_1723_);
lean_dec_ref(v_a_1722_);
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2(lean_object* v_00_u03b1_1729_, lean_object* v_bs_1730_, lean_object* v_k_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_){
_start:
{
lean_object* v___x_1737_; 
v___x_1737_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(v_bs_1730_, v_k_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1738_, lean_object* v_bs_1739_, lean_object* v_k_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
lean_object* v_res_1746_; 
v_res_1746_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2(v_00_u03b1_1738_, v_bs_1739_, v_k_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec_ref(v_bs_1739_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1(lean_object* v_00_u03b1_1747_, lean_object* v_bs_1748_, lean_object* v_k_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_){
_start:
{
lean_object* v___x_1755_; 
v___x_1755_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v_bs_1748_, v_k_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
return v___x_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___boxed(lean_object* v_00_u03b1_1756_, lean_object* v_bs_1757_, lean_object* v_k_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_){
_start:
{
lean_object* v_res_1764_; 
v_res_1764_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1(v_00_u03b1_1756_, v_bs_1757_, v_k_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(lean_object* v_ctorVal_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_){
_start:
{
uint8_t v___x_1771_; lean_object* v___x_1772_; 
v___x_1771_ = 0;
v___x_1772_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(v_ctorVal_1765_, v___x_1771_, v_a_1766_, v_a_1767_, v_a_1768_, v_a_1769_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f___boxed(lean_object* v_ctorVal_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_){
_start:
{
lean_object* v_res_1779_; 
v_res_1779_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_1773_, v_a_1774_, v_a_1775_, v_a_1776_, v_a_1777_);
lean_dec(v_a_1777_);
lean_dec_ref(v_a_1776_);
lean_dec(v_a_1775_);
lean_dec_ref(v_a_1774_);
return v_res_1779_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1(void){
_start:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1781_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__0));
v___x_1782_ = l_Lean_stringToMessageData(v___x_1781_);
return v___x_1782_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3(void){
_start:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1784_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__2));
v___x_1785_ = l_Lean_stringToMessageData(v___x_1784_);
return v___x_1785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(lean_object* v_ctorName_1786_){
_start:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1787_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1);
v___x_1788_ = l_Lean_MessageData_ofName(v_ctorName_1786_);
v___x_1789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1787_);
lean_ctor_set(v___x_1789_, 1, v___x_1788_);
v___x_1790_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3);
v___x_1791_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1791_, 0, v___x_1789_);
lean_ctor_set(v___x_1791_, 1, v___x_1790_);
return v___x_1791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(lean_object* v_ctorName_1792_, lean_object* v_mvarId_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_){
_start:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1799_ = l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(v_ctorName_1792_);
v___x_1800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1800_, 0, v_mvarId_1793_);
v___x_1801_ = l_Lean_indentD(v___x_1800_);
v___x_1802_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1799_);
lean_ctor_set(v___x_1802_, 1, v___x_1801_);
v___x_1803_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_1802_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg___boxed(lean_object* v_ctorName_1804_, lean_object* v_mvarId_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_){
_start:
{
lean_object* v_res_1811_; 
v_res_1811_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(v_ctorName_1804_, v_mvarId_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_);
lean_dec(v_a_1809_);
lean_dec_ref(v_a_1808_);
lean_dec(v_a_1807_);
lean_dec_ref(v_a_1806_);
return v_res_1811_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure(lean_object* v_00_u03b1_1812_, lean_object* v_ctorName_1813_, lean_object* v_mvarId_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_){
_start:
{
lean_object* v___x_1820_; 
v___x_1820_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(v_ctorName_1813_, v_mvarId_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_);
return v___x_1820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___boxed(lean_object* v_00_u03b1_1821_, lean_object* v_ctorName_1822_, lean_object* v_mvarId_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_){
_start:
{
lean_object* v_res_1829_; 
v_res_1829_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure(v_00_u03b1_1821_, v_ctorName_1822_, v_mvarId_1823_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_);
lean_dec(v_a_1827_);
lean_dec_ref(v_a_1826_);
lean_dec(v_a_1825_);
lean_dec_ref(v_a_1824_);
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0(lean_object* v_ctorName_1830_, lean_object* v_as_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_){
_start:
{
if (lean_obj_tag(v_as_1831_) == 0)
{
lean_object* v___x_1837_; lean_object* v___x_1838_; 
lean_dec(v_ctorName_1830_);
v___x_1837_ = lean_box(0);
v___x_1838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1837_);
return v___x_1838_;
}
else
{
lean_object* v_head_1839_; lean_object* v_tail_1840_; lean_object* v___x_1841_; 
v_head_1839_ = lean_ctor_get(v_as_1831_, 0);
lean_inc_n(v_head_1839_, 2);
v_tail_1840_ = lean_ctor_get(v_as_1831_, 1);
lean_inc(v_tail_1840_);
lean_dec_ref_known(v_as_1831_, 2);
v___x_1841_ = l_Lean_MVarId_assumptionCore(v_head_1839_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; uint8_t v___x_1843_; 
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
lean_inc(v_a_1842_);
lean_dec_ref_known(v___x_1841_, 1);
v___x_1843_ = lean_unbox(v_a_1842_);
lean_dec(v_a_1842_);
if (v___x_1843_ == 0)
{
lean_object* v___x_1844_; 
lean_dec(v_tail_1840_);
v___x_1844_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(v_ctorName_1830_, v_head_1839_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
return v___x_1844_;
}
else
{
lean_dec(v_head_1839_);
v_as_1831_ = v_tail_1840_;
goto _start;
}
}
else
{
lean_object* v_a_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1853_; 
lean_dec(v_tail_1840_);
lean_dec(v_head_1839_);
lean_dec(v_ctorName_1830_);
v_a_1846_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1853_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1848_ = v___x_1841_;
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_a_1846_);
lean_dec(v___x_1841_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1851_; 
if (v_isShared_1849_ == 0)
{
v___x_1851_ = v___x_1848_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v_a_1846_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
return v___x_1851_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0___boxed(lean_object* v_ctorName_1854_, lean_object* v_as_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_){
_start:
{
lean_object* v_res_1861_; 
v_res_1861_ = l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0(v_ctorName_1854_, v_as_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_);
lean_dec(v___y_1859_);
lean_dec_ref(v___y_1858_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
return v_res_1861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(lean_object* v_mvarId_1862_, lean_object* v_ctorName_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_){
_start:
{
lean_object* v___x_1869_; 
v___x_1869_ = l_Lean_MVarId_splitAndCore(v_mvarId_1862_, v_a_1864_, v_a_1865_, v_a_1866_, v_a_1867_);
if (lean_obj_tag(v___x_1869_) == 0)
{
lean_object* v_a_1870_; lean_object* v___x_1871_; 
v_a_1870_ = lean_ctor_get(v___x_1869_, 0);
lean_inc(v_a_1870_);
lean_dec_ref_known(v___x_1869_, 1);
v___x_1871_ = l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0(v_ctorName_1863_, v_a_1870_, v_a_1864_, v_a_1865_, v_a_1866_, v_a_1867_);
return v___x_1871_;
}
else
{
lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1879_; 
lean_dec(v_ctorName_1863_);
v_a_1872_ = lean_ctor_get(v___x_1869_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1874_ = v___x_1869_;
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v___x_1869_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1877_; 
if (v_isShared_1875_ == 0)
{
v___x_1877_ = v___x_1874_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_a_1872_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption___boxed(lean_object* v_mvarId_1880_, lean_object* v_ctorName_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_){
_start:
{
lean_object* v_res_1887_; 
v_res_1887_ = l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(v_mvarId_1880_, v_ctorName_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_);
lean_dec(v_a_1885_);
lean_dec_ref(v_a_1884_);
lean_dec(v_a_1883_);
lean_dec_ref(v_a_1882_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0(lean_object* v_msg_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
lean_object* v___f_1895_; lean_object* v___x_905__overap_1896_; lean_object* v___x_1897_; 
v___f_1895_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0___closed__0));
v___x_905__overap_1896_ = lean_panic_fn_borrowed(v___f_1895_, v_msg_1889_);
lean_inc(v___y_1893_);
lean_inc_ref(v___y_1892_);
lean_inc(v___y_1891_);
lean_inc_ref(v___y_1890_);
v___x_1897_ = lean_apply_5(v___x_905__overap_1896_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, lean_box(0));
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0___boxed(lean_object* v_msg_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_){
_start:
{
lean_object* v_res_1904_; 
v_res_1904_ = l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0(v_msg_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
return v_res_1904_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1905_; double v___x_1906_; 
v___x_1905_ = lean_unsigned_to_nat(0u);
v___x_1906_ = lean_float_of_nat(v___x_1905_);
return v___x_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(lean_object* v_cls_1910_, lean_object* v_msg_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_){
_start:
{
lean_object* v_ref_1917_; lean_object* v___x_1918_; lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1963_; 
v_ref_1917_ = lean_ctor_get(v___y_1914_, 2);
v___x_1918_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msg_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_);
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1921_ = v___x_1918_;
v_isShared_1922_ = v_isSharedCheck_1963_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1918_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1963_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1923_; lean_object* v_traceState_1924_; lean_object* v_env_1925_; lean_object* v_nextMacroScope_1926_; lean_object* v_ngen_1927_; lean_object* v_auxDeclNGen_1928_; lean_object* v_cache_1929_; lean_object* v_messages_1930_; lean_object* v_infoState_1931_; lean_object* v_snapshotTasks_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1962_; 
v___x_1923_ = lean_st_ref_take(v___y_1915_);
v_traceState_1924_ = lean_ctor_get(v___x_1923_, 4);
v_env_1925_ = lean_ctor_get(v___x_1923_, 0);
v_nextMacroScope_1926_ = lean_ctor_get(v___x_1923_, 1);
v_ngen_1927_ = lean_ctor_get(v___x_1923_, 2);
v_auxDeclNGen_1928_ = lean_ctor_get(v___x_1923_, 3);
v_cache_1929_ = lean_ctor_get(v___x_1923_, 5);
v_messages_1930_ = lean_ctor_get(v___x_1923_, 6);
v_infoState_1931_ = lean_ctor_get(v___x_1923_, 7);
v_snapshotTasks_1932_ = lean_ctor_get(v___x_1923_, 8);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1934_ = v___x_1923_;
v_isShared_1935_ = v_isSharedCheck_1962_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_snapshotTasks_1932_);
lean_inc(v_infoState_1931_);
lean_inc(v_messages_1930_);
lean_inc(v_cache_1929_);
lean_inc(v_traceState_1924_);
lean_inc(v_auxDeclNGen_1928_);
lean_inc(v_ngen_1927_);
lean_inc(v_nextMacroScope_1926_);
lean_inc(v_env_1925_);
lean_dec(v___x_1923_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1962_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
uint64_t v_tid_1936_; lean_object* v_traces_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1961_; 
v_tid_1936_ = lean_ctor_get_uint64(v_traceState_1924_, sizeof(void*)*1);
v_traces_1937_ = lean_ctor_get(v_traceState_1924_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v_traceState_1924_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1939_ = v_traceState_1924_;
v_isShared_1940_ = v_isSharedCheck_1961_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_traces_1937_);
lean_dec(v_traceState_1924_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1961_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1941_; double v___x_1942_; uint8_t v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1951_; 
v___x_1941_ = lean_box(0);
v___x_1942_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0);
v___x_1943_ = 0;
v___x_1944_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_1945_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1945_, 0, v_cls_1910_);
lean_ctor_set(v___x_1945_, 1, v___x_1941_);
lean_ctor_set(v___x_1945_, 2, v___x_1944_);
lean_ctor_set_float(v___x_1945_, sizeof(void*)*3, v___x_1942_);
lean_ctor_set_float(v___x_1945_, sizeof(void*)*3 + 8, v___x_1942_);
lean_ctor_set_uint8(v___x_1945_, sizeof(void*)*3 + 16, v___x_1943_);
v___x_1946_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__2));
v___x_1947_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1945_);
lean_ctor_set(v___x_1947_, 1, v_a_1919_);
lean_ctor_set(v___x_1947_, 2, v___x_1946_);
lean_inc(v_ref_1917_);
v___x_1948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1948_, 0, v_ref_1917_);
lean_ctor_set(v___x_1948_, 1, v___x_1947_);
v___x_1949_ = l_Lean_PersistentArray_push___redArg(v_traces_1937_, v___x_1948_);
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 0, v___x_1949_);
v___x_1951_ = v___x_1939_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v___x_1949_);
lean_ctor_set_uint64(v_reuseFailAlloc_1960_, sizeof(void*)*1, v_tid_1936_);
v___x_1951_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
lean_object* v___x_1953_; 
if (v_isShared_1935_ == 0)
{
lean_ctor_set(v___x_1934_, 4, v___x_1951_);
v___x_1953_ = v___x_1934_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_env_1925_);
lean_ctor_set(v_reuseFailAlloc_1959_, 1, v_nextMacroScope_1926_);
lean_ctor_set(v_reuseFailAlloc_1959_, 2, v_ngen_1927_);
lean_ctor_set(v_reuseFailAlloc_1959_, 3, v_auxDeclNGen_1928_);
lean_ctor_set(v_reuseFailAlloc_1959_, 4, v___x_1951_);
lean_ctor_set(v_reuseFailAlloc_1959_, 5, v_cache_1929_);
lean_ctor_set(v_reuseFailAlloc_1959_, 6, v_messages_1930_);
lean_ctor_set(v_reuseFailAlloc_1959_, 7, v_infoState_1931_);
lean_ctor_set(v_reuseFailAlloc_1959_, 8, v_snapshotTasks_1932_);
v___x_1953_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1957_; 
v___x_1954_ = lean_st_ref_put(v___y_1915_, v___x_1953_);
v___x_1955_ = lean_box(0);
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 0, v___x_1955_);
v___x_1957_ = v___x_1921_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v___x_1955_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___boxed(lean_object* v_cls_1964_, lean_object* v_msg_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_){
_start:
{
lean_object* v_res_1971_; 
v_res_1971_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_1964_, v_msg_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
lean_dec(v___y_1967_);
lean_dec_ref(v___y_1966_);
return v_res_1971_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3(void){
_start:
{
lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1975_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__2));
v___x_1976_ = lean_unsigned_to_nat(30u);
v___x_1977_ = lean_unsigned_to_nat(96u);
v___x_1978_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__1));
v___x_1979_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__0));
v___x_1980_ = l_mkPanicMessageWithDecl(v___x_1979_, v___x_1978_, v___x_1977_, v___x_1976_, v___x_1975_);
return v___x_1980_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9(void){
_start:
{
lean_object* v_cls_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v_cls_1989_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_1990_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__8));
v___x_1991_ = l_Lean_Name_append(v___x_1990_, v_cls_1989_);
return v___x_1991_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11(void){
_start:
{
lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1993_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__10));
v___x_1994_ = l_Lean_stringToMessageData(v___x_1993_);
return v___x_1994_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13(void){
_start:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; 
v___x_1996_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__12));
v___x_1997_ = l_Lean_stringToMessageData(v___x_1996_);
return v___x_1997_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15(void){
_start:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1999_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__14));
v___x_2000_ = l_Lean_stringToMessageData(v___x_1999_);
return v___x_2000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(lean_object* v_ctorName_2001_, lean_object* v_mvarId_2002_, lean_object* v_h_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_){
_start:
{
lean_object* v___y_2010_; lean_object* v___y_2011_; lean_object* v___y_2012_; lean_object* v___y_2013_; lean_object* v_toCold_2029_; lean_object* v_options_2030_; uint8_t v_hasTrace_2031_; 
v_toCold_2029_ = lean_ctor_get(v_a_2006_, 0);
v_options_2030_ = lean_ctor_get(v_toCold_2029_, 2);
v_hasTrace_2031_ = lean_ctor_get_uint8(v_options_2030_, sizeof(void*)*1);
if (v_hasTrace_2031_ == 0)
{
v___y_2010_ = v_a_2004_;
v___y_2011_ = v_a_2005_;
v___y_2012_ = v_a_2006_;
v___y_2013_ = v_a_2007_;
goto v___jp_2009_;
}
else
{
lean_object* v_inheritedTraceOptions_2032_; lean_object* v_cls_2033_; lean_object* v___x_2034_; uint8_t v___x_2035_; 
v_inheritedTraceOptions_2032_ = lean_ctor_get(v_toCold_2029_, 11);
v_cls_2033_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_2034_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_2035_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2032_, v_options_2030_, v___x_2034_);
if (v___x_2035_ == 0)
{
v___y_2010_ = v_a_2004_;
v___y_2011_ = v_a_2005_;
v___y_2012_ = v_a_2006_;
v___y_2013_ = v_a_2007_;
goto v___jp_2009_;
}
else
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; 
v___x_2036_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11);
lean_inc(v_ctorName_2001_);
v___x_2037_ = l_Lean_MessageData_ofName(v_ctorName_2001_);
v___x_2038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2036_);
lean_ctor_set(v___x_2038_, 1, v___x_2037_);
v___x_2039_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13);
v___x_2040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2040_, 0, v___x_2038_);
lean_ctor_set(v___x_2040_, 1, v___x_2039_);
lean_inc(v_h_2003_);
v___x_2041_ = l_Lean_mkFVar(v_h_2003_);
v___x_2042_ = l_Lean_MessageData_ofExpr(v___x_2041_);
v___x_2043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2043_, 0, v___x_2040_);
lean_ctor_set(v___x_2043_, 1, v___x_2042_);
v___x_2044_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15);
v___x_2045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2045_, 0, v___x_2043_);
lean_ctor_set(v___x_2045_, 1, v___x_2044_);
lean_inc(v_mvarId_2002_);
v___x_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2046_, 0, v_mvarId_2002_);
v___x_2047_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2045_);
lean_ctor_set(v___x_2047_, 1, v___x_2046_);
v___x_2048_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2033_, v___x_2047_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_);
if (lean_obj_tag(v___x_2048_) == 0)
{
lean_dec_ref_known(v___x_2048_, 1);
v___y_2010_ = v_a_2004_;
v___y_2011_ = v_a_2005_;
v___y_2012_ = v_a_2006_;
v___y_2013_ = v_a_2007_;
goto v___jp_2009_;
}
else
{
lean_dec(v_h_2003_);
lean_dec(v_mvarId_2002_);
lean_dec(v_ctorName_2001_);
return v___x_2048_;
}
}
}
v___jp_2009_:
{
lean_object* v___x_2014_; lean_object* v___x_2015_; 
v___x_2014_ = lean_box(0);
v___x_2015_ = l_Lean_Meta_injection(v_mvarId_2002_, v_h_2003_, v___x_2014_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v_a_2016_; 
v_a_2016_ = lean_ctor_get(v___x_2015_, 0);
lean_inc(v_a_2016_);
lean_dec_ref_known(v___x_2015_, 1);
if (lean_obj_tag(v_a_2016_) == 0)
{
lean_object* v___x_2017_; lean_object* v___x_2018_; 
lean_dec(v_ctorName_2001_);
v___x_2017_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3);
v___x_2018_ = l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0(v___x_2017_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_);
return v___x_2018_;
}
else
{
lean_object* v_mvarId_2019_; lean_object* v___x_2020_; 
v_mvarId_2019_ = lean_ctor_get(v_a_2016_, 0);
lean_inc(v_mvarId_2019_);
lean_dec_ref_known(v_a_2016_, 3);
v___x_2020_ = l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(v_mvarId_2019_, v_ctorName_2001_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_);
return v___x_2020_;
}
}
else
{
lean_object* v_a_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2028_; 
lean_dec(v_ctorName_2001_);
v_a_2021_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2023_ = v___x_2015_;
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_a_2021_);
lean_dec(v___x_2015_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2026_; 
if (v_isShared_2024_ == 0)
{
v___x_2026_ = v___x_2023_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_a_2021_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___boxed(lean_object* v_ctorName_2049_, lean_object* v_mvarId_2050_, lean_object* v_h_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_){
_start:
{
lean_object* v_res_2057_; 
v_res_2057_ = l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(v_ctorName_2049_, v_mvarId_2050_, v_h_2051_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_);
lean_dec(v_a_2055_);
lean_dec_ref(v_a_2054_);
lean_dec(v_a_2053_);
lean_dec_ref(v_a_2052_);
return v_res_2057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(lean_object* v_type_2058_, lean_object* v_k_2059_, uint8_t v_cleanupAnnotations_2060_, uint8_t v_whnfType_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_){
_start:
{
lean_object* v___f_2067_; lean_object* v___x_2068_; 
v___f_2067_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2067_, 0, v_k_2059_);
v___x_2068_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_2058_, v___f_2067_, v_cleanupAnnotations_2060_, v_whnfType_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
if (lean_obj_tag(v___x_2068_) == 0)
{
lean_object* v_a_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2076_; 
v_a_2069_ = lean_ctor_get(v___x_2068_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v___x_2068_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2071_ = v___x_2068_;
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_a_2069_);
lean_dec(v___x_2068_);
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
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2084_; 
v_a_2077_ = lean_ctor_get(v___x_2068_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2068_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2079_ = v___x_2068_;
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_a_2077_);
lean_dec(v___x_2068_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg___boxed(lean_object* v_type_2085_, lean_object* v_k_2086_, lean_object* v_cleanupAnnotations_2087_, lean_object* v_whnfType_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2094_; uint8_t v_whnfType_boxed_2095_; lean_object* v_res_2096_; 
v_cleanupAnnotations_boxed_2094_ = lean_unbox(v_cleanupAnnotations_2087_);
v_whnfType_boxed_2095_ = lean_unbox(v_whnfType_2088_);
v_res_2096_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_type_2085_, v_k_2086_, v_cleanupAnnotations_boxed_2094_, v_whnfType_boxed_2095_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0(lean_object* v_00_u03b1_2097_, lean_object* v_type_2098_, lean_object* v_k_2099_, uint8_t v_cleanupAnnotations_2100_, uint8_t v_whnfType_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_){
_start:
{
lean_object* v___x_2107_; 
v___x_2107_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_type_2098_, v_k_2099_, v_cleanupAnnotations_2100_, v_whnfType_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_);
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___boxed(lean_object* v_00_u03b1_2108_, lean_object* v_type_2109_, lean_object* v_k_2110_, lean_object* v_cleanupAnnotations_2111_, lean_object* v_whnfType_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2118_; uint8_t v_whnfType_boxed_2119_; lean_object* v_res_2120_; 
v_cleanupAnnotations_boxed_2118_ = lean_unbox(v_cleanupAnnotations_2111_);
v_whnfType_boxed_2119_ = lean_unbox(v_whnfType_2112_);
v_res_2120_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0(v_00_u03b1_2108_, v_type_2109_, v_k_2110_, v_cleanupAnnotations_boxed_2118_, v_whnfType_boxed_2119_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
lean_dec(v___y_2116_);
lean_dec_ref(v___y_2115_);
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2113_);
return v_res_2120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0(lean_object* v___x_2121_, lean_object* v_ctorName_2122_, lean_object* v_xs_2123_, lean_object* v_type_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_){
_start:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2130_ = lean_box(0);
v___x_2131_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_2124_, v___x_2130_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_);
if (lean_obj_tag(v___x_2131_) == 0)
{
lean_object* v_a_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
v_a_2132_ = lean_ctor_get(v___x_2131_, 0);
lean_inc(v_a_2132_);
lean_dec_ref_known(v___x_2131_, 1);
v___x_2133_ = l_Lean_Expr_mvarId_x21(v_a_2132_);
v___x_2134_ = lean_array_get_size(v_xs_2123_);
v___x_2135_ = lean_unsigned_to_nat(1u);
v___x_2136_ = lean_nat_sub(v___x_2134_, v___x_2135_);
v___x_2137_ = lean_array_get_borrowed(v___x_2121_, v_xs_2123_, v___x_2136_);
lean_dec(v___x_2136_);
v___x_2138_ = l_Lean_Expr_fvarId_x21(v___x_2137_);
v___x_2139_ = l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(v_ctorName_2122_, v___x_2133_, v___x_2138_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_);
if (lean_obj_tag(v___x_2139_) == 0)
{
uint8_t v___x_2140_; uint8_t v___x_2141_; uint8_t v___x_2142_; lean_object* v___x_2143_; 
lean_dec_ref_known(v___x_2139_, 1);
v___x_2140_ = 0;
v___x_2141_ = 1;
v___x_2142_ = 1;
v___x_2143_ = l_Lean_Meta_mkLambdaFVars(v_xs_2123_, v_a_2132_, v___x_2140_, v___x_2141_, v___x_2140_, v___x_2141_, v___x_2142_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_);
return v___x_2143_;
}
else
{
lean_object* v_a_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2151_; 
lean_dec(v_a_2132_);
v_a_2144_ = lean_ctor_get(v___x_2139_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2146_ = v___x_2139_;
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_dec(v___x_2139_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2149_; 
if (v_isShared_2147_ == 0)
{
v___x_2149_ = v___x_2146_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v_a_2144_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
}
}
else
{
lean_dec(v_ctorName_2122_);
return v___x_2131_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0___boxed(lean_object* v___x_2152_, lean_object* v_ctorName_2153_, lean_object* v_xs_2154_, lean_object* v_type_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_){
_start:
{
lean_object* v_res_2161_; 
v_res_2161_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0(v___x_2152_, v_ctorName_2153_, v_xs_2154_, v_type_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_);
lean_dec(v___y_2159_);
lean_dec_ref(v___y_2158_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
lean_dec_ref(v_xs_2154_);
lean_dec_ref(v___x_2152_);
return v_res_2161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(lean_object* v_ctorName_2162_, lean_object* v_targetType_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_){
_start:
{
lean_object* v___x_2169_; lean_object* v___f_2170_; uint8_t v___x_2171_; lean_object* v___x_2172_; 
v___x_2169_ = l_Lean_instInhabitedExpr;
v___f_2170_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2170_, 0, v___x_2169_);
lean_closure_set(v___f_2170_, 1, v_ctorName_2162_);
v___x_2171_ = 0;
v___x_2172_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_targetType_2163_, v___f_2170_, v___x_2171_, v___x_2171_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_);
return v___x_2172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___boxed(lean_object* v_ctorName_2173_, lean_object* v_targetType_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_){
_start:
{
lean_object* v_res_2180_; 
v_res_2180_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_ctorName_2173_, v_targetType_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_);
lean_dec(v_a_2178_);
lean_dec_ref(v_a_2177_);
lean_dec(v_a_2176_);
lean_dec_ref(v_a_2175_);
return v_res_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheoremNameFor(lean_object* v_ctorName_2184_){
_start:
{
lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2185_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheoremNameFor___closed__1));
v___x_2186_ = l_Lean_Name_append(v_ctorName_2184_, v___x_2185_);
return v___x_2186_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(lean_object* v_e_2187_, lean_object* v___y_2188_){
_start:
{
uint8_t v___x_2190_; 
v___x_2190_ = l_Lean_Expr_hasMVar(v_e_2187_);
if (v___x_2190_ == 0)
{
lean_object* v___x_2191_; 
v___x_2191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2191_, 0, v_e_2187_);
return v___x_2191_;
}
else
{
lean_object* v___x_2192_; lean_object* v_mctx_2193_; lean_object* v___x_2194_; lean_object* v_fst_2195_; lean_object* v_snd_2196_; lean_object* v___x_2197_; lean_object* v_cache_2198_; lean_object* v_zetaDeltaFVarIds_2199_; lean_object* v_postponed_2200_; lean_object* v_diag_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2210_; 
v___x_2192_ = lean_st_ref_get(v___y_2188_);
v_mctx_2193_ = lean_ctor_get(v___x_2192_, 0);
lean_inc_ref(v_mctx_2193_);
lean_dec(v___x_2192_);
v___x_2194_ = l_Lean_instantiateMVarsCore(v_mctx_2193_, v_e_2187_);
v_fst_2195_ = lean_ctor_get(v___x_2194_, 0);
lean_inc(v_fst_2195_);
v_snd_2196_ = lean_ctor_get(v___x_2194_, 1);
lean_inc(v_snd_2196_);
lean_dec_ref(v___x_2194_);
v___x_2197_ = lean_st_ref_take(v___y_2188_);
v_cache_2198_ = lean_ctor_get(v___x_2197_, 1);
v_zetaDeltaFVarIds_2199_ = lean_ctor_get(v___x_2197_, 2);
v_postponed_2200_ = lean_ctor_get(v___x_2197_, 3);
v_diag_2201_ = lean_ctor_get(v___x_2197_, 4);
v_isSharedCheck_2210_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2210_ == 0)
{
lean_object* v_unused_2211_; 
v_unused_2211_ = lean_ctor_get(v___x_2197_, 0);
lean_dec(v_unused_2211_);
v___x_2203_ = v___x_2197_;
v_isShared_2204_ = v_isSharedCheck_2210_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_diag_2201_);
lean_inc(v_postponed_2200_);
lean_inc(v_zetaDeltaFVarIds_2199_);
lean_inc(v_cache_2198_);
lean_dec(v___x_2197_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2210_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___x_2206_; 
if (v_isShared_2204_ == 0)
{
lean_ctor_set(v___x_2203_, 0, v_snd_2196_);
v___x_2206_ = v___x_2203_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v_snd_2196_);
lean_ctor_set(v_reuseFailAlloc_2209_, 1, v_cache_2198_);
lean_ctor_set(v_reuseFailAlloc_2209_, 2, v_zetaDeltaFVarIds_2199_);
lean_ctor_set(v_reuseFailAlloc_2209_, 3, v_postponed_2200_);
lean_ctor_set(v_reuseFailAlloc_2209_, 4, v_diag_2201_);
v___x_2206_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2207_ = lean_st_ref_put(v___y_2188_, v___x_2206_);
v___x_2208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2208_, 0, v_fst_2195_);
return v___x_2208_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg___boxed(lean_object* v_e_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_){
_start:
{
lean_object* v_res_2215_; 
v_res_2215_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_e_2212_, v___y_2213_);
lean_dec(v___y_2213_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0(lean_object* v_e_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_){
_start:
{
lean_object* v___x_2222_; 
v___x_2222_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_e_2216_, v___y_2218_);
return v___x_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___boxed(lean_object* v_e_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_){
_start:
{
lean_object* v_res_2229_; 
v_res_2229_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0(v_e_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
return v_res_2229_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0(void){
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
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2233_ = ((size_t)5ULL);
v___x_2234_ = lean_unsigned_to_nat(0u);
v___x_2235_ = lean_unsigned_to_nat(32u);
v___x_2236_ = lean_mk_empty_array_with_capacity(v___x_2235_);
v___x_2237_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0);
v___x_2238_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2238_, 0, v___x_2237_);
lean_ctor_set(v___x_2238_, 1, v___x_2236_);
lean_ctor_set(v___x_2238_, 2, v___x_2234_);
lean_ctor_set(v___x_2238_, 3, v___x_2234_);
lean_ctor_set_usize(v___x_2238_, 4, v___x_2233_);
return v___x_2238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(lean_object* v___y_2239_){
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
v___x_2261_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1);
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
v___x_2266_ = lean_st_ref_put(v___y_2239_, v___x_2265_);
v___x_2267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2267_, 0, v_traces_2243_);
return v___x_2267_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___boxed(lean_object* v___y_2273_, lean_object* v___y_2274_){
_start:
{
lean_object* v_res_2275_; 
v_res_2275_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v___y_2273_);
lean_dec(v___y_2273_);
return v_res_2275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1(lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_){
_start:
{
lean_object* v___x_2281_; 
v___x_2281_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v___y_2279_);
return v___x_2281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___boxed(lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_){
_start:
{
lean_object* v_res_2287_; 
v_res_2287_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1(v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_);
lean_dec(v___y_2285_);
lean_dec_ref(v___y_2284_);
lean_dec(v___y_2283_);
lean_dec_ref(v___y_2282_);
return v_res_2287_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(lean_object* v_opts_2288_, lean_object* v_opt_2289_){
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2___boxed(lean_object* v_opts_2298_, lean_object* v_opt_2299_){
_start:
{
uint8_t v_res_2300_; lean_object* v_r_2301_; 
v_res_2300_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_opts_2298_, v_opt_2299_);
lean_dec_ref(v_opt_2299_);
lean_dec_ref(v_opts_2298_);
v_r_2301_ = lean_box(v_res_2300_);
return v_r_2301_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2303_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__0));
v___x_2304_ = l_Lean_stringToMessageData(v___x_2303_);
return v___x_2304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0(lean_object* v_name_2305_, lean_object* v_x_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_){
_start:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; 
v___x_2312_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1);
v___x_2313_ = l_Lean_MessageData_ofName(v_name_2305_);
v___x_2314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2314_, 0, v___x_2312_);
lean_ctor_set(v___x_2314_, 1, v___x_2313_);
v___x_2315_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_2316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2314_);
lean_ctor_set(v___x_2316_, 1, v___x_2315_);
v___x_2317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2316_);
return v___x_2317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed(lean_object* v_name_2318_, lean_object* v_x_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_){
_start:
{
lean_object* v_res_2325_; 
v_res_2325_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0(v_name_2318_, v_x_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec_ref(v_x_2319_);
return v_res_2325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(lean_object* v_name_2326_, lean_object* v_val_2327_, lean_object* v_name_2328_, lean_object* v_levelParams_2329_, uint8_t v___x_2330_, lean_object* v_____r_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_){
_start:
{
lean_object* v___x_2337_; 
lean_inc_ref(v_val_2327_);
v___x_2337_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2326_, v_val_2327_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v_a_2338_; lean_object* v___x_2339_; lean_object* v_a_2340_; lean_object* v___x_2341_; lean_object* v_a_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2354_; 
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
lean_inc(v_a_2338_);
lean_dec_ref_known(v___x_2337_, 1);
v___x_2339_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2327_, v___y_2333_);
v_a_2340_ = lean_ctor_get(v___x_2339_, 0);
lean_inc(v_a_2340_);
lean_dec_ref(v___x_2339_);
v___x_2341_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2338_, v___y_2333_);
v_a_2342_ = lean_ctor_get(v___x_2341_, 0);
v_isSharedCheck_2354_ = !lean_is_exclusive(v___x_2341_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2344_ = v___x_2341_;
v_isShared_2345_ = v_isSharedCheck_2354_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_a_2342_);
lean_dec(v___x_2341_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2354_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2351_; 
lean_inc(v_name_2328_);
v___x_2346_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2346_, 0, v_name_2328_);
lean_ctor_set(v___x_2346_, 1, v_levelParams_2329_);
lean_ctor_set(v___x_2346_, 2, v_a_2340_);
v___x_2347_ = lean_box(0);
v___x_2348_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2348_, 0, v_name_2328_);
lean_ctor_set(v___x_2348_, 1, v___x_2347_);
v___x_2349_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2346_);
lean_ctor_set(v___x_2349_, 1, v_a_2342_);
lean_ctor_set(v___x_2349_, 2, v___x_2348_);
if (v_isShared_2345_ == 0)
{
lean_ctor_set_tag(v___x_2344_, 2);
lean_ctor_set(v___x_2344_, 0, v___x_2349_);
v___x_2351_ = v___x_2344_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v___x_2349_);
v___x_2351_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
lean_object* v___x_2352_; 
v___x_2352_ = l_Lean_addDecl(v___x_2351_, v___x_2330_, v___y_2334_, v___y_2335_);
return v___x_2352_;
}
}
}
else
{
lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2362_; 
lean_dec(v_levelParams_2329_);
lean_dec(v_name_2328_);
lean_dec_ref(v_val_2327_);
v_a_2355_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2357_ = v___x_2337_;
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v___x_2337_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2360_; 
if (v_isShared_2358_ == 0)
{
v___x_2360_ = v___x_2357_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_a_2355_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1___boxed(lean_object* v_name_2363_, lean_object* v_val_2364_, lean_object* v_name_2365_, lean_object* v_levelParams_2366_, lean_object* v___x_2367_, lean_object* v_____r_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_){
_start:
{
uint8_t v___x_12398__boxed_2374_; lean_object* v_res_2375_; 
v___x_12398__boxed_2374_ = lean_unbox(v___x_2367_);
v_res_2375_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(v_name_2363_, v_val_2364_, v_name_2365_, v_levelParams_2366_, v___x_12398__boxed_2374_, v_____r_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
lean_dec(v___y_2370_);
lean_dec_ref(v___y_2369_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(lean_object* v_name_2376_, lean_object* v_val_2377_, lean_object* v_name_2378_, lean_object* v_levelParams_2379_, lean_object* v_____r_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_){
_start:
{
lean_object* v___x_2386_; 
lean_inc_ref(v_val_2377_);
v___x_2386_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2376_, v_val_2377_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_);
if (lean_obj_tag(v___x_2386_) == 0)
{
lean_object* v_a_2387_; lean_object* v___x_2388_; lean_object* v_a_2389_; lean_object* v___x_2390_; lean_object* v_a_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2404_; 
v_a_2387_ = lean_ctor_get(v___x_2386_, 0);
lean_inc(v_a_2387_);
lean_dec_ref_known(v___x_2386_, 1);
v___x_2388_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2377_, v___y_2382_);
v_a_2389_ = lean_ctor_get(v___x_2388_, 0);
lean_inc(v_a_2389_);
lean_dec_ref(v___x_2388_);
v___x_2390_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2387_, v___y_2382_);
v_a_2391_ = lean_ctor_get(v___x_2390_, 0);
v_isSharedCheck_2404_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2404_ == 0)
{
v___x_2393_ = v___x_2390_;
v_isShared_2394_ = v_isSharedCheck_2404_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_a_2391_);
lean_dec(v___x_2390_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2404_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2400_; 
lean_inc(v_name_2378_);
v___x_2395_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2395_, 0, v_name_2378_);
lean_ctor_set(v___x_2395_, 1, v_levelParams_2379_);
lean_ctor_set(v___x_2395_, 2, v_a_2389_);
v___x_2396_ = lean_box(0);
v___x_2397_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2397_, 0, v_name_2378_);
lean_ctor_set(v___x_2397_, 1, v___x_2396_);
v___x_2398_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2398_, 0, v___x_2395_);
lean_ctor_set(v___x_2398_, 1, v_a_2391_);
lean_ctor_set(v___x_2398_, 2, v___x_2397_);
if (v_isShared_2394_ == 0)
{
lean_ctor_set_tag(v___x_2393_, 2);
lean_ctor_set(v___x_2393_, 0, v___x_2398_);
v___x_2400_ = v___x_2393_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v___x_2398_);
v___x_2400_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
uint8_t v___x_2401_; lean_object* v___x_2402_; 
v___x_2401_ = 0;
v___x_2402_ = l_Lean_addDecl(v___x_2400_, v___x_2401_, v___y_2383_, v___y_2384_);
return v___x_2402_;
}
}
}
else
{
lean_object* v_a_2405_; lean_object* v___x_2407_; uint8_t v_isShared_2408_; uint8_t v_isSharedCheck_2412_; 
lean_dec(v_levelParams_2379_);
lean_dec(v_name_2378_);
lean_dec_ref(v_val_2377_);
v_a_2405_ = lean_ctor_get(v___x_2386_, 0);
v_isSharedCheck_2412_ = !lean_is_exclusive(v___x_2386_);
if (v_isSharedCheck_2412_ == 0)
{
v___x_2407_ = v___x_2386_;
v_isShared_2408_ = v_isSharedCheck_2412_;
goto v_resetjp_2406_;
}
else
{
lean_inc(v_a_2405_);
lean_dec(v___x_2386_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2___boxed(lean_object* v_name_2413_, lean_object* v_val_2414_, lean_object* v_name_2415_, lean_object* v_levelParams_2416_, lean_object* v_____r_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_){
_start:
{
lean_object* v_res_2423_; 
v_res_2423_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(v_name_2413_, v_val_2414_, v_name_2415_, v_levelParams_2416_, v_____r_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
return v_res_2423_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3_spec__4(size_t v_sz_2424_, size_t v_i_2425_, lean_object* v_bs_2426_){
_start:
{
uint8_t v___x_2427_; 
v___x_2427_ = lean_usize_dec_lt(v_i_2425_, v_sz_2424_);
if (v___x_2427_ == 0)
{
return v_bs_2426_;
}
else
{
lean_object* v_v_2428_; lean_object* v_msg_2429_; lean_object* v___x_2430_; lean_object* v_bs_x27_2431_; size_t v___x_2432_; size_t v___x_2433_; lean_object* v___x_2434_; 
v_v_2428_ = lean_array_uget_borrowed(v_bs_2426_, v_i_2425_);
v_msg_2429_ = lean_ctor_get(v_v_2428_, 1);
lean_inc_ref(v_msg_2429_);
v___x_2430_ = lean_unsigned_to_nat(0u);
v_bs_x27_2431_ = lean_array_uset(v_bs_2426_, v_i_2425_, v___x_2430_);
v___x_2432_ = ((size_t)1ULL);
v___x_2433_ = lean_usize_add(v_i_2425_, v___x_2432_);
v___x_2434_ = lean_array_uset(v_bs_x27_2431_, v_i_2425_, v_msg_2429_);
v_i_2425_ = v___x_2433_;
v_bs_2426_ = v___x_2434_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_2436_, lean_object* v_i_2437_, lean_object* v_bs_2438_){
_start:
{
size_t v_sz_boxed_2439_; size_t v_i_boxed_2440_; lean_object* v_res_2441_; 
v_sz_boxed_2439_ = lean_unbox_usize(v_sz_2436_);
lean_dec(v_sz_2436_);
v_i_boxed_2440_ = lean_unbox_usize(v_i_2437_);
lean_dec(v_i_2437_);
v_res_2441_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3_spec__4(v_sz_boxed_2439_, v_i_boxed_2440_, v_bs_2438_);
return v_res_2441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(lean_object* v_oldTraces_2442_, lean_object* v_data_2443_, lean_object* v_ref_2444_, lean_object* v_msg_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_){
_start:
{
lean_object* v_toCold_2451_; lean_object* v_currRecDepth_2452_; lean_object* v_ref_2453_; uint8_t v_diag_2454_; uint8_t v_suppressElabErrors_2455_; lean_object* v___x_2456_; lean_object* v_traceState_2457_; lean_object* v_traces_2458_; lean_object* v_ref_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; size_t v_sz_2462_; size_t v___x_2463_; lean_object* v___x_2464_; lean_object* v_msg_2465_; lean_object* v___x_2466_; lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2504_; 
v_toCold_2451_ = lean_ctor_get(v___y_2448_, 0);
v_currRecDepth_2452_ = lean_ctor_get(v___y_2448_, 1);
v_ref_2453_ = lean_ctor_get(v___y_2448_, 2);
v_diag_2454_ = lean_ctor_get_uint8(v___y_2448_, sizeof(void*)*3);
v_suppressElabErrors_2455_ = lean_ctor_get_uint8(v___y_2448_, sizeof(void*)*3 + 1);
v___x_2456_ = lean_st_ref_get(v___y_2449_);
v_traceState_2457_ = lean_ctor_get(v___x_2456_, 4);
lean_inc_ref(v_traceState_2457_);
lean_dec(v___x_2456_);
v_traces_2458_ = lean_ctor_get(v_traceState_2457_, 0);
lean_inc_ref(v_traces_2458_);
lean_dec_ref(v_traceState_2457_);
v_ref_2459_ = l_Lean_replaceRef(v_ref_2444_, v_ref_2453_);
lean_inc(v_currRecDepth_2452_);
lean_inc_ref(v_toCold_2451_);
v___x_2460_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2460_, 0, v_toCold_2451_);
lean_ctor_set(v___x_2460_, 1, v_currRecDepth_2452_);
lean_ctor_set(v___x_2460_, 2, v_ref_2459_);
lean_ctor_set_uint8(v___x_2460_, sizeof(void*)*3, v_diag_2454_);
lean_ctor_set_uint8(v___x_2460_, sizeof(void*)*3 + 1, v_suppressElabErrors_2455_);
v___x_2461_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2458_);
lean_dec_ref(v_traces_2458_);
v_sz_2462_ = lean_array_size(v___x_2461_);
v___x_2463_ = ((size_t)0ULL);
v___x_2464_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3_spec__4(v_sz_2462_, v___x_2463_, v___x_2461_);
v_msg_2465_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2465_, 0, v_data_2443_);
lean_ctor_set(v_msg_2465_, 1, v_msg_2445_);
lean_ctor_set(v_msg_2465_, 2, v___x_2464_);
v___x_2466_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msg_2465_, v___y_2446_, v___y_2447_, v___x_2460_, v___y_2449_);
lean_dec_ref_known(v___x_2460_, 3);
v_a_2467_ = lean_ctor_get(v___x_2466_, 0);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2469_ = v___x_2466_;
v_isShared_2470_ = v_isSharedCheck_2504_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___x_2466_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2504_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2471_; lean_object* v_traceState_2472_; lean_object* v_env_2473_; lean_object* v_nextMacroScope_2474_; lean_object* v_ngen_2475_; lean_object* v_auxDeclNGen_2476_; lean_object* v_cache_2477_; lean_object* v_messages_2478_; lean_object* v_infoState_2479_; lean_object* v_snapshotTasks_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2503_; 
v___x_2471_ = lean_st_ref_take(v___y_2449_);
v_traceState_2472_ = lean_ctor_get(v___x_2471_, 4);
v_env_2473_ = lean_ctor_get(v___x_2471_, 0);
v_nextMacroScope_2474_ = lean_ctor_get(v___x_2471_, 1);
v_ngen_2475_ = lean_ctor_get(v___x_2471_, 2);
v_auxDeclNGen_2476_ = lean_ctor_get(v___x_2471_, 3);
v_cache_2477_ = lean_ctor_get(v___x_2471_, 5);
v_messages_2478_ = lean_ctor_get(v___x_2471_, 6);
v_infoState_2479_ = lean_ctor_get(v___x_2471_, 7);
v_snapshotTasks_2480_ = lean_ctor_get(v___x_2471_, 8);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2471_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2482_ = v___x_2471_;
v_isShared_2483_ = v_isSharedCheck_2503_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_snapshotTasks_2480_);
lean_inc(v_infoState_2479_);
lean_inc(v_messages_2478_);
lean_inc(v_cache_2477_);
lean_inc(v_traceState_2472_);
lean_inc(v_auxDeclNGen_2476_);
lean_inc(v_ngen_2475_);
lean_inc(v_nextMacroScope_2474_);
lean_inc(v_env_2473_);
lean_dec(v___x_2471_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2503_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
uint64_t v_tid_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2501_; 
v_tid_2484_ = lean_ctor_get_uint64(v_traceState_2472_, sizeof(void*)*1);
v_isSharedCheck_2501_ = !lean_is_exclusive(v_traceState_2472_);
if (v_isSharedCheck_2501_ == 0)
{
lean_object* v_unused_2502_; 
v_unused_2502_ = lean_ctor_get(v_traceState_2472_, 0);
lean_dec(v_unused_2502_);
v___x_2486_ = v_traceState_2472_;
v_isShared_2487_ = v_isSharedCheck_2501_;
goto v_resetjp_2485_;
}
else
{
lean_dec(v_traceState_2472_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2501_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2491_; 
v___x_2488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2488_, 0, v_ref_2444_);
lean_ctor_set(v___x_2488_, 1, v_a_2467_);
v___x_2489_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2442_, v___x_2488_);
if (v_isShared_2487_ == 0)
{
lean_ctor_set(v___x_2486_, 0, v___x_2489_);
v___x_2491_ = v___x_2486_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v___x_2489_);
lean_ctor_set_uint64(v_reuseFailAlloc_2500_, sizeof(void*)*1, v_tid_2484_);
v___x_2491_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
lean_object* v___x_2493_; 
if (v_isShared_2483_ == 0)
{
lean_ctor_set(v___x_2482_, 4, v___x_2491_);
v___x_2493_ = v___x_2482_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v_env_2473_);
lean_ctor_set(v_reuseFailAlloc_2499_, 1, v_nextMacroScope_2474_);
lean_ctor_set(v_reuseFailAlloc_2499_, 2, v_ngen_2475_);
lean_ctor_set(v_reuseFailAlloc_2499_, 3, v_auxDeclNGen_2476_);
lean_ctor_set(v_reuseFailAlloc_2499_, 4, v___x_2491_);
lean_ctor_set(v_reuseFailAlloc_2499_, 5, v_cache_2477_);
lean_ctor_set(v_reuseFailAlloc_2499_, 6, v_messages_2478_);
lean_ctor_set(v_reuseFailAlloc_2499_, 7, v_infoState_2479_);
lean_ctor_set(v_reuseFailAlloc_2499_, 8, v_snapshotTasks_2480_);
v___x_2493_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2497_; 
v___x_2494_ = lean_st_ref_put(v___y_2449_, v___x_2493_);
v___x_2495_ = lean_box(0);
if (v_isShared_2470_ == 0)
{
lean_ctor_set(v___x_2469_, 0, v___x_2495_);
v___x_2497_ = v___x_2469_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v___x_2495_);
v___x_2497_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
return v___x_2497_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3___boxed(lean_object* v_oldTraces_2505_, lean_object* v_data_2506_, lean_object* v_ref_2507_, lean_object* v_msg_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(v_oldTraces_2505_, v_data_2506_, v_ref_2507_, v_msg_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_);
lean_dec(v___y_2512_);
lean_dec_ref(v___y_2511_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(lean_object* v_opts_2515_, lean_object* v_opt_2516_){
_start:
{
lean_object* v_name_2517_; lean_object* v_defValue_2518_; lean_object* v_map_2519_; lean_object* v___x_2520_; 
v_name_2517_ = lean_ctor_get(v_opt_2516_, 0);
v_defValue_2518_ = lean_ctor_get(v_opt_2516_, 1);
v_map_2519_ = lean_ctor_get(v_opts_2515_, 0);
v___x_2520_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2519_, v_name_2517_);
if (lean_obj_tag(v___x_2520_) == 0)
{
lean_inc(v_defValue_2518_);
return v_defValue_2518_;
}
else
{
lean_object* v_val_2521_; 
v_val_2521_ = lean_ctor_get(v___x_2520_, 0);
lean_inc(v_val_2521_);
lean_dec_ref_known(v___x_2520_, 1);
if (lean_obj_tag(v_val_2521_) == 3)
{
lean_object* v_v_2522_; 
v_v_2522_ = lean_ctor_get(v_val_2521_, 0);
lean_inc(v_v_2522_);
lean_dec_ref_known(v_val_2521_, 1);
return v_v_2522_;
}
else
{
lean_dec(v_val_2521_);
lean_inc(v_defValue_2518_);
return v_defValue_2518_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6___boxed(lean_object* v_opts_2523_, lean_object* v_opt_2524_){
_start:
{
lean_object* v_res_2525_; 
v_res_2525_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(v_opts_2523_, v_opt_2524_);
lean_dec_ref(v_opt_2524_);
lean_dec_ref(v_opts_2523_);
return v_res_2525_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5(lean_object* v_e_2526_){
_start:
{
if (lean_obj_tag(v_e_2526_) == 0)
{
uint8_t v___x_2527_; 
v___x_2527_ = 2;
return v___x_2527_;
}
else
{
uint8_t v___x_2528_; 
v___x_2528_ = 0;
return v___x_2528_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___boxed(lean_object* v_e_2529_){
_start:
{
uint8_t v_res_2530_; lean_object* v_r_2531_; 
v_res_2530_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5(v_e_2529_);
lean_dec_ref(v_e_2529_);
v_r_2531_ = lean_box(v_res_2530_);
return v_r_2531_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg(lean_object* v_x_2532_){
_start:
{
if (lean_obj_tag(v_x_2532_) == 0)
{
lean_object* v_a_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2541_; 
v_a_2534_ = lean_ctor_get(v_x_2532_, 0);
v_isSharedCheck_2541_ = !lean_is_exclusive(v_x_2532_);
if (v_isSharedCheck_2541_ == 0)
{
v___x_2536_ = v_x_2532_;
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_a_2534_);
lean_dec(v_x_2532_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v___x_2539_; 
if (v_isShared_2537_ == 0)
{
lean_ctor_set_tag(v___x_2536_, 1);
v___x_2539_ = v___x_2536_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_a_2534_);
v___x_2539_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
return v___x_2539_;
}
}
}
else
{
lean_object* v_a_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2549_; 
v_a_2542_ = lean_ctor_get(v_x_2532_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v_x_2532_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2544_ = v_x_2532_;
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_a_2542_);
lean_dec(v_x_2532_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v___x_2547_; 
if (v_isShared_2545_ == 0)
{
lean_ctor_set_tag(v___x_2544_, 0);
v___x_2547_ = v___x_2544_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_a_2542_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg___boxed(lean_object* v_x_2550_, lean_object* v___y_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg(v_x_2550_);
return v_res_2552_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2554_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__0));
v___x_2555_ = l_Lean_stringToMessageData(v___x_2554_);
return v___x_2555_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2556_; double v___x_2557_; 
v___x_2556_ = lean_unsigned_to_nat(1000u);
v___x_2557_ = lean_float_of_nat(v___x_2556_);
return v___x_2557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(lean_object* v_cls_2558_, uint8_t v_collapsed_2559_, lean_object* v_tag_2560_, lean_object* v_opts_2561_, uint8_t v_clsEnabled_2562_, lean_object* v_oldTraces_2563_, lean_object* v_msg_2564_, lean_object* v_resStartStop_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_){
_start:
{
lean_object* v_fst_2571_; lean_object* v_snd_2572_; lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v_data_2576_; lean_object* v_fst_2579_; lean_object* v_snd_2580_; lean_object* v___x_2581_; uint8_t v___x_2582_; lean_object* v___y_2584_; lean_object* v_a_2585_; uint8_t v___y_2600_; double v___y_2631_; 
v_fst_2571_ = lean_ctor_get(v_resStartStop_2565_, 0);
lean_inc(v_fst_2571_);
v_snd_2572_ = lean_ctor_get(v_resStartStop_2565_, 1);
lean_inc(v_snd_2572_);
lean_dec_ref(v_resStartStop_2565_);
v_fst_2579_ = lean_ctor_get(v_snd_2572_, 0);
lean_inc(v_fst_2579_);
v_snd_2580_ = lean_ctor_get(v_snd_2572_, 1);
lean_inc(v_snd_2580_);
lean_dec(v_snd_2572_);
v___x_2581_ = l_Lean_trace_profiler;
v___x_2582_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_opts_2561_, v___x_2581_);
if (v___x_2582_ == 0)
{
v___y_2600_ = v___x_2582_;
goto v___jp_2599_;
}
else
{
lean_object* v___x_2636_; uint8_t v___x_2637_; 
v___x_2636_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2637_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_opts_2561_, v___x_2636_);
if (v___x_2637_ == 0)
{
lean_object* v___x_2638_; lean_object* v___x_2639_; double v___x_2640_; double v___x_2641_; double v___x_2642_; 
v___x_2638_ = l_Lean_trace_profiler_threshold;
v___x_2639_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(v_opts_2561_, v___x_2638_);
v___x_2640_ = lean_float_of_nat(v___x_2639_);
v___x_2641_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2);
v___x_2642_ = lean_float_div(v___x_2640_, v___x_2641_);
v___y_2631_ = v___x_2642_;
goto v___jp_2630_;
}
else
{
lean_object* v___x_2643_; lean_object* v___x_2644_; double v___x_2645_; 
v___x_2643_ = l_Lean_trace_profiler_threshold;
v___x_2644_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(v_opts_2561_, v___x_2643_);
v___x_2645_ = lean_float_of_nat(v___x_2644_);
v___y_2631_ = v___x_2645_;
goto v___jp_2630_;
}
}
v___jp_2573_:
{
lean_object* v___x_2577_; 
lean_inc(v___y_2575_);
v___x_2577_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(v_oldTraces_2563_, v_data_2576_, v___y_2575_, v___y_2574_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_);
if (lean_obj_tag(v___x_2577_) == 0)
{
lean_object* v___x_2578_; 
lean_dec_ref_known(v___x_2577_, 1);
v___x_2578_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg(v_fst_2571_);
return v___x_2578_;
}
else
{
lean_dec(v_fst_2571_);
return v___x_2577_;
}
}
v___jp_2583_:
{
uint8_t v_result_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; double v___x_2589_; lean_object* v_data_2590_; 
v_result_2586_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5(v_fst_2571_);
v___x_2587_ = lean_box(v_result_2586_);
v___x_2588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2588_, 0, v___x_2587_);
v___x_2589_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0);
lean_inc_ref(v_tag_2560_);
lean_inc_ref(v___x_2588_);
lean_inc(v_cls_2558_);
v_data_2590_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2590_, 0, v_cls_2558_);
lean_ctor_set(v_data_2590_, 1, v___x_2588_);
lean_ctor_set(v_data_2590_, 2, v_tag_2560_);
lean_ctor_set_float(v_data_2590_, sizeof(void*)*3, v___x_2589_);
lean_ctor_set_float(v_data_2590_, sizeof(void*)*3 + 8, v___x_2589_);
lean_ctor_set_uint8(v_data_2590_, sizeof(void*)*3 + 16, v_collapsed_2559_);
if (v___x_2582_ == 0)
{
lean_dec_ref_known(v___x_2588_, 1);
lean_dec(v_snd_2580_);
lean_dec(v_fst_2579_);
lean_dec_ref(v_tag_2560_);
lean_dec(v_cls_2558_);
v___y_2574_ = v_a_2585_;
v___y_2575_ = v___y_2584_;
v_data_2576_ = v_data_2590_;
goto v___jp_2573_;
}
else
{
lean_object* v_data_2591_; double v___x_2592_; double v___x_2593_; 
lean_dec_ref_known(v_data_2590_, 3);
v_data_2591_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2591_, 0, v_cls_2558_);
lean_ctor_set(v_data_2591_, 1, v___x_2588_);
lean_ctor_set(v_data_2591_, 2, v_tag_2560_);
v___x_2592_ = lean_unbox_float(v_fst_2579_);
lean_dec(v_fst_2579_);
lean_ctor_set_float(v_data_2591_, sizeof(void*)*3, v___x_2592_);
v___x_2593_ = lean_unbox_float(v_snd_2580_);
lean_dec(v_snd_2580_);
lean_ctor_set_float(v_data_2591_, sizeof(void*)*3 + 8, v___x_2593_);
lean_ctor_set_uint8(v_data_2591_, sizeof(void*)*3 + 16, v_collapsed_2559_);
v___y_2574_ = v_a_2585_;
v___y_2575_ = v___y_2584_;
v_data_2576_ = v_data_2591_;
goto v___jp_2573_;
}
}
v___jp_2594_:
{
lean_object* v_ref_2595_; lean_object* v___x_2596_; 
v_ref_2595_ = lean_ctor_get(v___y_2568_, 2);
lean_inc(v___y_2569_);
lean_inc_ref(v___y_2568_);
lean_inc(v___y_2567_);
lean_inc_ref(v___y_2566_);
lean_inc(v_fst_2571_);
v___x_2596_ = lean_apply_6(v_msg_2564_, v_fst_2571_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, lean_box(0));
if (lean_obj_tag(v___x_2596_) == 0)
{
lean_object* v_a_2597_; 
v_a_2597_ = lean_ctor_get(v___x_2596_, 0);
lean_inc(v_a_2597_);
lean_dec_ref_known(v___x_2596_, 1);
v___y_2584_ = v_ref_2595_;
v_a_2585_ = v_a_2597_;
goto v___jp_2583_;
}
else
{
lean_object* v___x_2598_; 
lean_dec_ref_known(v___x_2596_, 1);
v___x_2598_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1);
v___y_2584_ = v_ref_2595_;
v_a_2585_ = v___x_2598_;
goto v___jp_2583_;
}
}
v___jp_2599_:
{
if (v_clsEnabled_2562_ == 0)
{
if (v___y_2600_ == 0)
{
lean_object* v___x_2601_; lean_object* v_traceState_2602_; lean_object* v_env_2603_; lean_object* v_nextMacroScope_2604_; lean_object* v_ngen_2605_; lean_object* v_auxDeclNGen_2606_; lean_object* v_cache_2607_; lean_object* v_messages_2608_; lean_object* v_infoState_2609_; lean_object* v_snapshotTasks_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2629_; 
lean_dec(v_snd_2580_);
lean_dec(v_fst_2579_);
lean_dec_ref(v_msg_2564_);
lean_dec_ref(v_tag_2560_);
lean_dec(v_cls_2558_);
v___x_2601_ = lean_st_ref_take(v___y_2569_);
v_traceState_2602_ = lean_ctor_get(v___x_2601_, 4);
v_env_2603_ = lean_ctor_get(v___x_2601_, 0);
v_nextMacroScope_2604_ = lean_ctor_get(v___x_2601_, 1);
v_ngen_2605_ = lean_ctor_get(v___x_2601_, 2);
v_auxDeclNGen_2606_ = lean_ctor_get(v___x_2601_, 3);
v_cache_2607_ = lean_ctor_get(v___x_2601_, 5);
v_messages_2608_ = lean_ctor_get(v___x_2601_, 6);
v_infoState_2609_ = lean_ctor_get(v___x_2601_, 7);
v_snapshotTasks_2610_ = lean_ctor_get(v___x_2601_, 8);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2612_ = v___x_2601_;
v_isShared_2613_ = v_isSharedCheck_2629_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_snapshotTasks_2610_);
lean_inc(v_infoState_2609_);
lean_inc(v_messages_2608_);
lean_inc(v_cache_2607_);
lean_inc(v_traceState_2602_);
lean_inc(v_auxDeclNGen_2606_);
lean_inc(v_ngen_2605_);
lean_inc(v_nextMacroScope_2604_);
lean_inc(v_env_2603_);
lean_dec(v___x_2601_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2629_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
uint64_t v_tid_2614_; lean_object* v_traces_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2628_; 
v_tid_2614_ = lean_ctor_get_uint64(v_traceState_2602_, sizeof(void*)*1);
v_traces_2615_ = lean_ctor_get(v_traceState_2602_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v_traceState_2602_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2617_ = v_traceState_2602_;
v_isShared_2618_ = v_isSharedCheck_2628_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_traces_2615_);
lean_dec(v_traceState_2602_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2628_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2619_; lean_object* v___x_2621_; 
v___x_2619_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2563_, v_traces_2615_);
lean_dec_ref(v_traces_2615_);
if (v_isShared_2618_ == 0)
{
lean_ctor_set(v___x_2617_, 0, v___x_2619_);
v___x_2621_ = v___x_2617_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v___x_2619_);
lean_ctor_set_uint64(v_reuseFailAlloc_2627_, sizeof(void*)*1, v_tid_2614_);
v___x_2621_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
lean_object* v___x_2623_; 
if (v_isShared_2613_ == 0)
{
lean_ctor_set(v___x_2612_, 4, v___x_2621_);
v___x_2623_ = v___x_2612_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_env_2603_);
lean_ctor_set(v_reuseFailAlloc_2626_, 1, v_nextMacroScope_2604_);
lean_ctor_set(v_reuseFailAlloc_2626_, 2, v_ngen_2605_);
lean_ctor_set(v_reuseFailAlloc_2626_, 3, v_auxDeclNGen_2606_);
lean_ctor_set(v_reuseFailAlloc_2626_, 4, v___x_2621_);
lean_ctor_set(v_reuseFailAlloc_2626_, 5, v_cache_2607_);
lean_ctor_set(v_reuseFailAlloc_2626_, 6, v_messages_2608_);
lean_ctor_set(v_reuseFailAlloc_2626_, 7, v_infoState_2609_);
lean_ctor_set(v_reuseFailAlloc_2626_, 8, v_snapshotTasks_2610_);
v___x_2623_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2624_ = lean_st_ref_put(v___y_2569_, v___x_2623_);
v___x_2625_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg(v_fst_2571_);
return v___x_2625_;
}
}
}
}
}
else
{
goto v___jp_2594_;
}
}
else
{
goto v___jp_2594_;
}
}
v___jp_2630_:
{
double v___x_2632_; double v___x_2633_; double v___x_2634_; uint8_t v___x_2635_; 
v___x_2632_ = lean_unbox_float(v_snd_2580_);
v___x_2633_ = lean_unbox_float(v_fst_2579_);
v___x_2634_ = lean_float_sub(v___x_2632_, v___x_2633_);
v___x_2635_ = lean_float_decLt(v___y_2631_, v___x_2634_);
v___y_2600_ = v___x_2635_;
goto v___jp_2599_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___boxed(lean_object* v_cls_2646_, lean_object* v_collapsed_2647_, lean_object* v_tag_2648_, lean_object* v_opts_2649_, lean_object* v_clsEnabled_2650_, lean_object* v_oldTraces_2651_, lean_object* v_msg_2652_, lean_object* v_resStartStop_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_){
_start:
{
uint8_t v_collapsed_boxed_2659_; uint8_t v_clsEnabled_boxed_2660_; lean_object* v_res_2661_; 
v_collapsed_boxed_2659_ = lean_unbox(v_collapsed_2647_);
v_clsEnabled_boxed_2660_ = lean_unbox(v_clsEnabled_2650_);
v_res_2661_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_2646_, v_collapsed_boxed_2659_, v_tag_2648_, v_opts_2649_, v_clsEnabled_boxed_2660_, v_oldTraces_2651_, v_msg_2652_, v_resStartStop_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_);
lean_dec(v___y_2657_);
lean_dec_ref(v___y_2656_);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
lean_dec_ref(v_opts_2649_);
return v_res_2661_;
}
}
static double _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0(void){
_start:
{
lean_object* v___x_2662_; double v___x_2663_; 
v___x_2662_ = lean_unsigned_to_nat(1000000000u);
v___x_2663_ = lean_float_of_nat(v___x_2662_);
return v___x_2663_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2(void){
_start:
{
lean_object* v___x_2665_; lean_object* v___x_2666_; 
v___x_2665_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1));
v___x_2666_ = l_Lean_stringToMessageData(v___x_2665_);
return v___x_2666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(lean_object* v_ctorVal_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_){
_start:
{
lean_object* v_toConstantVal_2673_; lean_object* v_toCold_2674_; lean_object* v_options_2675_; lean_object* v_name_2676_; lean_object* v_levelParams_2677_; lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2888_; 
v_toConstantVal_2673_ = lean_ctor_get(v_ctorVal_2667_, 0);
lean_inc_ref(v_toConstantVal_2673_);
v_toCold_2674_ = lean_ctor_get(v_a_2670_, 0);
v_options_2675_ = lean_ctor_get(v_toCold_2674_, 2);
v_name_2676_ = lean_ctor_get(v_toConstantVal_2673_, 0);
v_levelParams_2677_ = lean_ctor_get(v_toConstantVal_2673_, 1);
v_isSharedCheck_2888_ = !lean_is_exclusive(v_toConstantVal_2673_);
if (v_isSharedCheck_2888_ == 0)
{
lean_object* v_unused_2889_; 
v_unused_2889_ = lean_ctor_get(v_toConstantVal_2673_, 2);
lean_dec(v_unused_2889_);
v___x_2679_ = v_toConstantVal_2673_;
v_isShared_2680_ = v_isSharedCheck_2888_;
goto v_resetjp_2678_;
}
else
{
lean_inc(v_levelParams_2677_);
lean_inc(v_name_2676_);
lean_dec(v_toConstantVal_2673_);
v___x_2679_ = lean_box(0);
v_isShared_2680_ = v_isSharedCheck_2888_;
goto v_resetjp_2678_;
}
v_resetjp_2678_:
{
lean_object* v_inheritedTraceOptions_2681_; uint8_t v_hasTrace_2682_; lean_object* v_name_2683_; 
v_inheritedTraceOptions_2681_ = lean_ctor_get(v_toCold_2674_, 11);
v_hasTrace_2682_ = lean_ctor_get_uint8(v_options_2675_, sizeof(void*)*1);
lean_inc(v_name_2676_);
v_name_2683_ = l_Lean_Meta_mkInjectiveTheoremNameFor(v_name_2676_);
if (v_hasTrace_2682_ == 0)
{
lean_object* v___x_2684_; 
v___x_2684_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_);
if (lean_obj_tag(v___x_2684_) == 0)
{
lean_object* v_a_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2722_; 
v_a_2685_ = lean_ctor_get(v___x_2684_, 0);
v_isSharedCheck_2722_ = !lean_is_exclusive(v___x_2684_);
if (v_isSharedCheck_2722_ == 0)
{
v___x_2687_ = v___x_2684_;
v_isShared_2688_ = v_isSharedCheck_2722_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_a_2685_);
lean_dec(v___x_2684_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2722_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
if (lean_obj_tag(v_a_2685_) == 1)
{
lean_object* v_val_2689_; lean_object* v___x_2690_; 
lean_del_object(v___x_2687_);
v_val_2689_ = lean_ctor_get(v_a_2685_, 0);
lean_inc_n(v_val_2689_, 2);
lean_dec_ref_known(v_a_2685_, 1);
v___x_2690_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2676_, v_val_2689_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_);
if (lean_obj_tag(v___x_2690_) == 0)
{
lean_object* v_a_2691_; lean_object* v___x_2692_; lean_object* v_a_2693_; lean_object* v___x_2694_; lean_object* v_a_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2709_; 
v_a_2691_ = lean_ctor_get(v___x_2690_, 0);
lean_inc(v_a_2691_);
lean_dec_ref_known(v___x_2690_, 1);
v___x_2692_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2689_, v_a_2669_);
v_a_2693_ = lean_ctor_get(v___x_2692_, 0);
lean_inc(v_a_2693_);
lean_dec_ref(v___x_2692_);
v___x_2694_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2691_, v_a_2669_);
v_a_2695_ = lean_ctor_get(v___x_2694_, 0);
v_isSharedCheck_2709_ = !lean_is_exclusive(v___x_2694_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2697_ = v___x_2694_;
v_isShared_2698_ = v_isSharedCheck_2709_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_a_2695_);
lean_dec(v___x_2694_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2709_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2700_; 
lean_inc(v_name_2683_);
if (v_isShared_2680_ == 0)
{
lean_ctor_set(v___x_2679_, 2, v_a_2693_);
lean_ctor_set(v___x_2679_, 0, v_name_2683_);
v___x_2700_ = v___x_2679_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v_name_2683_);
lean_ctor_set(v_reuseFailAlloc_2708_, 1, v_levelParams_2677_);
lean_ctor_set(v_reuseFailAlloc_2708_, 2, v_a_2693_);
v___x_2700_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2705_; 
v___x_2701_ = lean_box(0);
v___x_2702_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2702_, 0, v_name_2683_);
lean_ctor_set(v___x_2702_, 1, v___x_2701_);
v___x_2703_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2700_);
lean_ctor_set(v___x_2703_, 1, v_a_2695_);
lean_ctor_set(v___x_2703_, 2, v___x_2702_);
if (v_isShared_2698_ == 0)
{
lean_ctor_set_tag(v___x_2697_, 2);
lean_ctor_set(v___x_2697_, 0, v___x_2703_);
v___x_2705_ = v___x_2697_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v___x_2703_);
v___x_2705_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
lean_object* v___x_2706_; 
v___x_2706_ = l_Lean_addDecl(v___x_2705_, v_hasTrace_2682_, v_a_2670_, v_a_2671_);
return v___x_2706_;
}
}
}
}
else
{
lean_object* v_a_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2717_; 
lean_dec(v_val_2689_);
lean_dec(v_name_2683_);
lean_del_object(v___x_2679_);
lean_dec(v_levelParams_2677_);
v_a_2710_ = lean_ctor_get(v___x_2690_, 0);
v_isSharedCheck_2717_ = !lean_is_exclusive(v___x_2690_);
if (v_isSharedCheck_2717_ == 0)
{
v___x_2712_ = v___x_2690_;
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_a_2710_);
lean_dec(v___x_2690_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v___x_2715_; 
if (v_isShared_2713_ == 0)
{
v___x_2715_ = v___x_2712_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v_a_2710_);
v___x_2715_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
return v___x_2715_;
}
}
}
}
else
{
lean_object* v___x_2718_; lean_object* v___x_2720_; 
lean_dec(v_a_2685_);
lean_dec(v_name_2683_);
lean_del_object(v___x_2679_);
lean_dec(v_levelParams_2677_);
lean_dec(v_name_2676_);
v___x_2718_ = lean_box(0);
if (v_isShared_2688_ == 0)
{
lean_ctor_set(v___x_2687_, 0, v___x_2718_);
v___x_2720_ = v___x_2687_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v___x_2718_);
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
lean_dec(v_name_2683_);
lean_del_object(v___x_2679_);
lean_dec(v_levelParams_2677_);
lean_dec(v_name_2676_);
v_a_2723_ = lean_ctor_get(v___x_2684_, 0);
v_isSharedCheck_2730_ = !lean_is_exclusive(v___x_2684_);
if (v_isSharedCheck_2730_ == 0)
{
v___x_2725_ = v___x_2684_;
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_a_2723_);
lean_dec(v___x_2684_);
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
else
{
lean_object* v___f_2731_; lean_object* v_cls_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; uint8_t v___x_2735_; lean_object* v___y_2737_; lean_object* v___y_2738_; lean_object* v_a_2739_; lean_object* v___y_2749_; lean_object* v___y_2750_; lean_object* v_a_2751_; lean_object* v___y_2754_; lean_object* v___y_2755_; lean_object* v_a_2756_; lean_object* v___y_2759_; lean_object* v___y_2760_; lean_object* v___y_2761_; lean_object* v___y_2765_; lean_object* v___y_2766_; lean_object* v_a_2767_; lean_object* v___y_2780_; lean_object* v___y_2781_; lean_object* v_a_2782_; lean_object* v___y_2785_; lean_object* v___y_2786_; lean_object* v_a_2787_; lean_object* v___y_2790_; lean_object* v___y_2791_; lean_object* v___y_2792_; 
lean_inc(v_name_2683_);
v___f_2731_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2731_, 0, v_name_2683_);
v_cls_2732_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_2733_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_2734_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_2735_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2681_, v_options_2675_, v___x_2734_);
if (v___x_2735_ == 0)
{
lean_object* v___x_2830_; uint8_t v___x_2831_; 
v___x_2830_ = l_Lean_trace_profiler;
v___x_2831_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_2675_, v___x_2830_);
if (v___x_2831_ == 0)
{
lean_object* v___x_2832_; 
lean_dec_ref(v___f_2731_);
v___x_2832_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_);
if (lean_obj_tag(v___x_2832_) == 0)
{
lean_object* v_a_2833_; lean_object* v___x_2835_; uint8_t v_isShared_2836_; uint8_t v_isSharedCheck_2879_; 
v_a_2833_ = lean_ctor_get(v___x_2832_, 0);
v_isSharedCheck_2879_ = !lean_is_exclusive(v___x_2832_);
if (v_isSharedCheck_2879_ == 0)
{
v___x_2835_ = v___x_2832_;
v_isShared_2836_ = v_isSharedCheck_2879_;
goto v_resetjp_2834_;
}
else
{
lean_inc(v_a_2833_);
lean_dec(v___x_2832_);
v___x_2835_ = lean_box(0);
v_isShared_2836_ = v_isSharedCheck_2879_;
goto v_resetjp_2834_;
}
v_resetjp_2834_:
{
if (lean_obj_tag(v_a_2833_) == 1)
{
lean_object* v_val_2837_; lean_object* v___y_2839_; lean_object* v___y_2840_; lean_object* v___y_2841_; lean_object* v___y_2842_; 
lean_del_object(v___x_2835_);
v_val_2837_ = lean_ctor_get(v_a_2833_, 0);
lean_inc(v_val_2837_);
lean_dec_ref_known(v_a_2833_, 1);
if (v___x_2735_ == 0)
{
v___y_2839_ = v_a_2668_;
v___y_2840_ = v_a_2669_;
v___y_2841_ = v_a_2670_;
v___y_2842_ = v_a_2671_;
goto v___jp_2838_;
}
else
{
lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; 
v___x_2871_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
lean_inc(v_val_2837_);
v___x_2872_ = l_Lean_MessageData_ofExpr(v_val_2837_);
v___x_2873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2873_, 0, v___x_2871_);
lean_ctor_set(v___x_2873_, 1, v___x_2872_);
v___x_2874_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2732_, v___x_2873_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_);
if (lean_obj_tag(v___x_2874_) == 0)
{
lean_dec_ref_known(v___x_2874_, 1);
v___y_2839_ = v_a_2668_;
v___y_2840_ = v_a_2669_;
v___y_2841_ = v_a_2670_;
v___y_2842_ = v_a_2671_;
goto v___jp_2838_;
}
else
{
lean_dec(v_val_2837_);
lean_dec(v_name_2683_);
lean_del_object(v___x_2679_);
lean_dec(v_levelParams_2677_);
lean_dec(v_name_2676_);
return v___x_2874_;
}
}
v___jp_2838_:
{
lean_object* v___x_2843_; 
lean_inc(v_val_2837_);
v___x_2843_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2676_, v_val_2837_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_);
if (lean_obj_tag(v___x_2843_) == 0)
{
lean_object* v_a_2844_; lean_object* v___x_2845_; lean_object* v_a_2846_; lean_object* v___x_2847_; lean_object* v_a_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2862_; 
v_a_2844_ = lean_ctor_get(v___x_2843_, 0);
lean_inc(v_a_2844_);
lean_dec_ref_known(v___x_2843_, 1);
v___x_2845_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2837_, v___y_2840_);
v_a_2846_ = lean_ctor_get(v___x_2845_, 0);
lean_inc(v_a_2846_);
lean_dec_ref(v___x_2845_);
v___x_2847_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2844_, v___y_2840_);
v_a_2848_ = lean_ctor_get(v___x_2847_, 0);
v_isSharedCheck_2862_ = !lean_is_exclusive(v___x_2847_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2850_ = v___x_2847_;
v_isShared_2851_ = v_isSharedCheck_2862_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_a_2848_);
lean_dec(v___x_2847_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2862_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2853_; 
lean_inc(v_name_2683_);
if (v_isShared_2680_ == 0)
{
lean_ctor_set(v___x_2679_, 2, v_a_2846_);
lean_ctor_set(v___x_2679_, 0, v_name_2683_);
v___x_2853_ = v___x_2679_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v_name_2683_);
lean_ctor_set(v_reuseFailAlloc_2861_, 1, v_levelParams_2677_);
lean_ctor_set(v_reuseFailAlloc_2861_, 2, v_a_2846_);
v___x_2853_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2858_; 
v___x_2854_ = lean_box(0);
v___x_2855_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2855_, 0, v_name_2683_);
lean_ctor_set(v___x_2855_, 1, v___x_2854_);
v___x_2856_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2856_, 0, v___x_2853_);
lean_ctor_set(v___x_2856_, 1, v_a_2848_);
lean_ctor_set(v___x_2856_, 2, v___x_2855_);
if (v_isShared_2851_ == 0)
{
lean_ctor_set_tag(v___x_2850_, 2);
lean_ctor_set(v___x_2850_, 0, v___x_2856_);
v___x_2858_ = v___x_2850_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v___x_2856_);
v___x_2858_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
lean_object* v___x_2859_; 
v___x_2859_ = l_Lean_addDecl(v___x_2858_, v___x_2831_, v___y_2841_, v___y_2842_);
return v___x_2859_;
}
}
}
}
else
{
lean_object* v_a_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2870_; 
lean_dec(v_val_2837_);
lean_dec(v_name_2683_);
lean_del_object(v___x_2679_);
lean_dec(v_levelParams_2677_);
v_a_2863_ = lean_ctor_get(v___x_2843_, 0);
v_isSharedCheck_2870_ = !lean_is_exclusive(v___x_2843_);
if (v_isSharedCheck_2870_ == 0)
{
v___x_2865_ = v___x_2843_;
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_a_2863_);
lean_dec(v___x_2843_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2868_; 
if (v_isShared_2866_ == 0)
{
v___x_2868_ = v___x_2865_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v_a_2863_);
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
}
else
{
lean_object* v___x_2875_; lean_object* v___x_2877_; 
lean_dec(v_a_2833_);
lean_dec(v_name_2683_);
lean_del_object(v___x_2679_);
lean_dec(v_levelParams_2677_);
lean_dec(v_name_2676_);
v___x_2875_ = lean_box(0);
if (v_isShared_2836_ == 0)
{
lean_ctor_set(v___x_2835_, 0, v___x_2875_);
v___x_2877_ = v___x_2835_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v___x_2875_);
v___x_2877_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
return v___x_2877_;
}
}
}
}
else
{
lean_object* v_a_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2887_; 
lean_dec(v_name_2683_);
lean_del_object(v___x_2679_);
lean_dec(v_levelParams_2677_);
lean_dec(v_name_2676_);
v_a_2880_ = lean_ctor_get(v___x_2832_, 0);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2832_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2882_ = v___x_2832_;
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_a_2880_);
lean_dec(v___x_2832_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
lean_object* v___x_2885_; 
if (v_isShared_2883_ == 0)
{
v___x_2885_ = v___x_2882_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_a_2880_);
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
lean_del_object(v___x_2679_);
goto v___jp_2795_;
}
}
else
{
lean_del_object(v___x_2679_);
goto v___jp_2795_;
}
v___jp_2736_:
{
lean_object* v___x_2740_; double v___x_2741_; double v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; 
v___x_2740_ = lean_io_get_num_heartbeats();
v___x_2741_ = lean_float_of_nat(v___y_2737_);
v___x_2742_ = lean_float_of_nat(v___x_2740_);
v___x_2743_ = lean_box_float(v___x_2741_);
v___x_2744_ = lean_box_float(v___x_2742_);
v___x_2745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2743_);
lean_ctor_set(v___x_2745_, 1, v___x_2744_);
v___x_2746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2746_, 0, v_a_2739_);
lean_ctor_set(v___x_2746_, 1, v___x_2745_);
v___x_2747_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_2732_, v_hasTrace_2682_, v___x_2733_, v_options_2675_, v___x_2735_, v___y_2738_, v___f_2731_, v___x_2746_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_);
return v___x_2747_;
}
v___jp_2748_:
{
lean_object* v___x_2752_; 
v___x_2752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2752_, 0, v_a_2751_);
v___y_2737_ = v___y_2749_;
v___y_2738_ = v___y_2750_;
v_a_2739_ = v___x_2752_;
goto v___jp_2736_;
}
v___jp_2753_:
{
lean_object* v___x_2757_; 
v___x_2757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2757_, 0, v_a_2756_);
v___y_2737_ = v___y_2754_;
v___y_2738_ = v___y_2755_;
v_a_2739_ = v___x_2757_;
goto v___jp_2736_;
}
v___jp_2758_:
{
if (lean_obj_tag(v___y_2761_) == 0)
{
lean_object* v_a_2762_; 
v_a_2762_ = lean_ctor_get(v___y_2761_, 0);
lean_inc(v_a_2762_);
lean_dec_ref_known(v___y_2761_, 1);
v___y_2754_ = v___y_2759_;
v___y_2755_ = v___y_2760_;
v_a_2756_ = v_a_2762_;
goto v___jp_2753_;
}
else
{
lean_object* v_a_2763_; 
v_a_2763_ = lean_ctor_get(v___y_2761_, 0);
lean_inc(v_a_2763_);
lean_dec_ref_known(v___y_2761_, 1);
v___y_2749_ = v___y_2759_;
v___y_2750_ = v___y_2760_;
v_a_2751_ = v_a_2763_;
goto v___jp_2748_;
}
}
v___jp_2764_:
{
lean_object* v___x_2768_; double v___x_2769_; double v___x_2770_; double v___x_2771_; double v___x_2772_; double v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; 
v___x_2768_ = lean_io_mono_nanos_now();
v___x_2769_ = lean_float_of_nat(v___y_2766_);
v___x_2770_ = lean_float_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0);
v___x_2771_ = lean_float_div(v___x_2769_, v___x_2770_);
v___x_2772_ = lean_float_of_nat(v___x_2768_);
v___x_2773_ = lean_float_div(v___x_2772_, v___x_2770_);
v___x_2774_ = lean_box_float(v___x_2771_);
v___x_2775_ = lean_box_float(v___x_2773_);
v___x_2776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2776_, 0, v___x_2774_);
lean_ctor_set(v___x_2776_, 1, v___x_2775_);
v___x_2777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2777_, 0, v_a_2767_);
lean_ctor_set(v___x_2777_, 1, v___x_2776_);
v___x_2778_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_2732_, v_hasTrace_2682_, v___x_2733_, v_options_2675_, v___x_2735_, v___y_2765_, v___f_2731_, v___x_2777_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_);
return v___x_2778_;
}
v___jp_2779_:
{
lean_object* v___x_2783_; 
v___x_2783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2783_, 0, v_a_2782_);
v___y_2765_ = v___y_2781_;
v___y_2766_ = v___y_2780_;
v_a_2767_ = v___x_2783_;
goto v___jp_2764_;
}
v___jp_2784_:
{
lean_object* v___x_2788_; 
v___x_2788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2788_, 0, v_a_2787_);
v___y_2765_ = v___y_2786_;
v___y_2766_ = v___y_2785_;
v_a_2767_ = v___x_2788_;
goto v___jp_2764_;
}
v___jp_2789_:
{
if (lean_obj_tag(v___y_2792_) == 0)
{
lean_object* v_a_2793_; 
v_a_2793_ = lean_ctor_get(v___y_2792_, 0);
lean_inc(v_a_2793_);
lean_dec_ref_known(v___y_2792_, 1);
v___y_2780_ = v___y_2791_;
v___y_2781_ = v___y_2790_;
v_a_2782_ = v_a_2793_;
goto v___jp_2779_;
}
else
{
lean_object* v_a_2794_; 
v_a_2794_ = lean_ctor_get(v___y_2792_, 0);
lean_inc(v_a_2794_);
lean_dec_ref_known(v___y_2792_, 1);
v___y_2785_ = v___y_2791_;
v___y_2786_ = v___y_2790_;
v_a_2787_ = v_a_2794_;
goto v___jp_2784_;
}
}
v___jp_2795_:
{
lean_object* v___x_2796_; lean_object* v_a_2797_; lean_object* v___x_2798_; uint8_t v___x_2799_; 
v___x_2796_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v_a_2671_);
v_a_2797_ = lean_ctor_get(v___x_2796_, 0);
lean_inc(v_a_2797_);
lean_dec_ref(v___x_2796_);
v___x_2798_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2799_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_2675_, v___x_2798_);
if (v___x_2799_ == 0)
{
lean_object* v___x_2800_; lean_object* v___x_2801_; 
v___x_2800_ = lean_io_mono_nanos_now();
v___x_2801_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_);
if (lean_obj_tag(v___x_2801_) == 0)
{
lean_object* v_a_2802_; 
v_a_2802_ = lean_ctor_get(v___x_2801_, 0);
lean_inc(v_a_2802_);
lean_dec_ref_known(v___x_2801_, 1);
if (lean_obj_tag(v_a_2802_) == 1)
{
if (v___x_2735_ == 0)
{
lean_object* v_val_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; 
v_val_2803_ = lean_ctor_get(v_a_2802_, 0);
lean_inc(v_val_2803_);
lean_dec_ref_known(v_a_2802_, 1);
v___x_2804_ = lean_box(0);
v___x_2805_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(v_name_2676_, v_val_2803_, v_name_2683_, v_levelParams_2677_, v___x_2799_, v___x_2804_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_);
v___y_2790_ = v_a_2797_;
v___y_2791_ = v___x_2800_;
v___y_2792_ = v___x_2805_;
goto v___jp_2789_;
}
else
{
lean_object* v_val_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; 
v_val_2806_ = lean_ctor_get(v_a_2802_, 0);
lean_inc_n(v_val_2806_, 2);
lean_dec_ref_known(v_a_2802_, 1);
v___x_2807_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_2808_ = l_Lean_MessageData_ofExpr(v_val_2806_);
v___x_2809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2809_, 0, v___x_2807_);
lean_ctor_set(v___x_2809_, 1, v___x_2808_);
v___x_2810_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2732_, v___x_2809_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_);
if (lean_obj_tag(v___x_2810_) == 0)
{
lean_object* v_a_2811_; lean_object* v___x_2812_; 
v_a_2811_ = lean_ctor_get(v___x_2810_, 0);
lean_inc(v_a_2811_);
lean_dec_ref_known(v___x_2810_, 1);
v___x_2812_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(v_name_2676_, v_val_2806_, v_name_2683_, v_levelParams_2677_, v___x_2799_, v_a_2811_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_);
v___y_2790_ = v_a_2797_;
v___y_2791_ = v___x_2800_;
v___y_2792_ = v___x_2812_;
goto v___jp_2789_;
}
else
{
lean_dec(v_val_2806_);
lean_dec(v_name_2683_);
lean_dec(v_levelParams_2677_);
lean_dec(v_name_2676_);
v___y_2790_ = v_a_2797_;
v___y_2791_ = v___x_2800_;
v___y_2792_ = v___x_2810_;
goto v___jp_2789_;
}
}
}
else
{
lean_object* v___x_2813_; 
lean_dec(v_a_2802_);
lean_dec(v_name_2683_);
lean_dec(v_levelParams_2677_);
lean_dec(v_name_2676_);
v___x_2813_ = lean_box(0);
v___y_2780_ = v___x_2800_;
v___y_2781_ = v_a_2797_;
v_a_2782_ = v___x_2813_;
goto v___jp_2779_;
}
}
else
{
lean_object* v_a_2814_; 
lean_dec(v_name_2683_);
lean_dec(v_levelParams_2677_);
lean_dec(v_name_2676_);
v_a_2814_ = lean_ctor_get(v___x_2801_, 0);
lean_inc(v_a_2814_);
lean_dec_ref_known(v___x_2801_, 1);
v___y_2785_ = v___x_2800_;
v___y_2786_ = v_a_2797_;
v_a_2787_ = v_a_2814_;
goto v___jp_2784_;
}
}
else
{
lean_object* v___x_2815_; lean_object* v___x_2816_; 
v___x_2815_ = lean_io_get_num_heartbeats();
v___x_2816_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_);
if (lean_obj_tag(v___x_2816_) == 0)
{
lean_object* v_a_2817_; 
v_a_2817_ = lean_ctor_get(v___x_2816_, 0);
lean_inc(v_a_2817_);
lean_dec_ref_known(v___x_2816_, 1);
if (lean_obj_tag(v_a_2817_) == 1)
{
if (v___x_2735_ == 0)
{
lean_object* v_val_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; 
v_val_2818_ = lean_ctor_get(v_a_2817_, 0);
lean_inc(v_val_2818_);
lean_dec_ref_known(v_a_2817_, 1);
v___x_2819_ = lean_box(0);
v___x_2820_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(v_name_2676_, v_val_2818_, v_name_2683_, v_levelParams_2677_, v___x_2819_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_);
v___y_2759_ = v___x_2815_;
v___y_2760_ = v_a_2797_;
v___y_2761_ = v___x_2820_;
goto v___jp_2758_;
}
else
{
lean_object* v_val_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; 
v_val_2821_ = lean_ctor_get(v_a_2817_, 0);
lean_inc_n(v_val_2821_, 2);
lean_dec_ref_known(v_a_2817_, 1);
v___x_2822_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_2823_ = l_Lean_MessageData_ofExpr(v_val_2821_);
v___x_2824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2824_, 0, v___x_2822_);
lean_ctor_set(v___x_2824_, 1, v___x_2823_);
v___x_2825_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2732_, v___x_2824_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_);
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_object* v_a_2826_; lean_object* v___x_2827_; 
v_a_2826_ = lean_ctor_get(v___x_2825_, 0);
lean_inc(v_a_2826_);
lean_dec_ref_known(v___x_2825_, 1);
v___x_2827_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(v_name_2676_, v_val_2821_, v_name_2683_, v_levelParams_2677_, v_a_2826_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_);
v___y_2759_ = v___x_2815_;
v___y_2760_ = v_a_2797_;
v___y_2761_ = v___x_2827_;
goto v___jp_2758_;
}
else
{
lean_dec(v_val_2821_);
lean_dec(v_name_2683_);
lean_dec(v_levelParams_2677_);
lean_dec(v_name_2676_);
v___y_2759_ = v___x_2815_;
v___y_2760_ = v_a_2797_;
v___y_2761_ = v___x_2825_;
goto v___jp_2758_;
}
}
}
else
{
lean_object* v___x_2828_; 
lean_dec(v_a_2817_);
lean_dec(v_name_2683_);
lean_dec(v_levelParams_2677_);
lean_dec(v_name_2676_);
v___x_2828_ = lean_box(0);
v___y_2754_ = v___x_2815_;
v___y_2755_ = v_a_2797_;
v_a_2756_ = v___x_2828_;
goto v___jp_2753_;
}
}
else
{
lean_object* v_a_2829_; 
lean_dec(v_name_2683_);
lean_dec(v_levelParams_2677_);
lean_dec(v_name_2676_);
v_a_2829_ = lean_ctor_get(v___x_2816_, 0);
lean_inc(v_a_2829_);
lean_dec_ref_known(v___x_2816_, 1);
v___y_2749_ = v___x_2815_;
v___y_2750_ = v_a_2797_;
v_a_2751_ = v_a_2829_;
goto v___jp_2748_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___boxed(lean_object* v_ctorVal_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_){
_start:
{
lean_object* v_res_2896_; 
v_res_2896_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(v_ctorVal_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_);
lean_dec(v_a_2894_);
lean_dec_ref(v_a_2893_);
lean_dec(v_a_2892_);
lean_dec_ref(v_a_2891_);
return v_res_2896_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4(lean_object* v_00_u03b1_2897_, lean_object* v_x_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_){
_start:
{
lean_object* v___x_2904_; 
v___x_2904_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg(v_x_2898_);
return v___x_2904_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2905_, lean_object* v_x_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_){
_start:
{
lean_object* v_res_2912_; 
v_res_2912_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4(v_00_u03b1_2905_, v_x_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_);
lean_dec(v___y_2910_);
lean_dec_ref(v___y_2909_);
lean_dec(v___y_2908_);
lean_dec_ref(v___y_2907_);
return v_res_2912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveEqTheoremNameFor(lean_object* v_ctorName_2916_){
_start:
{
lean_object* v___x_2917_; lean_object* v___x_2918_; 
v___x_2917_ = ((lean_object*)(l_Lean_Meta_mkInjectiveEqTheoremNameFor___closed__1));
v___x_2918_ = l_Lean_Name_append(v_ctorName_2916_, v___x_2917_);
return v___x_2918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(lean_object* v_ctorVal_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_){
_start:
{
uint8_t v___x_2925_; lean_object* v___x_2926_; 
v___x_2925_ = 1;
v___x_2926_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(v_ctorVal_2919_, v___x_2925_, v_a_2920_, v_a_2921_, v_a_2922_, v_a_2923_);
return v___x_2926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f___boxed(lean_object* v_ctorVal_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_){
_start:
{
lean_object* v_res_2933_; 
v_res_2933_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_2927_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_);
lean_dec(v_a_2931_);
lean_dec_ref(v_a_2930_);
lean_dec(v_a_2929_);
lean_dec_ref(v_a_2928_);
return v_res_2933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(lean_object* v_e_2934_, lean_object* v_t_2935_, lean_object* v_acc_2936_, lean_object* v_a_2937_){
_start:
{
lean_object* v___x_2939_; 
v___x_2939_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_t_2935_, v_a_2937_);
if (lean_obj_tag(v___x_2939_) == 0)
{
lean_object* v_a_2940_; lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_2963_; 
v_a_2940_ = lean_ctor_get(v___x_2939_, 0);
v_isSharedCheck_2963_ = !lean_is_exclusive(v___x_2939_);
if (v_isSharedCheck_2963_ == 0)
{
v___x_2942_ = v___x_2939_;
v_isShared_2943_ = v_isSharedCheck_2963_;
goto v_resetjp_2941_;
}
else
{
lean_inc(v_a_2940_);
lean_dec(v___x_2939_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_2963_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
lean_object* v___x_2949_; uint8_t v___x_2950_; 
v___x_2949_ = l_Lean_Expr_cleanupAnnotations(v_a_2940_);
v___x_2950_ = l_Lean_Expr_isApp(v___x_2949_);
if (v___x_2950_ == 0)
{
lean_dec_ref(v___x_2949_);
goto v___jp_2944_;
}
else
{
lean_object* v_arg_2951_; lean_object* v___x_2952_; uint8_t v___x_2953_; 
v_arg_2951_ = lean_ctor_get(v___x_2949_, 1);
lean_inc_ref(v_arg_2951_);
v___x_2952_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2949_);
v___x_2953_ = l_Lean_Expr_isApp(v___x_2952_);
if (v___x_2953_ == 0)
{
lean_dec_ref(v___x_2952_);
lean_dec_ref(v_arg_2951_);
goto v___jp_2944_;
}
else
{
lean_object* v_arg_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; uint8_t v___x_2957_; 
v_arg_2954_ = lean_ctor_get(v___x_2952_, 1);
lean_inc_ref(v_arg_2954_);
v___x_2955_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2952_);
v___x_2956_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__1));
v___x_2957_ = l_Lean_Expr_isConstOf(v___x_2955_, v___x_2956_);
lean_dec_ref(v___x_2955_);
if (v___x_2957_ == 0)
{
lean_dec_ref(v_arg_2954_);
lean_dec_ref(v_arg_2951_);
goto v___jp_2944_;
}
else
{
lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; 
lean_del_object(v___x_2942_);
v___x_2958_ = lean_unsigned_to_nat(0u);
v___x_2959_ = l_Lean_mkProj(v___x_2956_, v___x_2958_, v_e_2934_);
lean_inc_ref(v___x_2959_);
v___x_2960_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v___x_2959_, v_arg_2954_, v_acc_2936_, v_a_2937_);
if (lean_obj_tag(v___x_2960_) == 0)
{
lean_object* v_a_2961_; 
v_a_2961_ = lean_ctor_get(v___x_2960_, 0);
lean_inc(v_a_2961_);
lean_dec_ref_known(v___x_2960_, 1);
v_e_2934_ = v___x_2959_;
v_t_2935_ = v_arg_2951_;
v_acc_2936_ = v_a_2961_;
goto _start;
}
else
{
lean_dec_ref(v___x_2959_);
lean_dec_ref(v_arg_2951_);
return v___x_2960_;
}
}
}
}
v___jp_2944_:
{
lean_object* v___x_2945_; lean_object* v___x_2947_; 
v___x_2945_ = lean_array_push(v_acc_2936_, v_e_2934_);
if (v_isShared_2943_ == 0)
{
lean_ctor_set(v___x_2942_, 0, v___x_2945_);
v___x_2947_ = v___x_2942_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v___x_2945_);
v___x_2947_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
return v___x_2947_;
}
}
}
}
else
{
lean_object* v_a_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_2971_; 
lean_dec_ref(v_acc_2936_);
lean_dec_ref(v_e_2934_);
v_a_2964_ = lean_ctor_get(v___x_2939_, 0);
v_isSharedCheck_2971_ = !lean_is_exclusive(v___x_2939_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2966_ = v___x_2939_;
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_a_2964_);
lean_dec(v___x_2939_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
lean_object* v___x_2969_; 
if (v_isShared_2967_ == 0)
{
v___x_2969_ = v___x_2966_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v_a_2964_);
v___x_2969_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
return v___x_2969_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg___boxed(lean_object* v_e_2972_, lean_object* v_t_2973_, lean_object* v_acc_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_){
_start:
{
lean_object* v_res_2977_; 
v_res_2977_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v_e_2972_, v_t_2973_, v_acc_2974_, v_a_2975_);
lean_dec(v_a_2975_);
return v_res_2977_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go(lean_object* v_e_2978_, lean_object* v_t_2979_, lean_object* v_acc_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_){
_start:
{
lean_object* v___x_2986_; 
v___x_2986_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v_e_2978_, v_t_2979_, v_acc_2980_, v_a_2982_);
return v___x_2986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___boxed(lean_object* v_e_2987_, lean_object* v_t_2988_, lean_object* v_acc_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_){
_start:
{
lean_object* v_res_2995_; 
v_res_2995_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go(v_e_2987_, v_t_2988_, v_acc_2989_, v_a_2990_, v_a_2991_, v_a_2992_, v_a_2993_);
lean_dec(v_a_2993_);
lean_dec_ref(v_a_2992_);
lean_dec(v_a_2991_);
lean_dec_ref(v_a_2990_);
return v_res_2995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections(lean_object* v_e_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_){
_start:
{
lean_object* v___x_3002_; 
lean_inc(v_a_3000_);
lean_inc_ref(v_a_2999_);
lean_inc(v_a_2998_);
lean_inc_ref(v_a_2997_);
lean_inc_ref(v_e_2996_);
v___x_3002_ = lean_infer_type(v_e_2996_, v_a_2997_, v_a_2998_, v_a_2999_, v_a_3000_);
if (lean_obj_tag(v___x_3002_) == 0)
{
lean_object* v_a_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; 
v_a_3003_ = lean_ctor_get(v___x_3002_, 0);
lean_inc(v_a_3003_);
lean_dec_ref_known(v___x_3002_, 1);
v___x_3004_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_3005_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v_e_2996_, v_a_3003_, v___x_3004_, v_a_2998_);
return v___x_3005_;
}
else
{
lean_object* v_a_3006_; lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3013_; 
lean_dec_ref(v_e_2996_);
v_a_3006_ = lean_ctor_get(v___x_3002_, 0);
v_isSharedCheck_3013_ = !lean_is_exclusive(v___x_3002_);
if (v_isSharedCheck_3013_ == 0)
{
v___x_3008_ = v___x_3002_;
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
else
{
lean_inc(v_a_3006_);
lean_dec(v___x_3002_);
v___x_3008_ = lean_box(0);
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
v_resetjp_3007_:
{
lean_object* v___x_3011_; 
if (v_isShared_3009_ == 0)
{
v___x_3011_ = v___x_3008_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_a_3006_);
v___x_3011_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
return v___x_3011_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections___boxed(lean_object* v_e_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_){
_start:
{
lean_object* v_res_3020_; 
v_res_3020_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections(v_e_3014_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
lean_dec(v_a_3018_);
lean_dec_ref(v_a_3017_);
lean_dec(v_a_3016_);
lean_dec_ref(v_a_3015_);
return v_res_3020_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_x_3021_, lean_object* v_x_3022_, lean_object* v_x_3023_, lean_object* v_x_3024_){
_start:
{
lean_object* v_ks_3025_; lean_object* v_vs_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3050_; 
v_ks_3025_ = lean_ctor_get(v_x_3021_, 0);
v_vs_3026_ = lean_ctor_get(v_x_3021_, 1);
v_isSharedCheck_3050_ = !lean_is_exclusive(v_x_3021_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3028_ = v_x_3021_;
v_isShared_3029_ = v_isSharedCheck_3050_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_vs_3026_);
lean_inc(v_ks_3025_);
lean_dec(v_x_3021_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3050_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v___x_3030_; uint8_t v___x_3031_; 
v___x_3030_ = lean_array_get_size(v_ks_3025_);
v___x_3031_ = lean_nat_dec_lt(v_x_3022_, v___x_3030_);
if (v___x_3031_ == 0)
{
lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3035_; 
lean_dec(v_x_3022_);
v___x_3032_ = lean_array_push(v_ks_3025_, v_x_3023_);
v___x_3033_ = lean_array_push(v_vs_3026_, v_x_3024_);
if (v_isShared_3029_ == 0)
{
lean_ctor_set(v___x_3028_, 1, v___x_3033_);
lean_ctor_set(v___x_3028_, 0, v___x_3032_);
v___x_3035_ = v___x_3028_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v___x_3032_);
lean_ctor_set(v_reuseFailAlloc_3036_, 1, v___x_3033_);
v___x_3035_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
return v___x_3035_;
}
}
else
{
lean_object* v_k_x27_3037_; uint8_t v___x_3038_; 
v_k_x27_3037_ = lean_array_fget_borrowed(v_ks_3025_, v_x_3022_);
v___x_3038_ = l_Lean_instBEqMVarId_beq(v_x_3023_, v_k_x27_3037_);
if (v___x_3038_ == 0)
{
lean_object* v___x_3040_; 
if (v_isShared_3029_ == 0)
{
v___x_3040_ = v___x_3028_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_ks_3025_);
lean_ctor_set(v_reuseFailAlloc_3044_, 1, v_vs_3026_);
v___x_3040_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
lean_object* v___x_3041_; lean_object* v___x_3042_; 
v___x_3041_ = lean_unsigned_to_nat(1u);
v___x_3042_ = lean_nat_add(v_x_3022_, v___x_3041_);
lean_dec(v_x_3022_);
v_x_3021_ = v___x_3040_;
v_x_3022_ = v___x_3042_;
goto _start;
}
}
else
{
lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3048_; 
v___x_3045_ = lean_array_fset(v_ks_3025_, v_x_3022_, v_x_3023_);
v___x_3046_ = lean_array_fset(v_vs_3026_, v_x_3022_, v_x_3024_);
lean_dec(v_x_3022_);
if (v_isShared_3029_ == 0)
{
lean_ctor_set(v___x_3028_, 1, v___x_3046_);
lean_ctor_set(v___x_3028_, 0, v___x_3045_);
v___x_3048_ = v___x_3028_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v___x_3045_);
lean_ctor_set(v_reuseFailAlloc_3049_, 1, v___x_3046_);
v___x_3048_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
return v___x_3048_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_n_3051_, lean_object* v_k_3052_, lean_object* v_v_3053_){
_start:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; 
v___x_3054_ = lean_unsigned_to_nat(0u);
v___x_3055_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_n_3051_, v___x_3054_, v_k_3052_, v_v_3053_);
return v___x_3055_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_3056_; 
v___x_3056_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_3056_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(lean_object* v_x_3057_, size_t v_x_3058_, size_t v_x_3059_, lean_object* v_x_3060_, lean_object* v_x_3061_){
_start:
{
if (lean_obj_tag(v_x_3057_) == 0)
{
lean_object* v_es_3062_; size_t v___x_3063_; size_t v___x_3064_; lean_object* v_j_3065_; lean_object* v___x_3066_; uint8_t v___x_3067_; 
v_es_3062_ = lean_ctor_get(v_x_3057_, 0);
v___x_3063_ = ((size_t)31ULL);
v___x_3064_ = lean_usize_land(v_x_3058_, v___x_3063_);
v_j_3065_ = lean_usize_to_nat(v___x_3064_);
v___x_3066_ = lean_array_get_size(v_es_3062_);
v___x_3067_ = lean_nat_dec_lt(v_j_3065_, v___x_3066_);
if (v___x_3067_ == 0)
{
lean_dec(v_j_3065_);
lean_dec(v_x_3061_);
lean_dec(v_x_3060_);
return v_x_3057_;
}
else
{
lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3106_; 
lean_inc_ref(v_es_3062_);
v_isSharedCheck_3106_ = !lean_is_exclusive(v_x_3057_);
if (v_isSharedCheck_3106_ == 0)
{
lean_object* v_unused_3107_; 
v_unused_3107_ = lean_ctor_get(v_x_3057_, 0);
lean_dec(v_unused_3107_);
v___x_3069_ = v_x_3057_;
v_isShared_3070_ = v_isSharedCheck_3106_;
goto v_resetjp_3068_;
}
else
{
lean_dec(v_x_3057_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3106_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v_v_3071_; lean_object* v___x_3072_; lean_object* v_xs_x27_3073_; lean_object* v___y_3075_; 
v_v_3071_ = lean_array_fget(v_es_3062_, v_j_3065_);
v___x_3072_ = lean_box(0);
v_xs_x27_3073_ = lean_array_fset(v_es_3062_, v_j_3065_, v___x_3072_);
switch(lean_obj_tag(v_v_3071_))
{
case 0:
{
lean_object* v_key_3080_; lean_object* v_val_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3091_; 
v_key_3080_ = lean_ctor_get(v_v_3071_, 0);
v_val_3081_ = lean_ctor_get(v_v_3071_, 1);
v_isSharedCheck_3091_ = !lean_is_exclusive(v_v_3071_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3083_ = v_v_3071_;
v_isShared_3084_ = v_isSharedCheck_3091_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_val_3081_);
lean_inc(v_key_3080_);
lean_dec(v_v_3071_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3091_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
uint8_t v___x_3085_; 
v___x_3085_ = l_Lean_instBEqMVarId_beq(v_x_3060_, v_key_3080_);
if (v___x_3085_ == 0)
{
lean_object* v___x_3086_; lean_object* v___x_3087_; 
lean_del_object(v___x_3083_);
v___x_3086_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3080_, v_val_3081_, v_x_3060_, v_x_3061_);
v___x_3087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3087_, 0, v___x_3086_);
v___y_3075_ = v___x_3087_;
goto v___jp_3074_;
}
else
{
lean_object* v___x_3089_; 
lean_dec(v_val_3081_);
lean_dec(v_key_3080_);
if (v_isShared_3084_ == 0)
{
lean_ctor_set(v___x_3083_, 1, v_x_3061_);
lean_ctor_set(v___x_3083_, 0, v_x_3060_);
v___x_3089_ = v___x_3083_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_x_3060_);
lean_ctor_set(v_reuseFailAlloc_3090_, 1, v_x_3061_);
v___x_3089_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
v___y_3075_ = v___x_3089_;
goto v___jp_3074_;
}
}
}
}
case 1:
{
lean_object* v_node_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3104_; 
v_node_3092_ = lean_ctor_get(v_v_3071_, 0);
v_isSharedCheck_3104_ = !lean_is_exclusive(v_v_3071_);
if (v_isSharedCheck_3104_ == 0)
{
v___x_3094_ = v_v_3071_;
v_isShared_3095_ = v_isSharedCheck_3104_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_node_3092_);
lean_dec(v_v_3071_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3104_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
size_t v___x_3096_; size_t v___x_3097_; size_t v___x_3098_; size_t v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3102_; 
v___x_3096_ = ((size_t)5ULL);
v___x_3097_ = lean_usize_shift_right(v_x_3058_, v___x_3096_);
v___x_3098_ = ((size_t)1ULL);
v___x_3099_ = lean_usize_add(v_x_3059_, v___x_3098_);
v___x_3100_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_node_3092_, v___x_3097_, v___x_3099_, v_x_3060_, v_x_3061_);
if (v_isShared_3095_ == 0)
{
lean_ctor_set(v___x_3094_, 0, v___x_3100_);
v___x_3102_ = v___x_3094_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v___x_3100_);
v___x_3102_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
v___y_3075_ = v___x_3102_;
goto v___jp_3074_;
}
}
}
default: 
{
lean_object* v___x_3105_; 
v___x_3105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3105_, 0, v_x_3060_);
lean_ctor_set(v___x_3105_, 1, v_x_3061_);
v___y_3075_ = v___x_3105_;
goto v___jp_3074_;
}
}
v___jp_3074_:
{
lean_object* v___x_3076_; lean_object* v___x_3078_; 
v___x_3076_ = lean_array_fset(v_xs_x27_3073_, v_j_3065_, v___y_3075_);
lean_dec(v_j_3065_);
if (v_isShared_3070_ == 0)
{
lean_ctor_set(v___x_3069_, 0, v___x_3076_);
v___x_3078_ = v___x_3069_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v___x_3076_);
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
lean_object* v_ks_3108_; lean_object* v_vs_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3127_; 
v_ks_3108_ = lean_ctor_get(v_x_3057_, 0);
v_vs_3109_ = lean_ctor_get(v_x_3057_, 1);
v_isSharedCheck_3127_ = !lean_is_exclusive(v_x_3057_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3111_ = v_x_3057_;
v_isShared_3112_ = v_isSharedCheck_3127_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_vs_3109_);
lean_inc(v_ks_3108_);
lean_dec(v_x_3057_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3127_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
lean_object* v___x_3114_; 
if (v_isShared_3112_ == 0)
{
v___x_3114_ = v___x_3111_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v_ks_3108_);
lean_ctor_set(v_reuseFailAlloc_3126_, 1, v_vs_3109_);
v___x_3114_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
lean_object* v_newNode_3115_; size_t v___x_3116_; uint8_t v___x_3117_; 
v_newNode_3115_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(v___x_3114_, v_x_3060_, v_x_3061_);
v___x_3116_ = ((size_t)7ULL);
v___x_3117_ = lean_usize_dec_le(v___x_3116_, v_x_3059_);
if (v___x_3117_ == 0)
{
lean_object* v___x_3118_; lean_object* v___x_3119_; uint8_t v___x_3120_; 
v___x_3118_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3115_);
v___x_3119_ = lean_unsigned_to_nat(4u);
v___x_3120_ = lean_nat_dec_lt(v___x_3118_, v___x_3119_);
lean_dec(v___x_3118_);
if (v___x_3120_ == 0)
{
lean_object* v_ks_3121_; lean_object* v_vs_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; 
v_ks_3121_ = lean_ctor_get(v_newNode_3115_, 0);
lean_inc_ref(v_ks_3121_);
v_vs_3122_ = lean_ctor_get(v_newNode_3115_, 1);
lean_inc_ref(v_vs_3122_);
lean_dec_ref(v_newNode_3115_);
v___x_3123_ = lean_unsigned_to_nat(0u);
v___x_3124_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_3125_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(v_x_3059_, v_ks_3121_, v_vs_3122_, v___x_3123_, v___x_3124_);
lean_dec_ref(v_vs_3122_);
lean_dec_ref(v_ks_3121_);
return v___x_3125_;
}
else
{
return v_newNode_3115_;
}
}
else
{
return v_newNode_3115_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(size_t v_depth_3128_, lean_object* v_keys_3129_, lean_object* v_vals_3130_, lean_object* v_i_3131_, lean_object* v_entries_3132_){
_start:
{
lean_object* v___x_3133_; uint8_t v___x_3134_; 
v___x_3133_ = lean_array_get_size(v_keys_3129_);
v___x_3134_ = lean_nat_dec_lt(v_i_3131_, v___x_3133_);
if (v___x_3134_ == 0)
{
lean_dec(v_i_3131_);
return v_entries_3132_;
}
else
{
lean_object* v_k_3135_; lean_object* v_v_3136_; uint64_t v___x_3137_; size_t v_h_3138_; size_t v___x_3139_; lean_object* v___x_3140_; size_t v___x_3141_; size_t v___x_3142_; size_t v___x_3143_; size_t v_h_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; 
v_k_3135_ = lean_array_fget_borrowed(v_keys_3129_, v_i_3131_);
v_v_3136_ = lean_array_fget_borrowed(v_vals_3130_, v_i_3131_);
v___x_3137_ = l_Lean_instHashableMVarId_hash(v_k_3135_);
v_h_3138_ = lean_uint64_to_usize(v___x_3137_);
v___x_3139_ = ((size_t)5ULL);
v___x_3140_ = lean_unsigned_to_nat(1u);
v___x_3141_ = ((size_t)1ULL);
v___x_3142_ = lean_usize_sub(v_depth_3128_, v___x_3141_);
v___x_3143_ = lean_usize_mul(v___x_3139_, v___x_3142_);
v_h_3144_ = lean_usize_shift_right(v_h_3138_, v___x_3143_);
v___x_3145_ = lean_nat_add(v_i_3131_, v___x_3140_);
lean_dec(v_i_3131_);
lean_inc(v_v_3136_);
lean_inc(v_k_3135_);
v___x_3146_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_entries_3132_, v_h_3144_, v_depth_3128_, v_k_3135_, v_v_3136_);
v_i_3131_ = v___x_3145_;
v_entries_3132_ = v___x_3146_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_depth_3148_, lean_object* v_keys_3149_, lean_object* v_vals_3150_, lean_object* v_i_3151_, lean_object* v_entries_3152_){
_start:
{
size_t v_depth_boxed_3153_; lean_object* v_res_3154_; 
v_depth_boxed_3153_ = lean_unbox_usize(v_depth_3148_);
lean_dec(v_depth_3148_);
v_res_3154_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_boxed_3153_, v_keys_3149_, v_vals_3150_, v_i_3151_, v_entries_3152_);
lean_dec_ref(v_vals_3150_);
lean_dec_ref(v_keys_3149_);
return v_res_3154_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_3155_, lean_object* v_x_3156_, lean_object* v_x_3157_, lean_object* v_x_3158_, lean_object* v_x_3159_){
_start:
{
size_t v_x_4985__boxed_3160_; size_t v_x_4986__boxed_3161_; lean_object* v_res_3162_; 
v_x_4985__boxed_3160_ = lean_unbox_usize(v_x_3156_);
lean_dec(v_x_3156_);
v_x_4986__boxed_3161_ = lean_unbox_usize(v_x_3157_);
lean_dec(v_x_3157_);
v_res_3162_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_x_3155_, v_x_4985__boxed_3160_, v_x_4986__boxed_3161_, v_x_3158_, v_x_3159_);
return v_res_3162_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(lean_object* v_x_3163_, lean_object* v_x_3164_, lean_object* v_x_3165_){
_start:
{
uint64_t v___x_3166_; size_t v___x_3167_; size_t v___x_3168_; lean_object* v___x_3169_; 
v___x_3166_ = l_Lean_instHashableMVarId_hash(v_x_3164_);
v___x_3167_ = lean_uint64_to_usize(v___x_3166_);
v___x_3168_ = ((size_t)1ULL);
v___x_3169_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_x_3163_, v___x_3167_, v___x_3168_, v_x_3164_, v_x_3165_);
return v___x_3169_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(lean_object* v_mvarId_3170_, lean_object* v_val_3171_, lean_object* v___y_3172_){
_start:
{
lean_object* v___x_3174_; lean_object* v_mctx_3175_; lean_object* v_cache_3176_; lean_object* v_zetaDeltaFVarIds_3177_; lean_object* v_postponed_3178_; lean_object* v_diag_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3208_; 
v___x_3174_ = lean_st_ref_take(v___y_3172_);
v_mctx_3175_ = lean_ctor_get(v___x_3174_, 0);
v_cache_3176_ = lean_ctor_get(v___x_3174_, 1);
v_zetaDeltaFVarIds_3177_ = lean_ctor_get(v___x_3174_, 2);
v_postponed_3178_ = lean_ctor_get(v___x_3174_, 3);
v_diag_3179_ = lean_ctor_get(v___x_3174_, 4);
v_isSharedCheck_3208_ = !lean_is_exclusive(v___x_3174_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_3181_ = v___x_3174_;
v_isShared_3182_ = v_isSharedCheck_3208_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_diag_3179_);
lean_inc(v_postponed_3178_);
lean_inc(v_zetaDeltaFVarIds_3177_);
lean_inc(v_cache_3176_);
lean_inc(v_mctx_3175_);
lean_dec(v___x_3174_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3208_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v_depth_3183_; lean_object* v_levelAssignDepth_3184_; lean_object* v_lmvarCounter_3185_; lean_object* v_mvarCounter_3186_; lean_object* v_lDecls_3187_; lean_object* v_decls_3188_; lean_object* v_userNames_3189_; lean_object* v_lAssignment_3190_; lean_object* v_eAssignment_3191_; lean_object* v_dAssignment_3192_; lean_object* v_instanceTypedMVars_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3207_; 
v_depth_3183_ = lean_ctor_get(v_mctx_3175_, 0);
v_levelAssignDepth_3184_ = lean_ctor_get(v_mctx_3175_, 1);
v_lmvarCounter_3185_ = lean_ctor_get(v_mctx_3175_, 2);
v_mvarCounter_3186_ = lean_ctor_get(v_mctx_3175_, 3);
v_lDecls_3187_ = lean_ctor_get(v_mctx_3175_, 4);
v_decls_3188_ = lean_ctor_get(v_mctx_3175_, 5);
v_userNames_3189_ = lean_ctor_get(v_mctx_3175_, 6);
v_lAssignment_3190_ = lean_ctor_get(v_mctx_3175_, 7);
v_eAssignment_3191_ = lean_ctor_get(v_mctx_3175_, 8);
v_dAssignment_3192_ = lean_ctor_get(v_mctx_3175_, 9);
v_instanceTypedMVars_3193_ = lean_ctor_get(v_mctx_3175_, 10);
v_isSharedCheck_3207_ = !lean_is_exclusive(v_mctx_3175_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3195_ = v_mctx_3175_;
v_isShared_3196_ = v_isSharedCheck_3207_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_instanceTypedMVars_3193_);
lean_inc(v_dAssignment_3192_);
lean_inc(v_eAssignment_3191_);
lean_inc(v_lAssignment_3190_);
lean_inc(v_userNames_3189_);
lean_inc(v_decls_3188_);
lean_inc(v_lDecls_3187_);
lean_inc(v_mvarCounter_3186_);
lean_inc(v_lmvarCounter_3185_);
lean_inc(v_levelAssignDepth_3184_);
lean_inc(v_depth_3183_);
lean_dec(v_mctx_3175_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3207_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v___x_3197_; lean_object* v___x_3199_; 
v___x_3197_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(v_eAssignment_3191_, v_mvarId_3170_, v_val_3171_);
if (v_isShared_3196_ == 0)
{
lean_ctor_set(v___x_3195_, 8, v___x_3197_);
v___x_3199_ = v___x_3195_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_depth_3183_);
lean_ctor_set(v_reuseFailAlloc_3206_, 1, v_levelAssignDepth_3184_);
lean_ctor_set(v_reuseFailAlloc_3206_, 2, v_lmvarCounter_3185_);
lean_ctor_set(v_reuseFailAlloc_3206_, 3, v_mvarCounter_3186_);
lean_ctor_set(v_reuseFailAlloc_3206_, 4, v_lDecls_3187_);
lean_ctor_set(v_reuseFailAlloc_3206_, 5, v_decls_3188_);
lean_ctor_set(v_reuseFailAlloc_3206_, 6, v_userNames_3189_);
lean_ctor_set(v_reuseFailAlloc_3206_, 7, v_lAssignment_3190_);
lean_ctor_set(v_reuseFailAlloc_3206_, 8, v___x_3197_);
lean_ctor_set(v_reuseFailAlloc_3206_, 9, v_dAssignment_3192_);
lean_ctor_set(v_reuseFailAlloc_3206_, 10, v_instanceTypedMVars_3193_);
v___x_3199_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
lean_object* v___x_3201_; 
if (v_isShared_3182_ == 0)
{
lean_ctor_set(v___x_3181_, 0, v___x_3199_);
v___x_3201_ = v___x_3181_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v___x_3199_);
lean_ctor_set(v_reuseFailAlloc_3205_, 1, v_cache_3176_);
lean_ctor_set(v_reuseFailAlloc_3205_, 2, v_zetaDeltaFVarIds_3177_);
lean_ctor_set(v_reuseFailAlloc_3205_, 3, v_postponed_3178_);
lean_ctor_set(v_reuseFailAlloc_3205_, 4, v_diag_3179_);
v___x_3201_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; 
v___x_3202_ = lean_st_ref_put(v___y_3172_, v___x_3201_);
v___x_3203_ = lean_box(0);
v___x_3204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3204_, 0, v___x_3203_);
return v___x_3204_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg___boxed(lean_object* v_mvarId_3209_, lean_object* v_val_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_){
_start:
{
lean_object* v_res_3213_; 
v_res_3213_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(v_mvarId_3209_, v_val_3210_, v___y_3211_);
lean_dec(v___y_3211_);
return v_res_3213_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(lean_object* v___f_3214_, lean_object* v_a_3215_, lean_object* v_x_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_){
_start:
{
lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3222_ = lean_box(0);
lean_inc(v___y_3220_);
lean_inc_ref(v___y_3219_);
lean_inc(v___y_3218_);
lean_inc_ref(v___y_3217_);
v___x_3223_ = lean_apply_7(v___f_3214_, v___x_3222_, v_a_3215_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, lean_box(0));
return v___x_3223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1___boxed(lean_object* v___f_3224_, lean_object* v_a_3225_, lean_object* v_x_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_){
_start:
{
lean_object* v_res_3232_; 
v_res_3232_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(v___f_3224_, v_a_3225_, v_x_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_);
lean_dec(v___y_3230_);
lean_dec_ref(v___y_3229_);
lean_dec(v___y_3228_);
lean_dec_ref(v___y_3227_);
return v_res_3232_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3234_; lean_object* v___x_3235_; 
v___x_3234_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___closed__0));
v___x_3235_ = l_Lean_stringToMessageData(v___x_3234_);
return v___x_3235_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(lean_object* v___f_3236_, lean_object* v_a_3237_, lean_object* v_x_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_){
_start:
{
lean_object* v___x_3244_; lean_object* v___x_3245_; 
v___x_3244_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___closed__1, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___closed__1);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___boxed(lean_object* v___f_3256_, lean_object* v_a_3257_, lean_object* v_x_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_){
_start:
{
lean_object* v_res_3264_; 
v_res_3264_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(v___f_3256_, v_a_3257_, v_x_3258_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_);
lean_dec(v___y_3262_);
lean_dec_ref(v___y_3261_);
lean_dec(v___y_3260_);
lean_dec_ref(v___y_3259_);
lean_dec(v_x_3258_);
return v_res_3264_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0(uint8_t v___x_3265_, lean_object* v_____r_3266_, lean_object* v_mvarId_u2082_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_){
_start:
{
lean_object* v___x_3273_; 
v___x_3273_ = l_Lean_Meta_introSubstEq(v_mvarId_u2082_3267_, v___x_3265_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_);
if (lean_obj_tag(v___x_3273_) == 0)
{
lean_object* v_a_3274_; lean_object* v___x_3276_; uint8_t v_isShared_3277_; uint8_t v_isSharedCheck_3283_; 
v_a_3274_ = lean_ctor_get(v___x_3273_, 0);
v_isSharedCheck_3283_ = !lean_is_exclusive(v___x_3273_);
if (v_isSharedCheck_3283_ == 0)
{
v___x_3276_ = v___x_3273_;
v_isShared_3277_ = v_isSharedCheck_3283_;
goto v_resetjp_3275_;
}
else
{
lean_inc(v_a_3274_);
lean_dec(v___x_3273_);
v___x_3276_ = lean_box(0);
v_isShared_3277_ = v_isSharedCheck_3283_;
goto v_resetjp_3275_;
}
v_resetjp_3275_:
{
lean_object* v_snd_3278_; lean_object* v___x_3279_; lean_object* v___x_3281_; 
v_snd_3278_ = lean_ctor_get(v_a_3274_, 1);
lean_inc(v_snd_3278_);
lean_dec(v_a_3274_);
v___x_3279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3279_, 0, v_snd_3278_);
if (v_isShared_3277_ == 0)
{
lean_ctor_set(v___x_3276_, 0, v___x_3279_);
v___x_3281_ = v___x_3276_;
goto v_reusejp_3280_;
}
else
{
lean_object* v_reuseFailAlloc_3282_; 
v_reuseFailAlloc_3282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3282_, 0, v___x_3279_);
v___x_3281_ = v_reuseFailAlloc_3282_;
goto v_reusejp_3280_;
}
v_reusejp_3280_:
{
return v___x_3281_;
}
}
}
else
{
lean_object* v_a_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3291_; 
v_a_3284_ = lean_ctor_get(v___x_3273_, 0);
v_isSharedCheck_3291_ = !lean_is_exclusive(v___x_3273_);
if (v_isSharedCheck_3291_ == 0)
{
v___x_3286_ = v___x_3273_;
v_isShared_3287_ = v_isSharedCheck_3291_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_a_3284_);
lean_dec(v___x_3273_);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0___boxed(lean_object* v___x_3292_, lean_object* v_____r_3293_, lean_object* v_mvarId_u2082_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_){
_start:
{
uint8_t v___x_5273__boxed_3300_; lean_object* v_res_3301_; 
v___x_5273__boxed_3300_ = lean_unbox(v___x_3292_);
v_res_3301_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0(v___x_5273__boxed_3300_, v_____r_3293_, v_mvarId_u2082_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_);
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3297_);
lean_dec(v___y_3296_);
lean_dec_ref(v___y_3295_);
return v_res_3301_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; 
v___x_3307_ = lean_box(0);
v___x_3308_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__2));
v___x_3309_ = l_Lean_mkConst(v___x_3308_, v___x_3307_);
return v___x_3309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg(lean_object* v_a_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_){
_start:
{
lean_object* v___y_3317_; lean_object* v___x_3337_; 
lean_inc(v_a_3310_);
v___x_3337_ = l_Lean_MVarId_getType(v_a_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_);
if (lean_obj_tag(v___x_3337_) == 0)
{
lean_object* v_a_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3397_; 
v_a_3338_ = lean_ctor_get(v___x_3337_, 0);
v_isSharedCheck_3397_ = !lean_is_exclusive(v___x_3337_);
if (v_isSharedCheck_3397_ == 0)
{
v___x_3340_ = v___x_3337_;
v_isShared_3341_ = v_isSharedCheck_3397_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_a_3338_);
lean_dec(v___x_3337_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3397_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
if (lean_obj_tag(v_a_3338_) == 7)
{
lean_object* v_binderType_3342_; lean_object* v_body_3343_; uint8_t v___x_3344_; 
v_binderType_3342_ = lean_ctor_get(v_a_3338_, 1);
lean_inc_ref(v_binderType_3342_);
v_body_3343_ = lean_ctor_get(v_a_3338_, 2);
lean_inc_ref(v_body_3343_);
lean_dec_ref_known(v_a_3338_, 3);
v___x_3344_ = l_Lean_Expr_hasLooseBVars(v_body_3343_);
if (v___x_3344_ == 0)
{
lean_object* v___x_3345_; 
lean_del_object(v___x_3340_);
v___x_3345_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_3342_, v___y_3312_);
if (lean_obj_tag(v___x_3345_) == 0)
{
lean_object* v_a_3346_; lean_object* v___x_3347_; lean_object* v___f_3348_; lean_object* v___x_3349_; uint8_t v___x_3350_; 
v_a_3346_ = lean_ctor_get(v___x_3345_, 0);
lean_inc(v_a_3346_);
lean_dec_ref_known(v___x_3345_, 1);
v___x_3347_ = lean_box(v___x_3344_);
v___f_3348_ = lean_alloc_closure((void*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3348_, 0, v___x_3347_);
v___x_3349_ = l_Lean_Expr_cleanupAnnotations(v_a_3346_);
v___x_3350_ = l_Lean_Expr_isApp(v___x_3349_);
if (v___x_3350_ == 0)
{
lean_object* v___x_3351_; lean_object* v___x_3352_; 
lean_dec_ref(v___x_3349_);
lean_dec_ref(v_body_3343_);
v___x_3351_ = lean_box(0);
v___x_3352_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(v___f_3348_, v_a_3310_, v___x_3351_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_);
v___y_3317_ = v___x_3352_;
goto v___jp_3316_;
}
else
{
lean_object* v_arg_3353_; lean_object* v___x_3354_; uint8_t v___x_3355_; 
v_arg_3353_ = lean_ctor_get(v___x_3349_, 1);
lean_inc_ref(v_arg_3353_);
v___x_3354_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3349_);
v___x_3355_ = l_Lean_Expr_isApp(v___x_3354_);
if (v___x_3355_ == 0)
{
lean_object* v___x_3356_; lean_object* v___x_3357_; 
lean_dec_ref(v___x_3354_);
lean_dec_ref(v_arg_3353_);
lean_dec_ref(v_body_3343_);
v___x_3356_ = lean_box(0);
v___x_3357_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(v___f_3348_, v_a_3310_, v___x_3356_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_);
v___y_3317_ = v___x_3357_;
goto v___jp_3316_;
}
else
{
lean_object* v_arg_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; uint8_t v___x_3361_; 
v_arg_3358_ = lean_ctor_get(v___x_3354_, 1);
lean_inc_ref(v_arg_3358_);
v___x_3359_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3354_);
v___x_3360_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__1));
v___x_3361_ = l_Lean_Expr_isConstOf(v___x_3359_, v___x_3360_);
lean_dec_ref(v___x_3359_);
if (v___x_3361_ == 0)
{
lean_object* v___x_3362_; lean_object* v___x_3363_; 
lean_dec_ref(v_arg_3358_);
lean_dec_ref(v_arg_3353_);
lean_dec_ref(v_body_3343_);
v___x_3362_ = lean_box(0);
v___x_3363_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(v___f_3348_, v_a_3310_, v___x_3362_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_);
v___y_3317_ = v___x_3363_;
goto v___jp_3316_;
}
else
{
lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; 
v___x_3364_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__3, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__3_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__3);
v___x_3365_ = l_Lean_mkApp3(v___x_3364_, v_arg_3358_, v_arg_3353_, v_body_3343_);
v___x_3366_ = lean_unsigned_to_nat(1u);
lean_inc(v_a_3310_);
v___x_3367_ = l_Lean_MVarId_applyN(v_a_3310_, v___x_3365_, v___x_3366_, v___x_3361_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_);
if (lean_obj_tag(v___x_3367_) == 0)
{
lean_object* v_a_3368_; 
v_a_3368_ = lean_ctor_get(v___x_3367_, 0);
lean_inc(v_a_3368_);
lean_dec_ref_known(v___x_3367_, 1);
if (lean_obj_tag(v_a_3368_) == 1)
{
lean_object* v_tail_3369_; 
v_tail_3369_ = lean_ctor_get(v_a_3368_, 1);
if (lean_obj_tag(v_tail_3369_) == 0)
{
lean_object* v_head_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; 
lean_dec_ref(v___f_3348_);
lean_dec(v_a_3310_);
v_head_3370_ = lean_ctor_get(v_a_3368_, 0);
lean_inc(v_head_3370_);
lean_dec_ref_known(v_a_3368_, 2);
v___x_3371_ = lean_box(0);
v___x_3372_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0(v___x_3344_, v___x_3371_, v_head_3370_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_);
v___y_3317_ = v___x_3372_;
goto v___jp_3316_;
}
else
{
lean_object* v___x_3373_; 
v___x_3373_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(v___f_3348_, v_a_3310_, v_a_3368_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_);
lean_dec_ref_known(v_a_3368_, 2);
v___y_3317_ = v___x_3373_;
goto v___jp_3316_;
}
}
else
{
lean_object* v___x_3374_; 
v___x_3374_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(v___f_3348_, v_a_3310_, v_a_3368_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_);
lean_dec(v_a_3368_);
v___y_3317_ = v___x_3374_;
goto v___jp_3316_;
}
}
else
{
lean_object* v_a_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3382_; 
lean_dec_ref(v___f_3348_);
lean_dec(v_a_3310_);
v_a_3375_ = lean_ctor_get(v___x_3367_, 0);
v_isSharedCheck_3382_ = !lean_is_exclusive(v___x_3367_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3377_ = v___x_3367_;
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
else
{
lean_inc(v_a_3375_);
lean_dec(v___x_3367_);
v___x_3377_ = lean_box(0);
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
v_resetjp_3376_:
{
lean_object* v___x_3380_; 
if (v_isShared_3378_ == 0)
{
v___x_3380_ = v___x_3377_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v_a_3375_);
v___x_3380_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
return v___x_3380_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3383_; lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3390_; 
lean_dec_ref(v_body_3343_);
lean_dec(v_a_3310_);
v_a_3383_ = lean_ctor_get(v___x_3345_, 0);
v_isSharedCheck_3390_ = !lean_is_exclusive(v___x_3345_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3385_ = v___x_3345_;
v_isShared_3386_ = v_isSharedCheck_3390_;
goto v_resetjp_3384_;
}
else
{
lean_inc(v_a_3383_);
lean_dec(v___x_3345_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3390_;
goto v_resetjp_3384_;
}
v_resetjp_3384_:
{
lean_object* v___x_3388_; 
if (v_isShared_3386_ == 0)
{
v___x_3388_ = v___x_3385_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v_a_3383_);
v___x_3388_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
return v___x_3388_;
}
}
}
}
else
{
lean_object* v___x_3392_; 
lean_dec_ref(v_body_3343_);
lean_dec_ref(v_binderType_3342_);
if (v_isShared_3341_ == 0)
{
lean_ctor_set(v___x_3340_, 0, v_a_3310_);
v___x_3392_ = v___x_3340_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v_a_3310_);
v___x_3392_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
return v___x_3392_;
}
}
}
else
{
lean_object* v___x_3395_; 
lean_dec(v_a_3338_);
if (v_isShared_3341_ == 0)
{
lean_ctor_set(v___x_3340_, 0, v_a_3310_);
v___x_3395_ = v___x_3340_;
goto v_reusejp_3394_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v_a_3310_);
v___x_3395_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3394_;
}
v_reusejp_3394_:
{
return v___x_3395_;
}
}
}
}
else
{
lean_object* v_a_3398_; lean_object* v___x_3400_; uint8_t v_isShared_3401_; uint8_t v_isSharedCheck_3405_; 
lean_dec(v_a_3310_);
v_a_3398_ = lean_ctor_get(v___x_3337_, 0);
v_isSharedCheck_3405_ = !lean_is_exclusive(v___x_3337_);
if (v_isSharedCheck_3405_ == 0)
{
v___x_3400_ = v___x_3337_;
v_isShared_3401_ = v_isSharedCheck_3405_;
goto v_resetjp_3399_;
}
else
{
lean_inc(v_a_3398_);
lean_dec(v___x_3337_);
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
v___jp_3316_:
{
if (lean_obj_tag(v___y_3317_) == 0)
{
lean_object* v_a_3318_; lean_object* v___x_3320_; uint8_t v_isShared_3321_; uint8_t v_isSharedCheck_3328_; 
v_a_3318_ = lean_ctor_get(v___y_3317_, 0);
v_isSharedCheck_3328_ = !lean_is_exclusive(v___y_3317_);
if (v_isSharedCheck_3328_ == 0)
{
v___x_3320_ = v___y_3317_;
v_isShared_3321_ = v_isSharedCheck_3328_;
goto v_resetjp_3319_;
}
else
{
lean_inc(v_a_3318_);
lean_dec(v___y_3317_);
v___x_3320_ = lean_box(0);
v_isShared_3321_ = v_isSharedCheck_3328_;
goto v_resetjp_3319_;
}
v_resetjp_3319_:
{
if (lean_obj_tag(v_a_3318_) == 0)
{
lean_object* v_a_3322_; lean_object* v___x_3324_; 
v_a_3322_ = lean_ctor_get(v_a_3318_, 0);
lean_inc(v_a_3322_);
lean_dec_ref_known(v_a_3318_, 1);
if (v_isShared_3321_ == 0)
{
lean_ctor_set(v___x_3320_, 0, v_a_3322_);
v___x_3324_ = v___x_3320_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3325_; 
v_reuseFailAlloc_3325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3325_, 0, v_a_3322_);
v___x_3324_ = v_reuseFailAlloc_3325_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
return v___x_3324_;
}
}
else
{
lean_object* v_a_3326_; 
lean_del_object(v___x_3320_);
v_a_3326_ = lean_ctor_get(v_a_3318_, 0);
lean_inc(v_a_3326_);
lean_dec_ref_known(v_a_3318_, 1);
v_a_3310_ = v_a_3326_;
goto _start;
}
}
}
else
{
lean_object* v_a_3329_; lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3336_; 
v_a_3329_ = lean_ctor_get(v___y_3317_, 0);
v_isSharedCheck_3336_ = !lean_is_exclusive(v___y_3317_);
if (v_isSharedCheck_3336_ == 0)
{
v___x_3331_ = v___y_3317_;
v_isShared_3332_ = v_isSharedCheck_3336_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_a_3329_);
lean_dec(v___y_3317_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3336_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
lean_object* v___x_3334_; 
if (v_isShared_3332_ == 0)
{
v___x_3334_ = v___x_3331_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v_a_3329_);
v___x_3334_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
return v___x_3334_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___boxed(lean_object* v_a_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_){
_start:
{
lean_object* v_res_3412_; 
v_res_3412_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg(v_a_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_);
lean_dec(v___y_3410_);
lean_dec_ref(v___y_3409_);
lean_dec(v___y_3408_);
lean_dec_ref(v___y_3407_);
return v_res_3412_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; 
v___x_3418_ = lean_box(0);
v___x_3419_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__2));
v___x_3420_ = l_Lean_mkConst(v___x_3419_, v___x_3418_);
return v___x_3420_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6(void){
_start:
{
lean_object* v___x_3426_; lean_object* v___x_3427_; 
v___x_3426_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__5));
v___x_3427_ = l_Lean_stringToMessageData(v___x_3426_);
return v___x_3427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0(lean_object* v_ctorVal_3428_, lean_object* v_xs_3429_, lean_object* v_type_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_){
_start:
{
lean_object* v___x_3436_; lean_object* v___x_3437_; 
v___x_3436_ = lean_box(0);
v___x_3437_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_3430_, v___x_3436_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_);
if (lean_obj_tag(v___x_3437_) == 0)
{
lean_object* v_a_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; uint8_t v___x_3442_; uint8_t v___x_3443_; lean_object* v___y_3445_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; 
v_a_3438_ = lean_ctor_get(v___x_3437_, 0);
lean_inc(v_a_3438_);
lean_dec_ref_known(v___x_3437_, 1);
v___x_3439_ = l_Lean_Expr_mvarId_x21(v_a_3438_);
v___x_3440_ = lean_box(0);
v___x_3441_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3);
v___x_3442_ = 1;
v___x_3443_ = 0;
v___x_3456_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__4));
v___x_3457_ = lean_box(0);
v___x_3458_ = l_Lean_MVarId_apply(v___x_3439_, v___x_3441_, v___x_3456_, v___x_3457_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_);
if (lean_obj_tag(v___x_3458_) == 0)
{
lean_object* v_a_3459_; lean_object* v___y_3461_; lean_object* v___y_3462_; lean_object* v___y_3463_; lean_object* v___y_3464_; 
v_a_3459_ = lean_ctor_get(v___x_3458_, 0);
lean_inc(v_a_3459_);
lean_dec_ref_known(v___x_3458_, 1);
if (lean_obj_tag(v_a_3459_) == 1)
{
lean_object* v_tail_3473_; 
v_tail_3473_ = lean_ctor_get(v_a_3459_, 1);
lean_inc(v_tail_3473_);
if (lean_obj_tag(v_tail_3473_) == 1)
{
lean_object* v_tail_3474_; 
v_tail_3474_ = lean_ctor_get(v_tail_3473_, 1);
if (lean_obj_tag(v_tail_3474_) == 0)
{
lean_object* v_toConstantVal_3475_; lean_object* v_head_3476_; lean_object* v_head_3477_; lean_object* v_name_3478_; lean_object* v_levelParams_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; 
v_toConstantVal_3475_ = lean_ctor_get(v_ctorVal_3428_, 0);
lean_inc_ref(v_toConstantVal_3475_);
lean_dec_ref(v_ctorVal_3428_);
v_head_3476_ = lean_ctor_get(v_a_3459_, 0);
lean_inc(v_head_3476_);
lean_dec_ref_known(v_a_3459_, 2);
v_head_3477_ = lean_ctor_get(v_tail_3473_, 0);
lean_inc(v_head_3477_);
lean_dec_ref_known(v_tail_3473_, 2);
v_name_3478_ = lean_ctor_get(v_toConstantVal_3475_, 0);
lean_inc_n(v_name_3478_, 2);
v_levelParams_3479_ = lean_ctor_get(v_toConstantVal_3475_, 1);
lean_inc(v_levelParams_3479_);
lean_dec_ref(v_toConstantVal_3475_);
v___x_3480_ = l_Lean_Meta_mkInjectiveTheoremNameFor(v_name_3478_);
v___x_3481_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(v_levelParams_3479_, v___x_3440_);
v___x_3482_ = l_Lean_mkConst(v___x_3480_, v___x_3481_);
v___x_3483_ = l_Lean_mkAppN(v___x_3482_, v_xs_3429_);
v___x_3484_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(v_head_3476_, v___x_3483_, v___y_3432_);
lean_dec_ref(v___x_3484_);
v___x_3485_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg(v_head_3477_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_);
if (lean_obj_tag(v___x_3485_) == 0)
{
lean_object* v_a_3486_; lean_object* v___x_3487_; 
v_a_3486_ = lean_ctor_get(v___x_3485_, 0);
lean_inc(v_a_3486_);
lean_dec_ref_known(v___x_3485_, 1);
v___x_3487_ = l_Lean_MVarId_refl(v_a_3486_, v___x_3442_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_);
if (lean_obj_tag(v___x_3487_) == 0)
{
lean_dec(v_name_3478_);
v___y_3445_ = v___x_3487_;
goto v___jp_3444_;
}
else
{
lean_object* v_a_3488_; uint8_t v___y_3490_; uint8_t v___x_3493_; 
v_a_3488_ = lean_ctor_get(v___x_3487_, 0);
lean_inc(v_a_3488_);
v___x_3493_ = l_Lean_Exception_isInterrupt(v_a_3488_);
if (v___x_3493_ == 0)
{
uint8_t v___x_3494_; 
v___x_3494_ = l_Lean_Exception_isRuntime(v_a_3488_);
v___y_3490_ = v___x_3494_;
goto v___jp_3489_;
}
else
{
lean_dec(v_a_3488_);
v___y_3490_ = v___x_3493_;
goto v___jp_3489_;
}
v___jp_3489_:
{
if (v___y_3490_ == 0)
{
lean_object* v___x_3491_; lean_object* v___x_3492_; 
lean_dec_ref_known(v___x_3487_, 1);
v___x_3491_ = l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(v_name_3478_);
v___x_3492_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_3491_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_);
v___y_3445_ = v___x_3492_;
goto v___jp_3444_;
}
else
{
lean_dec(v_name_3478_);
v___y_3445_ = v___x_3487_;
goto v___jp_3444_;
}
}
}
}
else
{
lean_object* v_a_3495_; lean_object* v___x_3497_; uint8_t v_isShared_3498_; uint8_t v_isSharedCheck_3502_; 
lean_dec(v_name_3478_);
lean_dec(v_a_3438_);
v_a_3495_ = lean_ctor_get(v___x_3485_, 0);
v_isSharedCheck_3502_ = !lean_is_exclusive(v___x_3485_);
if (v_isSharedCheck_3502_ == 0)
{
v___x_3497_ = v___x_3485_;
v_isShared_3498_ = v_isSharedCheck_3502_;
goto v_resetjp_3496_;
}
else
{
lean_inc(v_a_3495_);
lean_dec(v___x_3485_);
v___x_3497_ = lean_box(0);
v_isShared_3498_ = v_isSharedCheck_3502_;
goto v_resetjp_3496_;
}
v_resetjp_3496_:
{
lean_object* v___x_3500_; 
if (v_isShared_3498_ == 0)
{
v___x_3500_ = v___x_3497_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v_a_3495_);
v___x_3500_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
return v___x_3500_;
}
}
}
}
else
{
lean_dec_ref_known(v_tail_3473_, 2);
lean_dec_ref_known(v_a_3459_, 2);
lean_dec(v_a_3438_);
v___y_3461_ = v___y_3431_;
v___y_3462_ = v___y_3432_;
v___y_3463_ = v___y_3433_;
v___y_3464_ = v___y_3434_;
goto v___jp_3460_;
}
}
else
{
lean_dec(v_tail_3473_);
lean_dec_ref_known(v_a_3459_, 2);
lean_dec(v_a_3438_);
v___y_3461_ = v___y_3431_;
v___y_3462_ = v___y_3432_;
v___y_3463_ = v___y_3433_;
v___y_3464_ = v___y_3434_;
goto v___jp_3460_;
}
}
else
{
lean_dec(v_a_3459_);
lean_dec(v_a_3438_);
v___y_3461_ = v___y_3431_;
v___y_3462_ = v___y_3432_;
v___y_3463_ = v___y_3433_;
v___y_3464_ = v___y_3434_;
goto v___jp_3460_;
}
v___jp_3460_:
{
lean_object* v_toConstantVal_3465_; lean_object* v_name_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; 
v_toConstantVal_3465_ = lean_ctor_get(v_ctorVal_3428_, 0);
lean_inc_ref(v_toConstantVal_3465_);
lean_dec_ref(v_ctorVal_3428_);
v_name_3466_ = lean_ctor_get(v_toConstantVal_3465_, 0);
lean_inc(v_name_3466_);
lean_dec_ref(v_toConstantVal_3465_);
v___x_3467_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6);
v___x_3468_ = l_Lean_MessageData_ofName(v_name_3466_);
v___x_3469_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3469_, 0, v___x_3467_);
lean_ctor_set(v___x_3469_, 1, v___x_3468_);
v___x_3470_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_3471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3471_, 0, v___x_3469_);
lean_ctor_set(v___x_3471_, 1, v___x_3470_);
v___x_3472_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_3471_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_);
return v___x_3472_;
}
}
else
{
lean_object* v_a_3503_; lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3510_; 
lean_dec(v_a_3438_);
lean_dec_ref(v_ctorVal_3428_);
v_a_3503_ = lean_ctor_get(v___x_3458_, 0);
v_isSharedCheck_3510_ = !lean_is_exclusive(v___x_3458_);
if (v_isSharedCheck_3510_ == 0)
{
v___x_3505_ = v___x_3458_;
v_isShared_3506_ = v_isSharedCheck_3510_;
goto v_resetjp_3504_;
}
else
{
lean_inc(v_a_3503_);
lean_dec(v___x_3458_);
v___x_3505_ = lean_box(0);
v_isShared_3506_ = v_isSharedCheck_3510_;
goto v_resetjp_3504_;
}
v_resetjp_3504_:
{
lean_object* v___x_3508_; 
if (v_isShared_3506_ == 0)
{
v___x_3508_ = v___x_3505_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v_a_3503_);
v___x_3508_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
return v___x_3508_;
}
}
}
v___jp_3444_:
{
if (lean_obj_tag(v___y_3445_) == 0)
{
uint8_t v___x_3446_; lean_object* v___x_3447_; 
lean_dec_ref_known(v___y_3445_, 1);
v___x_3446_ = 1;
v___x_3447_ = l_Lean_Meta_mkLambdaFVars(v_xs_3429_, v_a_3438_, v___x_3443_, v___x_3442_, v___x_3443_, v___x_3442_, v___x_3446_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_);
return v___x_3447_;
}
else
{
lean_object* v_a_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3455_; 
lean_dec(v_a_3438_);
v_a_3448_ = lean_ctor_get(v___y_3445_, 0);
v_isSharedCheck_3455_ = !lean_is_exclusive(v___y_3445_);
if (v_isSharedCheck_3455_ == 0)
{
v___x_3450_ = v___y_3445_;
v_isShared_3451_ = v_isSharedCheck_3455_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_a_3448_);
lean_dec(v___y_3445_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3455_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v___x_3453_; 
if (v_isShared_3451_ == 0)
{
v___x_3453_ = v___x_3450_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v_a_3448_);
v___x_3453_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
return v___x_3453_;
}
}
}
}
}
else
{
lean_dec_ref(v_ctorVal_3428_);
return v___x_3437_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___boxed(lean_object* v_ctorVal_3511_, lean_object* v_xs_3512_, lean_object* v_type_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_){
_start:
{
lean_object* v_res_3519_; 
v_res_3519_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0(v_ctorVal_3511_, v_xs_3512_, v_type_3513_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_);
lean_dec(v___y_3517_);
lean_dec_ref(v___y_3516_);
lean_dec(v___y_3515_);
lean_dec_ref(v___y_3514_);
lean_dec_ref(v_xs_3512_);
return v_res_3519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(lean_object* v_ctorVal_3520_, lean_object* v_targetType_3521_, lean_object* v_a_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_){
_start:
{
lean_object* v___f_3527_; uint8_t v___x_3528_; lean_object* v___x_3529_; 
v___f_3527_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3527_, 0, v_ctorVal_3520_);
v___x_3528_ = 0;
v___x_3529_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_targetType_3521_, v___f_3527_, v___x_3528_, v___x_3528_, v_a_3522_, v_a_3523_, v_a_3524_, v_a_3525_);
return v___x_3529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___boxed(lean_object* v_ctorVal_3530_, lean_object* v_targetType_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_){
_start:
{
lean_object* v_res_3537_; 
v_res_3537_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3530_, v_targetType_3531_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_);
lean_dec(v_a_3535_);
lean_dec_ref(v_a_3534_);
lean_dec(v_a_3533_);
lean_dec_ref(v_a_3532_);
return v_res_3537_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0(lean_object* v_mvarId_3538_, lean_object* v_val_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_){
_start:
{
lean_object* v___x_3545_; 
v___x_3545_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(v_mvarId_3538_, v_val_3539_, v___y_3541_);
return v___x_3545_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___boxed(lean_object* v_mvarId_3546_, lean_object* v_val_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_){
_start:
{
lean_object* v_res_3553_; 
v_res_3553_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0(v_mvarId_3546_, v_val_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_);
lean_dec(v___y_3551_);
lean_dec_ref(v___y_3550_);
lean_dec(v___y_3549_);
lean_dec_ref(v___y_3548_);
return v_res_3553_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1(lean_object* v_inst_3554_, lean_object* v_a_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_){
_start:
{
lean_object* v___x_3561_; 
v___x_3561_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg(v_a_3555_, v___y_3556_, v___y_3557_, v___y_3558_, v___y_3559_);
return v___x_3561_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___boxed(lean_object* v_inst_3562_, lean_object* v_a_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_){
_start:
{
lean_object* v_res_3569_; 
v_res_3569_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1(v_inst_3562_, v_a_3563_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_);
lean_dec(v___y_3567_);
lean_dec_ref(v___y_3566_);
lean_dec(v___y_3565_);
lean_dec_ref(v___y_3564_);
return v_res_3569_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0(lean_object* v_00_u03b2_3570_, lean_object* v_x_3571_, lean_object* v_x_3572_, lean_object* v_x_3573_){
_start:
{
lean_object* v___x_3574_; 
v___x_3574_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(v_x_3571_, v_x_3572_, v_x_3573_);
return v___x_3574_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3575_, lean_object* v_x_3576_, size_t v_x_3577_, size_t v_x_3578_, lean_object* v_x_3579_, lean_object* v_x_3580_){
_start:
{
lean_object* v___x_3581_; 
v___x_3581_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_x_3576_, v_x_3577_, v_x_3578_, v_x_3579_, v_x_3580_);
return v___x_3581_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3582_, lean_object* v_x_3583_, lean_object* v_x_3584_, lean_object* v_x_3585_, lean_object* v_x_3586_, lean_object* v_x_3587_){
_start:
{
size_t v_x_5824__boxed_3588_; size_t v_x_5825__boxed_3589_; lean_object* v_res_3590_; 
v_x_5824__boxed_3588_ = lean_unbox_usize(v_x_3584_);
lean_dec(v_x_3584_);
v_x_5825__boxed_3589_ = lean_unbox_usize(v_x_3585_);
lean_dec(v_x_3585_);
v_res_3590_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1(v_00_u03b2_3582_, v_x_3583_, v_x_5824__boxed_3588_, v_x_5825__boxed_3589_, v_x_3586_, v_x_3587_);
return v_res_3590_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_3591_, lean_object* v_n_3592_, lean_object* v_k_3593_, lean_object* v_v_3594_){
_start:
{
lean_object* v___x_3595_; 
v___x_3595_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(v_n_3592_, v_k_3593_, v_v_3594_);
return v___x_3595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_3596_, size_t v_depth_3597_, lean_object* v_keys_3598_, lean_object* v_vals_3599_, lean_object* v_heq_3600_, lean_object* v_i_3601_, lean_object* v_entries_3602_){
_start:
{
lean_object* v___x_3603_; 
v___x_3603_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_3597_, v_keys_3598_, v_vals_3599_, v_i_3601_, v_entries_3602_);
return v___x_3603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_3604_, lean_object* v_depth_3605_, lean_object* v_keys_3606_, lean_object* v_vals_3607_, lean_object* v_heq_3608_, lean_object* v_i_3609_, lean_object* v_entries_3610_){
_start:
{
size_t v_depth_boxed_3611_; lean_object* v_res_3612_; 
v_depth_boxed_3611_ = lean_unbox_usize(v_depth_3605_);
lean_dec(v_depth_3605_);
v_res_3612_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_3604_, v_depth_boxed_3611_, v_keys_3606_, v_vals_3607_, v_heq_3608_, v_i_3609_, v_entries_3610_);
lean_dec_ref(v_vals_3607_);
lean_dec_ref(v_keys_3606_);
return v_res_3612_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_3613_, lean_object* v_x_3614_, lean_object* v_x_3615_, lean_object* v_x_3616_, lean_object* v_x_3617_){
_start:
{
lean_object* v___x_3618_; 
v___x_3618_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_x_3614_, v_x_3615_, v_x_3616_, v_x_3617_);
return v___x_3618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(lean_object* v_ctorVal_3619_, lean_object* v_val_3620_, lean_object* v_name_3621_, lean_object* v_levelParams_3622_, uint8_t v___x_3623_, uint8_t v_hasTrace_3624_, lean_object* v_____r_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_){
_start:
{
lean_object* v___x_3631_; 
lean_inc_ref(v_val_3620_);
v___x_3631_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3619_, v_val_3620_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_);
if (lean_obj_tag(v___x_3631_) == 0)
{
lean_object* v_a_3632_; lean_object* v___x_3633_; lean_object* v_a_3634_; lean_object* v___x_3635_; lean_object* v_a_3636_; lean_object* v___x_3638_; uint8_t v_isShared_3639_; uint8_t v_isSharedCheck_3652_; 
v_a_3632_ = lean_ctor_get(v___x_3631_, 0);
lean_inc(v_a_3632_);
lean_dec_ref_known(v___x_3631_, 1);
v___x_3633_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3620_, v___y_3627_);
v_a_3634_ = lean_ctor_get(v___x_3633_, 0);
lean_inc(v_a_3634_);
lean_dec_ref(v___x_3633_);
v___x_3635_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3632_, v___y_3627_);
v_a_3636_ = lean_ctor_get(v___x_3635_, 0);
v_isSharedCheck_3652_ = !lean_is_exclusive(v___x_3635_);
if (v_isSharedCheck_3652_ == 0)
{
v___x_3638_ = v___x_3635_;
v_isShared_3639_ = v_isSharedCheck_3652_;
goto v_resetjp_3637_;
}
else
{
lean_inc(v_a_3636_);
lean_dec(v___x_3635_);
v___x_3638_ = lean_box(0);
v_isShared_3639_ = v_isSharedCheck_3652_;
goto v_resetjp_3637_;
}
v_resetjp_3637_:
{
lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3645_; 
lean_inc_n(v_name_3621_, 2);
v___x_3640_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3640_, 0, v_name_3621_);
lean_ctor_set(v___x_3640_, 1, v_levelParams_3622_);
lean_ctor_set(v___x_3640_, 2, v_a_3634_);
v___x_3641_ = lean_box(0);
v___x_3642_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3642_, 0, v_name_3621_);
lean_ctor_set(v___x_3642_, 1, v___x_3641_);
v___x_3643_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3643_, 0, v___x_3640_);
lean_ctor_set(v___x_3643_, 1, v_a_3636_);
lean_ctor_set(v___x_3643_, 2, v___x_3642_);
if (v_isShared_3639_ == 0)
{
lean_ctor_set_tag(v___x_3638_, 2);
lean_ctor_set(v___x_3638_, 0, v___x_3643_);
v___x_3645_ = v___x_3638_;
goto v_reusejp_3644_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v___x_3643_);
v___x_3645_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3644_;
}
v_reusejp_3644_:
{
lean_object* v___x_3646_; 
v___x_3646_ = l_Lean_addDecl(v___x_3645_, v___x_3623_, v___y_3628_, v___y_3629_);
if (lean_obj_tag(v___x_3646_) == 0)
{
lean_object* v___x_3647_; uint8_t v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; 
lean_dec_ref_known(v___x_3646_, 1);
v___x_3647_ = l_Lean_Meta_simpExtension;
v___x_3648_ = 0;
v___x_3649_ = lean_unsigned_to_nat(1000u);
v___x_3650_ = l_Lean_Meta_addSimpTheorem(v___x_3647_, v_name_3621_, v_hasTrace_3624_, v___x_3623_, v___x_3648_, v___x_3649_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_);
return v___x_3650_;
}
else
{
lean_dec(v_name_3621_);
return v___x_3646_;
}
}
}
}
else
{
lean_object* v_a_3653_; lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3660_; 
lean_dec(v_levelParams_3622_);
lean_dec(v_name_3621_);
lean_dec_ref(v_val_3620_);
v_a_3653_ = lean_ctor_get(v___x_3631_, 0);
v_isSharedCheck_3660_ = !lean_is_exclusive(v___x_3631_);
if (v_isSharedCheck_3660_ == 0)
{
v___x_3655_ = v___x_3631_;
v_isShared_3656_ = v_isSharedCheck_3660_;
goto v_resetjp_3654_;
}
else
{
lean_inc(v_a_3653_);
lean_dec(v___x_3631_);
v___x_3655_ = lean_box(0);
v_isShared_3656_ = v_isSharedCheck_3660_;
goto v_resetjp_3654_;
}
v_resetjp_3654_:
{
lean_object* v___x_3658_; 
if (v_isShared_3656_ == 0)
{
v___x_3658_ = v___x_3655_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3659_; 
v_reuseFailAlloc_3659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3659_, 0, v_a_3653_);
v___x_3658_ = v_reuseFailAlloc_3659_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
return v___x_3658_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1___boxed(lean_object* v_ctorVal_3661_, lean_object* v_val_3662_, lean_object* v_name_3663_, lean_object* v_levelParams_3664_, lean_object* v___x_3665_, lean_object* v_hasTrace_3666_, lean_object* v_____r_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_){
_start:
{
uint8_t v___x_8689__boxed_3673_; uint8_t v_hasTrace_boxed_3674_; lean_object* v_res_3675_; 
v___x_8689__boxed_3673_ = lean_unbox(v___x_3665_);
v_hasTrace_boxed_3674_ = lean_unbox(v_hasTrace_3666_);
v_res_3675_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(v_ctorVal_3661_, v_val_3662_, v_name_3663_, v_levelParams_3664_, v___x_8689__boxed_3673_, v_hasTrace_boxed_3674_, v_____r_3667_, v___y_3668_, v___y_3669_, v___y_3670_, v___y_3671_);
lean_dec(v___y_3671_);
lean_dec_ref(v___y_3670_);
lean_dec(v___y_3669_);
lean_dec_ref(v___y_3668_);
return v_res_3675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(lean_object* v_ctorVal_3676_, lean_object* v_val_3677_, lean_object* v_name_3678_, lean_object* v_levelParams_3679_, uint8_t v___x_3680_, lean_object* v_____r_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_){
_start:
{
lean_object* v___x_3687_; 
lean_inc_ref(v_val_3677_);
v___x_3687_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3676_, v_val_3677_, v___y_3682_, v___y_3683_, v___y_3684_, v___y_3685_);
if (lean_obj_tag(v___x_3687_) == 0)
{
lean_object* v_a_3688_; lean_object* v___x_3689_; lean_object* v_a_3690_; lean_object* v___x_3691_; lean_object* v_a_3692_; lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3709_; 
v_a_3688_ = lean_ctor_get(v___x_3687_, 0);
lean_inc(v_a_3688_);
lean_dec_ref_known(v___x_3687_, 1);
v___x_3689_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3677_, v___y_3683_);
v_a_3690_ = lean_ctor_get(v___x_3689_, 0);
lean_inc(v_a_3690_);
lean_dec_ref(v___x_3689_);
v___x_3691_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3688_, v___y_3683_);
v_a_3692_ = lean_ctor_get(v___x_3691_, 0);
v_isSharedCheck_3709_ = !lean_is_exclusive(v___x_3691_);
if (v_isSharedCheck_3709_ == 0)
{
v___x_3694_ = v___x_3691_;
v_isShared_3695_ = v_isSharedCheck_3709_;
goto v_resetjp_3693_;
}
else
{
lean_inc(v_a_3692_);
lean_dec(v___x_3691_);
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3709_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3701_; 
lean_inc_n(v_name_3678_, 2);
v___x_3696_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3696_, 0, v_name_3678_);
lean_ctor_set(v___x_3696_, 1, v_levelParams_3679_);
lean_ctor_set(v___x_3696_, 2, v_a_3690_);
v___x_3697_ = lean_box(0);
v___x_3698_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3698_, 0, v_name_3678_);
lean_ctor_set(v___x_3698_, 1, v___x_3697_);
v___x_3699_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3699_, 0, v___x_3696_);
lean_ctor_set(v___x_3699_, 1, v_a_3692_);
lean_ctor_set(v___x_3699_, 2, v___x_3698_);
if (v_isShared_3695_ == 0)
{
lean_ctor_set_tag(v___x_3694_, 2);
lean_ctor_set(v___x_3694_, 0, v___x_3699_);
v___x_3701_ = v___x_3694_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v___x_3699_);
v___x_3701_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
uint8_t v___x_3702_; lean_object* v___x_3703_; 
v___x_3702_ = 0;
v___x_3703_ = l_Lean_addDecl(v___x_3701_, v___x_3702_, v___y_3684_, v___y_3685_);
if (lean_obj_tag(v___x_3703_) == 0)
{
lean_object* v___x_3704_; uint8_t v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; 
lean_dec_ref_known(v___x_3703_, 1);
v___x_3704_ = l_Lean_Meta_simpExtension;
v___x_3705_ = 0;
v___x_3706_ = lean_unsigned_to_nat(1000u);
v___x_3707_ = l_Lean_Meta_addSimpTheorem(v___x_3704_, v_name_3678_, v___x_3680_, v___x_3702_, v___x_3705_, v___x_3706_, v___y_3682_, v___y_3683_, v___y_3684_, v___y_3685_);
return v___x_3707_;
}
else
{
lean_dec(v_name_3678_);
return v___x_3703_;
}
}
}
}
else
{
lean_object* v_a_3710_; lean_object* v___x_3712_; uint8_t v_isShared_3713_; uint8_t v_isSharedCheck_3717_; 
lean_dec(v_levelParams_3679_);
lean_dec(v_name_3678_);
lean_dec_ref(v_val_3677_);
v_a_3710_ = lean_ctor_get(v___x_3687_, 0);
v_isSharedCheck_3717_ = !lean_is_exclusive(v___x_3687_);
if (v_isSharedCheck_3717_ == 0)
{
v___x_3712_ = v___x_3687_;
v_isShared_3713_ = v_isSharedCheck_3717_;
goto v_resetjp_3711_;
}
else
{
lean_inc(v_a_3710_);
lean_dec(v___x_3687_);
v___x_3712_ = lean_box(0);
v_isShared_3713_ = v_isSharedCheck_3717_;
goto v_resetjp_3711_;
}
v_resetjp_3711_:
{
lean_object* v___x_3715_; 
if (v_isShared_3713_ == 0)
{
v___x_3715_ = v___x_3712_;
goto v_reusejp_3714_;
}
else
{
lean_object* v_reuseFailAlloc_3716_; 
v_reuseFailAlloc_3716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3716_, 0, v_a_3710_);
v___x_3715_ = v_reuseFailAlloc_3716_;
goto v_reusejp_3714_;
}
v_reusejp_3714_:
{
return v___x_3715_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0___boxed(lean_object* v_ctorVal_3718_, lean_object* v_val_3719_, lean_object* v_name_3720_, lean_object* v_levelParams_3721_, lean_object* v___x_3722_, lean_object* v_____r_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_){
_start:
{
uint8_t v___x_8777__boxed_3729_; lean_object* v_res_3730_; 
v___x_8777__boxed_3729_ = lean_unbox(v___x_3722_);
v_res_3730_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(v_ctorVal_3718_, v_val_3719_, v_name_3720_, v_levelParams_3721_, v___x_8777__boxed_3729_, v_____r_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_);
lean_dec(v___y_3727_);
lean_dec_ref(v___y_3726_);
lean_dec(v___y_3725_);
lean_dec_ref(v___y_3724_);
return v_res_3730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(lean_object* v_ctorVal_3731_, lean_object* v_a_3732_, lean_object* v_a_3733_, lean_object* v_a_3734_, lean_object* v_a_3735_){
_start:
{
lean_object* v_toConstantVal_3737_; lean_object* v_toCold_3738_; lean_object* v_options_3739_; lean_object* v_name_3740_; lean_object* v_levelParams_3741_; lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3961_; 
v_toConstantVal_3737_ = lean_ctor_get(v_ctorVal_3731_, 0);
lean_inc_ref(v_toConstantVal_3737_);
v_toCold_3738_ = lean_ctor_get(v_a_3734_, 0);
v_options_3739_ = lean_ctor_get(v_toCold_3738_, 2);
v_name_3740_ = lean_ctor_get(v_toConstantVal_3737_, 0);
v_levelParams_3741_ = lean_ctor_get(v_toConstantVal_3737_, 1);
v_isSharedCheck_3961_ = !lean_is_exclusive(v_toConstantVal_3737_);
if (v_isSharedCheck_3961_ == 0)
{
lean_object* v_unused_3962_; 
v_unused_3962_ = lean_ctor_get(v_toConstantVal_3737_, 2);
lean_dec(v_unused_3962_);
v___x_3743_ = v_toConstantVal_3737_;
v_isShared_3744_ = v_isSharedCheck_3961_;
goto v_resetjp_3742_;
}
else
{
lean_inc(v_levelParams_3741_);
lean_inc(v_name_3740_);
lean_dec(v_toConstantVal_3737_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3961_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
lean_object* v_inheritedTraceOptions_3745_; uint8_t v_hasTrace_3746_; lean_object* v_name_3747_; 
v_inheritedTraceOptions_3745_ = lean_ctor_get(v_toCold_3738_, 11);
v_hasTrace_3746_ = lean_ctor_get_uint8(v_options_3739_, sizeof(void*)*1);
v_name_3747_ = l_Lean_Meta_mkInjectiveEqTheoremNameFor(v_name_3740_);
if (v_hasTrace_3746_ == 0)
{
lean_object* v___x_3748_; 
lean_inc_ref(v_ctorVal_3731_);
v___x_3748_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3731_, v_a_3732_, v_a_3733_, v_a_3734_, v_a_3735_);
if (lean_obj_tag(v___x_3748_) == 0)
{
lean_object* v_a_3749_; lean_object* v___x_3751_; uint8_t v_isShared_3752_; uint8_t v_isSharedCheck_3791_; 
v_a_3749_ = lean_ctor_get(v___x_3748_, 0);
v_isSharedCheck_3791_ = !lean_is_exclusive(v___x_3748_);
if (v_isSharedCheck_3791_ == 0)
{
v___x_3751_ = v___x_3748_;
v_isShared_3752_ = v_isSharedCheck_3791_;
goto v_resetjp_3750_;
}
else
{
lean_inc(v_a_3749_);
lean_dec(v___x_3748_);
v___x_3751_ = lean_box(0);
v_isShared_3752_ = v_isSharedCheck_3791_;
goto v_resetjp_3750_;
}
v_resetjp_3750_:
{
if (lean_obj_tag(v_a_3749_) == 1)
{
lean_object* v_val_3753_; lean_object* v___x_3754_; 
lean_del_object(v___x_3751_);
v_val_3753_ = lean_ctor_get(v_a_3749_, 0);
lean_inc_n(v_val_3753_, 2);
lean_dec_ref_known(v_a_3749_, 1);
v___x_3754_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3731_, v_val_3753_, v_a_3732_, v_a_3733_, v_a_3734_, v_a_3735_);
if (lean_obj_tag(v___x_3754_) == 0)
{
lean_object* v_a_3755_; lean_object* v___x_3756_; lean_object* v_a_3757_; lean_object* v___x_3758_; lean_object* v_a_3759_; lean_object* v___x_3761_; uint8_t v_isShared_3762_; uint8_t v_isSharedCheck_3778_; 
v_a_3755_ = lean_ctor_get(v___x_3754_, 0);
lean_inc(v_a_3755_);
lean_dec_ref_known(v___x_3754_, 1);
v___x_3756_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3753_, v_a_3733_);
v_a_3757_ = lean_ctor_get(v___x_3756_, 0);
lean_inc(v_a_3757_);
lean_dec_ref(v___x_3756_);
v___x_3758_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3755_, v_a_3733_);
v_a_3759_ = lean_ctor_get(v___x_3758_, 0);
v_isSharedCheck_3778_ = !lean_is_exclusive(v___x_3758_);
if (v_isSharedCheck_3778_ == 0)
{
v___x_3761_ = v___x_3758_;
v_isShared_3762_ = v_isSharedCheck_3778_;
goto v_resetjp_3760_;
}
else
{
lean_inc(v_a_3759_);
lean_dec(v___x_3758_);
v___x_3761_ = lean_box(0);
v_isShared_3762_ = v_isSharedCheck_3778_;
goto v_resetjp_3760_;
}
v_resetjp_3760_:
{
lean_object* v___x_3764_; 
lean_inc(v_name_3747_);
if (v_isShared_3744_ == 0)
{
lean_ctor_set(v___x_3743_, 2, v_a_3757_);
lean_ctor_set(v___x_3743_, 0, v_name_3747_);
v___x_3764_ = v___x_3743_;
goto v_reusejp_3763_;
}
else
{
lean_object* v_reuseFailAlloc_3777_; 
v_reuseFailAlloc_3777_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3777_, 0, v_name_3747_);
lean_ctor_set(v_reuseFailAlloc_3777_, 1, v_levelParams_3741_);
lean_ctor_set(v_reuseFailAlloc_3777_, 2, v_a_3757_);
v___x_3764_ = v_reuseFailAlloc_3777_;
goto v_reusejp_3763_;
}
v_reusejp_3763_:
{
lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3769_; 
v___x_3765_ = lean_box(0);
lean_inc(v_name_3747_);
v___x_3766_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3766_, 0, v_name_3747_);
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
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v___x_3767_);
v___x_3769_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3768_;
}
v_reusejp_3768_:
{
lean_object* v___x_3770_; 
v___x_3770_ = l_Lean_addDecl(v___x_3769_, v_hasTrace_3746_, v_a_3734_, v_a_3735_);
if (lean_obj_tag(v___x_3770_) == 0)
{
lean_object* v___x_3771_; uint8_t v___x_3772_; uint8_t v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; 
lean_dec_ref_known(v___x_3770_, 1);
v___x_3771_ = l_Lean_Meta_simpExtension;
v___x_3772_ = 1;
v___x_3773_ = 0;
v___x_3774_ = lean_unsigned_to_nat(1000u);
v___x_3775_ = l_Lean_Meta_addSimpTheorem(v___x_3771_, v_name_3747_, v___x_3772_, v_hasTrace_3746_, v___x_3773_, v___x_3774_, v_a_3732_, v_a_3733_, v_a_3734_, v_a_3735_);
return v___x_3775_;
}
else
{
lean_dec(v_name_3747_);
return v___x_3770_;
}
}
}
}
}
else
{
lean_object* v_a_3779_; lean_object* v___x_3781_; uint8_t v_isShared_3782_; uint8_t v_isSharedCheck_3786_; 
lean_dec(v_val_3753_);
lean_dec(v_name_3747_);
lean_del_object(v___x_3743_);
lean_dec(v_levelParams_3741_);
v_a_3779_ = lean_ctor_get(v___x_3754_, 0);
v_isSharedCheck_3786_ = !lean_is_exclusive(v___x_3754_);
if (v_isSharedCheck_3786_ == 0)
{
v___x_3781_ = v___x_3754_;
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
else
{
lean_inc(v_a_3779_);
lean_dec(v___x_3754_);
v___x_3781_ = lean_box(0);
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
v_resetjp_3780_:
{
lean_object* v___x_3784_; 
if (v_isShared_3782_ == 0)
{
v___x_3784_ = v___x_3781_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3785_; 
v_reuseFailAlloc_3785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v_a_3779_);
v___x_3784_ = v_reuseFailAlloc_3785_;
goto v_reusejp_3783_;
}
v_reusejp_3783_:
{
return v___x_3784_;
}
}
}
}
else
{
lean_object* v___x_3787_; lean_object* v___x_3789_; 
lean_dec(v_a_3749_);
lean_dec(v_name_3747_);
lean_del_object(v___x_3743_);
lean_dec(v_levelParams_3741_);
lean_dec_ref(v_ctorVal_3731_);
v___x_3787_ = lean_box(0);
if (v_isShared_3752_ == 0)
{
lean_ctor_set(v___x_3751_, 0, v___x_3787_);
v___x_3789_ = v___x_3751_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v___x_3787_);
v___x_3789_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
return v___x_3789_;
}
}
}
}
else
{
lean_object* v_a_3792_; lean_object* v___x_3794_; uint8_t v_isShared_3795_; uint8_t v_isSharedCheck_3799_; 
lean_dec(v_name_3747_);
lean_del_object(v___x_3743_);
lean_dec(v_levelParams_3741_);
lean_dec_ref(v_ctorVal_3731_);
v_a_3792_ = lean_ctor_get(v___x_3748_, 0);
v_isSharedCheck_3799_ = !lean_is_exclusive(v___x_3748_);
if (v_isSharedCheck_3799_ == 0)
{
v___x_3794_ = v___x_3748_;
v_isShared_3795_ = v_isSharedCheck_3799_;
goto v_resetjp_3793_;
}
else
{
lean_inc(v_a_3792_);
lean_dec(v___x_3748_);
v___x_3794_ = lean_box(0);
v_isShared_3795_ = v_isSharedCheck_3799_;
goto v_resetjp_3793_;
}
v_resetjp_3793_:
{
lean_object* v___x_3797_; 
if (v_isShared_3795_ == 0)
{
v___x_3797_ = v___x_3794_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v_a_3792_);
v___x_3797_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
return v___x_3797_;
}
}
}
}
else
{
lean_object* v___f_3800_; lean_object* v_cls_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; uint8_t v___x_3804_; lean_object* v___y_3806_; lean_object* v___y_3807_; lean_object* v_a_3808_; lean_object* v___y_3818_; lean_object* v___y_3819_; lean_object* v_a_3820_; lean_object* v___y_3823_; lean_object* v___y_3824_; lean_object* v_a_3825_; lean_object* v___y_3828_; lean_object* v___y_3829_; lean_object* v___y_3830_; lean_object* v___y_3834_; lean_object* v___y_3835_; lean_object* v_a_3836_; lean_object* v___y_3849_; lean_object* v___y_3850_; lean_object* v_a_3851_; lean_object* v___y_3854_; lean_object* v___y_3855_; lean_object* v_a_3856_; lean_object* v___y_3859_; lean_object* v___y_3860_; lean_object* v___y_3861_; 
lean_inc(v_name_3747_);
v___f_3800_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3800_, 0, v_name_3747_);
v_cls_3801_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_3802_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_3803_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_3804_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3745_, v_options_3739_, v___x_3803_);
if (v___x_3804_ == 0)
{
lean_object* v___x_3899_; uint8_t v___x_3900_; 
v___x_3899_ = l_Lean_trace_profiler;
v___x_3900_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_3739_, v___x_3899_);
if (v___x_3900_ == 0)
{
lean_object* v___x_3901_; 
lean_dec_ref(v___f_3800_);
lean_inc_ref(v_ctorVal_3731_);
v___x_3901_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3731_, v_a_3732_, v_a_3733_, v_a_3734_, v_a_3735_);
if (lean_obj_tag(v___x_3901_) == 0)
{
lean_object* v_a_3902_; lean_object* v___x_3904_; uint8_t v_isShared_3905_; uint8_t v_isSharedCheck_3952_; 
v_a_3902_ = lean_ctor_get(v___x_3901_, 0);
v_isSharedCheck_3952_ = !lean_is_exclusive(v___x_3901_);
if (v_isSharedCheck_3952_ == 0)
{
v___x_3904_ = v___x_3901_;
v_isShared_3905_ = v_isSharedCheck_3952_;
goto v_resetjp_3903_;
}
else
{
lean_inc(v_a_3902_);
lean_dec(v___x_3901_);
v___x_3904_ = lean_box(0);
v_isShared_3905_ = v_isSharedCheck_3952_;
goto v_resetjp_3903_;
}
v_resetjp_3903_:
{
if (lean_obj_tag(v_a_3902_) == 1)
{
lean_object* v_val_3906_; lean_object* v___y_3908_; lean_object* v___y_3909_; lean_object* v___y_3910_; lean_object* v___y_3911_; 
lean_del_object(v___x_3904_);
v_val_3906_ = lean_ctor_get(v_a_3902_, 0);
lean_inc(v_val_3906_);
lean_dec_ref_known(v_a_3902_, 1);
if (v___x_3804_ == 0)
{
v___y_3908_ = v_a_3732_;
v___y_3909_ = v_a_3733_;
v___y_3910_ = v_a_3734_;
v___y_3911_ = v_a_3735_;
goto v___jp_3907_;
}
else
{
lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; 
v___x_3944_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
lean_inc(v_val_3906_);
v___x_3945_ = l_Lean_MessageData_ofExpr(v_val_3906_);
v___x_3946_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3946_, 0, v___x_3944_);
lean_ctor_set(v___x_3946_, 1, v___x_3945_);
v___x_3947_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_3801_, v___x_3946_, v_a_3732_, v_a_3733_, v_a_3734_, v_a_3735_);
if (lean_obj_tag(v___x_3947_) == 0)
{
lean_dec_ref_known(v___x_3947_, 1);
v___y_3908_ = v_a_3732_;
v___y_3909_ = v_a_3733_;
v___y_3910_ = v_a_3734_;
v___y_3911_ = v_a_3735_;
goto v___jp_3907_;
}
else
{
lean_dec(v_val_3906_);
lean_dec(v_name_3747_);
lean_del_object(v___x_3743_);
lean_dec(v_levelParams_3741_);
lean_dec_ref(v_ctorVal_3731_);
return v___x_3947_;
}
}
v___jp_3907_:
{
lean_object* v___x_3912_; 
lean_inc(v_val_3906_);
v___x_3912_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3731_, v_val_3906_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_);
if (lean_obj_tag(v___x_3912_) == 0)
{
lean_object* v_a_3913_; lean_object* v___x_3914_; lean_object* v_a_3915_; lean_object* v___x_3916_; lean_object* v_a_3917_; lean_object* v___x_3919_; uint8_t v_isShared_3920_; uint8_t v_isSharedCheck_3935_; 
v_a_3913_ = lean_ctor_get(v___x_3912_, 0);
lean_inc(v_a_3913_);
lean_dec_ref_known(v___x_3912_, 1);
v___x_3914_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3906_, v___y_3909_);
v_a_3915_ = lean_ctor_get(v___x_3914_, 0);
lean_inc(v_a_3915_);
lean_dec_ref(v___x_3914_);
v___x_3916_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3913_, v___y_3909_);
v_a_3917_ = lean_ctor_get(v___x_3916_, 0);
v_isSharedCheck_3935_ = !lean_is_exclusive(v___x_3916_);
if (v_isSharedCheck_3935_ == 0)
{
v___x_3919_ = v___x_3916_;
v_isShared_3920_ = v_isSharedCheck_3935_;
goto v_resetjp_3918_;
}
else
{
lean_inc(v_a_3917_);
lean_dec(v___x_3916_);
v___x_3919_ = lean_box(0);
v_isShared_3920_ = v_isSharedCheck_3935_;
goto v_resetjp_3918_;
}
v_resetjp_3918_:
{
lean_object* v___x_3922_; 
lean_inc(v_name_3747_);
if (v_isShared_3744_ == 0)
{
lean_ctor_set(v___x_3743_, 2, v_a_3915_);
lean_ctor_set(v___x_3743_, 0, v_name_3747_);
v___x_3922_ = v___x_3743_;
goto v_reusejp_3921_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v_name_3747_);
lean_ctor_set(v_reuseFailAlloc_3934_, 1, v_levelParams_3741_);
lean_ctor_set(v_reuseFailAlloc_3934_, 2, v_a_3915_);
v___x_3922_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3921_;
}
v_reusejp_3921_:
{
lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3927_; 
v___x_3923_ = lean_box(0);
lean_inc(v_name_3747_);
v___x_3924_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3924_, 0, v_name_3747_);
lean_ctor_set(v___x_3924_, 1, v___x_3923_);
v___x_3925_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3925_, 0, v___x_3922_);
lean_ctor_set(v___x_3925_, 1, v_a_3917_);
lean_ctor_set(v___x_3925_, 2, v___x_3924_);
if (v_isShared_3920_ == 0)
{
lean_ctor_set_tag(v___x_3919_, 2);
lean_ctor_set(v___x_3919_, 0, v___x_3925_);
v___x_3927_ = v___x_3919_;
goto v_reusejp_3926_;
}
else
{
lean_object* v_reuseFailAlloc_3933_; 
v_reuseFailAlloc_3933_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3933_, 0, v___x_3925_);
v___x_3927_ = v_reuseFailAlloc_3933_;
goto v_reusejp_3926_;
}
v_reusejp_3926_:
{
lean_object* v___x_3928_; 
v___x_3928_ = l_Lean_addDecl(v___x_3927_, v___x_3900_, v___y_3910_, v___y_3911_);
if (lean_obj_tag(v___x_3928_) == 0)
{
lean_object* v___x_3929_; uint8_t v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; 
lean_dec_ref_known(v___x_3928_, 1);
v___x_3929_ = l_Lean_Meta_simpExtension;
v___x_3930_ = 0;
v___x_3931_ = lean_unsigned_to_nat(1000u);
v___x_3932_ = l_Lean_Meta_addSimpTheorem(v___x_3929_, v_name_3747_, v_hasTrace_3746_, v___x_3900_, v___x_3930_, v___x_3931_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_);
return v___x_3932_;
}
else
{
lean_dec(v_name_3747_);
return v___x_3928_;
}
}
}
}
}
else
{
lean_object* v_a_3936_; lean_object* v___x_3938_; uint8_t v_isShared_3939_; uint8_t v_isSharedCheck_3943_; 
lean_dec(v_val_3906_);
lean_dec(v_name_3747_);
lean_del_object(v___x_3743_);
lean_dec(v_levelParams_3741_);
v_a_3936_ = lean_ctor_get(v___x_3912_, 0);
v_isSharedCheck_3943_ = !lean_is_exclusive(v___x_3912_);
if (v_isSharedCheck_3943_ == 0)
{
v___x_3938_ = v___x_3912_;
v_isShared_3939_ = v_isSharedCheck_3943_;
goto v_resetjp_3937_;
}
else
{
lean_inc(v_a_3936_);
lean_dec(v___x_3912_);
v___x_3938_ = lean_box(0);
v_isShared_3939_ = v_isSharedCheck_3943_;
goto v_resetjp_3937_;
}
v_resetjp_3937_:
{
lean_object* v___x_3941_; 
if (v_isShared_3939_ == 0)
{
v___x_3941_ = v___x_3938_;
goto v_reusejp_3940_;
}
else
{
lean_object* v_reuseFailAlloc_3942_; 
v_reuseFailAlloc_3942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3942_, 0, v_a_3936_);
v___x_3941_ = v_reuseFailAlloc_3942_;
goto v_reusejp_3940_;
}
v_reusejp_3940_:
{
return v___x_3941_;
}
}
}
}
}
else
{
lean_object* v___x_3948_; lean_object* v___x_3950_; 
lean_dec(v_a_3902_);
lean_dec(v_name_3747_);
lean_del_object(v___x_3743_);
lean_dec(v_levelParams_3741_);
lean_dec_ref(v_ctorVal_3731_);
v___x_3948_ = lean_box(0);
if (v_isShared_3905_ == 0)
{
lean_ctor_set(v___x_3904_, 0, v___x_3948_);
v___x_3950_ = v___x_3904_;
goto v_reusejp_3949_;
}
else
{
lean_object* v_reuseFailAlloc_3951_; 
v_reuseFailAlloc_3951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3951_, 0, v___x_3948_);
v___x_3950_ = v_reuseFailAlloc_3951_;
goto v_reusejp_3949_;
}
v_reusejp_3949_:
{
return v___x_3950_;
}
}
}
}
else
{
lean_object* v_a_3953_; lean_object* v___x_3955_; uint8_t v_isShared_3956_; uint8_t v_isSharedCheck_3960_; 
lean_dec(v_name_3747_);
lean_del_object(v___x_3743_);
lean_dec(v_levelParams_3741_);
lean_dec_ref(v_ctorVal_3731_);
v_a_3953_ = lean_ctor_get(v___x_3901_, 0);
v_isSharedCheck_3960_ = !lean_is_exclusive(v___x_3901_);
if (v_isSharedCheck_3960_ == 0)
{
v___x_3955_ = v___x_3901_;
v_isShared_3956_ = v_isSharedCheck_3960_;
goto v_resetjp_3954_;
}
else
{
lean_inc(v_a_3953_);
lean_dec(v___x_3901_);
v___x_3955_ = lean_box(0);
v_isShared_3956_ = v_isSharedCheck_3960_;
goto v_resetjp_3954_;
}
v_resetjp_3954_:
{
lean_object* v___x_3958_; 
if (v_isShared_3956_ == 0)
{
v___x_3958_ = v___x_3955_;
goto v_reusejp_3957_;
}
else
{
lean_object* v_reuseFailAlloc_3959_; 
v_reuseFailAlloc_3959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3959_, 0, v_a_3953_);
v___x_3958_ = v_reuseFailAlloc_3959_;
goto v_reusejp_3957_;
}
v_reusejp_3957_:
{
return v___x_3958_;
}
}
}
}
else
{
lean_del_object(v___x_3743_);
goto v___jp_3864_;
}
}
else
{
lean_del_object(v___x_3743_);
goto v___jp_3864_;
}
v___jp_3805_:
{
lean_object* v___x_3809_; double v___x_3810_; double v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; 
v___x_3809_ = lean_io_get_num_heartbeats();
v___x_3810_ = lean_float_of_nat(v___y_3807_);
v___x_3811_ = lean_float_of_nat(v___x_3809_);
v___x_3812_ = lean_box_float(v___x_3810_);
v___x_3813_ = lean_box_float(v___x_3811_);
v___x_3814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3814_, 0, v___x_3812_);
lean_ctor_set(v___x_3814_, 1, v___x_3813_);
v___x_3815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3815_, 0, v_a_3808_);
lean_ctor_set(v___x_3815_, 1, v___x_3814_);
v___x_3816_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_3801_, v_hasTrace_3746_, v___x_3802_, v_options_3739_, v___x_3804_, v___y_3806_, v___f_3800_, v___x_3815_, v_a_3732_, v_a_3733_, v_a_3734_, v_a_3735_);
return v___x_3816_;
}
v___jp_3817_:
{
lean_object* v___x_3821_; 
v___x_3821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3821_, 0, v_a_3820_);
v___y_3806_ = v___y_3818_;
v___y_3807_ = v___y_3819_;
v_a_3808_ = v___x_3821_;
goto v___jp_3805_;
}
v___jp_3822_:
{
lean_object* v___x_3826_; 
v___x_3826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3826_, 0, v_a_3825_);
v___y_3806_ = v___y_3823_;
v___y_3807_ = v___y_3824_;
v_a_3808_ = v___x_3826_;
goto v___jp_3805_;
}
v___jp_3827_:
{
if (lean_obj_tag(v___y_3830_) == 0)
{
lean_object* v_a_3831_; 
v_a_3831_ = lean_ctor_get(v___y_3830_, 0);
lean_inc(v_a_3831_);
lean_dec_ref_known(v___y_3830_, 1);
v___y_3823_ = v___y_3828_;
v___y_3824_ = v___y_3829_;
v_a_3825_ = v_a_3831_;
goto v___jp_3822_;
}
else
{
lean_object* v_a_3832_; 
v_a_3832_ = lean_ctor_get(v___y_3830_, 0);
lean_inc(v_a_3832_);
lean_dec_ref_known(v___y_3830_, 1);
v___y_3818_ = v___y_3828_;
v___y_3819_ = v___y_3829_;
v_a_3820_ = v_a_3832_;
goto v___jp_3817_;
}
}
v___jp_3833_:
{
lean_object* v___x_3837_; double v___x_3838_; double v___x_3839_; double v___x_3840_; double v___x_3841_; double v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; 
v___x_3837_ = lean_io_mono_nanos_now();
v___x_3838_ = lean_float_of_nat(v___y_3835_);
v___x_3839_ = lean_float_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0);
v___x_3840_ = lean_float_div(v___x_3838_, v___x_3839_);
v___x_3841_ = lean_float_of_nat(v___x_3837_);
v___x_3842_ = lean_float_div(v___x_3841_, v___x_3839_);
v___x_3843_ = lean_box_float(v___x_3840_);
v___x_3844_ = lean_box_float(v___x_3842_);
v___x_3845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3845_, 0, v___x_3843_);
lean_ctor_set(v___x_3845_, 1, v___x_3844_);
v___x_3846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3846_, 0, v_a_3836_);
lean_ctor_set(v___x_3846_, 1, v___x_3845_);
v___x_3847_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_3801_, v_hasTrace_3746_, v___x_3802_, v_options_3739_, v___x_3804_, v___y_3834_, v___f_3800_, v___x_3846_, v_a_3732_, v_a_3733_, v_a_3734_, v_a_3735_);
return v___x_3847_;
}
v___jp_3848_:
{
lean_object* v___x_3852_; 
v___x_3852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3852_, 0, v_a_3851_);
v___y_3834_ = v___y_3849_;
v___y_3835_ = v___y_3850_;
v_a_3836_ = v___x_3852_;
goto v___jp_3833_;
}
v___jp_3853_:
{
lean_object* v___x_3857_; 
v___x_3857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3857_, 0, v_a_3856_);
v___y_3834_ = v___y_3854_;
v___y_3835_ = v___y_3855_;
v_a_3836_ = v___x_3857_;
goto v___jp_3833_;
}
v___jp_3858_:
{
if (lean_obj_tag(v___y_3861_) == 0)
{
lean_object* v_a_3862_; 
v_a_3862_ = lean_ctor_get(v___y_3861_, 0);
lean_inc(v_a_3862_);
lean_dec_ref_known(v___y_3861_, 1);
v___y_3849_ = v___y_3859_;
v___y_3850_ = v___y_3860_;
v_a_3851_ = v_a_3862_;
goto v___jp_3848_;
}
else
{
lean_object* v_a_3863_; 
v_a_3863_ = lean_ctor_get(v___y_3861_, 0);
lean_inc(v_a_3863_);
lean_dec_ref_known(v___y_3861_, 1);
v___y_3854_ = v___y_3859_;
v___y_3855_ = v___y_3860_;
v_a_3856_ = v_a_3863_;
goto v___jp_3853_;
}
}
v___jp_3864_:
{
lean_object* v___x_3865_; lean_object* v_a_3866_; lean_object* v___x_3867_; uint8_t v___x_3868_; 
v___x_3865_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v_a_3735_);
v_a_3866_ = lean_ctor_get(v___x_3865_, 0);
lean_inc(v_a_3866_);
lean_dec_ref(v___x_3865_);
v___x_3867_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3868_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_3739_, v___x_3867_);
if (v___x_3868_ == 0)
{
lean_object* v___x_3869_; lean_object* v___x_3870_; 
v___x_3869_ = lean_io_mono_nanos_now();
lean_inc_ref(v_ctorVal_3731_);
v___x_3870_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3731_, v_a_3732_, v_a_3733_, v_a_3734_, v_a_3735_);
if (lean_obj_tag(v___x_3870_) == 0)
{
lean_object* v_a_3871_; 
v_a_3871_ = lean_ctor_get(v___x_3870_, 0);
lean_inc(v_a_3871_);
lean_dec_ref_known(v___x_3870_, 1);
if (lean_obj_tag(v_a_3871_) == 1)
{
if (v___x_3804_ == 0)
{
lean_object* v_val_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; 
v_val_3872_ = lean_ctor_get(v_a_3871_, 0);
lean_inc(v_val_3872_);
lean_dec_ref_known(v_a_3871_, 1);
v___x_3873_ = lean_box(0);
v___x_3874_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(v_ctorVal_3731_, v_val_3872_, v_name_3747_, v_levelParams_3741_, v___x_3868_, v_hasTrace_3746_, v___x_3873_, v_a_3732_, v_a_3733_, v_a_3734_, v_a_3735_);
v___y_3859_ = v_a_3866_;
v___y_3860_ = v___x_3869_;
v___y_3861_ = v___x_3874_;
goto v___jp_3858_;
}
else
{
lean_object* v_val_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; 
v_val_3875_ = lean_ctor_get(v_a_3871_, 0);
lean_inc_n(v_val_3875_, 2);
lean_dec_ref_known(v_a_3871_, 1);
v___x_3876_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_3877_ = l_Lean_MessageData_ofExpr(v_val_3875_);
v___x_3878_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3878_, 0, v___x_3876_);
lean_ctor_set(v___x_3878_, 1, v___x_3877_);
v___x_3879_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_3801_, v___x_3878_, v_a_3732_, v_a_3733_, v_a_3734_, v_a_3735_);
if (lean_obj_tag(v___x_3879_) == 0)
{
lean_object* v_a_3880_; lean_object* v___x_3881_; 
v_a_3880_ = lean_ctor_get(v___x_3879_, 0);
lean_inc(v_a_3880_);
lean_dec_ref_known(v___x_3879_, 1);
v___x_3881_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(v_ctorVal_3731_, v_val_3875_, v_name_3747_, v_levelParams_3741_, v___x_3868_, v_hasTrace_3746_, v_a_3880_, v_a_3732_, v_a_3733_, v_a_3734_, v_a_3735_);
v___y_3859_ = v_a_3866_;
v___y_3860_ = v___x_3869_;
v___y_3861_ = v___x_3881_;
goto v___jp_3858_;
}
else
{
lean_dec(v_val_3875_);
lean_dec(v_name_3747_);
lean_dec(v_levelParams_3741_);
lean_dec_ref(v_ctorVal_3731_);
v___y_3859_ = v_a_3866_;
v___y_3860_ = v___x_3869_;
v___y_3861_ = v___x_3879_;
goto v___jp_3858_;
}
}
}
else
{
lean_object* v___x_3882_; 
lean_dec(v_a_3871_);
lean_dec(v_name_3747_);
lean_dec(v_levelParams_3741_);
lean_dec_ref(v_ctorVal_3731_);
v___x_3882_ = lean_box(0);
v___y_3849_ = v_a_3866_;
v___y_3850_ = v___x_3869_;
v_a_3851_ = v___x_3882_;
goto v___jp_3848_;
}
}
else
{
lean_object* v_a_3883_; 
lean_dec(v_name_3747_);
lean_dec(v_levelParams_3741_);
lean_dec_ref(v_ctorVal_3731_);
v_a_3883_ = lean_ctor_get(v___x_3870_, 0);
lean_inc(v_a_3883_);
lean_dec_ref_known(v___x_3870_, 1);
v___y_3854_ = v_a_3866_;
v___y_3855_ = v___x_3869_;
v_a_3856_ = v_a_3883_;
goto v___jp_3853_;
}
}
else
{
lean_object* v___x_3884_; lean_object* v___x_3885_; 
v___x_3884_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_ctorVal_3731_);
v___x_3885_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3731_, v_a_3732_, v_a_3733_, v_a_3734_, v_a_3735_);
if (lean_obj_tag(v___x_3885_) == 0)
{
lean_object* v_a_3886_; 
v_a_3886_ = lean_ctor_get(v___x_3885_, 0);
lean_inc(v_a_3886_);
lean_dec_ref_known(v___x_3885_, 1);
if (lean_obj_tag(v_a_3886_) == 1)
{
if (v___x_3804_ == 0)
{
lean_object* v_val_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; 
v_val_3887_ = lean_ctor_get(v_a_3886_, 0);
lean_inc(v_val_3887_);
lean_dec_ref_known(v_a_3886_, 1);
v___x_3888_ = lean_box(0);
v___x_3889_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(v_ctorVal_3731_, v_val_3887_, v_name_3747_, v_levelParams_3741_, v___x_3868_, v___x_3888_, v_a_3732_, v_a_3733_, v_a_3734_, v_a_3735_);
v___y_3828_ = v_a_3866_;
v___y_3829_ = v___x_3884_;
v___y_3830_ = v___x_3889_;
goto v___jp_3827_;
}
else
{
lean_object* v_val_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; 
v_val_3890_ = lean_ctor_get(v_a_3886_, 0);
lean_inc_n(v_val_3890_, 2);
lean_dec_ref_known(v_a_3886_, 1);
v___x_3891_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_3892_ = l_Lean_MessageData_ofExpr(v_val_3890_);
v___x_3893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3893_, 0, v___x_3891_);
lean_ctor_set(v___x_3893_, 1, v___x_3892_);
v___x_3894_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_3801_, v___x_3893_, v_a_3732_, v_a_3733_, v_a_3734_, v_a_3735_);
if (lean_obj_tag(v___x_3894_) == 0)
{
lean_object* v_a_3895_; lean_object* v___x_3896_; 
v_a_3895_ = lean_ctor_get(v___x_3894_, 0);
lean_inc(v_a_3895_);
lean_dec_ref_known(v___x_3894_, 1);
v___x_3896_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(v_ctorVal_3731_, v_val_3890_, v_name_3747_, v_levelParams_3741_, v___x_3868_, v_a_3895_, v_a_3732_, v_a_3733_, v_a_3734_, v_a_3735_);
v___y_3828_ = v_a_3866_;
v___y_3829_ = v___x_3884_;
v___y_3830_ = v___x_3896_;
goto v___jp_3827_;
}
else
{
lean_dec(v_val_3890_);
lean_dec(v_name_3747_);
lean_dec(v_levelParams_3741_);
lean_dec_ref(v_ctorVal_3731_);
v___y_3828_ = v_a_3866_;
v___y_3829_ = v___x_3884_;
v___y_3830_ = v___x_3894_;
goto v___jp_3827_;
}
}
}
else
{
lean_object* v___x_3897_; 
lean_dec(v_a_3886_);
lean_dec(v_name_3747_);
lean_dec(v_levelParams_3741_);
lean_dec_ref(v_ctorVal_3731_);
v___x_3897_ = lean_box(0);
v___y_3823_ = v_a_3866_;
v___y_3824_ = v___x_3884_;
v_a_3825_ = v___x_3897_;
goto v___jp_3822_;
}
}
else
{
lean_object* v_a_3898_; 
lean_dec(v_name_3747_);
lean_dec(v_levelParams_3741_);
lean_dec_ref(v_ctorVal_3731_);
v_a_3898_ = lean_ctor_get(v___x_3885_, 0);
lean_inc(v_a_3898_);
lean_dec_ref_known(v___x_3885_, 1);
v___y_3818_ = v_a_3866_;
v___y_3819_ = v___x_3884_;
v_a_3820_ = v_a_3898_;
goto v___jp_3817_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___boxed(lean_object* v_ctorVal_3963_, lean_object* v_a_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_, lean_object* v_a_3967_, lean_object* v_a_3968_){
_start:
{
lean_object* v_res_3969_; 
v_res_3969_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(v_ctorVal_3963_, v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_);
lean_dec(v_a_3967_);
lean_dec_ref(v_a_3966_);
lean_dec(v_a_3965_);
lean_dec_ref(v_a_3964_);
return v_res_3969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(lean_object* v_name_3970_, lean_object* v_decl_3971_, lean_object* v_ref_3972_){
_start:
{
lean_object* v_defValue_3974_; lean_object* v_descr_3975_; lean_object* v_deprecation_x3f_3976_; lean_object* v___x_3977_; uint8_t v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; 
v_defValue_3974_ = lean_ctor_get(v_decl_3971_, 0);
v_descr_3975_ = lean_ctor_get(v_decl_3971_, 1);
v_deprecation_x3f_3976_ = lean_ctor_get(v_decl_3971_, 2);
v___x_3977_ = lean_alloc_ctor(1, 0, 1);
v___x_3978_ = lean_unbox(v_defValue_3974_);
lean_ctor_set_uint8(v___x_3977_, 0, v___x_3978_);
lean_inc(v_deprecation_x3f_3976_);
lean_inc_ref(v_descr_3975_);
lean_inc_n(v_name_3970_, 2);
v___x_3979_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3979_, 0, v_name_3970_);
lean_ctor_set(v___x_3979_, 1, v_ref_3972_);
lean_ctor_set(v___x_3979_, 2, v___x_3977_);
lean_ctor_set(v___x_3979_, 3, v_descr_3975_);
lean_ctor_set(v___x_3979_, 4, v_deprecation_x3f_3976_);
v___x_3980_ = lean_register_option(v_name_3970_, v___x_3979_);
if (lean_obj_tag(v___x_3980_) == 0)
{
lean_object* v___x_3982_; uint8_t v_isShared_3983_; uint8_t v_isSharedCheck_3988_; 
v_isSharedCheck_3988_ = !lean_is_exclusive(v___x_3980_);
if (v_isSharedCheck_3988_ == 0)
{
lean_object* v_unused_3989_; 
v_unused_3989_ = lean_ctor_get(v___x_3980_, 0);
lean_dec(v_unused_3989_);
v___x_3982_ = v___x_3980_;
v_isShared_3983_ = v_isSharedCheck_3988_;
goto v_resetjp_3981_;
}
else
{
lean_dec(v___x_3980_);
v___x_3982_ = lean_box(0);
v_isShared_3983_ = v_isSharedCheck_3988_;
goto v_resetjp_3981_;
}
v_resetjp_3981_:
{
lean_object* v___x_3984_; lean_object* v___x_3986_; 
lean_inc(v_defValue_3974_);
v___x_3984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3984_, 0, v_name_3970_);
lean_ctor_set(v___x_3984_, 1, v_defValue_3974_);
if (v_isShared_3983_ == 0)
{
lean_ctor_set(v___x_3982_, 0, v___x_3984_);
v___x_3986_ = v___x_3982_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v___x_3984_);
v___x_3986_ = v_reuseFailAlloc_3987_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
return v___x_3986_;
}
}
}
else
{
lean_object* v_a_3990_; lean_object* v___x_3992_; uint8_t v_isShared_3993_; uint8_t v_isSharedCheck_3997_; 
lean_dec(v_name_3970_);
v_a_3990_ = lean_ctor_get(v___x_3980_, 0);
v_isSharedCheck_3997_ = !lean_is_exclusive(v___x_3980_);
if (v_isSharedCheck_3997_ == 0)
{
v___x_3992_ = v___x_3980_;
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
else
{
lean_inc(v_a_3990_);
lean_dec(v___x_3980_);
v___x_3992_ = lean_box(0);
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
v_resetjp_3991_:
{
lean_object* v___x_3995_; 
if (v_isShared_3993_ == 0)
{
v___x_3995_ = v___x_3992_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v_a_3990_);
v___x_3995_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3994_;
}
v_reusejp_3994_:
{
return v___x_3995_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_3998_, lean_object* v_decl_3999_, lean_object* v_ref_4000_, lean_object* v_a_4001_){
_start:
{
lean_object* v_res_4002_; 
v_res_4002_ = l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(v_name_3998_, v_decl_3999_, v_ref_4000_);
lean_dec_ref(v_decl_3999_);
return v_res_4002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; 
v___x_4017_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_));
v___x_4018_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_));
v___x_4019_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_));
v___x_4020_ = l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(v___x_4017_, v___x_4018_, v___x_4019_);
return v___x_4020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4____boxed(lean_object* v_a_4021_){
_start:
{
lean_object* v_res_4022_; 
v_res_4022_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_();
return v_res_4022_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(lean_object* v___y_4023_, uint8_t v_isExporting_4024_, lean_object* v___x_4025_, lean_object* v___y_4026_, lean_object* v___x_4027_, lean_object* v_a_x3f_4028_){
_start:
{
lean_object* v___x_4030_; lean_object* v_env_4031_; lean_object* v_nextMacroScope_4032_; lean_object* v_ngen_4033_; lean_object* v_auxDeclNGen_4034_; lean_object* v_traceState_4035_; lean_object* v_messages_4036_; lean_object* v_infoState_4037_; lean_object* v_snapshotTasks_4038_; lean_object* v___x_4040_; uint8_t v_isShared_4041_; uint8_t v_isSharedCheck_4063_; 
v___x_4030_ = lean_st_ref_take(v___y_4023_);
v_env_4031_ = lean_ctor_get(v___x_4030_, 0);
v_nextMacroScope_4032_ = lean_ctor_get(v___x_4030_, 1);
v_ngen_4033_ = lean_ctor_get(v___x_4030_, 2);
v_auxDeclNGen_4034_ = lean_ctor_get(v___x_4030_, 3);
v_traceState_4035_ = lean_ctor_get(v___x_4030_, 4);
v_messages_4036_ = lean_ctor_get(v___x_4030_, 6);
v_infoState_4037_ = lean_ctor_get(v___x_4030_, 7);
v_snapshotTasks_4038_ = lean_ctor_get(v___x_4030_, 8);
v_isSharedCheck_4063_ = !lean_is_exclusive(v___x_4030_);
if (v_isSharedCheck_4063_ == 0)
{
lean_object* v_unused_4064_; 
v_unused_4064_ = lean_ctor_get(v___x_4030_, 5);
lean_dec(v_unused_4064_);
v___x_4040_ = v___x_4030_;
v_isShared_4041_ = v_isSharedCheck_4063_;
goto v_resetjp_4039_;
}
else
{
lean_inc(v_snapshotTasks_4038_);
lean_inc(v_infoState_4037_);
lean_inc(v_messages_4036_);
lean_inc(v_traceState_4035_);
lean_inc(v_auxDeclNGen_4034_);
lean_inc(v_ngen_4033_);
lean_inc(v_nextMacroScope_4032_);
lean_inc(v_env_4031_);
lean_dec(v___x_4030_);
v___x_4040_ = lean_box(0);
v_isShared_4041_ = v_isSharedCheck_4063_;
goto v_resetjp_4039_;
}
v_resetjp_4039_:
{
lean_object* v___x_4042_; lean_object* v___x_4044_; 
v___x_4042_ = l_Lean_Environment_setExporting(v_env_4031_, v_isExporting_4024_);
if (v_isShared_4041_ == 0)
{
lean_ctor_set(v___x_4040_, 5, v___x_4025_);
lean_ctor_set(v___x_4040_, 0, v___x_4042_);
v___x_4044_ = v___x_4040_;
goto v_reusejp_4043_;
}
else
{
lean_object* v_reuseFailAlloc_4062_; 
v_reuseFailAlloc_4062_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4062_, 0, v___x_4042_);
lean_ctor_set(v_reuseFailAlloc_4062_, 1, v_nextMacroScope_4032_);
lean_ctor_set(v_reuseFailAlloc_4062_, 2, v_ngen_4033_);
lean_ctor_set(v_reuseFailAlloc_4062_, 3, v_auxDeclNGen_4034_);
lean_ctor_set(v_reuseFailAlloc_4062_, 4, v_traceState_4035_);
lean_ctor_set(v_reuseFailAlloc_4062_, 5, v___x_4025_);
lean_ctor_set(v_reuseFailAlloc_4062_, 6, v_messages_4036_);
lean_ctor_set(v_reuseFailAlloc_4062_, 7, v_infoState_4037_);
lean_ctor_set(v_reuseFailAlloc_4062_, 8, v_snapshotTasks_4038_);
v___x_4044_ = v_reuseFailAlloc_4062_;
goto v_reusejp_4043_;
}
v_reusejp_4043_:
{
lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v_mctx_4047_; lean_object* v_zetaDeltaFVarIds_4048_; lean_object* v_postponed_4049_; lean_object* v_diag_4050_; lean_object* v___x_4052_; uint8_t v_isShared_4053_; uint8_t v_isSharedCheck_4060_; 
v___x_4045_ = lean_st_ref_put(v___y_4023_, v___x_4044_);
v___x_4046_ = lean_st_ref_take(v___y_4026_);
v_mctx_4047_ = lean_ctor_get(v___x_4046_, 0);
v_zetaDeltaFVarIds_4048_ = lean_ctor_get(v___x_4046_, 2);
v_postponed_4049_ = lean_ctor_get(v___x_4046_, 3);
v_diag_4050_ = lean_ctor_get(v___x_4046_, 4);
v_isSharedCheck_4060_ = !lean_is_exclusive(v___x_4046_);
if (v_isSharedCheck_4060_ == 0)
{
lean_object* v_unused_4061_; 
v_unused_4061_ = lean_ctor_get(v___x_4046_, 1);
lean_dec(v_unused_4061_);
v___x_4052_ = v___x_4046_;
v_isShared_4053_ = v_isSharedCheck_4060_;
goto v_resetjp_4051_;
}
else
{
lean_inc(v_diag_4050_);
lean_inc(v_postponed_4049_);
lean_inc(v_zetaDeltaFVarIds_4048_);
lean_inc(v_mctx_4047_);
lean_dec(v___x_4046_);
v___x_4052_ = lean_box(0);
v_isShared_4053_ = v_isSharedCheck_4060_;
goto v_resetjp_4051_;
}
v_resetjp_4051_:
{
lean_object* v___x_4055_; 
if (v_isShared_4053_ == 0)
{
lean_ctor_set(v___x_4052_, 1, v___x_4027_);
v___x_4055_ = v___x_4052_;
goto v_reusejp_4054_;
}
else
{
lean_object* v_reuseFailAlloc_4059_; 
v_reuseFailAlloc_4059_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4059_, 0, v_mctx_4047_);
lean_ctor_set(v_reuseFailAlloc_4059_, 1, v___x_4027_);
lean_ctor_set(v_reuseFailAlloc_4059_, 2, v_zetaDeltaFVarIds_4048_);
lean_ctor_set(v_reuseFailAlloc_4059_, 3, v_postponed_4049_);
lean_ctor_set(v_reuseFailAlloc_4059_, 4, v_diag_4050_);
v___x_4055_ = v_reuseFailAlloc_4059_;
goto v_reusejp_4054_;
}
v_reusejp_4054_:
{
lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; 
v___x_4056_ = lean_st_ref_put(v___y_4026_, v___x_4055_);
v___x_4057_ = lean_box(0);
v___x_4058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4058_, 0, v___x_4057_);
return v___x_4058_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0___boxed(lean_object* v___y_4065_, lean_object* v_isExporting_4066_, lean_object* v___x_4067_, lean_object* v___y_4068_, lean_object* v___x_4069_, lean_object* v_a_x3f_4070_, lean_object* v___y_4071_){
_start:
{
uint8_t v_isExporting_boxed_4072_; lean_object* v_res_4073_; 
v_isExporting_boxed_4072_ = lean_unbox(v_isExporting_4066_);
v_res_4073_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(v___y_4065_, v_isExporting_boxed_4072_, v___x_4067_, v___y_4068_, v___x_4069_, v_a_x3f_4070_);
lean_dec(v_a_x3f_4070_);
lean_dec(v___y_4068_);
lean_dec(v___y_4065_);
return v_res_4073_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_4074_; 
v___x_4074_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4074_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4075_; lean_object* v___x_4076_; 
v___x_4075_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0);
v___x_4076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4076_, 0, v___x_4075_);
return v___x_4076_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_4077_; lean_object* v___x_4078_; 
v___x_4077_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1);
v___x_4078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4078_, 0, v___x_4077_);
lean_ctor_set(v___x_4078_, 1, v___x_4077_);
return v___x_4078_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_4079_; lean_object* v___x_4080_; 
v___x_4079_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1);
v___x_4080_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4080_, 0, v___x_4079_);
lean_ctor_set(v___x_4080_, 1, v___x_4079_);
lean_ctor_set(v___x_4080_, 2, v___x_4079_);
lean_ctor_set(v___x_4080_, 3, v___x_4079_);
lean_ctor_set(v___x_4080_, 4, v___x_4079_);
lean_ctor_set(v___x_4080_, 5, v___x_4079_);
return v___x_4080_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(lean_object* v_x_4081_, uint8_t v_isExporting_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_){
_start:
{
lean_object* v___x_4088_; lean_object* v_env_4089_; lean_object* v___x_4090_; uint8_t v_isModule_4091_; 
v___x_4088_ = lean_st_ref_get(v___y_4086_);
v_env_4089_ = lean_ctor_get(v___x_4088_, 0);
lean_inc_ref(v_env_4089_);
lean_dec(v___x_4088_);
v___x_4090_ = l_Lean_Environment_header(v_env_4089_);
v_isModule_4091_ = lean_ctor_get_uint8(v___x_4090_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4090_);
if (v_isModule_4091_ == 0)
{
lean_object* v___x_4092_; 
lean_dec_ref(v_env_4089_);
lean_inc(v___y_4086_);
lean_inc_ref(v___y_4085_);
lean_inc(v___y_4084_);
lean_inc_ref(v___y_4083_);
v___x_4092_ = lean_apply_5(v_x_4081_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, lean_box(0));
return v___x_4092_;
}
else
{
uint8_t v_isExporting_4093_; 
v_isExporting_4093_ = lean_ctor_get_uint8(v_env_4089_, sizeof(void*)*8);
lean_dec_ref(v_env_4089_);
if (v_isExporting_4082_ == 0)
{
if (v_isExporting_4093_ == 0)
{
lean_object* v___x_4159_; 
lean_inc(v___y_4086_);
lean_inc_ref(v___y_4085_);
lean_inc(v___y_4084_);
lean_inc_ref(v___y_4083_);
v___x_4159_ = lean_apply_5(v_x_4081_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, lean_box(0));
return v___x_4159_;
}
else
{
goto v___jp_4094_;
}
}
else
{
if (v_isExporting_4093_ == 0)
{
goto v___jp_4094_;
}
else
{
lean_object* v___x_4160_; 
lean_inc(v___y_4086_);
lean_inc_ref(v___y_4085_);
lean_inc(v___y_4084_);
lean_inc_ref(v___y_4083_);
v___x_4160_ = lean_apply_5(v_x_4081_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, lean_box(0));
return v___x_4160_;
}
}
v___jp_4094_:
{
lean_object* v___x_4095_; lean_object* v_env_4096_; lean_object* v_nextMacroScope_4097_; lean_object* v_ngen_4098_; lean_object* v_auxDeclNGen_4099_; lean_object* v_traceState_4100_; lean_object* v_messages_4101_; lean_object* v_infoState_4102_; lean_object* v_snapshotTasks_4103_; lean_object* v___x_4105_; uint8_t v_isShared_4106_; uint8_t v_isSharedCheck_4157_; 
v___x_4095_ = lean_st_ref_take(v___y_4086_);
v_env_4096_ = lean_ctor_get(v___x_4095_, 0);
v_nextMacroScope_4097_ = lean_ctor_get(v___x_4095_, 1);
v_ngen_4098_ = lean_ctor_get(v___x_4095_, 2);
v_auxDeclNGen_4099_ = lean_ctor_get(v___x_4095_, 3);
v_traceState_4100_ = lean_ctor_get(v___x_4095_, 4);
v_messages_4101_ = lean_ctor_get(v___x_4095_, 6);
v_infoState_4102_ = lean_ctor_get(v___x_4095_, 7);
v_snapshotTasks_4103_ = lean_ctor_get(v___x_4095_, 8);
v_isSharedCheck_4157_ = !lean_is_exclusive(v___x_4095_);
if (v_isSharedCheck_4157_ == 0)
{
lean_object* v_unused_4158_; 
v_unused_4158_ = lean_ctor_get(v___x_4095_, 5);
lean_dec(v_unused_4158_);
v___x_4105_ = v___x_4095_;
v_isShared_4106_ = v_isSharedCheck_4157_;
goto v_resetjp_4104_;
}
else
{
lean_inc(v_snapshotTasks_4103_);
lean_inc(v_infoState_4102_);
lean_inc(v_messages_4101_);
lean_inc(v_traceState_4100_);
lean_inc(v_auxDeclNGen_4099_);
lean_inc(v_ngen_4098_);
lean_inc(v_nextMacroScope_4097_);
lean_inc(v_env_4096_);
lean_dec(v___x_4095_);
v___x_4105_ = lean_box(0);
v_isShared_4106_ = v_isSharedCheck_4157_;
goto v_resetjp_4104_;
}
v_resetjp_4104_:
{
lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4110_; 
v___x_4107_ = l_Lean_Environment_setExporting(v_env_4096_, v_isExporting_4082_);
v___x_4108_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2);
if (v_isShared_4106_ == 0)
{
lean_ctor_set(v___x_4105_, 5, v___x_4108_);
lean_ctor_set(v___x_4105_, 0, v___x_4107_);
v___x_4110_ = v___x_4105_;
goto v_reusejp_4109_;
}
else
{
lean_object* v_reuseFailAlloc_4156_; 
v_reuseFailAlloc_4156_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4156_, 0, v___x_4107_);
lean_ctor_set(v_reuseFailAlloc_4156_, 1, v_nextMacroScope_4097_);
lean_ctor_set(v_reuseFailAlloc_4156_, 2, v_ngen_4098_);
lean_ctor_set(v_reuseFailAlloc_4156_, 3, v_auxDeclNGen_4099_);
lean_ctor_set(v_reuseFailAlloc_4156_, 4, v_traceState_4100_);
lean_ctor_set(v_reuseFailAlloc_4156_, 5, v___x_4108_);
lean_ctor_set(v_reuseFailAlloc_4156_, 6, v_messages_4101_);
lean_ctor_set(v_reuseFailAlloc_4156_, 7, v_infoState_4102_);
lean_ctor_set(v_reuseFailAlloc_4156_, 8, v_snapshotTasks_4103_);
v___x_4110_ = v_reuseFailAlloc_4156_;
goto v_reusejp_4109_;
}
v_reusejp_4109_:
{
lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v_mctx_4113_; lean_object* v_zetaDeltaFVarIds_4114_; lean_object* v_postponed_4115_; lean_object* v_diag_4116_; lean_object* v___x_4118_; uint8_t v_isShared_4119_; uint8_t v_isSharedCheck_4154_; 
v___x_4111_ = lean_st_ref_put(v___y_4086_, v___x_4110_);
v___x_4112_ = lean_st_ref_take(v___y_4084_);
v_mctx_4113_ = lean_ctor_get(v___x_4112_, 0);
v_zetaDeltaFVarIds_4114_ = lean_ctor_get(v___x_4112_, 2);
v_postponed_4115_ = lean_ctor_get(v___x_4112_, 3);
v_diag_4116_ = lean_ctor_get(v___x_4112_, 4);
v_isSharedCheck_4154_ = !lean_is_exclusive(v___x_4112_);
if (v_isSharedCheck_4154_ == 0)
{
lean_object* v_unused_4155_; 
v_unused_4155_ = lean_ctor_get(v___x_4112_, 1);
lean_dec(v_unused_4155_);
v___x_4118_ = v___x_4112_;
v_isShared_4119_ = v_isSharedCheck_4154_;
goto v_resetjp_4117_;
}
else
{
lean_inc(v_diag_4116_);
lean_inc(v_postponed_4115_);
lean_inc(v_zetaDeltaFVarIds_4114_);
lean_inc(v_mctx_4113_);
lean_dec(v___x_4112_);
v___x_4118_ = lean_box(0);
v_isShared_4119_ = v_isSharedCheck_4154_;
goto v_resetjp_4117_;
}
v_resetjp_4117_:
{
lean_object* v___x_4120_; lean_object* v___x_4122_; 
v___x_4120_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3);
if (v_isShared_4119_ == 0)
{
lean_ctor_set(v___x_4118_, 1, v___x_4120_);
v___x_4122_ = v___x_4118_;
goto v_reusejp_4121_;
}
else
{
lean_object* v_reuseFailAlloc_4153_; 
v_reuseFailAlloc_4153_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4153_, 0, v_mctx_4113_);
lean_ctor_set(v_reuseFailAlloc_4153_, 1, v___x_4120_);
lean_ctor_set(v_reuseFailAlloc_4153_, 2, v_zetaDeltaFVarIds_4114_);
lean_ctor_set(v_reuseFailAlloc_4153_, 3, v_postponed_4115_);
lean_ctor_set(v_reuseFailAlloc_4153_, 4, v_diag_4116_);
v___x_4122_ = v_reuseFailAlloc_4153_;
goto v_reusejp_4121_;
}
v_reusejp_4121_:
{
lean_object* v___x_4123_; lean_object* v_r_4124_; 
v___x_4123_ = lean_st_ref_put(v___y_4084_, v___x_4122_);
lean_inc(v___y_4086_);
lean_inc_ref(v___y_4085_);
lean_inc(v___y_4084_);
lean_inc_ref(v___y_4083_);
v_r_4124_ = lean_apply_5(v_x_4081_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, lean_box(0));
if (lean_obj_tag(v_r_4124_) == 0)
{
lean_object* v_a_4125_; lean_object* v___x_4127_; uint8_t v_isShared_4128_; uint8_t v_isSharedCheck_4141_; 
v_a_4125_ = lean_ctor_get(v_r_4124_, 0);
v_isSharedCheck_4141_ = !lean_is_exclusive(v_r_4124_);
if (v_isSharedCheck_4141_ == 0)
{
v___x_4127_ = v_r_4124_;
v_isShared_4128_ = v_isSharedCheck_4141_;
goto v_resetjp_4126_;
}
else
{
lean_inc(v_a_4125_);
lean_dec(v_r_4124_);
v___x_4127_ = lean_box(0);
v_isShared_4128_ = v_isSharedCheck_4141_;
goto v_resetjp_4126_;
}
v_resetjp_4126_:
{
lean_object* v___x_4130_; 
lean_inc(v_a_4125_);
if (v_isShared_4128_ == 0)
{
lean_ctor_set_tag(v___x_4127_, 1);
v___x_4130_ = v___x_4127_;
goto v_reusejp_4129_;
}
else
{
lean_object* v_reuseFailAlloc_4140_; 
v_reuseFailAlloc_4140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4140_, 0, v_a_4125_);
v___x_4130_ = v_reuseFailAlloc_4140_;
goto v_reusejp_4129_;
}
v_reusejp_4129_:
{
lean_object* v___x_4131_; lean_object* v___x_4133_; uint8_t v_isShared_4134_; uint8_t v_isSharedCheck_4138_; 
v___x_4131_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(v___y_4086_, v_isExporting_4093_, v___x_4108_, v___y_4084_, v___x_4120_, v___x_4130_);
lean_dec_ref(v___x_4130_);
v_isSharedCheck_4138_ = !lean_is_exclusive(v___x_4131_);
if (v_isSharedCheck_4138_ == 0)
{
lean_object* v_unused_4139_; 
v_unused_4139_ = lean_ctor_get(v___x_4131_, 0);
lean_dec(v_unused_4139_);
v___x_4133_ = v___x_4131_;
v_isShared_4134_ = v_isSharedCheck_4138_;
goto v_resetjp_4132_;
}
else
{
lean_dec(v___x_4131_);
v___x_4133_ = lean_box(0);
v_isShared_4134_ = v_isSharedCheck_4138_;
goto v_resetjp_4132_;
}
v_resetjp_4132_:
{
lean_object* v___x_4136_; 
if (v_isShared_4134_ == 0)
{
lean_ctor_set(v___x_4133_, 0, v_a_4125_);
v___x_4136_ = v___x_4133_;
goto v_reusejp_4135_;
}
else
{
lean_object* v_reuseFailAlloc_4137_; 
v_reuseFailAlloc_4137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4137_, 0, v_a_4125_);
v___x_4136_ = v_reuseFailAlloc_4137_;
goto v_reusejp_4135_;
}
v_reusejp_4135_:
{
return v___x_4136_;
}
}
}
}
}
else
{
lean_object* v_a_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4146_; uint8_t v_isShared_4147_; uint8_t v_isSharedCheck_4151_; 
v_a_4142_ = lean_ctor_get(v_r_4124_, 0);
lean_inc(v_a_4142_);
lean_dec_ref_known(v_r_4124_, 1);
v___x_4143_ = lean_box(0);
v___x_4144_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(v___y_4086_, v_isExporting_4093_, v___x_4108_, v___y_4084_, v___x_4120_, v___x_4143_);
v_isSharedCheck_4151_ = !lean_is_exclusive(v___x_4144_);
if (v_isSharedCheck_4151_ == 0)
{
lean_object* v_unused_4152_; 
v_unused_4152_ = lean_ctor_get(v___x_4144_, 0);
lean_dec(v_unused_4152_);
v___x_4146_ = v___x_4144_;
v_isShared_4147_ = v_isSharedCheck_4151_;
goto v_resetjp_4145_;
}
else
{
lean_dec(v___x_4144_);
v___x_4146_ = lean_box(0);
v_isShared_4147_ = v_isSharedCheck_4151_;
goto v_resetjp_4145_;
}
v_resetjp_4145_:
{
lean_object* v___x_4149_; 
if (v_isShared_4147_ == 0)
{
lean_ctor_set_tag(v___x_4146_, 1);
lean_ctor_set(v___x_4146_, 0, v_a_4142_);
v___x_4149_ = v___x_4146_;
goto v_reusejp_4148_;
}
else
{
lean_object* v_reuseFailAlloc_4150_; 
v_reuseFailAlloc_4150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4150_, 0, v_a_4142_);
v___x_4149_ = v_reuseFailAlloc_4150_;
goto v_reusejp_4148_;
}
v_reusejp_4148_:
{
return v___x_4149_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___boxed(lean_object* v_x_4161_, lean_object* v_isExporting_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_){
_start:
{
uint8_t v_isExporting_boxed_4168_; lean_object* v_res_4169_; 
v_isExporting_boxed_4168_ = lean_unbox(v_isExporting_4162_);
v_res_4169_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(v_x_4161_, v_isExporting_boxed_4168_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_);
lean_dec(v___y_4166_);
lean_dec_ref(v___y_4165_);
lean_dec(v___y_4164_);
lean_dec_ref(v___y_4163_);
return v_res_4169_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2(lean_object* v_00_u03b1_4170_, lean_object* v_x_4171_, uint8_t v_isExporting_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_){
_start:
{
lean_object* v___x_4178_; 
v___x_4178_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(v_x_4171_, v_isExporting_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_);
return v___x_4178_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___boxed(lean_object* v_00_u03b1_4179_, lean_object* v_x_4180_, lean_object* v_isExporting_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_){
_start:
{
uint8_t v_isExporting_boxed_4187_; lean_object* v_res_4188_; 
v_isExporting_boxed_4187_ = lean_unbox(v_isExporting_4181_);
v_res_4188_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2(v_00_u03b1_4179_, v_x_4180_, v_isExporting_boxed_4187_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_);
lean_dec(v___y_4185_);
lean_dec_ref(v___y_4184_);
lean_dec(v___y_4183_);
lean_dec_ref(v___y_4182_);
return v_res_4188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(lean_object* v_lctx_4189_, lean_object* v_localInsts_4190_, lean_object* v_x_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_){
_start:
{
lean_object* v___x_4197_; 
v___x_4197_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_4189_, v_localInsts_4190_, v_x_4191_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4195_);
if (lean_obj_tag(v___x_4197_) == 0)
{
lean_object* v_a_4198_; lean_object* v___x_4200_; uint8_t v_isShared_4201_; uint8_t v_isSharedCheck_4205_; 
v_a_4198_ = lean_ctor_get(v___x_4197_, 0);
v_isSharedCheck_4205_ = !lean_is_exclusive(v___x_4197_);
if (v_isSharedCheck_4205_ == 0)
{
v___x_4200_ = v___x_4197_;
v_isShared_4201_ = v_isSharedCheck_4205_;
goto v_resetjp_4199_;
}
else
{
lean_inc(v_a_4198_);
lean_dec(v___x_4197_);
v___x_4200_ = lean_box(0);
v_isShared_4201_ = v_isSharedCheck_4205_;
goto v_resetjp_4199_;
}
v_resetjp_4199_:
{
lean_object* v___x_4203_; 
if (v_isShared_4201_ == 0)
{
v___x_4203_ = v___x_4200_;
goto v_reusejp_4202_;
}
else
{
lean_object* v_reuseFailAlloc_4204_; 
v_reuseFailAlloc_4204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4204_, 0, v_a_4198_);
v___x_4203_ = v_reuseFailAlloc_4204_;
goto v_reusejp_4202_;
}
v_reusejp_4202_:
{
return v___x_4203_;
}
}
}
else
{
lean_object* v_a_4206_; lean_object* v___x_4208_; uint8_t v_isShared_4209_; uint8_t v_isSharedCheck_4213_; 
v_a_4206_ = lean_ctor_get(v___x_4197_, 0);
v_isSharedCheck_4213_ = !lean_is_exclusive(v___x_4197_);
if (v_isSharedCheck_4213_ == 0)
{
v___x_4208_ = v___x_4197_;
v_isShared_4209_ = v_isSharedCheck_4213_;
goto v_resetjp_4207_;
}
else
{
lean_inc(v_a_4206_);
lean_dec(v___x_4197_);
v___x_4208_ = lean_box(0);
v_isShared_4209_ = v_isSharedCheck_4213_;
goto v_resetjp_4207_;
}
v_resetjp_4207_:
{
lean_object* v___x_4211_; 
if (v_isShared_4209_ == 0)
{
v___x_4211_ = v___x_4208_;
goto v_reusejp_4210_;
}
else
{
lean_object* v_reuseFailAlloc_4212_; 
v_reuseFailAlloc_4212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4212_, 0, v_a_4206_);
v___x_4211_ = v_reuseFailAlloc_4212_;
goto v_reusejp_4210_;
}
v_reusejp_4210_:
{
return v___x_4211_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg___boxed(lean_object* v_lctx_4214_, lean_object* v_localInsts_4215_, lean_object* v_x_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_){
_start:
{
lean_object* v_res_4222_; 
v_res_4222_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v_lctx_4214_, v_localInsts_4215_, v_x_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_);
lean_dec(v___y_4220_);
lean_dec_ref(v___y_4219_);
lean_dec(v___y_4218_);
lean_dec_ref(v___y_4217_);
return v_res_4222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4(lean_object* v_00_u03b1_4223_, lean_object* v_lctx_4224_, lean_object* v_localInsts_4225_, lean_object* v_x_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_){
_start:
{
lean_object* v___x_4232_; 
v___x_4232_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v_lctx_4224_, v_localInsts_4225_, v_x_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_);
return v___x_4232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___boxed(lean_object* v_00_u03b1_4233_, lean_object* v_lctx_4234_, lean_object* v_localInsts_4235_, lean_object* v_x_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_){
_start:
{
lean_object* v_res_4242_; 
v_res_4242_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4(v_00_u03b1_4233_, v_lctx_4234_, v_localInsts_4235_, v_x_4236_, v___y_4237_, v___y_4238_, v___y_4239_, v___y_4240_);
lean_dec(v___y_4240_);
lean_dec_ref(v___y_4239_);
lean_dec(v___y_4238_);
lean_dec_ref(v___y_4237_);
return v_res_4242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__0(lean_object* v_declName_4243_, lean_object* v_x_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_){
_start:
{
lean_object* v___x_4250_; lean_object* v___x_4251_; 
v___x_4250_ = l_Lean_MessageData_ofName(v_declName_4243_);
v___x_4251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4251_, 0, v___x_4250_);
return v___x_4251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__0___boxed(lean_object* v_declName_4252_, lean_object* v_x_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_){
_start:
{
lean_object* v_res_4259_; 
v_res_4259_ = l_Lean_Meta_mkInjectiveTheorems___lam__0(v_declName_4252_, v_x_4253_, v___y_4254_, v___y_4255_, v___y_4256_, v___y_4257_);
lean_dec(v___y_4257_);
lean_dec_ref(v___y_4256_);
lean_dec(v___y_4255_);
lean_dec_ref(v___y_4254_);
lean_dec_ref(v_x_4253_);
return v_res_4259_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_4260_; 
v___x_4260_ = l_instMonadEIO(lean_box(0));
return v___x_4260_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(lean_object* v_msg_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_){
_start:
{
lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v_toApplicative_4273_; lean_object* v___x_4275_; uint8_t v_isShared_4276_; uint8_t v_isSharedCheck_4334_; 
v___x_4271_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0);
v___x_4272_ = l_StateRefT_x27_instMonad___redArg(v___x_4271_);
v_toApplicative_4273_ = lean_ctor_get(v___x_4272_, 0);
v_isSharedCheck_4334_ = !lean_is_exclusive(v___x_4272_);
if (v_isSharedCheck_4334_ == 0)
{
lean_object* v_unused_4335_; 
v_unused_4335_ = lean_ctor_get(v___x_4272_, 1);
lean_dec(v_unused_4335_);
v___x_4275_ = v___x_4272_;
v_isShared_4276_ = v_isSharedCheck_4334_;
goto v_resetjp_4274_;
}
else
{
lean_inc(v_toApplicative_4273_);
lean_dec(v___x_4272_);
v___x_4275_ = lean_box(0);
v_isShared_4276_ = v_isSharedCheck_4334_;
goto v_resetjp_4274_;
}
v_resetjp_4274_:
{
lean_object* v_toFunctor_4277_; lean_object* v_toSeq_4278_; lean_object* v_toSeqLeft_4279_; lean_object* v_toSeqRight_4280_; lean_object* v___x_4282_; uint8_t v_isShared_4283_; uint8_t v_isSharedCheck_4332_; 
v_toFunctor_4277_ = lean_ctor_get(v_toApplicative_4273_, 0);
v_toSeq_4278_ = lean_ctor_get(v_toApplicative_4273_, 2);
v_toSeqLeft_4279_ = lean_ctor_get(v_toApplicative_4273_, 3);
v_toSeqRight_4280_ = lean_ctor_get(v_toApplicative_4273_, 4);
v_isSharedCheck_4332_ = !lean_is_exclusive(v_toApplicative_4273_);
if (v_isSharedCheck_4332_ == 0)
{
lean_object* v_unused_4333_; 
v_unused_4333_ = lean_ctor_get(v_toApplicative_4273_, 1);
lean_dec(v_unused_4333_);
v___x_4282_ = v_toApplicative_4273_;
v_isShared_4283_ = v_isSharedCheck_4332_;
goto v_resetjp_4281_;
}
else
{
lean_inc(v_toSeqRight_4280_);
lean_inc(v_toSeqLeft_4279_);
lean_inc(v_toSeq_4278_);
lean_inc(v_toFunctor_4277_);
lean_dec(v_toApplicative_4273_);
v___x_4282_ = lean_box(0);
v_isShared_4283_ = v_isSharedCheck_4332_;
goto v_resetjp_4281_;
}
v_resetjp_4281_:
{
lean_object* v___f_4284_; lean_object* v___f_4285_; lean_object* v___f_4286_; lean_object* v___f_4287_; lean_object* v___x_4288_; lean_object* v___f_4289_; lean_object* v___f_4290_; lean_object* v___f_4291_; lean_object* v___x_4293_; 
v___f_4284_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__1));
v___f_4285_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__2));
lean_inc_ref(v_toFunctor_4277_);
v___f_4286_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4286_, 0, v_toFunctor_4277_);
v___f_4287_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4287_, 0, v_toFunctor_4277_);
v___x_4288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4288_, 0, v___f_4286_);
lean_ctor_set(v___x_4288_, 1, v___f_4287_);
v___f_4289_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4289_, 0, v_toSeqRight_4280_);
v___f_4290_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4290_, 0, v_toSeqLeft_4279_);
v___f_4291_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4291_, 0, v_toSeq_4278_);
if (v_isShared_4283_ == 0)
{
lean_ctor_set(v___x_4282_, 4, v___f_4289_);
lean_ctor_set(v___x_4282_, 3, v___f_4290_);
lean_ctor_set(v___x_4282_, 2, v___f_4291_);
lean_ctor_set(v___x_4282_, 1, v___f_4284_);
lean_ctor_set(v___x_4282_, 0, v___x_4288_);
v___x_4293_ = v___x_4282_;
goto v_reusejp_4292_;
}
else
{
lean_object* v_reuseFailAlloc_4331_; 
v_reuseFailAlloc_4331_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4331_, 0, v___x_4288_);
lean_ctor_set(v_reuseFailAlloc_4331_, 1, v___f_4284_);
lean_ctor_set(v_reuseFailAlloc_4331_, 2, v___f_4291_);
lean_ctor_set(v_reuseFailAlloc_4331_, 3, v___f_4290_);
lean_ctor_set(v_reuseFailAlloc_4331_, 4, v___f_4289_);
v___x_4293_ = v_reuseFailAlloc_4331_;
goto v_reusejp_4292_;
}
v_reusejp_4292_:
{
lean_object* v___x_4295_; 
if (v_isShared_4276_ == 0)
{
lean_ctor_set(v___x_4275_, 1, v___f_4285_);
lean_ctor_set(v___x_4275_, 0, v___x_4293_);
v___x_4295_ = v___x_4275_;
goto v_reusejp_4294_;
}
else
{
lean_object* v_reuseFailAlloc_4330_; 
v_reuseFailAlloc_4330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4330_, 0, v___x_4293_);
lean_ctor_set(v_reuseFailAlloc_4330_, 1, v___f_4285_);
v___x_4295_ = v_reuseFailAlloc_4330_;
goto v_reusejp_4294_;
}
v_reusejp_4294_:
{
lean_object* v___x_4296_; lean_object* v_toApplicative_4297_; lean_object* v___x_4299_; uint8_t v_isShared_4300_; uint8_t v_isSharedCheck_4328_; 
v___x_4296_ = l_StateRefT_x27_instMonad___redArg(v___x_4295_);
v_toApplicative_4297_ = lean_ctor_get(v___x_4296_, 0);
v_isSharedCheck_4328_ = !lean_is_exclusive(v___x_4296_);
if (v_isSharedCheck_4328_ == 0)
{
lean_object* v_unused_4329_; 
v_unused_4329_ = lean_ctor_get(v___x_4296_, 1);
lean_dec(v_unused_4329_);
v___x_4299_ = v___x_4296_;
v_isShared_4300_ = v_isSharedCheck_4328_;
goto v_resetjp_4298_;
}
else
{
lean_inc(v_toApplicative_4297_);
lean_dec(v___x_4296_);
v___x_4299_ = lean_box(0);
v_isShared_4300_ = v_isSharedCheck_4328_;
goto v_resetjp_4298_;
}
v_resetjp_4298_:
{
lean_object* v_toFunctor_4301_; lean_object* v_toSeq_4302_; lean_object* v_toSeqLeft_4303_; lean_object* v_toSeqRight_4304_; lean_object* v___x_4306_; uint8_t v_isShared_4307_; uint8_t v_isSharedCheck_4326_; 
v_toFunctor_4301_ = lean_ctor_get(v_toApplicative_4297_, 0);
v_toSeq_4302_ = lean_ctor_get(v_toApplicative_4297_, 2);
v_toSeqLeft_4303_ = lean_ctor_get(v_toApplicative_4297_, 3);
v_toSeqRight_4304_ = lean_ctor_get(v_toApplicative_4297_, 4);
v_isSharedCheck_4326_ = !lean_is_exclusive(v_toApplicative_4297_);
if (v_isSharedCheck_4326_ == 0)
{
lean_object* v_unused_4327_; 
v_unused_4327_ = lean_ctor_get(v_toApplicative_4297_, 1);
lean_dec(v_unused_4327_);
v___x_4306_ = v_toApplicative_4297_;
v_isShared_4307_ = v_isSharedCheck_4326_;
goto v_resetjp_4305_;
}
else
{
lean_inc(v_toSeqRight_4304_);
lean_inc(v_toSeqLeft_4303_);
lean_inc(v_toSeq_4302_);
lean_inc(v_toFunctor_4301_);
lean_dec(v_toApplicative_4297_);
v___x_4306_ = lean_box(0);
v_isShared_4307_ = v_isSharedCheck_4326_;
goto v_resetjp_4305_;
}
v_resetjp_4305_:
{
lean_object* v___f_4308_; lean_object* v___f_4309_; lean_object* v___f_4310_; lean_object* v___f_4311_; lean_object* v___x_4312_; lean_object* v___f_4313_; lean_object* v___f_4314_; lean_object* v___f_4315_; lean_object* v___x_4317_; 
v___f_4308_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__3));
v___f_4309_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__4));
lean_inc_ref(v_toFunctor_4301_);
v___f_4310_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4310_, 0, v_toFunctor_4301_);
v___f_4311_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4311_, 0, v_toFunctor_4301_);
v___x_4312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4312_, 0, v___f_4310_);
lean_ctor_set(v___x_4312_, 1, v___f_4311_);
v___f_4313_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4313_, 0, v_toSeqRight_4304_);
v___f_4314_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4314_, 0, v_toSeqLeft_4303_);
v___f_4315_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4315_, 0, v_toSeq_4302_);
if (v_isShared_4307_ == 0)
{
lean_ctor_set(v___x_4306_, 4, v___f_4313_);
lean_ctor_set(v___x_4306_, 3, v___f_4314_);
lean_ctor_set(v___x_4306_, 2, v___f_4315_);
lean_ctor_set(v___x_4306_, 1, v___f_4308_);
lean_ctor_set(v___x_4306_, 0, v___x_4312_);
v___x_4317_ = v___x_4306_;
goto v_reusejp_4316_;
}
else
{
lean_object* v_reuseFailAlloc_4325_; 
v_reuseFailAlloc_4325_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4325_, 0, v___x_4312_);
lean_ctor_set(v_reuseFailAlloc_4325_, 1, v___f_4308_);
lean_ctor_set(v_reuseFailAlloc_4325_, 2, v___f_4315_);
lean_ctor_set(v_reuseFailAlloc_4325_, 3, v___f_4314_);
lean_ctor_set(v_reuseFailAlloc_4325_, 4, v___f_4313_);
v___x_4317_ = v_reuseFailAlloc_4325_;
goto v_reusejp_4316_;
}
v_reusejp_4316_:
{
lean_object* v___x_4319_; 
if (v_isShared_4300_ == 0)
{
lean_ctor_set(v___x_4299_, 1, v___f_4309_);
lean_ctor_set(v___x_4299_, 0, v___x_4317_);
v___x_4319_ = v___x_4299_;
goto v_reusejp_4318_;
}
else
{
lean_object* v_reuseFailAlloc_4324_; 
v_reuseFailAlloc_4324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4324_, 0, v___x_4317_);
lean_ctor_set(v_reuseFailAlloc_4324_, 1, v___f_4309_);
v___x_4319_ = v_reuseFailAlloc_4324_;
goto v_reusejp_4318_;
}
v_reusejp_4318_:
{
lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_15665__overap_4322_; lean_object* v___x_4323_; 
v___x_4320_ = lean_box(0);
v___x_4321_ = l_instInhabitedOfMonad___redArg(v___x_4319_, v___x_4320_);
v___x_15665__overap_4322_ = lean_panic_fn_borrowed(v___x_4321_, v_msg_4265_);
lean_dec(v___x_4321_);
lean_inc(v___y_4269_);
lean_inc_ref(v___y_4268_);
lean_inc(v___y_4267_);
lean_inc_ref(v___y_4266_);
v___x_4323_ = lean_apply_5(v___x_15665__overap_4322_, v___y_4266_, v___y_4267_, v___y_4268_, v___y_4269_, lean_box(0));
return v___x_4323_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___boxed(lean_object* v_msg_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_){
_start:
{
lean_object* v_res_4342_; 
v_res_4342_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(v_msg_4336_, v___y_4337_, v___y_4338_, v___y_4339_, v___y_4340_);
lean_dec(v___y_4340_);
lean_dec_ref(v___y_4339_);
lean_dec(v___y_4338_);
lean_dec_ref(v___y_4337_);
return v_res_4342_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1(void){
_start:
{
lean_object* v___x_4344_; lean_object* v___x_4345_; 
v___x_4344_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__0));
v___x_4345_ = l_Lean_stringToMessageData(v___x_4344_);
return v___x_4345_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4(void){
_start:
{
lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; 
v___x_4348_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__2));
v___x_4349_ = lean_unsigned_to_nat(11u);
v___x_4350_ = lean_unsigned_to_nat(122u);
v___x_4351_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__3));
v___x_4352_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__2));
v___x_4353_ = l_mkPanicMessageWithDecl(v___x_4352_, v___x_4351_, v___x_4350_, v___x_4349_, v___x_4348_);
return v___x_4353_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(lean_object* v_constName_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_){
_start:
{
lean_object* v___x_4368_; lean_object* v_env_4369_; uint8_t v___x_4370_; lean_object* v___x_4371_; 
v___x_4368_ = lean_st_ref_get(v___y_4358_);
v_env_4369_ = lean_ctor_get(v___x_4368_, 0);
lean_inc_ref(v_env_4369_);
lean_dec(v___x_4368_);
v___x_4370_ = 0;
lean_inc(v_constName_4354_);
v___x_4371_ = l_Lean_Environment_findAsync_x3f(v_env_4369_, v_constName_4354_, v___x_4370_);
if (lean_obj_tag(v___x_4371_) == 1)
{
lean_object* v_val_4372_; uint8_t v_kind_4373_; 
v_val_4372_ = lean_ctor_get(v___x_4371_, 0);
lean_inc(v_val_4372_);
lean_dec_ref_known(v___x_4371_, 1);
v_kind_4373_ = lean_ctor_get_uint8(v_val_4372_, sizeof(void*)*3);
if (v_kind_4373_ == 6)
{
lean_object* v___x_4374_; 
v___x_4374_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_4372_);
if (lean_obj_tag(v___x_4374_) == 6)
{
lean_object* v_val_4375_; lean_object* v___x_4377_; uint8_t v_isShared_4378_; uint8_t v_isSharedCheck_4382_; 
lean_dec(v_constName_4354_);
v_val_4375_ = lean_ctor_get(v___x_4374_, 0);
v_isSharedCheck_4382_ = !lean_is_exclusive(v___x_4374_);
if (v_isSharedCheck_4382_ == 0)
{
v___x_4377_ = v___x_4374_;
v_isShared_4378_ = v_isSharedCheck_4382_;
goto v_resetjp_4376_;
}
else
{
lean_inc(v_val_4375_);
lean_dec(v___x_4374_);
v___x_4377_ = lean_box(0);
v_isShared_4378_ = v_isSharedCheck_4382_;
goto v_resetjp_4376_;
}
v_resetjp_4376_:
{
lean_object* v___x_4380_; 
if (v_isShared_4378_ == 0)
{
lean_ctor_set_tag(v___x_4377_, 0);
v___x_4380_ = v___x_4377_;
goto v_reusejp_4379_;
}
else
{
lean_object* v_reuseFailAlloc_4381_; 
v_reuseFailAlloc_4381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4381_, 0, v_val_4375_);
v___x_4380_ = v_reuseFailAlloc_4381_;
goto v_reusejp_4379_;
}
v_reusejp_4379_:
{
return v___x_4380_;
}
}
}
else
{
lean_object* v___x_4383_; lean_object* v___x_4384_; 
lean_dec_ref(v___x_4374_);
v___x_4383_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4);
v___x_4384_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(v___x_4383_, v___y_4355_, v___y_4356_, v___y_4357_, v___y_4358_);
if (lean_obj_tag(v___x_4384_) == 0)
{
lean_object* v_a_4385_; lean_object* v___x_4387_; uint8_t v_isShared_4388_; uint8_t v_isSharedCheck_4393_; 
v_a_4385_ = lean_ctor_get(v___x_4384_, 0);
v_isSharedCheck_4393_ = !lean_is_exclusive(v___x_4384_);
if (v_isSharedCheck_4393_ == 0)
{
v___x_4387_ = v___x_4384_;
v_isShared_4388_ = v_isSharedCheck_4393_;
goto v_resetjp_4386_;
}
else
{
lean_inc(v_a_4385_);
lean_dec(v___x_4384_);
v___x_4387_ = lean_box(0);
v_isShared_4388_ = v_isSharedCheck_4393_;
goto v_resetjp_4386_;
}
v_resetjp_4386_:
{
if (lean_obj_tag(v_a_4385_) == 0)
{
lean_del_object(v___x_4387_);
goto v___jp_4360_;
}
else
{
lean_object* v_val_4389_; lean_object* v___x_4391_; 
lean_dec(v_constName_4354_);
v_val_4389_ = lean_ctor_get(v_a_4385_, 0);
lean_inc(v_val_4389_);
lean_dec_ref_known(v_a_4385_, 1);
if (v_isShared_4388_ == 0)
{
lean_ctor_set(v___x_4387_, 0, v_val_4389_);
v___x_4391_ = v___x_4387_;
goto v_reusejp_4390_;
}
else
{
lean_object* v_reuseFailAlloc_4392_; 
v_reuseFailAlloc_4392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4392_, 0, v_val_4389_);
v___x_4391_ = v_reuseFailAlloc_4392_;
goto v_reusejp_4390_;
}
v_reusejp_4390_:
{
return v___x_4391_;
}
}
}
}
else
{
lean_object* v_a_4394_; lean_object* v___x_4396_; uint8_t v_isShared_4397_; uint8_t v_isSharedCheck_4401_; 
lean_dec(v_constName_4354_);
v_a_4394_ = lean_ctor_get(v___x_4384_, 0);
v_isSharedCheck_4401_ = !lean_is_exclusive(v___x_4384_);
if (v_isSharedCheck_4401_ == 0)
{
v___x_4396_ = v___x_4384_;
v_isShared_4397_ = v_isSharedCheck_4401_;
goto v_resetjp_4395_;
}
else
{
lean_inc(v_a_4394_);
lean_dec(v___x_4384_);
v___x_4396_ = lean_box(0);
v_isShared_4397_ = v_isSharedCheck_4401_;
goto v_resetjp_4395_;
}
v_resetjp_4395_:
{
lean_object* v___x_4399_; 
if (v_isShared_4397_ == 0)
{
v___x_4399_ = v___x_4396_;
goto v_reusejp_4398_;
}
else
{
lean_object* v_reuseFailAlloc_4400_; 
v_reuseFailAlloc_4400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4400_, 0, v_a_4394_);
v___x_4399_ = v_reuseFailAlloc_4400_;
goto v_reusejp_4398_;
}
v_reusejp_4398_:
{
return v___x_4399_;
}
}
}
}
}
else
{
lean_dec(v_val_4372_);
goto v___jp_4360_;
}
}
else
{
lean_dec(v___x_4371_);
goto v___jp_4360_;
}
v___jp_4360_:
{
lean_object* v___x_4361_; uint8_t v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; 
v___x_4361_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_4362_ = 0;
v___x_4363_ = l_Lean_MessageData_ofConstName(v_constName_4354_, v___x_4362_);
v___x_4364_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4364_, 0, v___x_4361_);
lean_ctor_set(v___x_4364_, 1, v___x_4363_);
v___x_4365_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1);
v___x_4366_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4366_, 0, v___x_4364_);
lean_ctor_set(v___x_4366_, 1, v___x_4365_);
v___x_4367_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_4366_, v___y_4355_, v___y_4356_, v___y_4357_, v___y_4358_);
return v___x_4367_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___boxed(lean_object* v_constName_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_){
_start:
{
lean_object* v_res_4408_; 
v_res_4408_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(v_constName_4402_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_);
lean_dec(v___y_4406_);
lean_dec_ref(v___y_4405_);
lean_dec(v___y_4404_);
lean_dec_ref(v___y_4403_);
return v_res_4408_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0(lean_object* v_head_4409_, lean_object* v___x_4410_, lean_object* v___x_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_){
_start:
{
lean_object* v___x_4417_; 
v___x_4417_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(v_head_4409_, v___y_4412_, v___y_4413_, v___y_4414_, v___y_4415_);
if (lean_obj_tag(v___x_4417_) == 0)
{
lean_object* v_a_4418_; lean_object* v___x_4420_; uint8_t v_isShared_4421_; uint8_t v_isSharedCheck_4429_; 
v_a_4418_ = lean_ctor_get(v___x_4417_, 0);
v_isSharedCheck_4429_ = !lean_is_exclusive(v___x_4417_);
if (v_isSharedCheck_4429_ == 0)
{
v___x_4420_ = v___x_4417_;
v_isShared_4421_ = v_isSharedCheck_4429_;
goto v_resetjp_4419_;
}
else
{
lean_inc(v_a_4418_);
lean_dec(v___x_4417_);
v___x_4420_ = lean_box(0);
v_isShared_4421_ = v_isSharedCheck_4429_;
goto v_resetjp_4419_;
}
v_resetjp_4419_:
{
lean_object* v_numFields_4422_; uint8_t v___x_4423_; 
v_numFields_4422_ = lean_ctor_get(v_a_4418_, 4);
v___x_4423_ = lean_nat_dec_lt(v___x_4410_, v_numFields_4422_);
if (v___x_4423_ == 0)
{
lean_object* v___x_4425_; 
lean_dec(v_a_4418_);
if (v_isShared_4421_ == 0)
{
lean_ctor_set(v___x_4420_, 0, v___x_4411_);
v___x_4425_ = v___x_4420_;
goto v_reusejp_4424_;
}
else
{
lean_object* v_reuseFailAlloc_4426_; 
v_reuseFailAlloc_4426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4426_, 0, v___x_4411_);
v___x_4425_ = v_reuseFailAlloc_4426_;
goto v_reusejp_4424_;
}
v_reusejp_4424_:
{
return v___x_4425_;
}
}
else
{
lean_object* v___x_4427_; 
lean_del_object(v___x_4420_);
lean_inc(v_a_4418_);
v___x_4427_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(v_a_4418_, v___y_4412_, v___y_4413_, v___y_4414_, v___y_4415_);
if (lean_obj_tag(v___x_4427_) == 0)
{
lean_object* v___x_4428_; 
lean_dec_ref_known(v___x_4427_, 1);
v___x_4428_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(v_a_4418_, v___y_4412_, v___y_4413_, v___y_4414_, v___y_4415_);
return v___x_4428_;
}
else
{
lean_dec(v_a_4418_);
return v___x_4427_;
}
}
}
}
else
{
lean_object* v_a_4430_; lean_object* v___x_4432_; uint8_t v_isShared_4433_; uint8_t v_isSharedCheck_4437_; 
v_a_4430_ = lean_ctor_get(v___x_4417_, 0);
v_isSharedCheck_4437_ = !lean_is_exclusive(v___x_4417_);
if (v_isSharedCheck_4437_ == 0)
{
v___x_4432_ = v___x_4417_;
v_isShared_4433_ = v_isSharedCheck_4437_;
goto v_resetjp_4431_;
}
else
{
lean_inc(v_a_4430_);
lean_dec(v___x_4417_);
v___x_4432_ = lean_box(0);
v_isShared_4433_ = v_isSharedCheck_4437_;
goto v_resetjp_4431_;
}
v_resetjp_4431_:
{
lean_object* v___x_4435_; 
if (v_isShared_4433_ == 0)
{
v___x_4435_ = v___x_4432_;
goto v_reusejp_4434_;
}
else
{
lean_object* v_reuseFailAlloc_4436_; 
v_reuseFailAlloc_4436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4436_, 0, v_a_4430_);
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
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0___boxed(lean_object* v_head_4438_, lean_object* v___x_4439_, lean_object* v___x_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_){
_start:
{
lean_object* v_res_4446_; 
v_res_4446_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0(v_head_4438_, v___x_4439_, v___x_4440_, v___y_4441_, v___y_4442_, v___y_4443_, v___y_4444_);
lean_dec(v___y_4444_);
lean_dec_ref(v___y_4443_);
lean_dec(v___y_4442_);
lean_dec_ref(v___y_4441_);
lean_dec(v___x_4439_);
return v_res_4446_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(uint8_t v___y_4447_, uint8_t v___x_4448_, lean_object* v_as_x27_4449_, lean_object* v_b_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_){
_start:
{
if (lean_obj_tag(v_as_x27_4449_) == 0)
{
lean_object* v___x_4456_; 
v___x_4456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4456_, 0, v_b_4450_);
return v___x_4456_;
}
else
{
lean_object* v_head_4457_; lean_object* v_tail_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; lean_object* v___f_4461_; uint8_t v___y_4463_; uint8_t v___x_4466_; 
v_head_4457_ = lean_ctor_get(v_as_x27_4449_, 0);
v_tail_4458_ = lean_ctor_get(v_as_x27_4449_, 1);
v___x_4459_ = lean_unsigned_to_nat(0u);
v___x_4460_ = lean_box(0);
lean_inc(v_head_4457_);
v___f_4461_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4461_, 0, v_head_4457_);
lean_closure_set(v___f_4461_, 1, v___x_4459_);
lean_closure_set(v___f_4461_, 2, v___x_4460_);
v___x_4466_ = l_Lean_isPrivateName(v_head_4457_);
if (v___x_4466_ == 0)
{
v___y_4463_ = v___y_4447_;
goto v___jp_4462_;
}
else
{
v___y_4463_ = v___x_4448_;
goto v___jp_4462_;
}
v___jp_4462_:
{
lean_object* v___x_4464_; 
v___x_4464_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(v___f_4461_, v___y_4463_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_);
if (lean_obj_tag(v___x_4464_) == 0)
{
lean_dec_ref_known(v___x_4464_, 1);
v_as_x27_4449_ = v_tail_4458_;
v_b_4450_ = v___x_4460_;
goto _start;
}
else
{
return v___x_4464_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___boxed(lean_object* v___y_4467_, lean_object* v___x_4468_, lean_object* v_as_x27_4469_, lean_object* v_b_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_){
_start:
{
uint8_t v___y_16772__boxed_4476_; uint8_t v___x_16773__boxed_4477_; lean_object* v_res_4478_; 
v___y_16772__boxed_4476_ = lean_unbox(v___y_4467_);
v___x_16773__boxed_4477_ = lean_unbox(v___x_4468_);
v_res_4478_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___y_16772__boxed_4476_, v___x_16773__boxed_4477_, v_as_x27_4469_, v_b_4470_, v___y_4471_, v___y_4472_, v___y_4473_, v___y_4474_);
lean_dec(v___y_4474_);
lean_dec_ref(v___y_4473_);
lean_dec(v___y_4472_);
lean_dec_ref(v___y_4471_);
lean_dec(v_as_x27_4469_);
return v_res_4478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__1(uint8_t v___y_4479_, uint8_t v_isUnsafe_4480_, lean_object* v_ctors_4481_, lean_object* v___x_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_){
_start:
{
lean_object* v___x_4488_; 
v___x_4488_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___y_4479_, v_isUnsafe_4480_, v_ctors_4481_, v___x_4482_, v___y_4483_, v___y_4484_, v___y_4485_, v___y_4486_);
if (lean_obj_tag(v___x_4488_) == 0)
{
lean_object* v___x_4490_; uint8_t v_isShared_4491_; uint8_t v_isSharedCheck_4495_; 
v_isSharedCheck_4495_ = !lean_is_exclusive(v___x_4488_);
if (v_isSharedCheck_4495_ == 0)
{
lean_object* v_unused_4496_; 
v_unused_4496_ = lean_ctor_get(v___x_4488_, 0);
lean_dec(v_unused_4496_);
v___x_4490_ = v___x_4488_;
v_isShared_4491_ = v_isSharedCheck_4495_;
goto v_resetjp_4489_;
}
else
{
lean_dec(v___x_4488_);
v___x_4490_ = lean_box(0);
v_isShared_4491_ = v_isSharedCheck_4495_;
goto v_resetjp_4489_;
}
v_resetjp_4489_:
{
lean_object* v___x_4493_; 
if (v_isShared_4491_ == 0)
{
lean_ctor_set(v___x_4490_, 0, v___x_4482_);
v___x_4493_ = v___x_4490_;
goto v_reusejp_4492_;
}
else
{
lean_object* v_reuseFailAlloc_4494_; 
v_reuseFailAlloc_4494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4494_, 0, v___x_4482_);
v___x_4493_ = v_reuseFailAlloc_4494_;
goto v_reusejp_4492_;
}
v_reusejp_4492_:
{
return v___x_4493_;
}
}
}
else
{
return v___x_4488_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed(lean_object* v___y_4497_, lean_object* v_isUnsafe_4498_, lean_object* v_ctors_4499_, lean_object* v___x_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_){
_start:
{
uint8_t v___y_16817__boxed_4506_; uint8_t v_isUnsafe_boxed_4507_; lean_object* v_res_4508_; 
v___y_16817__boxed_4506_ = lean_unbox(v___y_4497_);
v_isUnsafe_boxed_4507_ = lean_unbox(v_isUnsafe_4498_);
v_res_4508_ = l_Lean_Meta_mkInjectiveTheorems___lam__1(v___y_16817__boxed_4506_, v_isUnsafe_boxed_4507_, v_ctors_4499_, v___x_4500_, v___y_4501_, v___y_4502_, v___y_4503_, v___y_4504_);
lean_dec(v___y_4504_);
lean_dec_ref(v___y_4503_);
lean_dec(v___y_4502_);
lean_dec_ref(v___y_4501_);
lean_dec(v_ctors_4499_);
return v_res_4508_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4510_; lean_object* v___x_4511_; 
v___x_4510_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__0));
v___x_4511_ = l_Lean_stringToMessageData(v___x_4510_);
return v___x_4511_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(lean_object* v_constName_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_){
_start:
{
lean_object* v___x_4518_; lean_object* v_env_4519_; lean_object* v___x_4520_; 
v___x_4518_ = lean_st_ref_get(v___y_4516_);
v_env_4519_ = lean_ctor_get(v___x_4518_, 0);
lean_inc_ref(v_env_4519_);
lean_dec(v___x_4518_);
lean_inc(v_constName_4512_);
v___x_4520_ = l_Lean_isInductiveCore_x3f(v_env_4519_, v_constName_4512_);
if (lean_obj_tag(v___x_4520_) == 0)
{
lean_object* v___x_4521_; uint8_t v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; 
v___x_4521_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_4522_ = 0;
v___x_4523_ = l_Lean_MessageData_ofConstName(v_constName_4512_, v___x_4522_);
v___x_4524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4524_, 0, v___x_4521_);
lean_ctor_set(v___x_4524_, 1, v___x_4523_);
v___x_4525_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1);
v___x_4526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4526_, 0, v___x_4524_);
lean_ctor_set(v___x_4526_, 1, v___x_4525_);
v___x_4527_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_4526_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_);
return v___x_4527_;
}
else
{
lean_object* v_val_4528_; lean_object* v___x_4530_; uint8_t v_isShared_4531_; uint8_t v_isSharedCheck_4535_; 
lean_dec(v_constName_4512_);
v_val_4528_ = lean_ctor_get(v___x_4520_, 0);
v_isSharedCheck_4535_ = !lean_is_exclusive(v___x_4520_);
if (v_isSharedCheck_4535_ == 0)
{
v___x_4530_ = v___x_4520_;
v_isShared_4531_ = v_isSharedCheck_4535_;
goto v_resetjp_4529_;
}
else
{
lean_inc(v_val_4528_);
lean_dec(v___x_4520_);
v___x_4530_ = lean_box(0);
v_isShared_4531_ = v_isSharedCheck_4535_;
goto v_resetjp_4529_;
}
v_resetjp_4529_:
{
lean_object* v___x_4533_; 
if (v_isShared_4531_ == 0)
{
lean_ctor_set_tag(v___x_4530_, 0);
v___x_4533_ = v___x_4530_;
goto v_reusejp_4532_;
}
else
{
lean_object* v_reuseFailAlloc_4534_; 
v_reuseFailAlloc_4534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4534_, 0, v_val_4528_);
v___x_4533_ = v_reuseFailAlloc_4534_;
goto v_reusejp_4532_;
}
v_reusejp_4532_:
{
return v___x_4533_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___boxed(lean_object* v_constName_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_){
_start:
{
lean_object* v_res_4542_; 
v_res_4542_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_constName_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_);
lean_dec(v___y_4540_);
lean_dec_ref(v___y_4539_);
lean_dec(v___y_4538_);
lean_dec_ref(v___y_4537_);
return v_res_4542_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__0(void){
_start:
{
lean_object* v___x_4543_; 
v___x_4543_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4543_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__1(void){
_start:
{
lean_object* v___x_4544_; lean_object* v___x_4545_; 
v___x_4544_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__0, &l_Lean_Meta_mkInjectiveTheorems___closed__0_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__0);
v___x_4545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4545_, 0, v___x_4544_);
return v___x_4545_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__2(void){
_start:
{
lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; 
v___x_4546_ = lean_unsigned_to_nat(32u);
v___x_4547_ = lean_mk_empty_array_with_capacity(v___x_4546_);
v___x_4548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4548_, 0, v___x_4547_);
return v___x_4548_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__3(void){
_start:
{
size_t v___x_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; 
v___x_4549_ = ((size_t)5ULL);
v___x_4550_ = lean_unsigned_to_nat(0u);
v___x_4551_ = lean_unsigned_to_nat(32u);
v___x_4552_ = lean_mk_empty_array_with_capacity(v___x_4551_);
v___x_4553_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__2, &l_Lean_Meta_mkInjectiveTheorems___closed__2_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__2);
v___x_4554_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4554_, 0, v___x_4553_);
lean_ctor_set(v___x_4554_, 1, v___x_4552_);
lean_ctor_set(v___x_4554_, 2, v___x_4550_);
lean_ctor_set(v___x_4554_, 3, v___x_4550_);
lean_ctor_set_usize(v___x_4554_, 4, v___x_4549_);
return v___x_4554_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__4(void){
_start:
{
lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; 
v___x_4555_ = lean_box(1);
v___x_4556_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_4557_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_4558_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4558_, 0, v___x_4557_);
lean_ctor_set(v___x_4558_, 1, v___x_4556_);
lean_ctor_set(v___x_4558_, 2, v___x_4555_);
return v___x_4558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems(lean_object* v_declName_4561_, lean_object* v_a_4562_, lean_object* v_a_4563_, lean_object* v_a_4564_, lean_object* v_a_4565_){
_start:
{
lean_object* v___x_4567_; lean_object* v___x_4568_; 
v___x_4567_ = lean_st_ref_get(v_a_4565_);
lean_inc(v_declName_4561_);
v___x_4568_ = l_Lean_Meta_isInductivePredicate(v_declName_4561_, v_a_4562_, v_a_4563_, v_a_4564_, v_a_4565_);
if (lean_obj_tag(v___x_4568_) == 0)
{
lean_object* v_a_4569_; lean_object* v___x_4571_; uint8_t v_isShared_4572_; uint8_t v_isSharedCheck_4767_; 
v_a_4569_ = lean_ctor_get(v___x_4568_, 0);
v_isSharedCheck_4767_ = !lean_is_exclusive(v___x_4568_);
if (v_isSharedCheck_4767_ == 0)
{
v___x_4571_ = v___x_4568_;
v_isShared_4572_ = v_isSharedCheck_4767_;
goto v_resetjp_4570_;
}
else
{
lean_inc(v_a_4569_);
lean_dec(v___x_4568_);
v___x_4571_ = lean_box(0);
v_isShared_4572_ = v_isSharedCheck_4767_;
goto v_resetjp_4570_;
}
v_resetjp_4570_:
{
lean_object* v_env_4578_; lean_object* v___f_4579_; lean_object* v___x_4580_; uint8_t v___x_4581_; lean_object* v___y_4583_; lean_object* v___y_4584_; lean_object* v___y_4585_; uint8_t v___y_4586_; lean_object* v___y_4587_; lean_object* v___y_4588_; lean_object* v_a_4589_; lean_object* v___y_4599_; lean_object* v___y_4600_; lean_object* v___y_4601_; lean_object* v___y_4602_; uint8_t v___y_4603_; lean_object* v___y_4604_; lean_object* v_a_4605_; lean_object* v___y_4608_; lean_object* v___y_4609_; lean_object* v___y_4610_; lean_object* v___y_4611_; uint8_t v___y_4612_; lean_object* v___y_4613_; lean_object* v_a_4614_; lean_object* v___y_4617_; lean_object* v___y_4618_; lean_object* v___y_4619_; lean_object* v___y_4620_; uint8_t v___y_4621_; lean_object* v___y_4622_; lean_object* v_a_4623_; lean_object* v___y_4636_; lean_object* v___y_4637_; lean_object* v___y_4638_; lean_object* v___y_4639_; lean_object* v___y_4640_; uint8_t v___y_4641_; lean_object* v_a_4642_; lean_object* v___y_4645_; lean_object* v___y_4646_; lean_object* v___y_4647_; lean_object* v___y_4648_; lean_object* v___y_4649_; uint8_t v___y_4650_; lean_object* v_a_4651_; uint8_t v___y_4654_; lean_object* v___y_4655_; lean_object* v___y_4656_; lean_object* v___y_4657_; uint8_t v___y_4658_; uint8_t v___y_4696_; uint8_t v___x_4762_; 
v_env_4578_ = lean_ctor_get(v___x_4567_, 0);
lean_inc_ref(v_env_4578_);
lean_dec(v___x_4567_);
lean_inc(v_declName_4561_);
v___f_4579_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4579_, 0, v_declName_4561_);
v___x_4580_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__2));
v___x_4581_ = 1;
v___x_4762_ = l_Lean_Environment_contains(v_env_4578_, v___x_4580_, v___x_4581_);
if (v___x_4762_ == 0)
{
v___y_4696_ = v___x_4762_;
goto v___jp_4695_;
}
else
{
lean_object* v_toCold_4763_; lean_object* v_options_4764_; lean_object* v___x_4765_; uint8_t v___x_4766_; 
v_toCold_4763_ = lean_ctor_get(v_a_4564_, 0);
v_options_4764_ = lean_ctor_get(v_toCold_4763_, 2);
v___x_4765_ = l_Lean_Meta_genInjectivity;
v___x_4766_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_4764_, v___x_4765_);
v___y_4696_ = v___x_4766_;
goto v___jp_4695_;
}
v___jp_4573_:
{
lean_object* v___x_4574_; lean_object* v___x_4576_; 
v___x_4574_ = lean_box(0);
if (v_isShared_4572_ == 0)
{
lean_ctor_set(v___x_4571_, 0, v___x_4574_);
v___x_4576_ = v___x_4571_;
goto v_reusejp_4575_;
}
else
{
lean_object* v_reuseFailAlloc_4577_; 
v_reuseFailAlloc_4577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4577_, 0, v___x_4574_);
v___x_4576_ = v_reuseFailAlloc_4577_;
goto v_reusejp_4575_;
}
v_reusejp_4575_:
{
return v___x_4576_;
}
}
v___jp_4582_:
{
lean_object* v___x_4590_; double v___x_4591_; double v___x_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; 
v___x_4590_ = lean_io_get_num_heartbeats();
v___x_4591_ = lean_float_of_nat(v___y_4588_);
v___x_4592_ = lean_float_of_nat(v___x_4590_);
v___x_4593_ = lean_box_float(v___x_4591_);
v___x_4594_ = lean_box_float(v___x_4592_);
v___x_4595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4595_, 0, v___x_4593_);
lean_ctor_set(v___x_4595_, 1, v___x_4594_);
v___x_4596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4596_, 0, v_a_4589_);
lean_ctor_set(v___x_4596_, 1, v___x_4595_);
lean_inc_ref(v___y_4587_);
lean_inc(v___y_4585_);
v___x_4597_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v___y_4585_, v___x_4581_, v___y_4587_, v___y_4584_, v___y_4586_, v___y_4583_, v___f_4579_, v___x_4596_, v_a_4562_, v_a_4563_, v_a_4564_, v_a_4565_);
return v___x_4597_;
}
v___jp_4598_:
{
lean_object* v___x_4606_; 
v___x_4606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4606_, 0, v_a_4605_);
v___y_4583_ = v___y_4599_;
v___y_4584_ = v___y_4600_;
v___y_4585_ = v___y_4601_;
v___y_4586_ = v___y_4603_;
v___y_4587_ = v___y_4602_;
v___y_4588_ = v___y_4604_;
v_a_4589_ = v___x_4606_;
goto v___jp_4582_;
}
v___jp_4607_:
{
lean_object* v___x_4615_; 
v___x_4615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4615_, 0, v_a_4614_);
v___y_4583_ = v___y_4608_;
v___y_4584_ = v___y_4609_;
v___y_4585_ = v___y_4610_;
v___y_4586_ = v___y_4612_;
v___y_4587_ = v___y_4611_;
v___y_4588_ = v___y_4613_;
v_a_4589_ = v___x_4615_;
goto v___jp_4582_;
}
v___jp_4616_:
{
lean_object* v___x_4624_; double v___x_4625_; double v___x_4626_; double v___x_4627_; double v___x_4628_; double v___x_4629_; lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; 
v___x_4624_ = lean_io_mono_nanos_now();
v___x_4625_ = lean_float_of_nat(v___y_4618_);
v___x_4626_ = lean_float_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0);
v___x_4627_ = lean_float_div(v___x_4625_, v___x_4626_);
v___x_4628_ = lean_float_of_nat(v___x_4624_);
v___x_4629_ = lean_float_div(v___x_4628_, v___x_4626_);
v___x_4630_ = lean_box_float(v___x_4627_);
v___x_4631_ = lean_box_float(v___x_4629_);
v___x_4632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4632_, 0, v___x_4630_);
lean_ctor_set(v___x_4632_, 1, v___x_4631_);
v___x_4633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4633_, 0, v_a_4623_);
lean_ctor_set(v___x_4633_, 1, v___x_4632_);
lean_inc_ref(v___y_4622_);
lean_inc(v___y_4620_);
v___x_4634_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v___y_4620_, v___x_4581_, v___y_4622_, v___y_4619_, v___y_4621_, v___y_4617_, v___f_4579_, v___x_4633_, v_a_4562_, v_a_4563_, v_a_4564_, v_a_4565_);
return v___x_4634_;
}
v___jp_4635_:
{
lean_object* v___x_4643_; 
v___x_4643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4643_, 0, v_a_4642_);
v___y_4617_ = v___y_4636_;
v___y_4618_ = v___y_4637_;
v___y_4619_ = v___y_4638_;
v___y_4620_ = v___y_4639_;
v___y_4621_ = v___y_4641_;
v___y_4622_ = v___y_4640_;
v_a_4623_ = v___x_4643_;
goto v___jp_4616_;
}
v___jp_4644_:
{
lean_object* v___x_4652_; 
v___x_4652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4652_, 0, v_a_4651_);
v___y_4617_ = v___y_4645_;
v___y_4618_ = v___y_4646_;
v___y_4619_ = v___y_4647_;
v___y_4620_ = v___y_4648_;
v___y_4621_ = v___y_4650_;
v___y_4622_ = v___y_4649_;
v_a_4623_ = v___x_4652_;
goto v___jp_4616_;
}
v___jp_4653_:
{
lean_object* v___x_4659_; lean_object* v_a_4660_; lean_object* v___x_4661_; uint8_t v___x_4662_; 
v___x_4659_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v_a_4565_);
v_a_4660_ = lean_ctor_get(v___x_4659_, 0);
lean_inc(v_a_4660_);
lean_dec_ref(v___x_4659_);
v___x_4661_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4662_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v___y_4655_, v___x_4661_);
if (v___x_4662_ == 0)
{
lean_object* v___x_4663_; lean_object* v___x_4664_; 
v___x_4663_ = lean_io_mono_nanos_now();
v___x_4664_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4561_, v_a_4562_, v_a_4563_, v_a_4564_, v_a_4565_);
if (lean_obj_tag(v___x_4664_) == 0)
{
lean_object* v_a_4665_; uint8_t v_isUnsafe_4666_; 
v_a_4665_ = lean_ctor_get(v___x_4664_, 0);
lean_inc(v_a_4665_);
lean_dec_ref_known(v___x_4664_, 1);
v_isUnsafe_4666_ = lean_ctor_get_uint8(v_a_4665_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4666_ == 0)
{
lean_object* v_ctors_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___f_4673_; lean_object* v___x_4674_; 
v_ctors_4667_ = lean_ctor_get(v_a_4665_, 4);
lean_inc(v_ctors_4667_);
lean_dec(v_a_4665_);
v___x_4668_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4669_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4670_ = lean_box(0);
v___x_4671_ = lean_box(v___y_4654_);
v___x_4672_ = lean_box(v_isUnsafe_4666_);
v___f_4673_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed), 9, 4);
lean_closure_set(v___f_4673_, 0, v___x_4671_);
lean_closure_set(v___f_4673_, 1, v___x_4672_);
lean_closure_set(v___f_4673_, 2, v_ctors_4667_);
lean_closure_set(v___f_4673_, 3, v___x_4670_);
v___x_4674_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4668_, v___x_4669_, v___f_4673_, v_a_4562_, v_a_4563_, v_a_4564_, v_a_4565_);
if (lean_obj_tag(v___x_4674_) == 0)
{
lean_object* v_a_4675_; 
v_a_4675_ = lean_ctor_get(v___x_4674_, 0);
lean_inc(v_a_4675_);
lean_dec_ref_known(v___x_4674_, 1);
v___y_4636_ = v_a_4660_;
v___y_4637_ = v___x_4663_;
v___y_4638_ = v___y_4655_;
v___y_4639_ = v___y_4656_;
v___y_4640_ = v___y_4657_;
v___y_4641_ = v___y_4658_;
v_a_4642_ = v_a_4675_;
goto v___jp_4635_;
}
else
{
lean_object* v_a_4676_; 
v_a_4676_ = lean_ctor_get(v___x_4674_, 0);
lean_inc(v_a_4676_);
lean_dec_ref_known(v___x_4674_, 1);
v___y_4645_ = v_a_4660_;
v___y_4646_ = v___x_4663_;
v___y_4647_ = v___y_4655_;
v___y_4648_ = v___y_4656_;
v___y_4649_ = v___y_4657_;
v___y_4650_ = v___y_4658_;
v_a_4651_ = v_a_4676_;
goto v___jp_4644_;
}
}
else
{
lean_object* v___x_4677_; 
lean_dec(v_a_4665_);
v___x_4677_ = lean_box(0);
v___y_4636_ = v_a_4660_;
v___y_4637_ = v___x_4663_;
v___y_4638_ = v___y_4655_;
v___y_4639_ = v___y_4656_;
v___y_4640_ = v___y_4657_;
v___y_4641_ = v___y_4658_;
v_a_4642_ = v___x_4677_;
goto v___jp_4635_;
}
}
else
{
lean_object* v_a_4678_; 
v_a_4678_ = lean_ctor_get(v___x_4664_, 0);
lean_inc(v_a_4678_);
lean_dec_ref_known(v___x_4664_, 1);
v___y_4645_ = v_a_4660_;
v___y_4646_ = v___x_4663_;
v___y_4647_ = v___y_4655_;
v___y_4648_ = v___y_4656_;
v___y_4649_ = v___y_4657_;
v___y_4650_ = v___y_4658_;
v_a_4651_ = v_a_4678_;
goto v___jp_4644_;
}
}
else
{
lean_object* v___x_4679_; lean_object* v___x_4680_; 
v___x_4679_ = lean_io_get_num_heartbeats();
v___x_4680_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4561_, v_a_4562_, v_a_4563_, v_a_4564_, v_a_4565_);
if (lean_obj_tag(v___x_4680_) == 0)
{
lean_object* v_a_4681_; uint8_t v_isUnsafe_4682_; 
v_a_4681_ = lean_ctor_get(v___x_4680_, 0);
lean_inc(v_a_4681_);
lean_dec_ref_known(v___x_4680_, 1);
v_isUnsafe_4682_ = lean_ctor_get_uint8(v_a_4681_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4682_ == 0)
{
lean_object* v_ctors_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___f_4689_; lean_object* v___x_4690_; 
v_ctors_4683_ = lean_ctor_get(v_a_4681_, 4);
lean_inc(v_ctors_4683_);
lean_dec(v_a_4681_);
v___x_4684_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4685_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4686_ = lean_box(0);
v___x_4687_ = lean_box(v___y_4654_);
v___x_4688_ = lean_box(v_isUnsafe_4682_);
v___f_4689_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed), 9, 4);
lean_closure_set(v___f_4689_, 0, v___x_4687_);
lean_closure_set(v___f_4689_, 1, v___x_4688_);
lean_closure_set(v___f_4689_, 2, v_ctors_4683_);
lean_closure_set(v___f_4689_, 3, v___x_4686_);
v___x_4690_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4684_, v___x_4685_, v___f_4689_, v_a_4562_, v_a_4563_, v_a_4564_, v_a_4565_);
if (lean_obj_tag(v___x_4690_) == 0)
{
lean_object* v_a_4691_; 
v_a_4691_ = lean_ctor_get(v___x_4690_, 0);
lean_inc(v_a_4691_);
lean_dec_ref_known(v___x_4690_, 1);
v___y_4599_ = v_a_4660_;
v___y_4600_ = v___y_4655_;
v___y_4601_ = v___y_4656_;
v___y_4602_ = v___y_4657_;
v___y_4603_ = v___y_4658_;
v___y_4604_ = v___x_4679_;
v_a_4605_ = v_a_4691_;
goto v___jp_4598_;
}
else
{
lean_object* v_a_4692_; 
v_a_4692_ = lean_ctor_get(v___x_4690_, 0);
lean_inc(v_a_4692_);
lean_dec_ref_known(v___x_4690_, 1);
v___y_4608_ = v_a_4660_;
v___y_4609_ = v___y_4655_;
v___y_4610_ = v___y_4656_;
v___y_4611_ = v___y_4657_;
v___y_4612_ = v___y_4658_;
v___y_4613_ = v___x_4679_;
v_a_4614_ = v_a_4692_;
goto v___jp_4607_;
}
}
else
{
lean_object* v___x_4693_; 
lean_dec(v_a_4681_);
v___x_4693_ = lean_box(0);
v___y_4599_ = v_a_4660_;
v___y_4600_ = v___y_4655_;
v___y_4601_ = v___y_4656_;
v___y_4602_ = v___y_4657_;
v___y_4603_ = v___y_4658_;
v___y_4604_ = v___x_4679_;
v_a_4605_ = v___x_4693_;
goto v___jp_4598_;
}
}
else
{
lean_object* v_a_4694_; 
v_a_4694_ = lean_ctor_get(v___x_4680_, 0);
lean_inc(v_a_4694_);
lean_dec_ref_known(v___x_4680_, 1);
v___y_4608_ = v_a_4660_;
v___y_4609_ = v___y_4655_;
v___y_4610_ = v___y_4656_;
v___y_4611_ = v___y_4657_;
v___y_4612_ = v___y_4658_;
v___y_4613_ = v___x_4679_;
v_a_4614_ = v_a_4694_;
goto v___jp_4607_;
}
}
}
v___jp_4695_:
{
if (v___y_4696_ == 0)
{
lean_dec_ref(v___f_4579_);
lean_dec(v_a_4569_);
lean_dec(v_declName_4561_);
goto v___jp_4573_;
}
else
{
uint8_t v___x_4697_; 
v___x_4697_ = lean_unbox(v_a_4569_);
lean_dec(v_a_4569_);
if (v___x_4697_ == 0)
{
lean_object* v_toCold_4698_; lean_object* v_options_4699_; uint8_t v_hasTrace_4700_; 
lean_del_object(v___x_4571_);
v_toCold_4698_ = lean_ctor_get(v_a_4564_, 0);
v_options_4699_ = lean_ctor_get(v_toCold_4698_, 2);
v_hasTrace_4700_ = lean_ctor_get_uint8(v_options_4699_, sizeof(void*)*1);
if (v_hasTrace_4700_ == 0)
{
lean_object* v___x_4701_; 
lean_dec_ref(v___f_4579_);
v___x_4701_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4561_, v_a_4562_, v_a_4563_, v_a_4564_, v_a_4565_);
if (lean_obj_tag(v___x_4701_) == 0)
{
lean_object* v_a_4702_; lean_object* v___x_4704_; uint8_t v_isShared_4705_; uint8_t v_isSharedCheck_4719_; 
v_a_4702_ = lean_ctor_get(v___x_4701_, 0);
v_isSharedCheck_4719_ = !lean_is_exclusive(v___x_4701_);
if (v_isSharedCheck_4719_ == 0)
{
v___x_4704_ = v___x_4701_;
v_isShared_4705_ = v_isSharedCheck_4719_;
goto v_resetjp_4703_;
}
else
{
lean_inc(v_a_4702_);
lean_dec(v___x_4701_);
v___x_4704_ = lean_box(0);
v_isShared_4705_ = v_isSharedCheck_4719_;
goto v_resetjp_4703_;
}
v_resetjp_4703_:
{
uint8_t v_isUnsafe_4706_; 
v_isUnsafe_4706_ = lean_ctor_get_uint8(v_a_4702_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4706_ == 0)
{
lean_object* v_ctors_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___f_4713_; lean_object* v___x_4714_; 
lean_del_object(v___x_4704_);
v_ctors_4707_ = lean_ctor_get(v_a_4702_, 4);
lean_inc(v_ctors_4707_);
lean_dec(v_a_4702_);
v___x_4708_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4709_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4710_ = lean_box(0);
v___x_4711_ = lean_box(v___y_4696_);
v___x_4712_ = lean_box(v_isUnsafe_4706_);
v___f_4713_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed), 9, 4);
lean_closure_set(v___f_4713_, 0, v___x_4711_);
lean_closure_set(v___f_4713_, 1, v___x_4712_);
lean_closure_set(v___f_4713_, 2, v_ctors_4707_);
lean_closure_set(v___f_4713_, 3, v___x_4710_);
v___x_4714_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4708_, v___x_4709_, v___f_4713_, v_a_4562_, v_a_4563_, v_a_4564_, v_a_4565_);
return v___x_4714_;
}
else
{
lean_object* v___x_4715_; lean_object* v___x_4717_; 
lean_dec(v_a_4702_);
v___x_4715_ = lean_box(0);
if (v_isShared_4705_ == 0)
{
lean_ctor_set(v___x_4704_, 0, v___x_4715_);
v___x_4717_ = v___x_4704_;
goto v_reusejp_4716_;
}
else
{
lean_object* v_reuseFailAlloc_4718_; 
v_reuseFailAlloc_4718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4718_, 0, v___x_4715_);
v___x_4717_ = v_reuseFailAlloc_4718_;
goto v_reusejp_4716_;
}
v_reusejp_4716_:
{
return v___x_4717_;
}
}
}
}
else
{
lean_object* v_a_4720_; lean_object* v___x_4722_; uint8_t v_isShared_4723_; uint8_t v_isSharedCheck_4727_; 
v_a_4720_ = lean_ctor_get(v___x_4701_, 0);
v_isSharedCheck_4727_ = !lean_is_exclusive(v___x_4701_);
if (v_isSharedCheck_4727_ == 0)
{
v___x_4722_ = v___x_4701_;
v_isShared_4723_ = v_isSharedCheck_4727_;
goto v_resetjp_4721_;
}
else
{
lean_inc(v_a_4720_);
lean_dec(v___x_4701_);
v___x_4722_ = lean_box(0);
v_isShared_4723_ = v_isSharedCheck_4727_;
goto v_resetjp_4721_;
}
v_resetjp_4721_:
{
lean_object* v___x_4725_; 
if (v_isShared_4723_ == 0)
{
v___x_4725_ = v___x_4722_;
goto v_reusejp_4724_;
}
else
{
lean_object* v_reuseFailAlloc_4726_; 
v_reuseFailAlloc_4726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4726_, 0, v_a_4720_);
v___x_4725_ = v_reuseFailAlloc_4726_;
goto v_reusejp_4724_;
}
v_reusejp_4724_:
{
return v___x_4725_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; uint8_t v___x_4732_; 
v_inheritedTraceOptions_4728_ = lean_ctor_get(v_toCold_4698_, 11);
v___x_4729_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_4730_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_4731_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_4732_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4728_, v_options_4699_, v___x_4731_);
if (v___x_4732_ == 0)
{
lean_object* v___x_4733_; uint8_t v___x_4734_; 
v___x_4733_ = l_Lean_trace_profiler;
v___x_4734_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_4699_, v___x_4733_);
if (v___x_4734_ == 0)
{
lean_object* v___x_4735_; 
lean_dec_ref(v___f_4579_);
v___x_4735_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4561_, v_a_4562_, v_a_4563_, v_a_4564_, v_a_4565_);
if (lean_obj_tag(v___x_4735_) == 0)
{
lean_object* v_a_4736_; lean_object* v___x_4738_; uint8_t v_isShared_4739_; uint8_t v_isSharedCheck_4753_; 
v_a_4736_ = lean_ctor_get(v___x_4735_, 0);
v_isSharedCheck_4753_ = !lean_is_exclusive(v___x_4735_);
if (v_isSharedCheck_4753_ == 0)
{
v___x_4738_ = v___x_4735_;
v_isShared_4739_ = v_isSharedCheck_4753_;
goto v_resetjp_4737_;
}
else
{
lean_inc(v_a_4736_);
lean_dec(v___x_4735_);
v___x_4738_ = lean_box(0);
v_isShared_4739_ = v_isSharedCheck_4753_;
goto v_resetjp_4737_;
}
v_resetjp_4737_:
{
uint8_t v_isUnsafe_4740_; 
v_isUnsafe_4740_ = lean_ctor_get_uint8(v_a_4736_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4740_ == 0)
{
lean_object* v_ctors_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; lean_object* v___x_4745_; lean_object* v___x_4746_; lean_object* v___f_4747_; lean_object* v___x_4748_; 
lean_del_object(v___x_4738_);
v_ctors_4741_ = lean_ctor_get(v_a_4736_, 4);
lean_inc(v_ctors_4741_);
lean_dec(v_a_4736_);
v___x_4742_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4743_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4744_ = lean_box(0);
v___x_4745_ = lean_box(v___y_4696_);
v___x_4746_ = lean_box(v_isUnsafe_4740_);
v___f_4747_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed), 9, 4);
lean_closure_set(v___f_4747_, 0, v___x_4745_);
lean_closure_set(v___f_4747_, 1, v___x_4746_);
lean_closure_set(v___f_4747_, 2, v_ctors_4741_);
lean_closure_set(v___f_4747_, 3, v___x_4744_);
v___x_4748_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4742_, v___x_4743_, v___f_4747_, v_a_4562_, v_a_4563_, v_a_4564_, v_a_4565_);
return v___x_4748_;
}
else
{
lean_object* v___x_4749_; lean_object* v___x_4751_; 
lean_dec(v_a_4736_);
v___x_4749_ = lean_box(0);
if (v_isShared_4739_ == 0)
{
lean_ctor_set(v___x_4738_, 0, v___x_4749_);
v___x_4751_ = v___x_4738_;
goto v_reusejp_4750_;
}
else
{
lean_object* v_reuseFailAlloc_4752_; 
v_reuseFailAlloc_4752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4752_, 0, v___x_4749_);
v___x_4751_ = v_reuseFailAlloc_4752_;
goto v_reusejp_4750_;
}
v_reusejp_4750_:
{
return v___x_4751_;
}
}
}
}
else
{
lean_object* v_a_4754_; lean_object* v___x_4756_; uint8_t v_isShared_4757_; uint8_t v_isSharedCheck_4761_; 
v_a_4754_ = lean_ctor_get(v___x_4735_, 0);
v_isSharedCheck_4761_ = !lean_is_exclusive(v___x_4735_);
if (v_isSharedCheck_4761_ == 0)
{
v___x_4756_ = v___x_4735_;
v_isShared_4757_ = v_isSharedCheck_4761_;
goto v_resetjp_4755_;
}
else
{
lean_inc(v_a_4754_);
lean_dec(v___x_4735_);
v___x_4756_ = lean_box(0);
v_isShared_4757_ = v_isSharedCheck_4761_;
goto v_resetjp_4755_;
}
v_resetjp_4755_:
{
lean_object* v___x_4759_; 
if (v_isShared_4757_ == 0)
{
v___x_4759_ = v___x_4756_;
goto v_reusejp_4758_;
}
else
{
lean_object* v_reuseFailAlloc_4760_; 
v_reuseFailAlloc_4760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4760_, 0, v_a_4754_);
v___x_4759_ = v_reuseFailAlloc_4760_;
goto v_reusejp_4758_;
}
v_reusejp_4758_:
{
return v___x_4759_;
}
}
}
}
else
{
v___y_4654_ = v___y_4696_;
v___y_4655_ = v_options_4699_;
v___y_4656_ = v___x_4729_;
v___y_4657_ = v___x_4730_;
v___y_4658_ = v___x_4732_;
goto v___jp_4653_;
}
}
else
{
v___y_4654_ = v___y_4696_;
v___y_4655_ = v_options_4699_;
v___y_4656_ = v___x_4729_;
v___y_4657_ = v___x_4730_;
v___y_4658_ = v___x_4732_;
goto v___jp_4653_;
}
}
}
else
{
lean_dec_ref(v___f_4579_);
lean_dec(v_declName_4561_);
goto v___jp_4573_;
}
}
}
}
}
else
{
lean_object* v_a_4768_; lean_object* v___x_4770_; uint8_t v_isShared_4771_; uint8_t v_isSharedCheck_4775_; 
lean_dec(v___x_4567_);
lean_dec(v_declName_4561_);
v_a_4768_ = lean_ctor_get(v___x_4568_, 0);
v_isSharedCheck_4775_ = !lean_is_exclusive(v___x_4568_);
if (v_isSharedCheck_4775_ == 0)
{
v___x_4770_ = v___x_4568_;
v_isShared_4771_ = v_isSharedCheck_4775_;
goto v_resetjp_4769_;
}
else
{
lean_inc(v_a_4768_);
lean_dec(v___x_4568_);
v___x_4770_ = lean_box(0);
v_isShared_4771_ = v_isSharedCheck_4775_;
goto v_resetjp_4769_;
}
v_resetjp_4769_:
{
lean_object* v___x_4773_; 
if (v_isShared_4771_ == 0)
{
v___x_4773_ = v___x_4770_;
goto v_reusejp_4772_;
}
else
{
lean_object* v_reuseFailAlloc_4774_; 
v_reuseFailAlloc_4774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4774_, 0, v_a_4768_);
v___x_4773_ = v_reuseFailAlloc_4774_;
goto v_reusejp_4772_;
}
v_reusejp_4772_:
{
return v___x_4773_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___boxed(lean_object* v_declName_4776_, lean_object* v_a_4777_, lean_object* v_a_4778_, lean_object* v_a_4779_, lean_object* v_a_4780_, lean_object* v_a_4781_){
_start:
{
lean_object* v_res_4782_; 
v_res_4782_ = l_Lean_Meta_mkInjectiveTheorems(v_declName_4776_, v_a_4777_, v_a_4778_, v_a_4779_, v_a_4780_);
lean_dec(v_a_4780_);
lean_dec_ref(v_a_4779_);
lean_dec(v_a_4778_);
lean_dec_ref(v_a_4777_);
return v_res_4782_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3(uint8_t v___y_4783_, uint8_t v___x_4784_, lean_object* v_as_4785_, lean_object* v_as_x27_4786_, lean_object* v_b_4787_, lean_object* v_a_4788_, lean_object* v___y_4789_, lean_object* v___y_4790_, lean_object* v___y_4791_, lean_object* v___y_4792_){
_start:
{
lean_object* v___x_4794_; 
v___x_4794_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___y_4783_, v___x_4784_, v_as_x27_4786_, v_b_4787_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_);
return v___x_4794_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___boxed(lean_object* v___y_4795_, lean_object* v___x_4796_, lean_object* v_as_4797_, lean_object* v_as_x27_4798_, lean_object* v_b_4799_, lean_object* v_a_4800_, lean_object* v___y_4801_, lean_object* v___y_4802_, lean_object* v___y_4803_, lean_object* v___y_4804_, lean_object* v___y_4805_){
_start:
{
uint8_t v___y_17444__boxed_4806_; uint8_t v___x_17445__boxed_4807_; lean_object* v_res_4808_; 
v___y_17444__boxed_4806_ = lean_unbox(v___y_4795_);
v___x_17445__boxed_4807_ = lean_unbox(v___x_4796_);
v_res_4808_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3(v___y_17444__boxed_4806_, v___x_17445__boxed_4807_, v_as_4797_, v_as_x27_4798_, v_b_4799_, v_a_4800_, v___y_4801_, v___y_4802_, v___y_4803_, v___y_4804_);
lean_dec(v___y_4804_);
lean_dec_ref(v___y_4803_);
lean_dec(v___y_4802_);
lean_dec_ref(v___y_4801_);
lean_dec(v_as_x27_4798_);
lean_dec(v_as_4797_);
return v_res_4808_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4849_; lean_object* v___x_4850_; lean_object* v___x_4851_; 
v___x_4849_ = lean_unsigned_to_nat(4172903888u);
v___x_4850_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_));
v___x_4851_ = l_Lean_Name_num___override(v___x_4850_, v___x_4849_);
return v___x_4851_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; 
v___x_4853_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_));
v___x_4854_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4855_ = l_Lean_Name_str___override(v___x_4854_, v___x_4853_);
return v___x_4855_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4857_; lean_object* v___x_4858_; lean_object* v___x_4859_; 
v___x_4857_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_));
v___x_4858_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4859_ = l_Lean_Name_str___override(v___x_4858_, v___x_4857_);
return v___x_4859_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; 
v___x_4860_ = lean_unsigned_to_nat(2u);
v___x_4861_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4862_ = l_Lean_Name_num___override(v___x_4861_, v___x_4860_);
return v___x_4862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4864_; uint8_t v___x_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; 
v___x_4864_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_4865_ = 0;
v___x_4866_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4867_ = l_Lean_registerTraceClass(v___x_4864_, v___x_4865_, v___x_4866_);
return v___x_4867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2____boxed(lean_object* v_a_4868_){
_start:
{
lean_object* v_res_4869_; 
v_res_4869_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_();
return v_res_4869_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(lean_object* v_a_4870_, lean_object* v_b_4871_){
_start:
{
lean_object* v_array_4872_; lean_object* v_start_4873_; lean_object* v_stop_4874_; lean_object* v___x_4876_; uint8_t v_isShared_4877_; uint8_t v_isSharedCheck_4887_; 
v_array_4872_ = lean_ctor_get(v_a_4870_, 0);
v_start_4873_ = lean_ctor_get(v_a_4870_, 1);
v_stop_4874_ = lean_ctor_get(v_a_4870_, 2);
v_isSharedCheck_4887_ = !lean_is_exclusive(v_a_4870_);
if (v_isSharedCheck_4887_ == 0)
{
v___x_4876_ = v_a_4870_;
v_isShared_4877_ = v_isSharedCheck_4887_;
goto v_resetjp_4875_;
}
else
{
lean_inc(v_stop_4874_);
lean_inc(v_start_4873_);
lean_inc(v_array_4872_);
lean_dec(v_a_4870_);
v___x_4876_ = lean_box(0);
v_isShared_4877_ = v_isSharedCheck_4887_;
goto v_resetjp_4875_;
}
v_resetjp_4875_:
{
uint8_t v___x_4878_; 
v___x_4878_ = lean_nat_dec_lt(v_start_4873_, v_stop_4874_);
if (v___x_4878_ == 0)
{
lean_del_object(v___x_4876_);
lean_dec(v_stop_4874_);
lean_dec(v_start_4873_);
lean_dec_ref(v_array_4872_);
return v_b_4871_;
}
else
{
lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4882_; 
v___x_4879_ = lean_unsigned_to_nat(1u);
v___x_4880_ = lean_nat_add(v_start_4873_, v___x_4879_);
lean_inc_ref(v_array_4872_);
if (v_isShared_4877_ == 0)
{
lean_ctor_set(v___x_4876_, 1, v___x_4880_);
v___x_4882_ = v___x_4876_;
goto v_reusejp_4881_;
}
else
{
lean_object* v_reuseFailAlloc_4886_; 
v_reuseFailAlloc_4886_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4886_, 0, v_array_4872_);
lean_ctor_set(v_reuseFailAlloc_4886_, 1, v___x_4880_);
lean_ctor_set(v_reuseFailAlloc_4886_, 2, v_stop_4874_);
v___x_4882_ = v_reuseFailAlloc_4886_;
goto v_reusejp_4881_;
}
v_reusejp_4881_:
{
lean_object* v___x_4883_; lean_object* v___x_4884_; 
v___x_4883_ = lean_array_fget(v_array_4872_, v_start_4873_);
lean_dec(v_start_4873_);
lean_dec_ref(v_array_4872_);
v___x_4884_ = lean_array_push(v_b_4871_, v___x_4883_);
v_a_4870_ = v___x_4882_;
v_b_4871_ = v___x_4884_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_4888_; 
v___x_4888_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4888_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_4889_; lean_object* v___x_4890_; 
v___x_4889_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_4890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4890_, 0, v___x_4889_);
return v___x_4890_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_4891_; lean_object* v___x_4892_; lean_object* v___x_4893_; 
v___x_4891_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_4892_ = lean_unsigned_to_nat(0u);
v___x_4893_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_4893_, 0, v___x_4892_);
lean_ctor_set(v___x_4893_, 1, v___x_4892_);
lean_ctor_set(v___x_4893_, 2, v___x_4892_);
lean_ctor_set(v___x_4893_, 3, v___x_4892_);
lean_ctor_set(v___x_4893_, 4, v___x_4891_);
lean_ctor_set(v___x_4893_, 5, v___x_4891_);
lean_ctor_set(v___x_4893_, 6, v___x_4891_);
lean_ctor_set(v___x_4893_, 7, v___x_4891_);
lean_ctor_set(v___x_4893_, 8, v___x_4891_);
lean_ctor_set(v___x_4893_, 9, v___x_4891_);
lean_ctor_set(v___x_4893_, 10, v___x_4891_);
return v___x_4893_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_4894_; lean_object* v___x_4895_; lean_object* v___x_4896_; lean_object* v___x_4897_; 
v___x_4894_ = lean_box(1);
v___x_4895_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_4896_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_4897_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4897_, 0, v___x_4896_);
lean_ctor_set(v___x_4897_, 1, v___x_4895_);
lean_ctor_set(v___x_4897_, 2, v___x_4894_);
return v___x_4897_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_4899_; lean_object* v___x_4900_; 
v___x_4899_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4));
v___x_4900_ = l_Lean_stringToMessageData(v___x_4899_);
return v___x_4900_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_4902_; lean_object* v___x_4903_; 
v___x_4902_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_4903_ = l_Lean_stringToMessageData(v___x_4902_);
return v___x_4903_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_4905_; lean_object* v___x_4906_; 
v___x_4905_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_4906_ = l_Lean_stringToMessageData(v___x_4905_);
return v___x_4906_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_4908_; lean_object* v___x_4909_; 
v___x_4908_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_4909_ = l_Lean_stringToMessageData(v___x_4908_);
return v___x_4909_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_4911_; lean_object* v___x_4912_; 
v___x_4911_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_4912_ = l_Lean_stringToMessageData(v___x_4911_);
return v___x_4912_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15(void){
_start:
{
lean_object* v___x_4914_; lean_object* v___x_4915_; 
v___x_4914_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14));
v___x_4915_ = l_Lean_stringToMessageData(v___x_4914_);
return v___x_4915_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17(void){
_start:
{
lean_object* v___x_4917_; lean_object* v___x_4918_; 
v___x_4917_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16));
v___x_4918_ = l_Lean_stringToMessageData(v___x_4917_);
return v___x_4918_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_4919_, lean_object* v_declHint_4920_, lean_object* v___y_4921_){
_start:
{
lean_object* v___x_4923_; lean_object* v_env_4924_; uint8_t v___x_4925_; 
v___x_4923_ = lean_st_ref_get(v___y_4921_);
v_env_4924_ = lean_ctor_get(v___x_4923_, 0);
lean_inc_ref(v_env_4924_);
lean_dec(v___x_4923_);
v___x_4925_ = l_Lean_Name_isAnonymous(v_declHint_4920_);
if (v___x_4925_ == 0)
{
uint8_t v_isExporting_4926_; 
v_isExporting_4926_ = lean_ctor_get_uint8(v_env_4924_, sizeof(void*)*8);
if (v_isExporting_4926_ == 0)
{
lean_object* v___x_4927_; 
lean_dec_ref(v_env_4924_);
lean_dec(v_declHint_4920_);
v___x_4927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4927_, 0, v_msg_4919_);
return v___x_4927_;
}
else
{
lean_object* v___x_4928_; uint8_t v___x_4929_; 
lean_inc_ref(v_env_4924_);
v___x_4928_ = l_Lean_Environment_setExporting(v_env_4924_, v___x_4925_);
lean_inc(v_declHint_4920_);
lean_inc_ref(v___x_4928_);
v___x_4929_ = l_Lean_Environment_contains(v___x_4928_, v_declHint_4920_, v_isExporting_4926_);
if (v___x_4929_ == 0)
{
lean_object* v___x_4930_; 
lean_dec_ref(v___x_4928_);
lean_dec_ref(v_env_4924_);
lean_dec(v_declHint_4920_);
v___x_4930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4930_, 0, v_msg_4919_);
return v___x_4930_;
}
else
{
lean_object* v___x_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v_c_4936_; lean_object* v___x_4937_; 
v___x_4931_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_4932_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_4933_ = l_Lean_Options_empty;
v___x_4934_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4934_, 0, v___x_4928_);
lean_ctor_set(v___x_4934_, 1, v___x_4931_);
lean_ctor_set(v___x_4934_, 2, v___x_4932_);
lean_ctor_set(v___x_4934_, 3, v___x_4933_);
lean_inc(v_declHint_4920_);
v___x_4935_ = l_Lean_MessageData_ofConstName(v_declHint_4920_, v___x_4925_);
v_c_4936_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_4936_, 0, v___x_4934_);
lean_ctor_set(v_c_4936_, 1, v___x_4935_);
v___x_4937_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4924_, v_declHint_4920_);
if (lean_obj_tag(v___x_4937_) == 0)
{
lean_object* v___x_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; 
lean_dec_ref(v_env_4924_);
lean_dec(v_declHint_4920_);
v___x_4938_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_4939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4939_, 0, v___x_4938_);
lean_ctor_set(v___x_4939_, 1, v_c_4936_);
v___x_4940_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_4941_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4941_, 0, v___x_4939_);
lean_ctor_set(v___x_4941_, 1, v___x_4940_);
v___x_4942_ = l_Lean_MessageData_note(v___x_4941_);
v___x_4943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4943_, 0, v_msg_4919_);
lean_ctor_set(v___x_4943_, 1, v___x_4942_);
v___x_4944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4944_, 0, v___x_4943_);
return v___x_4944_;
}
else
{
lean_object* v_val_4945_; lean_object* v___x_4947_; uint8_t v_isShared_4948_; uint8_t v_isSharedCheck_4980_; 
v_val_4945_ = lean_ctor_get(v___x_4937_, 0);
v_isSharedCheck_4980_ = !lean_is_exclusive(v___x_4937_);
if (v_isSharedCheck_4980_ == 0)
{
v___x_4947_ = v___x_4937_;
v_isShared_4948_ = v_isSharedCheck_4980_;
goto v_resetjp_4946_;
}
else
{
lean_inc(v_val_4945_);
lean_dec(v___x_4937_);
v___x_4947_ = lean_box(0);
v_isShared_4948_ = v_isSharedCheck_4980_;
goto v_resetjp_4946_;
}
v_resetjp_4946_:
{
lean_object* v___x_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v_mod_4952_; uint8_t v___x_4953_; 
v___x_4949_ = lean_box(0);
v___x_4950_ = l_Lean_Environment_header(v_env_4924_);
lean_dec_ref(v_env_4924_);
v___x_4951_ = l_Lean_EnvironmentHeader_moduleNames(v___x_4950_);
v_mod_4952_ = lean_array_get(v___x_4949_, v___x_4951_, v_val_4945_);
lean_dec(v_val_4945_);
lean_dec_ref(v___x_4951_);
v___x_4953_ = l_Lean_isPrivateName(v_declHint_4920_);
lean_dec(v_declHint_4920_);
if (v___x_4953_ == 0)
{
lean_object* v___x_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; lean_object* v___x_4963_; lean_object* v___x_4965_; 
v___x_4954_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_4955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4955_, 0, v___x_4954_);
lean_ctor_set(v___x_4955_, 1, v_c_4936_);
v___x_4956_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_4957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4957_, 0, v___x_4955_);
lean_ctor_set(v___x_4957_, 1, v___x_4956_);
v___x_4958_ = l_Lean_MessageData_ofName(v_mod_4952_);
v___x_4959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4959_, 0, v___x_4957_);
lean_ctor_set(v___x_4959_, 1, v___x_4958_);
v___x_4960_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_4961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4961_, 0, v___x_4959_);
lean_ctor_set(v___x_4961_, 1, v___x_4960_);
v___x_4962_ = l_Lean_MessageData_note(v___x_4961_);
v___x_4963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4963_, 0, v_msg_4919_);
lean_ctor_set(v___x_4963_, 1, v___x_4962_);
if (v_isShared_4948_ == 0)
{
lean_ctor_set_tag(v___x_4947_, 0);
lean_ctor_set(v___x_4947_, 0, v___x_4963_);
v___x_4965_ = v___x_4947_;
goto v_reusejp_4964_;
}
else
{
lean_object* v_reuseFailAlloc_4966_; 
v_reuseFailAlloc_4966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4966_, 0, v___x_4963_);
v___x_4965_ = v_reuseFailAlloc_4966_;
goto v_reusejp_4964_;
}
v_reusejp_4964_:
{
return v___x_4965_;
}
}
else
{
lean_object* v___x_4967_; lean_object* v___x_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; lean_object* v___x_4976_; lean_object* v___x_4978_; 
v___x_4967_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_4968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4968_, 0, v___x_4967_);
lean_ctor_set(v___x_4968_, 1, v_c_4936_);
v___x_4969_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_4970_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4970_, 0, v___x_4968_);
lean_ctor_set(v___x_4970_, 1, v___x_4969_);
v___x_4971_ = l_Lean_MessageData_ofName(v_mod_4952_);
v___x_4972_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4972_, 0, v___x_4970_);
lean_ctor_set(v___x_4972_, 1, v___x_4971_);
v___x_4973_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_4974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4974_, 0, v___x_4972_);
lean_ctor_set(v___x_4974_, 1, v___x_4973_);
v___x_4975_ = l_Lean_MessageData_note(v___x_4974_);
v___x_4976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4976_, 0, v_msg_4919_);
lean_ctor_set(v___x_4976_, 1, v___x_4975_);
if (v_isShared_4948_ == 0)
{
lean_ctor_set_tag(v___x_4947_, 0);
lean_ctor_set(v___x_4947_, 0, v___x_4976_);
v___x_4978_ = v___x_4947_;
goto v_reusejp_4977_;
}
else
{
lean_object* v_reuseFailAlloc_4979_; 
v_reuseFailAlloc_4979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4979_, 0, v___x_4976_);
v___x_4978_ = v_reuseFailAlloc_4979_;
goto v_reusejp_4977_;
}
v_reusejp_4977_:
{
return v___x_4978_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4981_; 
lean_dec_ref(v_env_4924_);
lean_dec(v_declHint_4920_);
v___x_4981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4981_, 0, v_msg_4919_);
return v___x_4981_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_4982_, lean_object* v_declHint_4983_, lean_object* v___y_4984_, lean_object* v___y_4985_){
_start:
{
lean_object* v_res_4986_; 
v_res_4986_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_4982_, v_declHint_4983_, v___y_4984_);
lean_dec(v___y_4984_);
return v_res_4986_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_msg_4987_, lean_object* v_declHint_4988_, lean_object* v___y_4989_, lean_object* v___y_4990_, lean_object* v___y_4991_, lean_object* v___y_4992_){
_start:
{
lean_object* v___x_4994_; lean_object* v_a_4995_; lean_object* v___x_4997_; uint8_t v_isShared_4998_; uint8_t v_isSharedCheck_5004_; 
v___x_4994_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_4987_, v_declHint_4988_, v___y_4992_);
v_a_4995_ = lean_ctor_get(v___x_4994_, 0);
v_isSharedCheck_5004_ = !lean_is_exclusive(v___x_4994_);
if (v_isSharedCheck_5004_ == 0)
{
v___x_4997_ = v___x_4994_;
v_isShared_4998_ = v_isSharedCheck_5004_;
goto v_resetjp_4996_;
}
else
{
lean_inc(v_a_4995_);
lean_dec(v___x_4994_);
v___x_4997_ = lean_box(0);
v_isShared_4998_ = v_isSharedCheck_5004_;
goto v_resetjp_4996_;
}
v_resetjp_4996_:
{
lean_object* v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5002_; 
v___x_4999_ = l_Lean_unknownIdentifierMessageTag;
v___x_5000_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_5000_, 0, v___x_4999_);
lean_ctor_set(v___x_5000_, 1, v_a_4995_);
if (v_isShared_4998_ == 0)
{
lean_ctor_set(v___x_4997_, 0, v___x_5000_);
v___x_5002_ = v___x_4997_;
goto v_reusejp_5001_;
}
else
{
lean_object* v_reuseFailAlloc_5003_; 
v_reuseFailAlloc_5003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5003_, 0, v___x_5000_);
v___x_5002_ = v_reuseFailAlloc_5003_;
goto v_reusejp_5001_;
}
v_reusejp_5001_:
{
return v___x_5002_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v_msg_5005_, lean_object* v_declHint_5006_, lean_object* v___y_5007_, lean_object* v___y_5008_, lean_object* v___y_5009_, lean_object* v___y_5010_, lean_object* v___y_5011_){
_start:
{
lean_object* v_res_5012_; 
v_res_5012_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_5005_, v_declHint_5006_, v___y_5007_, v___y_5008_, v___y_5009_, v___y_5010_);
lean_dec(v___y_5010_);
lean_dec_ref(v___y_5009_);
lean_dec(v___y_5008_);
lean_dec_ref(v___y_5007_);
return v_res_5012_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_5013_, lean_object* v_msg_5014_, lean_object* v___y_5015_, lean_object* v___y_5016_, lean_object* v___y_5017_, lean_object* v___y_5018_){
_start:
{
lean_object* v_toCold_5020_; lean_object* v_currRecDepth_5021_; lean_object* v_ref_5022_; uint8_t v_diag_5023_; uint8_t v_suppressElabErrors_5024_; lean_object* v_ref_5025_; lean_object* v___x_5026_; lean_object* v___x_5027_; 
v_toCold_5020_ = lean_ctor_get(v___y_5017_, 0);
v_currRecDepth_5021_ = lean_ctor_get(v___y_5017_, 1);
v_ref_5022_ = lean_ctor_get(v___y_5017_, 2);
v_diag_5023_ = lean_ctor_get_uint8(v___y_5017_, sizeof(void*)*3);
v_suppressElabErrors_5024_ = lean_ctor_get_uint8(v___y_5017_, sizeof(void*)*3 + 1);
v_ref_5025_ = l_Lean_replaceRef(v_ref_5013_, v_ref_5022_);
lean_inc(v_currRecDepth_5021_);
lean_inc_ref(v_toCold_5020_);
v___x_5026_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5026_, 0, v_toCold_5020_);
lean_ctor_set(v___x_5026_, 1, v_currRecDepth_5021_);
lean_ctor_set(v___x_5026_, 2, v_ref_5025_);
lean_ctor_set_uint8(v___x_5026_, sizeof(void*)*3, v_diag_5023_);
lean_ctor_set_uint8(v___x_5026_, sizeof(void*)*3 + 1, v_suppressElabErrors_5024_);
v___x_5027_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v_msg_5014_, v___y_5015_, v___y_5016_, v___x_5026_, v___y_5018_);
lean_dec_ref_known(v___x_5026_, 3);
return v___x_5027_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_5028_, lean_object* v_msg_5029_, lean_object* v___y_5030_, lean_object* v___y_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_, lean_object* v___y_5034_){
_start:
{
lean_object* v_res_5035_; 
v_res_5035_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5028_, v_msg_5029_, v___y_5030_, v___y_5031_, v___y_5032_, v___y_5033_);
lean_dec(v___y_5033_);
lean_dec_ref(v___y_5032_);
lean_dec(v___y_5031_);
lean_dec_ref(v___y_5030_);
lean_dec(v_ref_5028_);
return v_res_5035_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_5036_, lean_object* v_msg_5037_, lean_object* v_declHint_5038_, lean_object* v___y_5039_, lean_object* v___y_5040_, lean_object* v___y_5041_, lean_object* v___y_5042_){
_start:
{
lean_object* v___x_5044_; lean_object* v_a_5045_; lean_object* v___x_5046_; 
v___x_5044_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_5037_, v_declHint_5038_, v___y_5039_, v___y_5040_, v___y_5041_, v___y_5042_);
v_a_5045_ = lean_ctor_get(v___x_5044_, 0);
lean_inc(v_a_5045_);
lean_dec_ref(v___x_5044_);
v___x_5046_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5036_, v_a_5045_, v___y_5039_, v___y_5040_, v___y_5041_, v___y_5042_);
return v___x_5046_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_5047_, lean_object* v_msg_5048_, lean_object* v_declHint_5049_, lean_object* v___y_5050_, lean_object* v___y_5051_, lean_object* v___y_5052_, lean_object* v___y_5053_, lean_object* v___y_5054_){
_start:
{
lean_object* v_res_5055_; 
v_res_5055_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5047_, v_msg_5048_, v_declHint_5049_, v___y_5050_, v___y_5051_, v___y_5052_, v___y_5053_);
lean_dec(v___y_5053_);
lean_dec_ref(v___y_5052_);
lean_dec(v___y_5051_);
lean_dec_ref(v___y_5050_);
lean_dec(v_ref_5047_);
return v_res_5055_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_5057_; lean_object* v___x_5058_; 
v___x_5057_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_5058_ = l_Lean_stringToMessageData(v___x_5057_);
return v___x_5058_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_5059_, lean_object* v_constName_5060_, lean_object* v___y_5061_, lean_object* v___y_5062_, lean_object* v___y_5063_, lean_object* v___y_5064_){
_start:
{
lean_object* v___x_5066_; uint8_t v___x_5067_; lean_object* v___x_5068_; lean_object* v___x_5069_; lean_object* v___x_5070_; lean_object* v___x_5071_; lean_object* v___x_5072_; 
v___x_5066_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_5067_ = 0;
lean_inc(v_constName_5060_);
v___x_5068_ = l_Lean_MessageData_ofConstName(v_constName_5060_, v___x_5067_);
v___x_5069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5069_, 0, v___x_5066_);
lean_ctor_set(v___x_5069_, 1, v___x_5068_);
v___x_5070_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_5071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5071_, 0, v___x_5069_);
lean_ctor_set(v___x_5071_, 1, v___x_5070_);
v___x_5072_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5059_, v___x_5071_, v_constName_5060_, v___y_5061_, v___y_5062_, v___y_5063_, v___y_5064_);
return v___x_5072_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_5073_, lean_object* v_constName_5074_, lean_object* v___y_5075_, lean_object* v___y_5076_, lean_object* v___y_5077_, lean_object* v___y_5078_, lean_object* v___y_5079_){
_start:
{
lean_object* v_res_5080_; 
v_res_5080_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(v_ref_5073_, v_constName_5074_, v___y_5075_, v___y_5076_, v___y_5077_, v___y_5078_);
lean_dec(v___y_5078_);
lean_dec_ref(v___y_5077_);
lean_dec(v___y_5076_);
lean_dec_ref(v___y_5075_);
lean_dec(v_ref_5073_);
return v_res_5080_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(lean_object* v_constName_5081_, lean_object* v___y_5082_, lean_object* v___y_5083_, lean_object* v___y_5084_, lean_object* v___y_5085_){
_start:
{
lean_object* v_ref_5087_; lean_object* v___x_5088_; 
v_ref_5087_ = lean_ctor_get(v___y_5084_, 2);
v___x_5088_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(v_ref_5087_, v_constName_5081_, v___y_5082_, v___y_5083_, v___y_5084_, v___y_5085_);
return v___x_5088_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_constName_5089_, lean_object* v___y_5090_, lean_object* v___y_5091_, lean_object* v___y_5092_, lean_object* v___y_5093_, lean_object* v___y_5094_){
_start:
{
lean_object* v_res_5095_; 
v_res_5095_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(v_constName_5089_, v___y_5090_, v___y_5091_, v___y_5092_, v___y_5093_);
lean_dec(v___y_5093_);
lean_dec_ref(v___y_5092_);
lean_dec(v___y_5091_);
lean_dec_ref(v___y_5090_);
return v_res_5095_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(lean_object* v_constName_5096_, lean_object* v___y_5097_, lean_object* v___y_5098_, lean_object* v___y_5099_, lean_object* v___y_5100_){
_start:
{
lean_object* v___x_5102_; lean_object* v_env_5103_; uint8_t v___x_5104_; lean_object* v___x_5105_; 
v___x_5102_ = lean_st_ref_get(v___y_5100_);
v_env_5103_ = lean_ctor_get(v___x_5102_, 0);
lean_inc_ref(v_env_5103_);
lean_dec(v___x_5102_);
v___x_5104_ = 0;
lean_inc(v_constName_5096_);
v___x_5105_ = l_Lean_Environment_find_x3f(v_env_5103_, v_constName_5096_, v___x_5104_);
if (lean_obj_tag(v___x_5105_) == 0)
{
lean_object* v___x_5106_; 
v___x_5106_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(v_constName_5096_, v___y_5097_, v___y_5098_, v___y_5099_, v___y_5100_);
return v___x_5106_;
}
else
{
lean_object* v_val_5107_; lean_object* v___x_5109_; uint8_t v_isShared_5110_; uint8_t v_isSharedCheck_5114_; 
lean_dec(v_constName_5096_);
v_val_5107_ = lean_ctor_get(v___x_5105_, 0);
v_isSharedCheck_5114_ = !lean_is_exclusive(v___x_5105_);
if (v_isSharedCheck_5114_ == 0)
{
v___x_5109_ = v___x_5105_;
v_isShared_5110_ = v_isSharedCheck_5114_;
goto v_resetjp_5108_;
}
else
{
lean_inc(v_val_5107_);
lean_dec(v___x_5105_);
v___x_5109_ = lean_box(0);
v_isShared_5110_ = v_isSharedCheck_5114_;
goto v_resetjp_5108_;
}
v_resetjp_5108_:
{
lean_object* v___x_5112_; 
if (v_isShared_5110_ == 0)
{
lean_ctor_set_tag(v___x_5109_, 0);
v___x_5112_ = v___x_5109_;
goto v_reusejp_5111_;
}
else
{
lean_object* v_reuseFailAlloc_5113_; 
v_reuseFailAlloc_5113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5113_, 0, v_val_5107_);
v___x_5112_ = v_reuseFailAlloc_5113_;
goto v_reusejp_5111_;
}
v_reusejp_5111_:
{
return v___x_5112_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0___boxed(lean_object* v_constName_5115_, lean_object* v___y_5116_, lean_object* v___y_5117_, lean_object* v___y_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_){
_start:
{
lean_object* v_res_5121_; 
v_res_5121_ = l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(v_constName_5115_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_);
lean_dec(v___y_5119_);
lean_dec_ref(v___y_5118_);
lean_dec(v___y_5117_);
lean_dec_ref(v___y_5116_);
return v_res_5121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(lean_object* v_x_5124_, lean_object* v_x_5125_, lean_object* v_x_5126_, lean_object* v___y_5127_, lean_object* v___y_5128_, lean_object* v___y_5129_, lean_object* v___y_5130_){
_start:
{
if (lean_obj_tag(v_x_5124_) == 5)
{
lean_object* v_fn_5132_; lean_object* v_arg_5133_; lean_object* v___x_5134_; lean_object* v___x_5135_; lean_object* v___x_5136_; 
v_fn_5132_ = lean_ctor_get(v_x_5124_, 0);
lean_inc_ref(v_fn_5132_);
v_arg_5133_ = lean_ctor_get(v_x_5124_, 1);
lean_inc_ref(v_arg_5133_);
lean_dec_ref_known(v_x_5124_, 2);
v___x_5134_ = lean_array_set(v_x_5125_, v_x_5126_, v_arg_5133_);
v___x_5135_ = lean_unsigned_to_nat(1u);
v___x_5136_ = lean_nat_sub(v_x_5126_, v___x_5135_);
lean_dec(v_x_5126_);
v_x_5124_ = v_fn_5132_;
v_x_5125_ = v___x_5134_;
v_x_5126_ = v___x_5136_;
goto _start;
}
else
{
lean_dec(v_x_5126_);
if (lean_obj_tag(v_x_5124_) == 4)
{
lean_object* v_declName_5138_; lean_object* v___x_5139_; 
v_declName_5138_ = lean_ctor_get(v_x_5124_, 0);
lean_inc(v_declName_5138_);
lean_dec_ref_known(v_x_5124_, 2);
v___x_5139_ = l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(v_declName_5138_, v___y_5127_, v___y_5128_, v___y_5129_, v___y_5130_);
if (lean_obj_tag(v___x_5139_) == 0)
{
lean_object* v_a_5140_; lean_object* v___x_5142_; uint8_t v_isShared_5143_; uint8_t v_isSharedCheck_5171_; 
v_a_5140_ = lean_ctor_get(v___x_5139_, 0);
v_isSharedCheck_5171_ = !lean_is_exclusive(v___x_5139_);
if (v_isSharedCheck_5171_ == 0)
{
v___x_5142_ = v___x_5139_;
v_isShared_5143_ = v_isSharedCheck_5171_;
goto v_resetjp_5141_;
}
else
{
lean_inc(v_a_5140_);
lean_dec(v___x_5139_);
v___x_5142_ = lean_box(0);
v_isShared_5143_ = v_isSharedCheck_5171_;
goto v_resetjp_5141_;
}
v_resetjp_5141_:
{
lean_object* v_lower_5145_; lean_object* v_upper_5146_; 
if (lean_obj_tag(v_a_5140_) == 5)
{
lean_object* v_val_5154_; lean_object* v___x_5156_; uint8_t v_isShared_5157_; uint8_t v_isSharedCheck_5168_; 
v_val_5154_ = lean_ctor_get(v_a_5140_, 0);
v_isSharedCheck_5168_ = !lean_is_exclusive(v_a_5140_);
if (v_isSharedCheck_5168_ == 0)
{
v___x_5156_ = v_a_5140_;
v_isShared_5157_ = v_isSharedCheck_5168_;
goto v_resetjp_5155_;
}
else
{
lean_inc(v_val_5154_);
lean_dec(v_a_5140_);
v___x_5156_ = lean_box(0);
v_isShared_5157_ = v_isSharedCheck_5168_;
goto v_resetjp_5155_;
}
v_resetjp_5155_:
{
lean_object* v_numParams_5158_; lean_object* v_numIndices_5159_; lean_object* v___x_5160_; uint8_t v___x_5161_; 
v_numParams_5158_ = lean_ctor_get(v_val_5154_, 1);
lean_inc(v_numParams_5158_);
v_numIndices_5159_ = lean_ctor_get(v_val_5154_, 2);
lean_inc(v_numIndices_5159_);
lean_dec_ref(v_val_5154_);
v___x_5160_ = lean_unsigned_to_nat(0u);
v___x_5161_ = lean_nat_dec_eq(v_numIndices_5159_, v___x_5160_);
lean_dec(v_numIndices_5159_);
if (v___x_5161_ == 0)
{
lean_object* v___x_5162_; uint8_t v___x_5163_; 
lean_del_object(v___x_5156_);
v___x_5162_ = lean_array_get_size(v_x_5125_);
v___x_5163_ = lean_nat_dec_le(v_numParams_5158_, v___x_5160_);
if (v___x_5163_ == 0)
{
v_lower_5145_ = v_numParams_5158_;
v_upper_5146_ = v___x_5162_;
goto v___jp_5144_;
}
else
{
lean_dec(v_numParams_5158_);
v_lower_5145_ = v___x_5160_;
v_upper_5146_ = v___x_5162_;
goto v___jp_5144_;
}
}
else
{
lean_object* v___x_5164_; lean_object* v___x_5166_; 
lean_dec(v_numParams_5158_);
lean_del_object(v___x_5142_);
lean_dec_ref(v_x_5125_);
v___x_5164_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2___closed__0));
if (v_isShared_5157_ == 0)
{
lean_ctor_set_tag(v___x_5156_, 0);
lean_ctor_set(v___x_5156_, 0, v___x_5164_);
v___x_5166_ = v___x_5156_;
goto v_reusejp_5165_;
}
else
{
lean_object* v_reuseFailAlloc_5167_; 
v_reuseFailAlloc_5167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5167_, 0, v___x_5164_);
v___x_5166_ = v_reuseFailAlloc_5167_;
goto v_reusejp_5165_;
}
v_reusejp_5165_:
{
return v___x_5166_;
}
}
}
}
else
{
lean_object* v___x_5169_; lean_object* v___x_5170_; 
lean_del_object(v___x_5142_);
lean_dec(v_a_5140_);
lean_dec_ref(v_x_5125_);
v___x_5169_ = lean_box(0);
v___x_5170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5170_, 0, v___x_5169_);
return v___x_5170_;
}
v___jp_5144_:
{
lean_object* v___x_5147_; lean_object* v___x_5148_; lean_object* v___x_5149_; lean_object* v___x_5150_; lean_object* v___x_5152_; 
v___x_5147_ = l_Array_toSubarray___redArg(v_x_5125_, v_lower_5145_, v_upper_5146_);
v___x_5148_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_5149_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(v___x_5147_, v___x_5148_);
v___x_5150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5150_, 0, v___x_5149_);
if (v_isShared_5143_ == 0)
{
lean_ctor_set(v___x_5142_, 0, v___x_5150_);
v___x_5152_ = v___x_5142_;
goto v_reusejp_5151_;
}
else
{
lean_object* v_reuseFailAlloc_5153_; 
v_reuseFailAlloc_5153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5153_, 0, v___x_5150_);
v___x_5152_ = v_reuseFailAlloc_5153_;
goto v_reusejp_5151_;
}
v_reusejp_5151_:
{
return v___x_5152_;
}
}
}
}
else
{
lean_object* v_a_5172_; lean_object* v___x_5174_; uint8_t v_isShared_5175_; uint8_t v_isSharedCheck_5179_; 
lean_dec_ref(v_x_5125_);
v_a_5172_ = lean_ctor_get(v___x_5139_, 0);
v_isSharedCheck_5179_ = !lean_is_exclusive(v___x_5139_);
if (v_isSharedCheck_5179_ == 0)
{
v___x_5174_ = v___x_5139_;
v_isShared_5175_ = v_isSharedCheck_5179_;
goto v_resetjp_5173_;
}
else
{
lean_inc(v_a_5172_);
lean_dec(v___x_5139_);
v___x_5174_ = lean_box(0);
v_isShared_5175_ = v_isSharedCheck_5179_;
goto v_resetjp_5173_;
}
v_resetjp_5173_:
{
lean_object* v___x_5177_; 
if (v_isShared_5175_ == 0)
{
v___x_5177_ = v___x_5174_;
goto v_reusejp_5176_;
}
else
{
lean_object* v_reuseFailAlloc_5178_; 
v_reuseFailAlloc_5178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5178_, 0, v_a_5172_);
v___x_5177_ = v_reuseFailAlloc_5178_;
goto v_reusejp_5176_;
}
v_reusejp_5176_:
{
return v___x_5177_;
}
}
}
}
else
{
lean_object* v___x_5180_; lean_object* v___x_5181_; 
lean_dec_ref(v_x_5125_);
lean_dec_ref(v_x_5124_);
v___x_5180_ = lean_box(0);
v___x_5181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5181_, 0, v___x_5180_);
return v___x_5181_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2___boxed(lean_object* v_x_5182_, lean_object* v_x_5183_, lean_object* v_x_5184_, lean_object* v___y_5185_, lean_object* v___y_5186_, lean_object* v___y_5187_, lean_object* v___y_5188_, lean_object* v___y_5189_){
_start:
{
lean_object* v_res_5190_; 
v_res_5190_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(v_x_5182_, v_x_5183_, v_x_5184_, v___y_5185_, v___y_5186_, v___y_5187_, v___y_5188_);
lean_dec(v___y_5188_);
lean_dec_ref(v___y_5187_);
lean_dec(v___y_5186_);
lean_dec_ref(v___y_5185_);
return v_res_5190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorAppIndices_x3f(lean_object* v_ctorApp_5191_, lean_object* v_a_5192_, lean_object* v_a_5193_, lean_object* v_a_5194_, lean_object* v_a_5195_){
_start:
{
lean_object* v___x_5197_; 
lean_inc(v_a_5195_);
lean_inc_ref(v_a_5194_);
lean_inc(v_a_5193_);
lean_inc_ref(v_a_5192_);
v___x_5197_ = lean_infer_type(v_ctorApp_5191_, v_a_5192_, v_a_5193_, v_a_5194_, v_a_5195_);
if (lean_obj_tag(v___x_5197_) == 0)
{
lean_object* v_a_5198_; lean_object* v___x_5199_; 
v_a_5198_ = lean_ctor_get(v___x_5197_, 0);
lean_inc(v_a_5198_);
lean_dec_ref_known(v___x_5197_, 1);
v___x_5199_ = l_Lean_Meta_whnfD(v_a_5198_, v_a_5192_, v_a_5193_, v_a_5194_, v_a_5195_);
if (lean_obj_tag(v___x_5199_) == 0)
{
lean_object* v_a_5200_; lean_object* v_dummy_5201_; lean_object* v_nargs_5202_; lean_object* v___x_5203_; lean_object* v___x_5204_; lean_object* v___x_5205_; lean_object* v___x_5206_; 
v_a_5200_ = lean_ctor_get(v___x_5199_, 0);
lean_inc(v_a_5200_);
lean_dec_ref_known(v___x_5199_, 1);
v_dummy_5201_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0);
v_nargs_5202_ = l_Lean_Expr_getAppNumArgs(v_a_5200_);
lean_inc(v_nargs_5202_);
v___x_5203_ = lean_mk_array(v_nargs_5202_, v_dummy_5201_);
v___x_5204_ = lean_unsigned_to_nat(1u);
v___x_5205_ = lean_nat_sub(v_nargs_5202_, v___x_5204_);
lean_dec(v_nargs_5202_);
v___x_5206_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(v_a_5200_, v___x_5203_, v___x_5205_, v_a_5192_, v_a_5193_, v_a_5194_, v_a_5195_);
return v___x_5206_;
}
else
{
lean_object* v_a_5207_; lean_object* v___x_5209_; uint8_t v_isShared_5210_; uint8_t v_isSharedCheck_5214_; 
v_a_5207_ = lean_ctor_get(v___x_5199_, 0);
v_isSharedCheck_5214_ = !lean_is_exclusive(v___x_5199_);
if (v_isSharedCheck_5214_ == 0)
{
v___x_5209_ = v___x_5199_;
v_isShared_5210_ = v_isSharedCheck_5214_;
goto v_resetjp_5208_;
}
else
{
lean_inc(v_a_5207_);
lean_dec(v___x_5199_);
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
lean_object* v_a_5215_; lean_object* v___x_5217_; uint8_t v_isShared_5218_; uint8_t v_isSharedCheck_5222_; 
v_a_5215_ = lean_ctor_get(v___x_5197_, 0);
v_isSharedCheck_5222_ = !lean_is_exclusive(v___x_5197_);
if (v_isSharedCheck_5222_ == 0)
{
v___x_5217_ = v___x_5197_;
v_isShared_5218_ = v_isSharedCheck_5222_;
goto v_resetjp_5216_;
}
else
{
lean_inc(v_a_5215_);
lean_dec(v___x_5197_);
v___x_5217_ = lean_box(0);
v_isShared_5218_ = v_isSharedCheck_5222_;
goto v_resetjp_5216_;
}
v_resetjp_5216_:
{
lean_object* v___x_5220_; 
if (v_isShared_5218_ == 0)
{
v___x_5220_ = v___x_5217_;
goto v_reusejp_5219_;
}
else
{
lean_object* v_reuseFailAlloc_5221_; 
v_reuseFailAlloc_5221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5221_, 0, v_a_5215_);
v___x_5220_ = v_reuseFailAlloc_5221_;
goto v_reusejp_5219_;
}
v_reusejp_5219_:
{
return v___x_5220_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorAppIndices_x3f___boxed(lean_object* v_ctorApp_5223_, lean_object* v_a_5224_, lean_object* v_a_5225_, lean_object* v_a_5226_, lean_object* v_a_5227_, lean_object* v_a_5228_){
_start:
{
lean_object* v_res_5229_; 
v_res_5229_ = l_Lean_Meta_getCtorAppIndices_x3f(v_ctorApp_5223_, v_a_5224_, v_a_5225_, v_a_5226_, v_a_5227_);
lean_dec(v_a_5227_);
lean_dec_ref(v_a_5226_);
lean_dec(v_a_5225_);
lean_dec_ref(v_a_5224_);
return v_res_5229_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1(lean_object* v_inst_5230_, lean_object* v_R_5231_, lean_object* v_a_5232_, lean_object* v_b_5233_){
_start:
{
lean_object* v___x_5234_; 
v___x_5234_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(v_a_5232_, v_b_5233_);
return v___x_5234_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0(lean_object* v_00_u03b1_5235_, lean_object* v_constName_5236_, lean_object* v___y_5237_, lean_object* v___y_5238_, lean_object* v___y_5239_, lean_object* v___y_5240_){
_start:
{
lean_object* v___x_5242_; 
v___x_5242_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(v_constName_5236_, v___y_5237_, v___y_5238_, v___y_5239_, v___y_5240_);
return v___x_5242_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b1_5243_, lean_object* v_constName_5244_, lean_object* v___y_5245_, lean_object* v___y_5246_, lean_object* v___y_5247_, lean_object* v___y_5248_, lean_object* v___y_5249_){
_start:
{
lean_object* v_res_5250_; 
v_res_5250_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0(v_00_u03b1_5243_, v_constName_5244_, v___y_5245_, v___y_5246_, v___y_5247_, v___y_5248_);
lean_dec(v___y_5248_);
lean_dec_ref(v___y_5247_);
lean_dec(v___y_5246_);
lean_dec_ref(v___y_5245_);
return v_res_5250_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_5251_, lean_object* v_ref_5252_, lean_object* v_constName_5253_, lean_object* v___y_5254_, lean_object* v___y_5255_, lean_object* v___y_5256_, lean_object* v___y_5257_){
_start:
{
lean_object* v___x_5259_; 
v___x_5259_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(v_ref_5252_, v_constName_5253_, v___y_5254_, v___y_5255_, v___y_5256_, v___y_5257_);
return v___x_5259_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_5260_, lean_object* v_ref_5261_, lean_object* v_constName_5262_, lean_object* v___y_5263_, lean_object* v___y_5264_, lean_object* v___y_5265_, lean_object* v___y_5266_, lean_object* v___y_5267_){
_start:
{
lean_object* v_res_5268_; 
v_res_5268_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1(v_00_u03b1_5260_, v_ref_5261_, v_constName_5262_, v___y_5263_, v___y_5264_, v___y_5265_, v___y_5266_);
lean_dec(v___y_5266_);
lean_dec_ref(v___y_5265_);
lean_dec(v___y_5264_);
lean_dec_ref(v___y_5263_);
lean_dec(v_ref_5261_);
return v_res_5268_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_5269_, lean_object* v_ref_5270_, lean_object* v_msg_5271_, lean_object* v_declHint_5272_, lean_object* v___y_5273_, lean_object* v___y_5274_, lean_object* v___y_5275_, lean_object* v___y_5276_){
_start:
{
lean_object* v___x_5278_; 
v___x_5278_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5270_, v_msg_5271_, v_declHint_5272_, v___y_5273_, v___y_5274_, v___y_5275_, v___y_5276_);
return v___x_5278_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_5279_, lean_object* v_ref_5280_, lean_object* v_msg_5281_, lean_object* v_declHint_5282_, lean_object* v___y_5283_, lean_object* v___y_5284_, lean_object* v___y_5285_, lean_object* v___y_5286_, lean_object* v___y_5287_){
_start:
{
lean_object* v_res_5288_; 
v_res_5288_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_5279_, v_ref_5280_, v_msg_5281_, v_declHint_5282_, v___y_5283_, v___y_5284_, v___y_5285_, v___y_5286_);
lean_dec(v___y_5286_);
lean_dec_ref(v___y_5285_);
lean_dec(v___y_5284_);
lean_dec_ref(v___y_5283_);
lean_dec(v_ref_5280_);
return v_res_5288_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_msg_5289_, lean_object* v_declHint_5290_, lean_object* v___y_5291_, lean_object* v___y_5292_, lean_object* v___y_5293_, lean_object* v___y_5294_){
_start:
{
lean_object* v___x_5296_; 
v___x_5296_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_5289_, v_declHint_5290_, v___y_5294_);
return v___x_5296_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_5297_, lean_object* v_declHint_5298_, lean_object* v___y_5299_, lean_object* v___y_5300_, lean_object* v___y_5301_, lean_object* v___y_5302_, lean_object* v___y_5303_){
_start:
{
lean_object* v_res_5304_; 
v_res_5304_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_5297_, v_declHint_5298_, v___y_5299_, v___y_5300_, v___y_5301_, v___y_5302_);
lean_dec(v___y_5302_);
lean_dec_ref(v___y_5301_);
lean_dec(v___y_5300_);
lean_dec_ref(v___y_5299_);
return v_res_5304_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_5305_, lean_object* v_ref_5306_, lean_object* v_msg_5307_, lean_object* v___y_5308_, lean_object* v___y_5309_, lean_object* v___y_5310_, lean_object* v___y_5311_){
_start:
{
lean_object* v___x_5313_; 
v___x_5313_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5306_, v_msg_5307_, v___y_5308_, v___y_5309_, v___y_5310_, v___y_5311_);
return v___x_5313_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_5314_, lean_object* v_ref_5315_, lean_object* v_msg_5316_, lean_object* v___y_5317_, lean_object* v___y_5318_, lean_object* v___y_5319_, lean_object* v___y_5320_, lean_object* v___y_5321_){
_start:
{
lean_object* v_res_5322_; 
v_res_5322_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_5314_, v_ref_5315_, v_msg_5316_, v___y_5317_, v___y_5318_, v___y_5319_, v___y_5320_);
lean_dec(v___y_5320_);
lean_dec_ref(v___y_5319_);
lean_dec(v___y_5318_);
lean_dec_ref(v___y_5317_);
lean_dec(v_ref_5315_);
return v_res_5322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0___boxed(lean_object* v_i_5323_, lean_object* v_body_5324_, lean_object* v_args2_5325_, lean_object* v_ctorVal_5326_, lean_object* v_args1_5327_, lean_object* v_k_5328_, lean_object* v_arg2_5329_, lean_object* v___y_5330_, lean_object* v___y_5331_, lean_object* v___y_5332_, lean_object* v___y_5333_, lean_object* v___y_5334_){
_start:
{
lean_object* v_res_5335_; 
v_res_5335_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0(v_i_5323_, v_body_5324_, v_args2_5325_, v_ctorVal_5326_, v_args1_5327_, v_k_5328_, v_arg2_5329_, v___y_5330_, v___y_5331_, v___y_5332_, v___y_5333_);
lean_dec(v___y_5333_);
lean_dec_ref(v___y_5332_);
lean_dec(v___y_5331_);
lean_dec_ref(v___y_5330_);
lean_dec_ref(v_body_5324_);
lean_dec(v_i_5323_);
return v_res_5335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(lean_object* v_ctorVal_5336_, lean_object* v_args1_5337_, lean_object* v_k_5338_, lean_object* v_i_5339_, lean_object* v_type_5340_, lean_object* v_args2_5341_, lean_object* v_a_5342_, lean_object* v_a_5343_, lean_object* v_a_5344_, lean_object* v_a_5345_){
_start:
{
lean_object* v___x_5347_; uint8_t v___x_5348_; 
v___x_5347_ = lean_array_get_size(v_args1_5337_);
v___x_5348_ = lean_nat_dec_lt(v_i_5339_, v___x_5347_);
if (v___x_5348_ == 0)
{
lean_object* v___x_5349_; 
lean_dec_ref(v_type_5340_);
lean_dec(v_i_5339_);
lean_dec_ref(v_args1_5337_);
lean_dec_ref(v_ctorVal_5336_);
lean_inc(v_a_5345_);
lean_inc_ref(v_a_5344_);
lean_inc(v_a_5343_);
lean_inc_ref(v_a_5342_);
v___x_5349_ = lean_apply_6(v_k_5338_, v_args2_5341_, v_a_5342_, v_a_5343_, v_a_5344_, v_a_5345_, lean_box(0));
return v___x_5349_;
}
else
{
lean_object* v___x_5350_; 
lean_inc(v_a_5345_);
lean_inc_ref(v_a_5344_);
lean_inc(v_a_5343_);
lean_inc_ref(v_a_5342_);
v___x_5350_ = lean_whnf(v_type_5340_, v_a_5342_, v_a_5343_, v_a_5344_, v_a_5345_);
if (lean_obj_tag(v___x_5350_) == 0)
{
lean_object* v_a_5351_; 
v_a_5351_ = lean_ctor_get(v___x_5350_, 0);
lean_inc(v_a_5351_);
lean_dec_ref_known(v___x_5350_, 1);
if (lean_obj_tag(v_a_5351_) == 7)
{
lean_object* v_binderName_5352_; lean_object* v_binderType_5353_; lean_object* v_body_5354_; lean_object* v___f_5355_; uint8_t v___x_5356_; uint8_t v___x_5357_; lean_object* v___x_5358_; 
v_binderName_5352_ = lean_ctor_get(v_a_5351_, 0);
lean_inc(v_binderName_5352_);
v_binderType_5353_ = lean_ctor_get(v_a_5351_, 1);
lean_inc_ref(v_binderType_5353_);
v_body_5354_ = lean_ctor_get(v_a_5351_, 2);
lean_inc_ref(v_body_5354_);
lean_dec_ref_known(v_a_5351_, 3);
v___f_5355_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0___boxed), 12, 6);
lean_closure_set(v___f_5355_, 0, v_i_5339_);
lean_closure_set(v___f_5355_, 1, v_body_5354_);
lean_closure_set(v___f_5355_, 2, v_args2_5341_);
lean_closure_set(v___f_5355_, 3, v_ctorVal_5336_);
lean_closure_set(v___f_5355_, 4, v_args1_5337_);
lean_closure_set(v___f_5355_, 5, v_k_5338_);
v___x_5356_ = 1;
v___x_5357_ = 0;
v___x_5358_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_binderName_5352_, v___x_5356_, v_binderType_5353_, v___f_5355_, v___x_5357_, v_a_5342_, v_a_5343_, v_a_5344_, v_a_5345_);
return v___x_5358_;
}
else
{
lean_object* v_toConstantVal_5359_; lean_object* v_name_5360_; lean_object* v___x_5361_; lean_object* v___x_5362_; lean_object* v___x_5363_; lean_object* v___x_5364_; lean_object* v___x_5365_; lean_object* v___x_5366_; 
lean_dec(v_a_5351_);
lean_dec_ref(v_args2_5341_);
lean_dec(v_i_5339_);
lean_dec_ref(v_k_5338_);
lean_dec_ref(v_args1_5337_);
v_toConstantVal_5359_ = lean_ctor_get(v_ctorVal_5336_, 0);
lean_inc_ref(v_toConstantVal_5359_);
lean_dec_ref(v_ctorVal_5336_);
v_name_5360_ = lean_ctor_get(v_toConstantVal_5359_, 0);
lean_inc(v_name_5360_);
lean_dec_ref(v_toConstantVal_5359_);
v___x_5361_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1);
v___x_5362_ = l_Lean_MessageData_ofName(v_name_5360_);
v___x_5363_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5363_, 0, v___x_5361_);
lean_ctor_set(v___x_5363_, 1, v___x_5362_);
v___x_5364_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_5365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5365_, 0, v___x_5363_);
lean_ctor_set(v___x_5365_, 1, v___x_5364_);
v___x_5366_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_5365_, v_a_5342_, v_a_5343_, v_a_5344_, v_a_5345_);
return v___x_5366_;
}
}
else
{
lean_object* v_a_5367_; lean_object* v___x_5369_; uint8_t v_isShared_5370_; uint8_t v_isSharedCheck_5374_; 
lean_dec_ref(v_args2_5341_);
lean_dec(v_i_5339_);
lean_dec_ref(v_k_5338_);
lean_dec_ref(v_args1_5337_);
lean_dec_ref(v_ctorVal_5336_);
v_a_5367_ = lean_ctor_get(v___x_5350_, 0);
v_isSharedCheck_5374_ = !lean_is_exclusive(v___x_5350_);
if (v_isSharedCheck_5374_ == 0)
{
v___x_5369_ = v___x_5350_;
v_isShared_5370_ = v_isSharedCheck_5374_;
goto v_resetjp_5368_;
}
else
{
lean_inc(v_a_5367_);
lean_dec(v___x_5350_);
v___x_5369_ = lean_box(0);
v_isShared_5370_ = v_isSharedCheck_5374_;
goto v_resetjp_5368_;
}
v_resetjp_5368_:
{
lean_object* v___x_5372_; 
if (v_isShared_5370_ == 0)
{
v___x_5372_ = v___x_5369_;
goto v_reusejp_5371_;
}
else
{
lean_object* v_reuseFailAlloc_5373_; 
v_reuseFailAlloc_5373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5373_, 0, v_a_5367_);
v___x_5372_ = v_reuseFailAlloc_5373_;
goto v_reusejp_5371_;
}
v_reusejp_5371_:
{
return v___x_5372_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0(lean_object* v_i_5375_, lean_object* v_body_5376_, lean_object* v_args2_5377_, lean_object* v_ctorVal_5378_, lean_object* v_args1_5379_, lean_object* v_k_5380_, lean_object* v_arg2_5381_, lean_object* v___y_5382_, lean_object* v___y_5383_, lean_object* v___y_5384_, lean_object* v___y_5385_){
_start:
{
lean_object* v___x_5387_; lean_object* v___x_5388_; lean_object* v___x_5389_; lean_object* v___x_5390_; lean_object* v___x_5391_; 
v___x_5387_ = lean_unsigned_to_nat(1u);
v___x_5388_ = lean_nat_add(v_i_5375_, v___x_5387_);
v___x_5389_ = lean_expr_instantiate1(v_body_5376_, v_arg2_5381_);
v___x_5390_ = lean_array_push(v_args2_5377_, v_arg2_5381_);
v___x_5391_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(v_ctorVal_5378_, v_args1_5379_, v_k_5380_, v___x_5388_, v___x_5389_, v___x_5390_, v___y_5382_, v___y_5383_, v___y_5384_, v___y_5385_);
return v___x_5391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___boxed(lean_object* v_ctorVal_5392_, lean_object* v_args1_5393_, lean_object* v_k_5394_, lean_object* v_i_5395_, lean_object* v_type_5396_, lean_object* v_args2_5397_, lean_object* v_a_5398_, lean_object* v_a_5399_, lean_object* v_a_5400_, lean_object* v_a_5401_, lean_object* v_a_5402_){
_start:
{
lean_object* v_res_5403_; 
v_res_5403_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(v_ctorVal_5392_, v_args1_5393_, v_k_5394_, v_i_5395_, v_type_5396_, v_args2_5397_, v_a_5398_, v_a_5399_, v_a_5400_, v_a_5401_);
lean_dec(v_a_5401_);
lean_dec_ref(v_a_5400_);
lean_dec(v_a_5399_);
lean_dec_ref(v_a_5398_);
return v_res_5403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0(lean_object* v_name_5404_, lean_object* v_us_5405_, lean_object* v_args1_5406_, lean_object* v___x_5407_, lean_object* v_numParams_5408_, lean_object* v___x_5409_, lean_object* v_args2_5410_, lean_object* v___y_5411_, lean_object* v___y_5412_, lean_object* v___y_5413_, lean_object* v___y_5414_){
_start:
{
lean_object* v___x_5416_; lean_object* v___x_5417_; lean_object* v___x_5418_; lean_object* v___x_5419_; 
lean_inc(v_us_5405_);
v___x_5416_ = l_Lean_mkConst(v_name_5404_, v_us_5405_);
lean_inc_ref(v___x_5416_);
v___x_5417_ = l_Lean_mkAppN(v___x_5416_, v_args1_5406_);
v___x_5418_ = l_Lean_mkAppN(v___x_5416_, v_args2_5410_);
lean_inc_ref(v___x_5418_);
lean_inc_ref(v___x_5417_);
v___x_5419_ = l_Lean_Meta_mkEqHEq(v___x_5417_, v___x_5418_, v___y_5411_, v___y_5412_, v___y_5413_, v___y_5414_);
if (lean_obj_tag(v___x_5419_) == 0)
{
lean_object* v_a_5420_; lean_object* v___x_5421_; uint8_t v___x_5422_; lean_object* v___x_5423_; 
v_a_5420_ = lean_ctor_get(v___x_5419_, 0);
lean_inc(v_a_5420_);
lean_dec_ref_known(v___x_5419_, 1);
lean_inc_ref_n(v_args2_5410_, 2);
v___x_5421_ = l_Array_toSubarray___redArg(v_args2_5410_, v___x_5407_, v_numParams_5408_);
v___x_5422_ = 1;
v___x_5423_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v_args1_5406_, v_args2_5410_, v___x_5422_, v___y_5411_, v___y_5412_, v___y_5413_, v___y_5414_);
if (lean_obj_tag(v___x_5423_) == 0)
{
lean_object* v_a_5424_; lean_object* v___x_5426_; uint8_t v_isShared_5427_; uint8_t v_isSharedCheck_5544_; 
v_a_5424_ = lean_ctor_get(v___x_5423_, 0);
v_isSharedCheck_5544_ = !lean_is_exclusive(v___x_5423_);
if (v_isSharedCheck_5544_ == 0)
{
v___x_5426_ = v___x_5423_;
v_isShared_5427_ = v_isSharedCheck_5544_;
goto v_resetjp_5425_;
}
else
{
lean_inc(v_a_5424_);
lean_dec(v___x_5423_);
v___x_5426_ = lean_box(0);
v_isShared_5427_ = v_isSharedCheck_5544_;
goto v_resetjp_5425_;
}
v_resetjp_5425_:
{
lean_object* v___x_5428_; 
v___x_5428_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f(v_a_5424_);
if (lean_obj_tag(v___x_5428_) == 1)
{
lean_object* v_val_5429_; lean_object* v___x_5430_; 
lean_del_object(v___x_5426_);
v_val_5429_ = lean_ctor_get(v___x_5428_, 0);
lean_inc(v_val_5429_);
lean_dec_ref_known(v___x_5428_, 1);
v___x_5430_ = l_Lean_mkArrow(v_a_5420_, v_val_5429_, v___y_5413_, v___y_5414_);
if (lean_obj_tag(v___x_5430_) == 0)
{
lean_object* v_a_5431_; lean_object* v___x_5432_; 
v_a_5431_ = lean_ctor_get(v___x_5430_, 0);
lean_inc(v_a_5431_);
lean_dec_ref_known(v___x_5430_, 1);
v___x_5432_ = l_Lean_Meta_getCtorAppIndices_x3f(v___x_5417_, v___y_5411_, v___y_5412_, v___y_5413_, v___y_5414_);
if (lean_obj_tag(v___x_5432_) == 0)
{
lean_object* v_a_5433_; lean_object* v___x_5435_; uint8_t v_isShared_5436_; uint8_t v_isSharedCheck_5523_; 
v_a_5433_ = lean_ctor_get(v___x_5432_, 0);
v_isSharedCheck_5523_ = !lean_is_exclusive(v___x_5432_);
if (v_isSharedCheck_5523_ == 0)
{
v___x_5435_ = v___x_5432_;
v_isShared_5436_ = v_isSharedCheck_5523_;
goto v_resetjp_5434_;
}
else
{
lean_inc(v_a_5433_);
lean_dec(v___x_5432_);
v___x_5435_ = lean_box(0);
v_isShared_5436_ = v_isSharedCheck_5523_;
goto v_resetjp_5434_;
}
v_resetjp_5434_:
{
if (lean_obj_tag(v_a_5433_) == 1)
{
lean_object* v_val_5437_; lean_object* v___x_5438_; 
lean_del_object(v___x_5435_);
v_val_5437_ = lean_ctor_get(v_a_5433_, 0);
lean_inc(v_val_5437_);
lean_dec_ref_known(v_a_5433_, 1);
v___x_5438_ = l_Lean_Meta_getCtorAppIndices_x3f(v___x_5418_, v___y_5411_, v___y_5412_, v___y_5413_, v___y_5414_);
if (lean_obj_tag(v___x_5438_) == 0)
{
lean_object* v_a_5439_; lean_object* v___x_5441_; uint8_t v_isShared_5442_; uint8_t v_isSharedCheck_5510_; 
v_a_5439_ = lean_ctor_get(v___x_5438_, 0);
v_isSharedCheck_5510_ = !lean_is_exclusive(v___x_5438_);
if (v_isSharedCheck_5510_ == 0)
{
v___x_5441_ = v___x_5438_;
v_isShared_5442_ = v_isSharedCheck_5510_;
goto v_resetjp_5440_;
}
else
{
lean_inc(v_a_5439_);
lean_dec(v___x_5438_);
v___x_5441_ = lean_box(0);
v_isShared_5442_ = v_isSharedCheck_5510_;
goto v_resetjp_5440_;
}
v_resetjp_5440_:
{
if (lean_obj_tag(v_a_5439_) == 1)
{
lean_object* v_val_5443_; lean_object* v___x_5445_; uint8_t v_isShared_5446_; uint8_t v_isSharedCheck_5505_; 
lean_del_object(v___x_5441_);
v_val_5443_ = lean_ctor_get(v_a_5439_, 0);
v_isSharedCheck_5505_ = !lean_is_exclusive(v_a_5439_);
if (v_isSharedCheck_5505_ == 0)
{
v___x_5445_ = v_a_5439_;
v_isShared_5446_ = v_isSharedCheck_5505_;
goto v_resetjp_5444_;
}
else
{
lean_inc(v_val_5443_);
lean_dec(v_a_5439_);
v___x_5445_ = lean_box(0);
v_isShared_5446_ = v_isSharedCheck_5505_;
goto v_resetjp_5444_;
}
v_resetjp_5444_:
{
lean_object* v___x_5447_; lean_object* v___x_5448_; lean_object* v___x_5449_; lean_object* v___x_5450_; uint8_t v___x_5451_; lean_object* v___x_5452_; 
v___x_5447_ = l_Subarray_copy___redArg(v___x_5409_);
v___x_5448_ = l_Array_append___redArg(v___x_5447_, v_val_5437_);
v___x_5449_ = l_Subarray_copy___redArg(v___x_5421_);
v___x_5450_ = l_Array_append___redArg(v___x_5449_, v_val_5443_);
lean_dec(v_val_5443_);
v___x_5451_ = 0;
v___x_5452_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v___x_5448_, v___x_5450_, v___x_5451_, v___y_5411_, v___y_5412_, v___y_5413_, v___y_5414_);
lean_dec_ref(v___x_5448_);
if (lean_obj_tag(v___x_5452_) == 0)
{
lean_object* v_a_5453_; lean_object* v___x_5454_; 
v_a_5453_ = lean_ctor_get(v___x_5452_, 0);
lean_inc(v_a_5453_);
lean_dec_ref_known(v___x_5452_, 1);
v___x_5454_ = l_Lean_mkArrowN(v_a_5453_, v_a_5431_, v___y_5413_, v___y_5414_);
lean_dec(v_a_5453_);
if (lean_obj_tag(v___x_5454_) == 0)
{
lean_object* v_a_5455_; uint8_t v___x_5456_; lean_object* v___x_5457_; 
v_a_5455_ = lean_ctor_get(v___x_5454_, 0);
lean_inc(v_a_5455_);
lean_dec_ref_known(v___x_5454_, 1);
v___x_5456_ = 1;
v___x_5457_ = l_Lean_Meta_mkForallFVars(v_args2_5410_, v_a_5455_, v___x_5451_, v___x_5422_, v___x_5422_, v___x_5456_, v___y_5411_, v___y_5412_, v___y_5413_, v___y_5414_);
lean_dec_ref(v_args2_5410_);
if (lean_obj_tag(v___x_5457_) == 0)
{
lean_object* v_a_5458_; lean_object* v___x_5459_; 
v_a_5458_ = lean_ctor_get(v___x_5457_, 0);
lean_inc(v_a_5458_);
lean_dec_ref_known(v___x_5457_, 1);
v___x_5459_ = l_Lean_Meta_mkForallFVars(v_args1_5406_, v_a_5458_, v___x_5451_, v___x_5422_, v___x_5422_, v___x_5456_, v___y_5411_, v___y_5412_, v___y_5413_, v___y_5414_);
if (lean_obj_tag(v___x_5459_) == 0)
{
lean_object* v_a_5460_; lean_object* v___x_5462_; uint8_t v_isShared_5463_; uint8_t v_isSharedCheck_5472_; 
v_a_5460_ = lean_ctor_get(v___x_5459_, 0);
v_isSharedCheck_5472_ = !lean_is_exclusive(v___x_5459_);
if (v_isSharedCheck_5472_ == 0)
{
v___x_5462_ = v___x_5459_;
v_isShared_5463_ = v_isSharedCheck_5472_;
goto v_resetjp_5461_;
}
else
{
lean_inc(v_a_5460_);
lean_dec(v___x_5459_);
v___x_5462_ = lean_box(0);
v_isShared_5463_ = v_isSharedCheck_5472_;
goto v_resetjp_5461_;
}
v_resetjp_5461_:
{
lean_object* v___x_5464_; lean_object* v___x_5465_; lean_object* v___x_5467_; 
v___x_5464_ = lean_array_get_size(v_val_5437_);
lean_dec(v_val_5437_);
v___x_5465_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5465_, 0, v_a_5460_);
lean_ctor_set(v___x_5465_, 1, v_us_5405_);
lean_ctor_set(v___x_5465_, 2, v___x_5464_);
if (v_isShared_5446_ == 0)
{
lean_ctor_set(v___x_5445_, 0, v___x_5465_);
v___x_5467_ = v___x_5445_;
goto v_reusejp_5466_;
}
else
{
lean_object* v_reuseFailAlloc_5471_; 
v_reuseFailAlloc_5471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5471_, 0, v___x_5465_);
v___x_5467_ = v_reuseFailAlloc_5471_;
goto v_reusejp_5466_;
}
v_reusejp_5466_:
{
lean_object* v___x_5469_; 
if (v_isShared_5463_ == 0)
{
lean_ctor_set(v___x_5462_, 0, v___x_5467_);
v___x_5469_ = v___x_5462_;
goto v_reusejp_5468_;
}
else
{
lean_object* v_reuseFailAlloc_5470_; 
v_reuseFailAlloc_5470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5470_, 0, v___x_5467_);
v___x_5469_ = v_reuseFailAlloc_5470_;
goto v_reusejp_5468_;
}
v_reusejp_5468_:
{
return v___x_5469_;
}
}
}
}
else
{
lean_object* v_a_5473_; lean_object* v___x_5475_; uint8_t v_isShared_5476_; uint8_t v_isSharedCheck_5480_; 
lean_del_object(v___x_5445_);
lean_dec(v_val_5437_);
lean_dec(v_us_5405_);
v_a_5473_ = lean_ctor_get(v___x_5459_, 0);
v_isSharedCheck_5480_ = !lean_is_exclusive(v___x_5459_);
if (v_isSharedCheck_5480_ == 0)
{
v___x_5475_ = v___x_5459_;
v_isShared_5476_ = v_isSharedCheck_5480_;
goto v_resetjp_5474_;
}
else
{
lean_inc(v_a_5473_);
lean_dec(v___x_5459_);
v___x_5475_ = lean_box(0);
v_isShared_5476_ = v_isSharedCheck_5480_;
goto v_resetjp_5474_;
}
v_resetjp_5474_:
{
lean_object* v___x_5478_; 
if (v_isShared_5476_ == 0)
{
v___x_5478_ = v___x_5475_;
goto v_reusejp_5477_;
}
else
{
lean_object* v_reuseFailAlloc_5479_; 
v_reuseFailAlloc_5479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5479_, 0, v_a_5473_);
v___x_5478_ = v_reuseFailAlloc_5479_;
goto v_reusejp_5477_;
}
v_reusejp_5477_:
{
return v___x_5478_;
}
}
}
}
else
{
lean_object* v_a_5481_; lean_object* v___x_5483_; uint8_t v_isShared_5484_; uint8_t v_isSharedCheck_5488_; 
lean_del_object(v___x_5445_);
lean_dec(v_val_5437_);
lean_dec(v_us_5405_);
v_a_5481_ = lean_ctor_get(v___x_5457_, 0);
v_isSharedCheck_5488_ = !lean_is_exclusive(v___x_5457_);
if (v_isSharedCheck_5488_ == 0)
{
v___x_5483_ = v___x_5457_;
v_isShared_5484_ = v_isSharedCheck_5488_;
goto v_resetjp_5482_;
}
else
{
lean_inc(v_a_5481_);
lean_dec(v___x_5457_);
v___x_5483_ = lean_box(0);
v_isShared_5484_ = v_isSharedCheck_5488_;
goto v_resetjp_5482_;
}
v_resetjp_5482_:
{
lean_object* v___x_5486_; 
if (v_isShared_5484_ == 0)
{
v___x_5486_ = v___x_5483_;
goto v_reusejp_5485_;
}
else
{
lean_object* v_reuseFailAlloc_5487_; 
v_reuseFailAlloc_5487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5487_, 0, v_a_5481_);
v___x_5486_ = v_reuseFailAlloc_5487_;
goto v_reusejp_5485_;
}
v_reusejp_5485_:
{
return v___x_5486_;
}
}
}
}
else
{
lean_object* v_a_5489_; lean_object* v___x_5491_; uint8_t v_isShared_5492_; uint8_t v_isSharedCheck_5496_; 
lean_del_object(v___x_5445_);
lean_dec(v_val_5437_);
lean_dec_ref(v_args2_5410_);
lean_dec(v_us_5405_);
v_a_5489_ = lean_ctor_get(v___x_5454_, 0);
v_isSharedCheck_5496_ = !lean_is_exclusive(v___x_5454_);
if (v_isSharedCheck_5496_ == 0)
{
v___x_5491_ = v___x_5454_;
v_isShared_5492_ = v_isSharedCheck_5496_;
goto v_resetjp_5490_;
}
else
{
lean_inc(v_a_5489_);
lean_dec(v___x_5454_);
v___x_5491_ = lean_box(0);
v_isShared_5492_ = v_isSharedCheck_5496_;
goto v_resetjp_5490_;
}
v_resetjp_5490_:
{
lean_object* v___x_5494_; 
if (v_isShared_5492_ == 0)
{
v___x_5494_ = v___x_5491_;
goto v_reusejp_5493_;
}
else
{
lean_object* v_reuseFailAlloc_5495_; 
v_reuseFailAlloc_5495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5495_, 0, v_a_5489_);
v___x_5494_ = v_reuseFailAlloc_5495_;
goto v_reusejp_5493_;
}
v_reusejp_5493_:
{
return v___x_5494_;
}
}
}
}
else
{
lean_object* v_a_5497_; lean_object* v___x_5499_; uint8_t v_isShared_5500_; uint8_t v_isSharedCheck_5504_; 
lean_del_object(v___x_5445_);
lean_dec(v_val_5437_);
lean_dec(v_a_5431_);
lean_dec_ref(v_args2_5410_);
lean_dec(v_us_5405_);
v_a_5497_ = lean_ctor_get(v___x_5452_, 0);
v_isSharedCheck_5504_ = !lean_is_exclusive(v___x_5452_);
if (v_isSharedCheck_5504_ == 0)
{
v___x_5499_ = v___x_5452_;
v_isShared_5500_ = v_isSharedCheck_5504_;
goto v_resetjp_5498_;
}
else
{
lean_inc(v_a_5497_);
lean_dec(v___x_5452_);
v___x_5499_ = lean_box(0);
v_isShared_5500_ = v_isSharedCheck_5504_;
goto v_resetjp_5498_;
}
v_resetjp_5498_:
{
lean_object* v___x_5502_; 
if (v_isShared_5500_ == 0)
{
v___x_5502_ = v___x_5499_;
goto v_reusejp_5501_;
}
else
{
lean_object* v_reuseFailAlloc_5503_; 
v_reuseFailAlloc_5503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5503_, 0, v_a_5497_);
v___x_5502_ = v_reuseFailAlloc_5503_;
goto v_reusejp_5501_;
}
v_reusejp_5501_:
{
return v___x_5502_;
}
}
}
}
}
else
{
lean_object* v___x_5506_; lean_object* v___x_5508_; 
lean_dec(v_a_5439_);
lean_dec(v_val_5437_);
lean_dec(v_a_5431_);
lean_dec_ref(v___x_5421_);
lean_dec_ref(v_args2_5410_);
lean_dec_ref(v___x_5409_);
lean_dec(v_us_5405_);
v___x_5506_ = lean_box(0);
if (v_isShared_5442_ == 0)
{
lean_ctor_set(v___x_5441_, 0, v___x_5506_);
v___x_5508_ = v___x_5441_;
goto v_reusejp_5507_;
}
else
{
lean_object* v_reuseFailAlloc_5509_; 
v_reuseFailAlloc_5509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5509_, 0, v___x_5506_);
v___x_5508_ = v_reuseFailAlloc_5509_;
goto v_reusejp_5507_;
}
v_reusejp_5507_:
{
return v___x_5508_;
}
}
}
}
else
{
lean_object* v_a_5511_; lean_object* v___x_5513_; uint8_t v_isShared_5514_; uint8_t v_isSharedCheck_5518_; 
lean_dec(v_val_5437_);
lean_dec(v_a_5431_);
lean_dec_ref(v___x_5421_);
lean_dec_ref(v_args2_5410_);
lean_dec_ref(v___x_5409_);
lean_dec(v_us_5405_);
v_a_5511_ = lean_ctor_get(v___x_5438_, 0);
v_isSharedCheck_5518_ = !lean_is_exclusive(v___x_5438_);
if (v_isSharedCheck_5518_ == 0)
{
v___x_5513_ = v___x_5438_;
v_isShared_5514_ = v_isSharedCheck_5518_;
goto v_resetjp_5512_;
}
else
{
lean_inc(v_a_5511_);
lean_dec(v___x_5438_);
v___x_5513_ = lean_box(0);
v_isShared_5514_ = v_isSharedCheck_5518_;
goto v_resetjp_5512_;
}
v_resetjp_5512_:
{
lean_object* v___x_5516_; 
if (v_isShared_5514_ == 0)
{
v___x_5516_ = v___x_5513_;
goto v_reusejp_5515_;
}
else
{
lean_object* v_reuseFailAlloc_5517_; 
v_reuseFailAlloc_5517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5517_, 0, v_a_5511_);
v___x_5516_ = v_reuseFailAlloc_5517_;
goto v_reusejp_5515_;
}
v_reusejp_5515_:
{
return v___x_5516_;
}
}
}
}
else
{
lean_object* v___x_5519_; lean_object* v___x_5521_; 
lean_dec(v_a_5433_);
lean_dec(v_a_5431_);
lean_dec_ref(v___x_5421_);
lean_dec_ref(v___x_5418_);
lean_dec_ref(v_args2_5410_);
lean_dec_ref(v___x_5409_);
lean_dec(v_us_5405_);
v___x_5519_ = lean_box(0);
if (v_isShared_5436_ == 0)
{
lean_ctor_set(v___x_5435_, 0, v___x_5519_);
v___x_5521_ = v___x_5435_;
goto v_reusejp_5520_;
}
else
{
lean_object* v_reuseFailAlloc_5522_; 
v_reuseFailAlloc_5522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5522_, 0, v___x_5519_);
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
lean_dec(v_a_5431_);
lean_dec_ref(v___x_5421_);
lean_dec_ref(v___x_5418_);
lean_dec_ref(v_args2_5410_);
lean_dec_ref(v___x_5409_);
lean_dec(v_us_5405_);
v_a_5524_ = lean_ctor_get(v___x_5432_, 0);
v_isSharedCheck_5531_ = !lean_is_exclusive(v___x_5432_);
if (v_isSharedCheck_5531_ == 0)
{
v___x_5526_ = v___x_5432_;
v_isShared_5527_ = v_isSharedCheck_5531_;
goto v_resetjp_5525_;
}
else
{
lean_inc(v_a_5524_);
lean_dec(v___x_5432_);
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
lean_dec_ref(v___x_5421_);
lean_dec_ref(v___x_5418_);
lean_dec_ref(v___x_5417_);
lean_dec_ref(v_args2_5410_);
lean_dec_ref(v___x_5409_);
lean_dec(v_us_5405_);
v_a_5532_ = lean_ctor_get(v___x_5430_, 0);
v_isSharedCheck_5539_ = !lean_is_exclusive(v___x_5430_);
if (v_isSharedCheck_5539_ == 0)
{
v___x_5534_ = v___x_5430_;
v_isShared_5535_ = v_isSharedCheck_5539_;
goto v_resetjp_5533_;
}
else
{
lean_inc(v_a_5532_);
lean_dec(v___x_5430_);
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
lean_dec(v___x_5428_);
lean_dec_ref(v___x_5421_);
lean_dec(v_a_5420_);
lean_dec_ref(v___x_5418_);
lean_dec_ref(v___x_5417_);
lean_dec_ref(v_args2_5410_);
lean_dec_ref(v___x_5409_);
lean_dec(v_us_5405_);
v___x_5540_ = lean_box(0);
if (v_isShared_5427_ == 0)
{
lean_ctor_set(v___x_5426_, 0, v___x_5540_);
v___x_5542_ = v___x_5426_;
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
lean_dec_ref(v___x_5421_);
lean_dec(v_a_5420_);
lean_dec_ref(v___x_5418_);
lean_dec_ref(v___x_5417_);
lean_dec_ref(v_args2_5410_);
lean_dec_ref(v___x_5409_);
lean_dec(v_us_5405_);
v_a_5545_ = lean_ctor_get(v___x_5423_, 0);
v_isSharedCheck_5552_ = !lean_is_exclusive(v___x_5423_);
if (v_isSharedCheck_5552_ == 0)
{
v___x_5547_ = v___x_5423_;
v_isShared_5548_ = v_isSharedCheck_5552_;
goto v_resetjp_5546_;
}
else
{
lean_inc(v_a_5545_);
lean_dec(v___x_5423_);
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
lean_dec_ref(v___x_5418_);
lean_dec_ref(v___x_5417_);
lean_dec_ref(v_args2_5410_);
lean_dec_ref(v___x_5409_);
lean_dec(v_numParams_5408_);
lean_dec(v___x_5407_);
lean_dec(v_us_5405_);
v_a_5553_ = lean_ctor_get(v___x_5419_, 0);
v_isSharedCheck_5560_ = !lean_is_exclusive(v___x_5419_);
if (v_isSharedCheck_5560_ == 0)
{
v___x_5555_ = v___x_5419_;
v_isShared_5556_ = v_isSharedCheck_5560_;
goto v_resetjp_5554_;
}
else
{
lean_inc(v_a_5553_);
lean_dec(v___x_5419_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0___boxed(lean_object* v_name_5561_, lean_object* v_us_5562_, lean_object* v_args1_5563_, lean_object* v___x_5564_, lean_object* v_numParams_5565_, lean_object* v___x_5566_, lean_object* v_args2_5567_, lean_object* v___y_5568_, lean_object* v___y_5569_, lean_object* v___y_5570_, lean_object* v___y_5571_, lean_object* v___y_5572_){
_start:
{
lean_object* v_res_5573_; 
v_res_5573_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0(v_name_5561_, v_us_5562_, v_args1_5563_, v___x_5564_, v_numParams_5565_, v___x_5566_, v_args2_5567_, v___y_5568_, v___y_5569_, v___y_5570_, v___y_5571_);
lean_dec(v___y_5571_);
lean_dec_ref(v___y_5570_);
lean_dec(v___y_5569_);
lean_dec_ref(v___y_5568_);
lean_dec_ref(v_args1_5563_);
return v_res_5573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1(lean_object* v_numParams_5574_, lean_object* v_name_5575_, lean_object* v_us_5576_, lean_object* v_ctorVal_5577_, lean_object* v_a_5578_, lean_object* v_args1_5579_, lean_object* v_x_5580_, lean_object* v___y_5581_, lean_object* v___y_5582_, lean_object* v___y_5583_, lean_object* v___y_5584_){
_start:
{
lean_object* v___x_5586_; lean_object* v___x_5587_; lean_object* v___f_5588_; lean_object* v___x_5589_; lean_object* v___x_5590_; lean_object* v___x_5591_; 
v___x_5586_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_5574_);
lean_inc_ref_n(v_args1_5579_, 3);
v___x_5587_ = l_Array_toSubarray___redArg(v_args1_5579_, v___x_5586_, v_numParams_5574_);
v___f_5588_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0___boxed), 12, 6);
lean_closure_set(v___f_5588_, 0, v_name_5575_);
lean_closure_set(v___f_5588_, 1, v_us_5576_);
lean_closure_set(v___f_5588_, 2, v_args1_5579_);
lean_closure_set(v___f_5588_, 3, v___x_5586_);
lean_closure_set(v___f_5588_, 4, v_numParams_5574_);
lean_closure_set(v___f_5588_, 5, v___x_5587_);
v___x_5589_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_5590_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___boxed), 11, 6);
lean_closure_set(v___x_5590_, 0, v_ctorVal_5577_);
lean_closure_set(v___x_5590_, 1, v_args1_5579_);
lean_closure_set(v___x_5590_, 2, v___f_5588_);
lean_closure_set(v___x_5590_, 3, v___x_5586_);
lean_closure_set(v___x_5590_, 4, v_a_5578_);
lean_closure_set(v___x_5590_, 5, v___x_5589_);
v___x_5591_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v_args1_5579_, v___x_5590_, v___y_5581_, v___y_5582_, v___y_5583_, v___y_5584_);
return v___x_5591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1___boxed(lean_object* v_numParams_5592_, lean_object* v_name_5593_, lean_object* v_us_5594_, lean_object* v_ctorVal_5595_, lean_object* v_a_5596_, lean_object* v_args1_5597_, lean_object* v_x_5598_, lean_object* v___y_5599_, lean_object* v___y_5600_, lean_object* v___y_5601_, lean_object* v___y_5602_, lean_object* v___y_5603_){
_start:
{
lean_object* v_res_5604_; 
v_res_5604_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1(v_numParams_5592_, v_name_5593_, v_us_5594_, v_ctorVal_5595_, v_a_5596_, v_args1_5597_, v_x_5598_, v___y_5599_, v___y_5600_, v___y_5601_, v___y_5602_);
lean_dec(v___y_5602_);
lean_dec_ref(v___y_5601_);
lean_dec(v___y_5600_);
lean_dec_ref(v___y_5599_);
lean_dec_ref(v_x_5598_);
return v_res_5604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(lean_object* v_ctorVal_5605_, lean_object* v_a_5606_, lean_object* v_a_5607_, lean_object* v_a_5608_, lean_object* v_a_5609_){
_start:
{
lean_object* v_toConstantVal_5611_; lean_object* v_numParams_5612_; lean_object* v_name_5613_; lean_object* v_levelParams_5614_; lean_object* v_type_5615_; lean_object* v___x_5616_; 
v_toConstantVal_5611_ = lean_ctor_get(v_ctorVal_5605_, 0);
v_numParams_5612_ = lean_ctor_get(v_ctorVal_5605_, 3);
lean_inc(v_numParams_5612_);
v_name_5613_ = lean_ctor_get(v_toConstantVal_5611_, 0);
lean_inc(v_name_5613_);
v_levelParams_5614_ = lean_ctor_get(v_toConstantVal_5611_, 1);
v_type_5615_ = lean_ctor_get(v_toConstantVal_5611_, 2);
lean_inc_ref(v_type_5615_);
v___x_5616_ = l_Lean_Meta_elimOptParam(v_type_5615_, v_a_5608_, v_a_5609_);
if (lean_obj_tag(v___x_5616_) == 0)
{
lean_object* v_a_5617_; lean_object* v___x_5618_; lean_object* v_us_5619_; lean_object* v___f_5620_; uint8_t v___x_5621_; lean_object* v___x_5622_; 
v_a_5617_ = lean_ctor_get(v___x_5616_, 0);
lean_inc_n(v_a_5617_, 2);
lean_dec_ref_known(v___x_5616_, 1);
v___x_5618_ = lean_box(0);
lean_inc(v_levelParams_5614_);
v_us_5619_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(v_levelParams_5614_, v___x_5618_);
v___f_5620_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1___boxed), 12, 5);
lean_closure_set(v___f_5620_, 0, v_numParams_5612_);
lean_closure_set(v___f_5620_, 1, v_name_5613_);
lean_closure_set(v___f_5620_, 2, v_us_5619_);
lean_closure_set(v___f_5620_, 3, v_ctorVal_5605_);
lean_closure_set(v___f_5620_, 4, v_a_5617_);
v___x_5621_ = 0;
v___x_5622_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_a_5617_, v___f_5620_, v___x_5621_, v_a_5606_, v_a_5607_, v_a_5608_, v_a_5609_);
return v___x_5622_;
}
else
{
lean_object* v_a_5623_; lean_object* v___x_5625_; uint8_t v_isShared_5626_; uint8_t v_isSharedCheck_5630_; 
lean_dec(v_name_5613_);
lean_dec(v_numParams_5612_);
lean_dec_ref(v_ctorVal_5605_);
v_a_5623_ = lean_ctor_get(v___x_5616_, 0);
v_isSharedCheck_5630_ = !lean_is_exclusive(v___x_5616_);
if (v_isSharedCheck_5630_ == 0)
{
v___x_5625_ = v___x_5616_;
v_isShared_5626_ = v_isSharedCheck_5630_;
goto v_resetjp_5624_;
}
else
{
lean_inc(v_a_5623_);
lean_dec(v___x_5616_);
v___x_5625_ = lean_box(0);
v_isShared_5626_ = v_isSharedCheck_5630_;
goto v_resetjp_5624_;
}
v_resetjp_5624_:
{
lean_object* v___x_5628_; 
if (v_isShared_5626_ == 0)
{
v___x_5628_ = v___x_5625_;
goto v_reusejp_5627_;
}
else
{
lean_object* v_reuseFailAlloc_5629_; 
v_reuseFailAlloc_5629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5629_, 0, v_a_5623_);
v___x_5628_ = v_reuseFailAlloc_5629_;
goto v_reusejp_5627_;
}
v_reusejp_5627_:
{
return v___x_5628_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___boxed(lean_object* v_ctorVal_5631_, lean_object* v_a_5632_, lean_object* v_a_5633_, lean_object* v_a_5634_, lean_object* v_a_5635_, lean_object* v_a_5636_){
_start:
{
lean_object* v_res_5637_; 
v_res_5637_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(v_ctorVal_5631_, v_a_5632_, v_a_5633_, v_a_5634_, v_a_5635_);
lean_dec(v_a_5635_);
lean_dec_ref(v_a_5634_);
lean_dec(v_a_5633_);
lean_dec_ref(v_a_5632_);
return v_res_5637_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1(void){
_start:
{
lean_object* v___x_5639_; lean_object* v___x_5640_; 
v___x_5639_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__0));
v___x_5640_ = l_Lean_stringToMessageData(v___x_5639_);
return v___x_5640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(lean_object* v_ctorVal_5641_, lean_object* v_a_5642_, lean_object* v_a_5643_, lean_object* v_a_5644_, lean_object* v_a_5645_){
_start:
{
lean_object* v_toConstantVal_5647_; lean_object* v_name_5648_; lean_object* v___x_5649_; lean_object* v___x_5650_; lean_object* v___x_5651_; lean_object* v___x_5652_; lean_object* v___x_5653_; lean_object* v___x_5654_; 
v_toConstantVal_5647_ = lean_ctor_get(v_ctorVal_5641_, 0);
lean_inc_ref(v_toConstantVal_5647_);
lean_dec_ref(v_ctorVal_5641_);
v_name_5648_ = lean_ctor_get(v_toConstantVal_5647_, 0);
lean_inc(v_name_5648_);
lean_dec_ref(v_toConstantVal_5647_);
v___x_5649_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1);
v___x_5650_ = l_Lean_MessageData_ofName(v_name_5648_);
v___x_5651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5651_, 0, v___x_5649_);
lean_ctor_set(v___x_5651_, 1, v___x_5650_);
v___x_5652_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_5653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5653_, 0, v___x_5651_);
lean_ctor_set(v___x_5653_, 1, v___x_5652_);
v___x_5654_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_5653_, v_a_5642_, v_a_5643_, v_a_5644_, v_a_5645_);
return v___x_5654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___boxed(lean_object* v_ctorVal_5655_, lean_object* v_a_5656_, lean_object* v_a_5657_, lean_object* v_a_5658_, lean_object* v_a_5659_, lean_object* v_a_5660_){
_start:
{
lean_object* v_res_5661_; 
v_res_5661_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5655_, v_a_5656_, v_a_5657_, v_a_5658_, v_a_5659_);
lean_dec(v_a_5659_);
lean_dec_ref(v_a_5658_);
lean_dec(v_a_5657_);
lean_dec_ref(v_a_5656_);
return v_res_5661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj(lean_object* v_00_u03b1_5662_, lean_object* v_ctorVal_5663_, lean_object* v_a_5664_, lean_object* v_a_5665_, lean_object* v_a_5666_, lean_object* v_a_5667_){
_start:
{
lean_object* v___x_5669_; 
v___x_5669_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5663_, v_a_5664_, v_a_5665_, v_a_5666_, v_a_5667_);
return v___x_5669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___boxed(lean_object* v_00_u03b1_5670_, lean_object* v_ctorVal_5671_, lean_object* v_a_5672_, lean_object* v_a_5673_, lean_object* v_a_5674_, lean_object* v_a_5675_, lean_object* v_a_5676_){
_start:
{
lean_object* v_res_5677_; 
v_res_5677_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj(v_00_u03b1_5670_, v_ctorVal_5671_, v_a_5672_, v_a_5673_, v_a_5674_, v_a_5675_);
lean_dec(v_a_5675_);
lean_dec_ref(v_a_5674_);
lean_dec(v_a_5673_);
lean_dec_ref(v_a_5672_);
return v_res_5677_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(lean_object* v_ctorVal_5683_, size_t v_sz_5684_, size_t v_i_5685_, lean_object* v_bs_5686_, lean_object* v___y_5687_, lean_object* v___y_5688_, lean_object* v___y_5689_, lean_object* v___y_5690_){
_start:
{
uint8_t v___x_5692_; 
v___x_5692_ = lean_usize_dec_lt(v_i_5685_, v_sz_5684_);
if (v___x_5692_ == 0)
{
lean_object* v___x_5693_; 
lean_dec_ref(v_ctorVal_5683_);
v___x_5693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5693_, 0, v_bs_5686_);
return v___x_5693_;
}
else
{
lean_object* v_v_5694_; lean_object* v___x_5695_; 
v_v_5694_ = lean_array_uget_borrowed(v_bs_5686_, v_i_5685_);
lean_inc(v___y_5690_);
lean_inc_ref(v___y_5689_);
lean_inc(v___y_5688_);
lean_inc_ref(v___y_5687_);
lean_inc(v_v_5694_);
v___x_5695_ = lean_infer_type(v_v_5694_, v___y_5687_, v___y_5688_, v___y_5689_, v___y_5690_);
if (lean_obj_tag(v___x_5695_) == 0)
{
lean_object* v_a_5696_; lean_object* v___x_5697_; 
v_a_5696_ = lean_ctor_get(v___x_5695_, 0);
lean_inc(v_a_5696_);
lean_dec_ref_known(v___x_5695_, 1);
v___x_5697_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_5696_, v___y_5688_);
if (lean_obj_tag(v___x_5697_) == 0)
{
lean_object* v_a_5698_; lean_object* v___x_5699_; lean_object* v_bs_x27_5700_; lean_object* v_a_5702_; lean_object* v___y_5708_; lean_object* v_lhs_5719_; lean_object* v_rhs_5720_; lean_object* v___x_5722_; uint8_t v___x_5723_; 
v_a_5698_ = lean_ctor_get(v___x_5697_, 0);
lean_inc(v_a_5698_);
lean_dec_ref_known(v___x_5697_, 1);
v___x_5699_ = lean_unsigned_to_nat(0u);
v_bs_x27_5700_ = lean_array_uset(v_bs_5686_, v_i_5685_, v___x_5699_);
v___x_5722_ = l_Lean_Expr_cleanupAnnotations(v_a_5698_);
v___x_5723_ = l_Lean_Expr_isApp(v___x_5722_);
if (v___x_5723_ == 0)
{
lean_object* v___x_5724_; 
lean_dec_ref(v___x_5722_);
lean_inc_ref(v_ctorVal_5683_);
v___x_5724_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5683_, v___y_5687_, v___y_5688_, v___y_5689_, v___y_5690_);
v___y_5708_ = v___x_5724_;
goto v___jp_5707_;
}
else
{
lean_object* v_arg_5725_; lean_object* v___x_5726_; uint8_t v___x_5727_; 
v_arg_5725_ = lean_ctor_get(v___x_5722_, 1);
lean_inc_ref(v_arg_5725_);
v___x_5726_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5722_);
v___x_5727_ = l_Lean_Expr_isApp(v___x_5726_);
if (v___x_5727_ == 0)
{
lean_object* v___x_5728_; 
lean_dec_ref(v___x_5726_);
lean_dec_ref(v_arg_5725_);
lean_inc_ref(v_ctorVal_5683_);
v___x_5728_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5683_, v___y_5687_, v___y_5688_, v___y_5689_, v___y_5690_);
v___y_5708_ = v___x_5728_;
goto v___jp_5707_;
}
else
{
lean_object* v_arg_5729_; lean_object* v___x_5730_; uint8_t v___x_5731_; 
v_arg_5729_ = lean_ctor_get(v___x_5726_, 1);
lean_inc_ref(v_arg_5729_);
v___x_5730_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5726_);
v___x_5731_ = l_Lean_Expr_isApp(v___x_5730_);
if (v___x_5731_ == 0)
{
lean_object* v___x_5732_; 
lean_dec_ref(v___x_5730_);
lean_dec_ref(v_arg_5729_);
lean_dec_ref(v_arg_5725_);
lean_inc_ref(v_ctorVal_5683_);
v___x_5732_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5683_, v___y_5687_, v___y_5688_, v___y_5689_, v___y_5690_);
v___y_5708_ = v___x_5732_;
goto v___jp_5707_;
}
else
{
lean_object* v_arg_5733_; lean_object* v___x_5734_; lean_object* v___x_5735_; uint8_t v___x_5736_; 
v_arg_5733_ = lean_ctor_get(v___x_5730_, 1);
lean_inc_ref(v_arg_5733_);
v___x_5734_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5730_);
v___x_5735_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__0));
v___x_5736_ = l_Lean_Expr_isConstOf(v___x_5734_, v___x_5735_);
if (v___x_5736_ == 0)
{
uint8_t v___x_5737_; 
lean_dec_ref(v_arg_5729_);
v___x_5737_ = l_Lean_Expr_isApp(v___x_5734_);
if (v___x_5737_ == 0)
{
lean_object* v___x_5738_; 
lean_dec_ref(v___x_5734_);
lean_dec_ref(v_arg_5733_);
lean_dec_ref(v_arg_5725_);
lean_inc_ref(v_ctorVal_5683_);
v___x_5738_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5683_, v___y_5687_, v___y_5688_, v___y_5689_, v___y_5690_);
v___y_5708_ = v___x_5738_;
goto v___jp_5707_;
}
else
{
lean_object* v___x_5739_; lean_object* v___x_5740_; uint8_t v___x_5741_; 
v___x_5739_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5734_);
v___x_5740_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__2));
v___x_5741_ = l_Lean_Expr_isConstOf(v___x_5739_, v___x_5740_);
lean_dec_ref(v___x_5739_);
if (v___x_5741_ == 0)
{
lean_object* v___x_5742_; 
lean_dec_ref(v_arg_5733_);
lean_dec_ref(v_arg_5725_);
lean_inc_ref(v_ctorVal_5683_);
v___x_5742_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5683_, v___y_5687_, v___y_5688_, v___y_5689_, v___y_5690_);
v___y_5708_ = v___x_5742_;
goto v___jp_5707_;
}
else
{
v_lhs_5719_ = v_arg_5733_;
v_rhs_5720_ = v_arg_5725_;
goto v___jp_5718_;
}
}
}
else
{
lean_dec_ref(v___x_5734_);
lean_dec_ref(v_arg_5733_);
v_lhs_5719_ = v_arg_5729_;
v_rhs_5720_ = v_arg_5725_;
goto v___jp_5718_;
}
}
}
}
v___jp_5701_:
{
size_t v___x_5703_; size_t v___x_5704_; lean_object* v___x_5705_; 
v___x_5703_ = ((size_t)1ULL);
v___x_5704_ = lean_usize_add(v_i_5685_, v___x_5703_);
v___x_5705_ = lean_array_uset(v_bs_x27_5700_, v_i_5685_, v_a_5702_);
v_i_5685_ = v___x_5704_;
v_bs_5686_ = v___x_5705_;
goto _start;
}
v___jp_5707_:
{
if (lean_obj_tag(v___y_5708_) == 0)
{
lean_object* v_a_5709_; 
v_a_5709_ = lean_ctor_get(v___y_5708_, 0);
lean_inc(v_a_5709_);
lean_dec_ref_known(v___y_5708_, 1);
v_a_5702_ = v_a_5709_;
goto v___jp_5701_;
}
else
{
lean_object* v_a_5710_; lean_object* v___x_5712_; uint8_t v_isShared_5713_; uint8_t v_isSharedCheck_5717_; 
lean_dec_ref(v_bs_x27_5700_);
lean_dec_ref(v_ctorVal_5683_);
v_a_5710_ = lean_ctor_get(v___y_5708_, 0);
v_isSharedCheck_5717_ = !lean_is_exclusive(v___y_5708_);
if (v_isSharedCheck_5717_ == 0)
{
v___x_5712_ = v___y_5708_;
v_isShared_5713_ = v_isSharedCheck_5717_;
goto v_resetjp_5711_;
}
else
{
lean_inc(v_a_5710_);
lean_dec(v___y_5708_);
v___x_5712_ = lean_box(0);
v_isShared_5713_ = v_isSharedCheck_5717_;
goto v_resetjp_5711_;
}
v_resetjp_5711_:
{
lean_object* v___x_5715_; 
if (v_isShared_5713_ == 0)
{
v___x_5715_ = v___x_5712_;
goto v_reusejp_5714_;
}
else
{
lean_object* v_reuseFailAlloc_5716_; 
v_reuseFailAlloc_5716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5716_, 0, v_a_5710_);
v___x_5715_ = v_reuseFailAlloc_5716_;
goto v_reusejp_5714_;
}
v_reusejp_5714_:
{
return v___x_5715_;
}
}
}
}
v___jp_5718_:
{
lean_object* v___x_5721_; 
v___x_5721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5721_, 0, v_lhs_5719_);
lean_ctor_set(v___x_5721_, 1, v_rhs_5720_);
v_a_5702_ = v___x_5721_;
goto v___jp_5701_;
}
}
else
{
lean_object* v_a_5743_; lean_object* v___x_5745_; uint8_t v_isShared_5746_; uint8_t v_isSharedCheck_5750_; 
lean_dec_ref(v_bs_5686_);
lean_dec_ref(v_ctorVal_5683_);
v_a_5743_ = lean_ctor_get(v___x_5697_, 0);
v_isSharedCheck_5750_ = !lean_is_exclusive(v___x_5697_);
if (v_isSharedCheck_5750_ == 0)
{
v___x_5745_ = v___x_5697_;
v_isShared_5746_ = v_isSharedCheck_5750_;
goto v_resetjp_5744_;
}
else
{
lean_inc(v_a_5743_);
lean_dec(v___x_5697_);
v___x_5745_ = lean_box(0);
v_isShared_5746_ = v_isSharedCheck_5750_;
goto v_resetjp_5744_;
}
v_resetjp_5744_:
{
lean_object* v___x_5748_; 
if (v_isShared_5746_ == 0)
{
v___x_5748_ = v___x_5745_;
goto v_reusejp_5747_;
}
else
{
lean_object* v_reuseFailAlloc_5749_; 
v_reuseFailAlloc_5749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5749_, 0, v_a_5743_);
v___x_5748_ = v_reuseFailAlloc_5749_;
goto v_reusejp_5747_;
}
v_reusejp_5747_:
{
return v___x_5748_;
}
}
}
}
else
{
lean_object* v_a_5751_; lean_object* v___x_5753_; uint8_t v_isShared_5754_; uint8_t v_isSharedCheck_5758_; 
lean_dec_ref(v_bs_5686_);
lean_dec_ref(v_ctorVal_5683_);
v_a_5751_ = lean_ctor_get(v___x_5695_, 0);
v_isSharedCheck_5758_ = !lean_is_exclusive(v___x_5695_);
if (v_isSharedCheck_5758_ == 0)
{
v___x_5753_ = v___x_5695_;
v_isShared_5754_ = v_isSharedCheck_5758_;
goto v_resetjp_5752_;
}
else
{
lean_inc(v_a_5751_);
lean_dec(v___x_5695_);
v___x_5753_ = lean_box(0);
v_isShared_5754_ = v_isSharedCheck_5758_;
goto v_resetjp_5752_;
}
v_resetjp_5752_:
{
lean_object* v___x_5756_; 
if (v_isShared_5754_ == 0)
{
v___x_5756_ = v___x_5753_;
goto v_reusejp_5755_;
}
else
{
lean_object* v_reuseFailAlloc_5757_; 
v_reuseFailAlloc_5757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5757_, 0, v_a_5751_);
v___x_5756_ = v_reuseFailAlloc_5757_;
goto v_reusejp_5755_;
}
v_reusejp_5755_:
{
return v___x_5756_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___boxed(lean_object* v_ctorVal_5759_, lean_object* v_sz_5760_, lean_object* v_i_5761_, lean_object* v_bs_5762_, lean_object* v___y_5763_, lean_object* v___y_5764_, lean_object* v___y_5765_, lean_object* v___y_5766_, lean_object* v___y_5767_){
_start:
{
size_t v_sz_boxed_5768_; size_t v_i_boxed_5769_; lean_object* v_res_5770_; 
v_sz_boxed_5768_ = lean_unbox_usize(v_sz_5760_);
lean_dec(v_sz_5760_);
v_i_boxed_5769_ = lean_unbox_usize(v_i_5761_);
lean_dec(v_i_5761_);
v_res_5770_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(v_ctorVal_5759_, v_sz_boxed_5768_, v_i_boxed_5769_, v_bs_5762_, v___y_5763_, v___y_5764_, v___y_5765_, v___y_5766_);
lean_dec(v___y_5766_);
lean_dec_ref(v___y_5765_);
lean_dec(v___y_5764_);
lean_dec_ref(v___y_5763_);
return v_res_5770_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5772_; lean_object* v___x_5773_; 
v___x_5772_ = lean_unsigned_to_nat(0u);
v___x_5773_ = l_Lean_Level_ofNat(v___x_5772_);
return v___x_5773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0(lean_object* v_ctorVal_5774_, lean_object* v_us_5775_, lean_object* v_numIndices_5776_, lean_object* v_xs_5777_, lean_object* v_type_5778_, lean_object* v___y_5779_, lean_object* v___y_5780_, lean_object* v___y_5781_, lean_object* v___y_5782_){
_start:
{
lean_object* v_toConstantVal_5784_; lean_object* v_induct_5785_; lean_object* v_numParams_5786_; lean_object* v___x_5787_; lean_object* v_noConfusionName_5788_; lean_object* v___x_5789_; lean_object* v___x_5790_; lean_object* v___x_5791_; lean_object* v_noConfusion_5792_; lean_object* v_noConfusion_5793_; lean_object* v_lower_5795_; lean_object* v_upper_5796_; lean_object* v___x_5903_; lean_object* v___x_5904_; lean_object* v___x_5905_; lean_object* v___x_5906_; lean_object* v_n_5907_; uint8_t v___x_5908_; 
v_toConstantVal_5784_ = lean_ctor_get(v_ctorVal_5774_, 0);
v_induct_5785_ = lean_ctor_get(v_ctorVal_5774_, 1);
v_numParams_5786_ = lean_ctor_get(v_ctorVal_5774_, 3);
v___x_5787_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__0));
lean_inc(v_induct_5785_);
v_noConfusionName_5788_ = l_Lean_Name_str___override(v_induct_5785_, v___x_5787_);
v___x_5789_ = lean_unsigned_to_nat(0u);
v___x_5790_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1);
v___x_5791_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5791_, 0, v___x_5790_);
lean_ctor_set(v___x_5791_, 1, v_us_5775_);
v_noConfusion_5792_ = l_Lean_mkConst(v_noConfusionName_5788_, v___x_5791_);
v_noConfusion_5793_ = l_Lean_Expr_app___override(v_noConfusion_5792_, v_type_5778_);
v___x_5903_ = lean_array_get_size(v_xs_5777_);
v___x_5904_ = lean_nat_sub(v___x_5903_, v_numParams_5786_);
v___x_5905_ = lean_nat_sub(v___x_5904_, v_numIndices_5776_);
lean_dec(v___x_5904_);
v___x_5906_ = lean_unsigned_to_nat(1u);
v_n_5907_ = lean_nat_sub(v___x_5905_, v___x_5906_);
lean_dec(v___x_5905_);
v___x_5908_ = lean_nat_dec_le(v_n_5907_, v___x_5789_);
if (v___x_5908_ == 0)
{
v_lower_5795_ = v_n_5907_;
v_upper_5796_ = v___x_5903_;
goto v___jp_5794_;
}
else
{
lean_dec(v_n_5907_);
v_lower_5795_ = v___x_5789_;
v_upper_5796_ = v___x_5903_;
goto v___jp_5794_;
}
v___jp_5794_:
{
lean_object* v___x_5797_; lean_object* v___x_5798_; lean_object* v_eqs_5799_; size_t v_sz_5800_; size_t v___x_5801_; lean_object* v___x_5802_; 
lean_inc_ref(v_xs_5777_);
v___x_5797_ = l_Array_toSubarray___redArg(v_xs_5777_, v_lower_5795_, v_upper_5796_);
v___x_5798_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v_eqs_5799_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(v___x_5797_, v___x_5798_);
v_sz_5800_ = lean_array_size(v_eqs_5799_);
v___x_5801_ = ((size_t)0ULL);
lean_inc_ref(v_eqs_5799_);
lean_inc_ref(v_ctorVal_5774_);
v___x_5802_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(v_ctorVal_5774_, v_sz_5800_, v___x_5801_, v_eqs_5799_, v___y_5779_, v___y_5780_, v___y_5781_, v___y_5782_);
if (lean_obj_tag(v___x_5802_) == 0)
{
lean_object* v_a_5803_; lean_object* v___x_5804_; lean_object* v_fst_5805_; lean_object* v_snd_5806_; lean_object* v___x_5807_; lean_object* v___x_5808_; lean_object* v___x_5809_; lean_object* v___x_5810_; 
v_a_5803_ = lean_ctor_get(v___x_5802_, 0);
lean_inc(v_a_5803_);
lean_dec_ref_known(v___x_5802_, 1);
v___x_5804_ = l_Array_unzip___redArg(v_a_5803_);
lean_dec(v_a_5803_);
v_fst_5805_ = lean_ctor_get(v___x_5804_, 0);
lean_inc(v_fst_5805_);
v_snd_5806_ = lean_ctor_get(v___x_5804_, 1);
lean_inc(v_snd_5806_);
lean_dec_ref(v___x_5804_);
v___x_5807_ = l_Lean_mkAppN(v_noConfusion_5793_, v_fst_5805_);
lean_dec(v_fst_5805_);
v___x_5808_ = l_Lean_mkAppN(v___x_5807_, v_snd_5806_);
lean_dec(v_snd_5806_);
v___x_5809_ = l_Lean_mkAppN(v___x_5808_, v_eqs_5799_);
lean_dec_ref(v_eqs_5799_);
lean_inc(v___y_5782_);
lean_inc_ref(v___y_5781_);
lean_inc(v___y_5780_);
lean_inc_ref(v___y_5779_);
lean_inc_ref(v___x_5809_);
v___x_5810_ = lean_infer_type(v___x_5809_, v___y_5779_, v___y_5780_, v___y_5781_, v___y_5782_);
if (lean_obj_tag(v___x_5810_) == 0)
{
lean_object* v_a_5811_; lean_object* v___x_5812_; 
v_a_5811_ = lean_ctor_get(v___x_5810_, 0);
lean_inc(v_a_5811_);
lean_dec_ref_known(v___x_5810_, 1);
lean_inc(v___y_5782_);
lean_inc_ref(v___y_5781_);
lean_inc(v___y_5780_);
lean_inc_ref(v___y_5779_);
v___x_5812_ = lean_whnf(v_a_5811_, v___y_5779_, v___y_5780_, v___y_5781_, v___y_5782_);
if (lean_obj_tag(v___x_5812_) == 0)
{
lean_object* v_a_5813_; 
v_a_5813_ = lean_ctor_get(v___x_5812_, 0);
lean_inc(v_a_5813_);
lean_dec_ref_known(v___x_5812_, 1);
if (lean_obj_tag(v_a_5813_) == 7)
{
lean_object* v_binderType_5814_; lean_object* v___x_5815_; lean_object* v___x_5816_; 
lean_inc_ref(v_toConstantVal_5784_);
lean_dec_ref(v_ctorVal_5774_);
v_binderType_5814_ = lean_ctor_get(v_a_5813_, 1);
lean_inc_ref(v_binderType_5814_);
lean_dec_ref_known(v_a_5813_, 3);
v___x_5815_ = lean_box(0);
v___x_5816_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_binderType_5814_, v___x_5815_, v___y_5779_, v___y_5780_, v___y_5781_, v___y_5782_);
if (lean_obj_tag(v___x_5816_) == 0)
{
lean_object* v_a_5817_; lean_object* v___x_5818_; lean_object* v___x_5819_; 
v_a_5817_ = lean_ctor_get(v___x_5816_, 0);
lean_inc(v_a_5817_);
lean_dec_ref_known(v___x_5816_, 1);
v___x_5818_ = l_Lean_Expr_mvarId_x21(v_a_5817_);
v___x_5819_ = l_Lean_MVarId_intros(v___x_5818_, v___y_5779_, v___y_5780_, v___y_5781_, v___y_5782_);
if (lean_obj_tag(v___x_5819_) == 0)
{
lean_object* v_a_5820_; lean_object* v_snd_5821_; lean_object* v_name_5822_; lean_object* v___x_5823_; 
v_a_5820_ = lean_ctor_get(v___x_5819_, 0);
lean_inc(v_a_5820_);
lean_dec_ref_known(v___x_5819_, 1);
v_snd_5821_ = lean_ctor_get(v_a_5820_, 1);
lean_inc(v_snd_5821_);
lean_dec(v_a_5820_);
v_name_5822_ = lean_ctor_get(v_toConstantVal_5784_, 0);
lean_inc(v_name_5822_);
lean_dec_ref(v_toConstantVal_5784_);
v___x_5823_ = l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(v_snd_5821_, v_name_5822_, v___y_5779_, v___y_5780_, v___y_5781_, v___y_5782_);
if (lean_obj_tag(v___x_5823_) == 0)
{
lean_object* v___x_5824_; lean_object* v___x_5825_; lean_object* v_a_5826_; lean_object* v___x_5828_; uint8_t v_isShared_5829_; uint8_t v_isSharedCheck_5853_; 
lean_dec_ref_known(v___x_5823_, 1);
v___x_5824_ = l_Lean_Expr_app___override(v___x_5809_, v_a_5817_);
v___x_5825_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v___x_5824_, v___y_5780_);
v_a_5826_ = lean_ctor_get(v___x_5825_, 0);
v_isSharedCheck_5853_ = !lean_is_exclusive(v___x_5825_);
if (v_isSharedCheck_5853_ == 0)
{
v___x_5828_ = v___x_5825_;
v_isShared_5829_ = v_isSharedCheck_5853_;
goto v_resetjp_5827_;
}
else
{
lean_inc(v_a_5826_);
lean_dec(v___x_5825_);
v___x_5828_ = lean_box(0);
v_isShared_5829_ = v_isSharedCheck_5853_;
goto v_resetjp_5827_;
}
v_resetjp_5827_:
{
uint8_t v___x_5830_; uint8_t v___x_5831_; uint8_t v___x_5832_; lean_object* v___x_5833_; 
v___x_5830_ = 0;
v___x_5831_ = 1;
v___x_5832_ = 1;
v___x_5833_ = l_Lean_Meta_mkLambdaFVars(v_xs_5777_, v_a_5826_, v___x_5830_, v___x_5831_, v___x_5830_, v___x_5831_, v___x_5832_, v___y_5779_, v___y_5780_, v___y_5781_, v___y_5782_);
lean_dec_ref(v_xs_5777_);
if (lean_obj_tag(v___x_5833_) == 0)
{
lean_object* v_a_5834_; lean_object* v___x_5836_; uint8_t v_isShared_5837_; uint8_t v_isSharedCheck_5844_; 
v_a_5834_ = lean_ctor_get(v___x_5833_, 0);
v_isSharedCheck_5844_ = !lean_is_exclusive(v___x_5833_);
if (v_isSharedCheck_5844_ == 0)
{
v___x_5836_ = v___x_5833_;
v_isShared_5837_ = v_isSharedCheck_5844_;
goto v_resetjp_5835_;
}
else
{
lean_inc(v_a_5834_);
lean_dec(v___x_5833_);
v___x_5836_ = lean_box(0);
v_isShared_5837_ = v_isSharedCheck_5844_;
goto v_resetjp_5835_;
}
v_resetjp_5835_:
{
lean_object* v___x_5839_; 
if (v_isShared_5829_ == 0)
{
lean_ctor_set_tag(v___x_5828_, 1);
lean_ctor_set(v___x_5828_, 0, v_a_5834_);
v___x_5839_ = v___x_5828_;
goto v_reusejp_5838_;
}
else
{
lean_object* v_reuseFailAlloc_5843_; 
v_reuseFailAlloc_5843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5843_, 0, v_a_5834_);
v___x_5839_ = v_reuseFailAlloc_5843_;
goto v_reusejp_5838_;
}
v_reusejp_5838_:
{
lean_object* v___x_5841_; 
if (v_isShared_5837_ == 0)
{
lean_ctor_set(v___x_5836_, 0, v___x_5839_);
v___x_5841_ = v___x_5836_;
goto v_reusejp_5840_;
}
else
{
lean_object* v_reuseFailAlloc_5842_; 
v_reuseFailAlloc_5842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5842_, 0, v___x_5839_);
v___x_5841_ = v_reuseFailAlloc_5842_;
goto v_reusejp_5840_;
}
v_reusejp_5840_:
{
return v___x_5841_;
}
}
}
}
else
{
lean_object* v_a_5845_; lean_object* v___x_5847_; uint8_t v_isShared_5848_; uint8_t v_isSharedCheck_5852_; 
lean_del_object(v___x_5828_);
v_a_5845_ = lean_ctor_get(v___x_5833_, 0);
v_isSharedCheck_5852_ = !lean_is_exclusive(v___x_5833_);
if (v_isSharedCheck_5852_ == 0)
{
v___x_5847_ = v___x_5833_;
v_isShared_5848_ = v_isSharedCheck_5852_;
goto v_resetjp_5846_;
}
else
{
lean_inc(v_a_5845_);
lean_dec(v___x_5833_);
v___x_5847_ = lean_box(0);
v_isShared_5848_ = v_isSharedCheck_5852_;
goto v_resetjp_5846_;
}
v_resetjp_5846_:
{
lean_object* v___x_5850_; 
if (v_isShared_5848_ == 0)
{
v___x_5850_ = v___x_5847_;
goto v_reusejp_5849_;
}
else
{
lean_object* v_reuseFailAlloc_5851_; 
v_reuseFailAlloc_5851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5851_, 0, v_a_5845_);
v___x_5850_ = v_reuseFailAlloc_5851_;
goto v_reusejp_5849_;
}
v_reusejp_5849_:
{
return v___x_5850_;
}
}
}
}
}
else
{
lean_object* v_a_5854_; lean_object* v___x_5856_; uint8_t v_isShared_5857_; uint8_t v_isSharedCheck_5861_; 
lean_dec(v_a_5817_);
lean_dec_ref(v___x_5809_);
lean_dec_ref(v_xs_5777_);
v_a_5854_ = lean_ctor_get(v___x_5823_, 0);
v_isSharedCheck_5861_ = !lean_is_exclusive(v___x_5823_);
if (v_isSharedCheck_5861_ == 0)
{
v___x_5856_ = v___x_5823_;
v_isShared_5857_ = v_isSharedCheck_5861_;
goto v_resetjp_5855_;
}
else
{
lean_inc(v_a_5854_);
lean_dec(v___x_5823_);
v___x_5856_ = lean_box(0);
v_isShared_5857_ = v_isSharedCheck_5861_;
goto v_resetjp_5855_;
}
v_resetjp_5855_:
{
lean_object* v___x_5859_; 
if (v_isShared_5857_ == 0)
{
v___x_5859_ = v___x_5856_;
goto v_reusejp_5858_;
}
else
{
lean_object* v_reuseFailAlloc_5860_; 
v_reuseFailAlloc_5860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5860_, 0, v_a_5854_);
v___x_5859_ = v_reuseFailAlloc_5860_;
goto v_reusejp_5858_;
}
v_reusejp_5858_:
{
return v___x_5859_;
}
}
}
}
else
{
lean_object* v_a_5862_; lean_object* v___x_5864_; uint8_t v_isShared_5865_; uint8_t v_isSharedCheck_5869_; 
lean_dec(v_a_5817_);
lean_dec_ref(v___x_5809_);
lean_dec_ref(v_toConstantVal_5784_);
lean_dec_ref(v_xs_5777_);
v_a_5862_ = lean_ctor_get(v___x_5819_, 0);
v_isSharedCheck_5869_ = !lean_is_exclusive(v___x_5819_);
if (v_isSharedCheck_5869_ == 0)
{
v___x_5864_ = v___x_5819_;
v_isShared_5865_ = v_isSharedCheck_5869_;
goto v_resetjp_5863_;
}
else
{
lean_inc(v_a_5862_);
lean_dec(v___x_5819_);
v___x_5864_ = lean_box(0);
v_isShared_5865_ = v_isSharedCheck_5869_;
goto v_resetjp_5863_;
}
v_resetjp_5863_:
{
lean_object* v___x_5867_; 
if (v_isShared_5865_ == 0)
{
v___x_5867_ = v___x_5864_;
goto v_reusejp_5866_;
}
else
{
lean_object* v_reuseFailAlloc_5868_; 
v_reuseFailAlloc_5868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5868_, 0, v_a_5862_);
v___x_5867_ = v_reuseFailAlloc_5868_;
goto v_reusejp_5866_;
}
v_reusejp_5866_:
{
return v___x_5867_;
}
}
}
}
else
{
lean_object* v_a_5870_; lean_object* v___x_5872_; uint8_t v_isShared_5873_; uint8_t v_isSharedCheck_5877_; 
lean_dec_ref(v___x_5809_);
lean_dec_ref(v_toConstantVal_5784_);
lean_dec_ref(v_xs_5777_);
v_a_5870_ = lean_ctor_get(v___x_5816_, 0);
v_isSharedCheck_5877_ = !lean_is_exclusive(v___x_5816_);
if (v_isSharedCheck_5877_ == 0)
{
v___x_5872_ = v___x_5816_;
v_isShared_5873_ = v_isSharedCheck_5877_;
goto v_resetjp_5871_;
}
else
{
lean_inc(v_a_5870_);
lean_dec(v___x_5816_);
v___x_5872_ = lean_box(0);
v_isShared_5873_ = v_isSharedCheck_5877_;
goto v_resetjp_5871_;
}
v_resetjp_5871_:
{
lean_object* v___x_5875_; 
if (v_isShared_5873_ == 0)
{
v___x_5875_ = v___x_5872_;
goto v_reusejp_5874_;
}
else
{
lean_object* v_reuseFailAlloc_5876_; 
v_reuseFailAlloc_5876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5876_, 0, v_a_5870_);
v___x_5875_ = v_reuseFailAlloc_5876_;
goto v_reusejp_5874_;
}
v_reusejp_5874_:
{
return v___x_5875_;
}
}
}
}
else
{
lean_object* v___x_5878_; 
lean_dec(v_a_5813_);
lean_dec_ref(v___x_5809_);
lean_dec_ref(v_xs_5777_);
v___x_5878_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5774_, v___y_5779_, v___y_5780_, v___y_5781_, v___y_5782_);
return v___x_5878_;
}
}
else
{
lean_object* v_a_5879_; lean_object* v___x_5881_; uint8_t v_isShared_5882_; uint8_t v_isSharedCheck_5886_; 
lean_dec_ref(v___x_5809_);
lean_dec_ref(v_xs_5777_);
lean_dec_ref(v_ctorVal_5774_);
v_a_5879_ = lean_ctor_get(v___x_5812_, 0);
v_isSharedCheck_5886_ = !lean_is_exclusive(v___x_5812_);
if (v_isSharedCheck_5886_ == 0)
{
v___x_5881_ = v___x_5812_;
v_isShared_5882_ = v_isSharedCheck_5886_;
goto v_resetjp_5880_;
}
else
{
lean_inc(v_a_5879_);
lean_dec(v___x_5812_);
v___x_5881_ = lean_box(0);
v_isShared_5882_ = v_isSharedCheck_5886_;
goto v_resetjp_5880_;
}
v_resetjp_5880_:
{
lean_object* v___x_5884_; 
if (v_isShared_5882_ == 0)
{
v___x_5884_ = v___x_5881_;
goto v_reusejp_5883_;
}
else
{
lean_object* v_reuseFailAlloc_5885_; 
v_reuseFailAlloc_5885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5885_, 0, v_a_5879_);
v___x_5884_ = v_reuseFailAlloc_5885_;
goto v_reusejp_5883_;
}
v_reusejp_5883_:
{
return v___x_5884_;
}
}
}
}
else
{
lean_object* v_a_5887_; lean_object* v___x_5889_; uint8_t v_isShared_5890_; uint8_t v_isSharedCheck_5894_; 
lean_dec_ref(v___x_5809_);
lean_dec_ref(v_xs_5777_);
lean_dec_ref(v_ctorVal_5774_);
v_a_5887_ = lean_ctor_get(v___x_5810_, 0);
v_isSharedCheck_5894_ = !lean_is_exclusive(v___x_5810_);
if (v_isSharedCheck_5894_ == 0)
{
v___x_5889_ = v___x_5810_;
v_isShared_5890_ = v_isSharedCheck_5894_;
goto v_resetjp_5888_;
}
else
{
lean_inc(v_a_5887_);
lean_dec(v___x_5810_);
v___x_5889_ = lean_box(0);
v_isShared_5890_ = v_isSharedCheck_5894_;
goto v_resetjp_5888_;
}
v_resetjp_5888_:
{
lean_object* v___x_5892_; 
if (v_isShared_5890_ == 0)
{
v___x_5892_ = v___x_5889_;
goto v_reusejp_5891_;
}
else
{
lean_object* v_reuseFailAlloc_5893_; 
v_reuseFailAlloc_5893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5893_, 0, v_a_5887_);
v___x_5892_ = v_reuseFailAlloc_5893_;
goto v_reusejp_5891_;
}
v_reusejp_5891_:
{
return v___x_5892_;
}
}
}
}
else
{
lean_object* v_a_5895_; lean_object* v___x_5897_; uint8_t v_isShared_5898_; uint8_t v_isSharedCheck_5902_; 
lean_dec_ref(v_eqs_5799_);
lean_dec_ref(v_noConfusion_5793_);
lean_dec_ref(v_xs_5777_);
lean_dec_ref(v_ctorVal_5774_);
v_a_5895_ = lean_ctor_get(v___x_5802_, 0);
v_isSharedCheck_5902_ = !lean_is_exclusive(v___x_5802_);
if (v_isSharedCheck_5902_ == 0)
{
v___x_5897_ = v___x_5802_;
v_isShared_5898_ = v_isSharedCheck_5902_;
goto v_resetjp_5896_;
}
else
{
lean_inc(v_a_5895_);
lean_dec(v___x_5802_);
v___x_5897_ = lean_box(0);
v_isShared_5898_ = v_isSharedCheck_5902_;
goto v_resetjp_5896_;
}
v_resetjp_5896_:
{
lean_object* v___x_5900_; 
if (v_isShared_5898_ == 0)
{
v___x_5900_ = v___x_5897_;
goto v_reusejp_5899_;
}
else
{
lean_object* v_reuseFailAlloc_5901_; 
v_reuseFailAlloc_5901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5901_, 0, v_a_5895_);
v___x_5900_ = v_reuseFailAlloc_5901_;
goto v_reusejp_5899_;
}
v_reusejp_5899_:
{
return v___x_5900_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___boxed(lean_object* v_ctorVal_5909_, lean_object* v_us_5910_, lean_object* v_numIndices_5911_, lean_object* v_xs_5912_, lean_object* v_type_5913_, lean_object* v___y_5914_, lean_object* v___y_5915_, lean_object* v___y_5916_, lean_object* v___y_5917_, lean_object* v___y_5918_){
_start:
{
lean_object* v_res_5919_; 
v_res_5919_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0(v_ctorVal_5909_, v_us_5910_, v_numIndices_5911_, v_xs_5912_, v_type_5913_, v___y_5914_, v___y_5915_, v___y_5916_, v___y_5917_);
lean_dec(v___y_5917_);
lean_dec_ref(v___y_5916_);
lean_dec(v___y_5915_);
lean_dec_ref(v___y_5914_);
lean_dec(v_numIndices_5911_);
return v_res_5919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(lean_object* v_ctorVal_5920_, lean_object* v_typeInfo_5921_, lean_object* v_a_5922_, lean_object* v_a_5923_, lean_object* v_a_5924_, lean_object* v_a_5925_){
_start:
{
lean_object* v_thmType_5927_; lean_object* v_us_5928_; lean_object* v_numIndices_5929_; lean_object* v___f_5930_; uint8_t v___x_5931_; lean_object* v___x_5932_; 
v_thmType_5927_ = lean_ctor_get(v_typeInfo_5921_, 0);
lean_inc_ref(v_thmType_5927_);
v_us_5928_ = lean_ctor_get(v_typeInfo_5921_, 1);
lean_inc(v_us_5928_);
v_numIndices_5929_ = lean_ctor_get(v_typeInfo_5921_, 2);
lean_inc(v_numIndices_5929_);
lean_dec_ref(v_typeInfo_5921_);
v___f_5930_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___boxed), 10, 3);
lean_closure_set(v___f_5930_, 0, v_ctorVal_5920_);
lean_closure_set(v___f_5930_, 1, v_us_5928_);
lean_closure_set(v___f_5930_, 2, v_numIndices_5929_);
v___x_5931_ = 0;
v___x_5932_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_thmType_5927_, v___f_5930_, v___x_5931_, v___x_5931_, v_a_5922_, v_a_5923_, v_a_5924_, v_a_5925_);
return v___x_5932_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___boxed(lean_object* v_ctorVal_5933_, lean_object* v_typeInfo_5934_, lean_object* v_a_5935_, lean_object* v_a_5936_, lean_object* v_a_5937_, lean_object* v_a_5938_, lean_object* v_a_5939_){
_start:
{
lean_object* v_res_5940_; 
v_res_5940_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(v_ctorVal_5933_, v_typeInfo_5934_, v_a_5935_, v_a_5936_, v_a_5937_, v_a_5938_);
lean_dec(v_a_5938_);
lean_dec_ref(v_a_5937_);
lean_dec(v_a_5936_);
lean_dec_ref(v_a_5935_);
return v_res_5940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHInjectiveTheoremNameFor(lean_object* v_ctorName_5943_){
_start:
{
lean_object* v___x_5944_; lean_object* v___x_5945_; 
v___x_5944_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0));
v___x_5945_ = l_Lean_Name_str___override(v_ctorName_5943_, v___x_5944_);
return v___x_5945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(lean_object* v_thmName_5946_, lean_object* v_ctorVal_5947_, lean_object* v_a_5948_, lean_object* v_a_5949_, lean_object* v_a_5950_, lean_object* v_a_5951_){
_start:
{
lean_object* v___x_5953_; 
lean_inc_ref(v_ctorVal_5947_);
v___x_5953_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(v_ctorVal_5947_, v_a_5948_, v_a_5949_, v_a_5950_, v_a_5951_);
if (lean_obj_tag(v___x_5953_) == 0)
{
lean_object* v_a_5954_; lean_object* v___x_5956_; uint8_t v_isShared_5957_; uint8_t v_isSharedCheck_6015_; 
v_a_5954_ = lean_ctor_get(v___x_5953_, 0);
v_isSharedCheck_6015_ = !lean_is_exclusive(v___x_5953_);
if (v_isSharedCheck_6015_ == 0)
{
v___x_5956_ = v___x_5953_;
v_isShared_5957_ = v_isSharedCheck_6015_;
goto v_resetjp_5955_;
}
else
{
lean_inc(v_a_5954_);
lean_dec(v___x_5953_);
v___x_5956_ = lean_box(0);
v_isShared_5957_ = v_isSharedCheck_6015_;
goto v_resetjp_5955_;
}
v_resetjp_5955_:
{
if (lean_obj_tag(v_a_5954_) == 1)
{
lean_object* v_val_5958_; lean_object* v___x_5959_; 
lean_del_object(v___x_5956_);
v_val_5958_ = lean_ctor_get(v_a_5954_, 0);
lean_inc_n(v_val_5958_, 2);
lean_dec_ref_known(v_a_5954_, 1);
lean_inc_ref(v_ctorVal_5947_);
v___x_5959_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(v_ctorVal_5947_, v_val_5958_, v_a_5948_, v_a_5949_, v_a_5950_, v_a_5951_);
if (lean_obj_tag(v___x_5959_) == 0)
{
lean_object* v_a_5960_; lean_object* v___x_5962_; uint8_t v_isShared_5963_; uint8_t v_isSharedCheck_6002_; 
v_a_5960_ = lean_ctor_get(v___x_5959_, 0);
v_isSharedCheck_6002_ = !lean_is_exclusive(v___x_5959_);
if (v_isSharedCheck_6002_ == 0)
{
v___x_5962_ = v___x_5959_;
v_isShared_5963_ = v_isSharedCheck_6002_;
goto v_resetjp_5961_;
}
else
{
lean_inc(v_a_5960_);
lean_dec(v___x_5959_);
v___x_5962_ = lean_box(0);
v_isShared_5963_ = v_isSharedCheck_6002_;
goto v_resetjp_5961_;
}
v_resetjp_5961_:
{
if (lean_obj_tag(v_a_5960_) == 1)
{
lean_object* v_toConstantVal_5964_; lean_object* v_val_5965_; lean_object* v___x_5967_; uint8_t v_isShared_5968_; uint8_t v_isSharedCheck_5997_; 
v_toConstantVal_5964_ = lean_ctor_get(v_ctorVal_5947_, 0);
lean_inc_ref(v_toConstantVal_5964_);
lean_dec_ref(v_ctorVal_5947_);
v_val_5965_ = lean_ctor_get(v_a_5960_, 0);
v_isSharedCheck_5997_ = !lean_is_exclusive(v_a_5960_);
if (v_isSharedCheck_5997_ == 0)
{
v___x_5967_ = v_a_5960_;
v_isShared_5968_ = v_isSharedCheck_5997_;
goto v_resetjp_5966_;
}
else
{
lean_inc(v_val_5965_);
lean_dec(v_a_5960_);
v___x_5967_ = lean_box(0);
v_isShared_5968_ = v_isSharedCheck_5997_;
goto v_resetjp_5966_;
}
v_resetjp_5966_:
{
lean_object* v_levelParams_5969_; lean_object* v___x_5971_; uint8_t v_isShared_5972_; uint8_t v_isSharedCheck_5994_; 
v_levelParams_5969_ = lean_ctor_get(v_toConstantVal_5964_, 1);
v_isSharedCheck_5994_ = !lean_is_exclusive(v_toConstantVal_5964_);
if (v_isSharedCheck_5994_ == 0)
{
lean_object* v_unused_5995_; lean_object* v_unused_5996_; 
v_unused_5995_ = lean_ctor_get(v_toConstantVal_5964_, 2);
lean_dec(v_unused_5995_);
v_unused_5996_ = lean_ctor_get(v_toConstantVal_5964_, 0);
lean_dec(v_unused_5996_);
v___x_5971_ = v_toConstantVal_5964_;
v_isShared_5972_ = v_isSharedCheck_5994_;
goto v_resetjp_5970_;
}
else
{
lean_inc(v_levelParams_5969_);
lean_dec(v_toConstantVal_5964_);
v___x_5971_ = lean_box(0);
v_isShared_5972_ = v_isSharedCheck_5994_;
goto v_resetjp_5970_;
}
v_resetjp_5970_:
{
lean_object* v_thmType_5973_; lean_object* v___x_5975_; uint8_t v_isShared_5976_; uint8_t v_isSharedCheck_5991_; 
v_thmType_5973_ = lean_ctor_get(v_val_5958_, 0);
v_isSharedCheck_5991_ = !lean_is_exclusive(v_val_5958_);
if (v_isSharedCheck_5991_ == 0)
{
lean_object* v_unused_5992_; lean_object* v_unused_5993_; 
v_unused_5992_ = lean_ctor_get(v_val_5958_, 2);
lean_dec(v_unused_5992_);
v_unused_5993_ = lean_ctor_get(v_val_5958_, 1);
lean_dec(v_unused_5993_);
v___x_5975_ = v_val_5958_;
v_isShared_5976_ = v_isSharedCheck_5991_;
goto v_resetjp_5974_;
}
else
{
lean_inc(v_thmType_5973_);
lean_dec(v_val_5958_);
v___x_5975_ = lean_box(0);
v_isShared_5976_ = v_isSharedCheck_5991_;
goto v_resetjp_5974_;
}
v_resetjp_5974_:
{
lean_object* v___x_5978_; 
lean_inc(v_thmName_5946_);
if (v_isShared_5972_ == 0)
{
lean_ctor_set(v___x_5971_, 2, v_thmType_5973_);
lean_ctor_set(v___x_5971_, 0, v_thmName_5946_);
v___x_5978_ = v___x_5971_;
goto v_reusejp_5977_;
}
else
{
lean_object* v_reuseFailAlloc_5990_; 
v_reuseFailAlloc_5990_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5990_, 0, v_thmName_5946_);
lean_ctor_set(v_reuseFailAlloc_5990_, 1, v_levelParams_5969_);
lean_ctor_set(v_reuseFailAlloc_5990_, 2, v_thmType_5973_);
v___x_5978_ = v_reuseFailAlloc_5990_;
goto v_reusejp_5977_;
}
v_reusejp_5977_:
{
lean_object* v___x_5979_; lean_object* v___x_5980_; lean_object* v___x_5982_; 
v___x_5979_ = lean_box(0);
v___x_5980_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5980_, 0, v_thmName_5946_);
lean_ctor_set(v___x_5980_, 1, v___x_5979_);
if (v_isShared_5976_ == 0)
{
lean_ctor_set(v___x_5975_, 2, v___x_5980_);
lean_ctor_set(v___x_5975_, 1, v_val_5965_);
lean_ctor_set(v___x_5975_, 0, v___x_5978_);
v___x_5982_ = v___x_5975_;
goto v_reusejp_5981_;
}
else
{
lean_object* v_reuseFailAlloc_5989_; 
v_reuseFailAlloc_5989_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5989_, 0, v___x_5978_);
lean_ctor_set(v_reuseFailAlloc_5989_, 1, v_val_5965_);
lean_ctor_set(v_reuseFailAlloc_5989_, 2, v___x_5980_);
v___x_5982_ = v_reuseFailAlloc_5989_;
goto v_reusejp_5981_;
}
v_reusejp_5981_:
{
lean_object* v___x_5984_; 
if (v_isShared_5968_ == 0)
{
lean_ctor_set(v___x_5967_, 0, v___x_5982_);
v___x_5984_ = v___x_5967_;
goto v_reusejp_5983_;
}
else
{
lean_object* v_reuseFailAlloc_5988_; 
v_reuseFailAlloc_5988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5988_, 0, v___x_5982_);
v___x_5984_ = v_reuseFailAlloc_5988_;
goto v_reusejp_5983_;
}
v_reusejp_5983_:
{
lean_object* v___x_5986_; 
if (v_isShared_5963_ == 0)
{
lean_ctor_set(v___x_5962_, 0, v___x_5984_);
v___x_5986_ = v___x_5962_;
goto v_reusejp_5985_;
}
else
{
lean_object* v_reuseFailAlloc_5987_; 
v_reuseFailAlloc_5987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5987_, 0, v___x_5984_);
v___x_5986_ = v_reuseFailAlloc_5987_;
goto v_reusejp_5985_;
}
v_reusejp_5985_:
{
return v___x_5986_;
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
lean_object* v___x_5998_; lean_object* v___x_6000_; 
lean_dec(v_a_5960_);
lean_dec(v_val_5958_);
lean_dec_ref(v_ctorVal_5947_);
lean_dec(v_thmName_5946_);
v___x_5998_ = lean_box(0);
if (v_isShared_5963_ == 0)
{
lean_ctor_set(v___x_5962_, 0, v___x_5998_);
v___x_6000_ = v___x_5962_;
goto v_reusejp_5999_;
}
else
{
lean_object* v_reuseFailAlloc_6001_; 
v_reuseFailAlloc_6001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6001_, 0, v___x_5998_);
v___x_6000_ = v_reuseFailAlloc_6001_;
goto v_reusejp_5999_;
}
v_reusejp_5999_:
{
return v___x_6000_;
}
}
}
}
else
{
lean_object* v_a_6003_; lean_object* v___x_6005_; uint8_t v_isShared_6006_; uint8_t v_isSharedCheck_6010_; 
lean_dec(v_val_5958_);
lean_dec_ref(v_ctorVal_5947_);
lean_dec(v_thmName_5946_);
v_a_6003_ = lean_ctor_get(v___x_5959_, 0);
v_isSharedCheck_6010_ = !lean_is_exclusive(v___x_5959_);
if (v_isSharedCheck_6010_ == 0)
{
v___x_6005_ = v___x_5959_;
v_isShared_6006_ = v_isSharedCheck_6010_;
goto v_resetjp_6004_;
}
else
{
lean_inc(v_a_6003_);
lean_dec(v___x_5959_);
v___x_6005_ = lean_box(0);
v_isShared_6006_ = v_isSharedCheck_6010_;
goto v_resetjp_6004_;
}
v_resetjp_6004_:
{
lean_object* v___x_6008_; 
if (v_isShared_6006_ == 0)
{
v___x_6008_ = v___x_6005_;
goto v_reusejp_6007_;
}
else
{
lean_object* v_reuseFailAlloc_6009_; 
v_reuseFailAlloc_6009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6009_, 0, v_a_6003_);
v___x_6008_ = v_reuseFailAlloc_6009_;
goto v_reusejp_6007_;
}
v_reusejp_6007_:
{
return v___x_6008_;
}
}
}
}
else
{
lean_object* v___x_6011_; lean_object* v___x_6013_; 
lean_dec(v_a_5954_);
lean_dec_ref(v_ctorVal_5947_);
lean_dec(v_thmName_5946_);
v___x_6011_ = lean_box(0);
if (v_isShared_5957_ == 0)
{
lean_ctor_set(v___x_5956_, 0, v___x_6011_);
v___x_6013_ = v___x_5956_;
goto v_reusejp_6012_;
}
else
{
lean_object* v_reuseFailAlloc_6014_; 
v_reuseFailAlloc_6014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6014_, 0, v___x_6011_);
v___x_6013_ = v_reuseFailAlloc_6014_;
goto v_reusejp_6012_;
}
v_reusejp_6012_:
{
return v___x_6013_;
}
}
}
}
else
{
lean_object* v_a_6016_; lean_object* v___x_6018_; uint8_t v_isShared_6019_; uint8_t v_isSharedCheck_6023_; 
lean_dec_ref(v_ctorVal_5947_);
lean_dec(v_thmName_5946_);
v_a_6016_ = lean_ctor_get(v___x_5953_, 0);
v_isSharedCheck_6023_ = !lean_is_exclusive(v___x_5953_);
if (v_isSharedCheck_6023_ == 0)
{
v___x_6018_ = v___x_5953_;
v_isShared_6019_ = v_isSharedCheck_6023_;
goto v_resetjp_6017_;
}
else
{
lean_inc(v_a_6016_);
lean_dec(v___x_5953_);
v___x_6018_ = lean_box(0);
v_isShared_6019_ = v_isSharedCheck_6023_;
goto v_resetjp_6017_;
}
v_resetjp_6017_:
{
lean_object* v___x_6021_; 
if (v_isShared_6019_ == 0)
{
v___x_6021_ = v___x_6018_;
goto v_reusejp_6020_;
}
else
{
lean_object* v_reuseFailAlloc_6022_; 
v_reuseFailAlloc_6022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6022_, 0, v_a_6016_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f___boxed(lean_object* v_thmName_6024_, lean_object* v_ctorVal_6025_, lean_object* v_a_6026_, lean_object* v_a_6027_, lean_object* v_a_6028_, lean_object* v_a_6029_, lean_object* v_a_6030_){
_start:
{
lean_object* v_res_6031_; 
v_res_6031_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(v_thmName_6024_, v_ctorVal_6025_, v_a_6026_, v_a_6027_, v_a_6028_, v_a_6029_);
lean_dec(v_a_6029_);
lean_dec_ref(v_a_6028_);
lean_dec(v_a_6027_);
lean_dec_ref(v_a_6026_);
return v_res_6031_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(lean_object* v_env_6032_, lean_object* v_n_6033_){
_start:
{
if (lean_obj_tag(v_n_6033_) == 1)
{
lean_object* v_pre_6034_; lean_object* v_str_6035_; lean_object* v___x_6036_; uint8_t v___x_6037_; 
v_pre_6034_ = lean_ctor_get(v_n_6033_, 0);
lean_inc(v_pre_6034_);
v_str_6035_ = lean_ctor_get(v_n_6033_, 1);
lean_inc_ref(v_str_6035_);
lean_dec_ref_known(v_n_6033_, 2);
v___x_6036_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0));
v___x_6037_ = lean_string_dec_eq(v_str_6035_, v___x_6036_);
lean_dec_ref(v_str_6035_);
if (v___x_6037_ == 0)
{
lean_dec(v_pre_6034_);
lean_dec_ref(v_env_6032_);
return v___x_6037_;
}
else
{
uint8_t v___x_6038_; lean_object* v___x_6039_; 
v___x_6038_ = 0;
v___x_6039_ = l_Lean_Environment_find_x3f(v_env_6032_, v_pre_6034_, v___x_6038_);
if (lean_obj_tag(v___x_6039_) == 1)
{
lean_object* v_val_6040_; 
v_val_6040_ = lean_ctor_get(v___x_6039_, 0);
lean_inc(v_val_6040_);
lean_dec_ref_known(v___x_6039_, 1);
if (lean_obj_tag(v_val_6040_) == 6)
{
lean_dec_ref_known(v_val_6040_, 1);
return v___x_6037_;
}
else
{
lean_dec(v_val_6040_);
return v___x_6038_;
}
}
else
{
lean_dec(v___x_6039_);
return v___x_6038_;
}
}
}
else
{
uint8_t v___x_6041_; 
lean_dec(v_n_6033_);
lean_dec_ref(v_env_6032_);
v___x_6041_ = 0;
return v___x_6041_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2____boxed(lean_object* v_env_6042_, lean_object* v_n_6043_){
_start:
{
uint8_t v_res_6044_; lean_object* v_r_6045_; 
v_res_6044_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(v_env_6042_, v_n_6043_);
v_r_6045_ = lean_box(v_res_6044_);
return v_r_6045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_6048_; lean_object* v___x_6049_; 
v___f_6048_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_));
v___x_6049_ = l_Lean_registerReservedNamePredicate(v___f_6048_);
return v___x_6049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2____boxed(lean_object* v_a_6050_){
_start:
{
lean_object* v_res_6051_; 
v_res_6051_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_();
return v_res_6051_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(lean_object* v_thm_6052_, lean_object* v___y_6053_){
_start:
{
lean_object* v___x_6055_; lean_object* v_env_6056_; lean_object* v_toConstantVal_6057_; lean_object* v_value_6058_; lean_object* v_all_6059_; uint8_t v___y_6061_; lean_object* v_type_6069_; uint8_t v___x_6070_; 
v___x_6055_ = lean_st_ref_get(v___y_6053_);
v_env_6056_ = lean_ctor_get(v___x_6055_, 0);
lean_inc_ref_n(v_env_6056_, 2);
lean_dec(v___x_6055_);
v_toConstantVal_6057_ = lean_ctor_get(v_thm_6052_, 0);
v_value_6058_ = lean_ctor_get(v_thm_6052_, 1);
v_all_6059_ = lean_ctor_get(v_thm_6052_, 2);
v_type_6069_ = lean_ctor_get(v_toConstantVal_6057_, 2);
v___x_6070_ = l_Lean_Environment_hasUnsafe(v_env_6056_, v_type_6069_);
if (v___x_6070_ == 0)
{
uint8_t v___x_6071_; 
v___x_6071_ = l_Lean_Environment_hasUnsafe(v_env_6056_, v_value_6058_);
v___y_6061_ = v___x_6071_;
goto v___jp_6060_;
}
else
{
lean_dec_ref(v_env_6056_);
v___y_6061_ = v___x_6070_;
goto v___jp_6060_;
}
v___jp_6060_:
{
if (v___y_6061_ == 0)
{
lean_object* v___x_6062_; lean_object* v___x_6063_; 
v___x_6062_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_6062_, 0, v_thm_6052_);
v___x_6063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6063_, 0, v___x_6062_);
return v___x_6063_;
}
else
{
lean_object* v___x_6064_; uint8_t v___x_6065_; lean_object* v___x_6066_; lean_object* v___x_6067_; lean_object* v___x_6068_; 
lean_inc(v_all_6059_);
lean_inc_ref(v_value_6058_);
lean_inc_ref(v_toConstantVal_6057_);
lean_dec_ref(v_thm_6052_);
v___x_6064_ = lean_box(0);
v___x_6065_ = 0;
v___x_6066_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_6066_, 0, v_toConstantVal_6057_);
lean_ctor_set(v___x_6066_, 1, v_value_6058_);
lean_ctor_set(v___x_6066_, 2, v___x_6064_);
lean_ctor_set(v___x_6066_, 3, v_all_6059_);
lean_ctor_set_uint8(v___x_6066_, sizeof(void*)*4, v___x_6065_);
v___x_6067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6067_, 0, v___x_6066_);
v___x_6068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6068_, 0, v___x_6067_);
return v___x_6068_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_thm_6072_, lean_object* v___y_6073_, lean_object* v___y_6074_){
_start:
{
lean_object* v_res_6075_; 
v_res_6075_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(v_thm_6072_, v___y_6073_);
lean_dec(v___y_6073_);
return v_res_6075_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0(lean_object* v_thm_6076_, lean_object* v___y_6077_, lean_object* v___y_6078_, lean_object* v___y_6079_, lean_object* v___y_6080_){
_start:
{
lean_object* v___x_6082_; 
v___x_6082_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(v_thm_6076_, v___y_6080_);
return v___x_6082_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___boxed(lean_object* v_thm_6083_, lean_object* v___y_6084_, lean_object* v___y_6085_, lean_object* v___y_6086_, lean_object* v___y_6087_, lean_object* v___y_6088_){
_start:
{
lean_object* v_res_6089_; 
v_res_6089_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0(v_thm_6083_, v___y_6084_, v___y_6085_, v___y_6086_, v___y_6087_);
lean_dec(v___y_6087_);
lean_dec_ref(v___y_6086_);
lean_dec(v___y_6085_);
lean_dec_ref(v___y_6084_);
return v_res_6089_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(lean_object* v_val_6090_, uint8_t v___x_6091_, lean_object* v___y_6092_, lean_object* v___y_6093_, lean_object* v___y_6094_, lean_object* v___y_6095_){
_start:
{
lean_object* v___x_6097_; lean_object* v_a_6098_; lean_object* v___x_6099_; 
v___x_6097_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(v_val_6090_, v___y_6095_);
v_a_6098_ = lean_ctor_get(v___x_6097_, 0);
lean_inc(v_a_6098_);
lean_dec_ref(v___x_6097_);
v___x_6099_ = l_Lean_addDecl(v_a_6098_, v___x_6091_, v___y_6094_, v___y_6095_);
return v___x_6099_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object* v_val_6100_, lean_object* v___x_6101_, lean_object* v___y_6102_, lean_object* v___y_6103_, lean_object* v___y_6104_, lean_object* v___y_6105_, lean_object* v___y_6106_){
_start:
{
uint8_t v___x_2127__boxed_6107_; lean_object* v_res_6108_; 
v___x_2127__boxed_6107_ = lean_unbox(v___x_6101_);
v_res_6108_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(v_val_6100_, v___x_2127__boxed_6107_, v___y_6102_, v___y_6103_, v___y_6104_, v___y_6105_);
lean_dec(v___y_6105_);
lean_dec_ref(v___y_6104_);
lean_dec(v___y_6103_);
lean_dec_ref(v___y_6102_);
return v_res_6108_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6111_; lean_object* v___x_6112_; lean_object* v___x_6113_; 
v___x_6111_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_6112_ = lean_unsigned_to_nat(0u);
v___x_6113_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_6113_, 0, v___x_6112_);
lean_ctor_set(v___x_6113_, 1, v___x_6112_);
lean_ctor_set(v___x_6113_, 2, v___x_6112_);
lean_ctor_set(v___x_6113_, 3, v___x_6112_);
lean_ctor_set(v___x_6113_, 4, v___x_6111_);
lean_ctor_set(v___x_6113_, 5, v___x_6111_);
lean_ctor_set(v___x_6113_, 6, v___x_6111_);
lean_ctor_set(v___x_6113_, 7, v___x_6111_);
lean_ctor_set(v___x_6113_, 8, v___x_6111_);
lean_ctor_set(v___x_6113_, 9, v___x_6111_);
lean_ctor_set(v___x_6113_, 10, v___x_6111_);
return v___x_6113_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6114_; lean_object* v___x_6115_; 
v___x_6114_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_6115_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6115_, 0, v___x_6114_);
lean_ctor_set(v___x_6115_, 1, v___x_6114_);
lean_ctor_set(v___x_6115_, 2, v___x_6114_);
lean_ctor_set(v___x_6115_, 3, v___x_6114_);
lean_ctor_set(v___x_6115_, 4, v___x_6114_);
lean_ctor_set(v___x_6115_, 5, v___x_6114_);
return v___x_6115_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6116_; lean_object* v___x_6117_; 
v___x_6116_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_6117_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6117_, 0, v___x_6116_);
lean_ctor_set(v___x_6117_, 1, v___x_6116_);
lean_ctor_set(v___x_6117_, 2, v___x_6116_);
lean_ctor_set(v___x_6117_, 3, v___x_6116_);
lean_ctor_set(v___x_6117_, 4, v___x_6116_);
return v___x_6117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(lean_object* v___x_6118_, lean_object* v_name_6119_, lean_object* v___y_6120_, lean_object* v___y_6121_){
_start:
{
if (lean_obj_tag(v_name_6119_) == 1)
{
lean_object* v_pre_6131_; lean_object* v_str_6132_; lean_object* v___x_6133_; uint8_t v___x_6134_; 
v_pre_6131_ = lean_ctor_get(v_name_6119_, 0);
lean_inc(v_pre_6131_);
v_str_6132_ = lean_ctor_get(v_name_6119_, 1);
v___x_6133_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0));
v___x_6134_ = lean_string_dec_eq(v_str_6132_, v___x_6133_);
if (v___x_6134_ == 0)
{
lean_dec_ref_known(v_name_6119_, 2);
lean_dec(v_pre_6131_);
lean_dec(v___x_6118_);
goto v___jp_6127_;
}
else
{
lean_object* v___x_6135_; lean_object* v_env_6136_; uint8_t v___x_6137_; lean_object* v___x_6138_; 
v___x_6135_ = lean_st_ref_get(v___y_6121_);
v_env_6136_ = lean_ctor_get(v___x_6135_, 0);
lean_inc_ref(v_env_6136_);
lean_dec(v___x_6135_);
v___x_6137_ = 0;
lean_inc(v_pre_6131_);
v___x_6138_ = l_Lean_Environment_find_x3f(v_env_6136_, v_pre_6131_, v___x_6137_);
if (lean_obj_tag(v___x_6138_) == 1)
{
lean_object* v_val_6139_; 
v_val_6139_ = lean_ctor_get(v___x_6138_, 0);
lean_inc(v_val_6139_);
lean_dec_ref_known(v___x_6138_, 1);
if (lean_obj_tag(v_val_6139_) == 6)
{
lean_object* v_val_6140_; lean_object* v___x_6142_; uint8_t v_isShared_6143_; uint8_t v_isSharedCheck_6190_; 
v_val_6140_ = lean_ctor_get(v_val_6139_, 0);
v_isSharedCheck_6190_ = !lean_is_exclusive(v_val_6139_);
if (v_isSharedCheck_6190_ == 0)
{
v___x_6142_ = v_val_6139_;
v_isShared_6143_ = v_isSharedCheck_6190_;
goto v_resetjp_6141_;
}
else
{
lean_inc(v_val_6140_);
lean_dec(v_val_6139_);
v___x_6142_ = lean_box(0);
v_isShared_6143_ = v_isSharedCheck_6190_;
goto v_resetjp_6141_;
}
v_resetjp_6141_:
{
uint8_t v___x_6144_; uint8_t v___x_6145_; uint8_t v___x_6146_; lean_object* v___x_6147_; uint64_t v___x_6148_; lean_object* v___x_6149_; lean_object* v___x_6150_; lean_object* v___x_6151_; lean_object* v___x_6152_; lean_object* v___x_6153_; lean_object* v___x_6154_; lean_object* v___x_6155_; lean_object* v___x_6156_; lean_object* v___x_6157_; lean_object* v___x_6158_; lean_object* v___x_6159_; lean_object* v___x_6160_; uint8_t v_a_6162_; lean_object* v___x_6168_; 
v___x_6144_ = 1;
v___x_6145_ = 0;
v___x_6146_ = 2;
v___x_6147_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_6147_, 0, v___x_6137_);
lean_ctor_set_uint8(v___x_6147_, 1, v___x_6137_);
lean_ctor_set_uint8(v___x_6147_, 2, v___x_6137_);
lean_ctor_set_uint8(v___x_6147_, 3, v___x_6137_);
lean_ctor_set_uint8(v___x_6147_, 4, v___x_6137_);
lean_ctor_set_uint8(v___x_6147_, 5, v___x_6134_);
lean_ctor_set_uint8(v___x_6147_, 6, v___x_6134_);
lean_ctor_set_uint8(v___x_6147_, 7, v___x_6137_);
lean_ctor_set_uint8(v___x_6147_, 8, v___x_6134_);
lean_ctor_set_uint8(v___x_6147_, 9, v___x_6144_);
lean_ctor_set_uint8(v___x_6147_, 10, v___x_6145_);
lean_ctor_set_uint8(v___x_6147_, 11, v___x_6134_);
lean_ctor_set_uint8(v___x_6147_, 12, v___x_6134_);
lean_ctor_set_uint8(v___x_6147_, 13, v___x_6134_);
lean_ctor_set_uint8(v___x_6147_, 14, v___x_6146_);
lean_ctor_set_uint8(v___x_6147_, 15, v___x_6134_);
lean_ctor_set_uint8(v___x_6147_, 16, v___x_6134_);
lean_ctor_set_uint8(v___x_6147_, 17, v___x_6134_);
lean_ctor_set_uint8(v___x_6147_, 18, v___x_6134_);
lean_ctor_set_uint8(v___x_6147_, 19, v___x_6137_);
v___x_6148_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_6147_);
v___x_6149_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_6149_, 0, v___x_6147_);
lean_ctor_set_uint64(v___x_6149_, sizeof(void*)*1, v___x_6148_);
v___x_6150_ = lean_unsigned_to_nat(0u);
v___x_6151_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_6152_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_6153_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_));
v___x_6154_ = lean_box(0);
lean_inc(v___x_6118_);
v___x_6155_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_6155_, 0, v___x_6149_);
lean_ctor_set(v___x_6155_, 1, v___x_6118_);
lean_ctor_set(v___x_6155_, 2, v___x_6152_);
lean_ctor_set(v___x_6155_, 3, v___x_6153_);
lean_ctor_set(v___x_6155_, 4, v___x_6154_);
lean_ctor_set(v___x_6155_, 5, v___x_6150_);
lean_ctor_set(v___x_6155_, 6, v___x_6154_);
lean_ctor_set_uint8(v___x_6155_, sizeof(void*)*7, v___x_6137_);
lean_ctor_set_uint8(v___x_6155_, sizeof(void*)*7 + 1, v___x_6137_);
lean_ctor_set_uint8(v___x_6155_, sizeof(void*)*7 + 2, v___x_6137_);
lean_ctor_set_uint8(v___x_6155_, sizeof(void*)*7 + 3, v___x_6134_);
v___x_6156_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6157_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6158_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6159_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6159_, 0, v___x_6156_);
lean_ctor_set(v___x_6159_, 1, v___x_6157_);
lean_ctor_set(v___x_6159_, 2, v___x_6118_);
lean_ctor_set(v___x_6159_, 3, v___x_6151_);
lean_ctor_set(v___x_6159_, 4, v___x_6158_);
v___x_6160_ = lean_st_mk_ref(v___x_6159_);
lean_inc_ref(v_name_6119_);
v___x_6168_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(v_name_6119_, v_val_6140_, v___x_6155_, v___x_6160_, v___y_6120_, v___y_6121_);
if (lean_obj_tag(v___x_6168_) == 0)
{
lean_object* v_a_6169_; 
v_a_6169_ = lean_ctor_get(v___x_6168_, 0);
lean_inc(v_a_6169_);
lean_dec_ref_known(v___x_6168_, 1);
if (lean_obj_tag(v_a_6169_) == 1)
{
lean_object* v_val_6170_; lean_object* v___x_6171_; lean_object* v___f_6172_; lean_object* v___x_6173_; 
v_val_6170_ = lean_ctor_get(v_a_6169_, 0);
lean_inc(v_val_6170_);
lean_dec_ref_known(v_a_6169_, 1);
v___x_6171_ = lean_box(v___x_6137_);
v___f_6172_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed), 7, 2);
lean_closure_set(v___f_6172_, 0, v_val_6170_);
lean_closure_set(v___f_6172_, 1, v___x_6171_);
v___x_6173_ = l_Lean_Meta_realizeConst(v_pre_6131_, v_name_6119_, v___f_6172_, v___x_6155_, v___x_6160_, v___y_6120_, v___y_6121_);
lean_dec_ref_known(v___x_6155_, 7);
if (lean_obj_tag(v___x_6173_) == 0)
{
lean_dec_ref_known(v___x_6173_, 1);
v_a_6162_ = v___x_6134_;
goto v___jp_6161_;
}
else
{
lean_object* v_a_6174_; lean_object* v___x_6176_; uint8_t v_isShared_6177_; uint8_t v_isSharedCheck_6181_; 
lean_dec(v___x_6160_);
lean_del_object(v___x_6142_);
v_a_6174_ = lean_ctor_get(v___x_6173_, 0);
v_isSharedCheck_6181_ = !lean_is_exclusive(v___x_6173_);
if (v_isSharedCheck_6181_ == 0)
{
v___x_6176_ = v___x_6173_;
v_isShared_6177_ = v_isSharedCheck_6181_;
goto v_resetjp_6175_;
}
else
{
lean_inc(v_a_6174_);
lean_dec(v___x_6173_);
v___x_6176_ = lean_box(0);
v_isShared_6177_ = v_isSharedCheck_6181_;
goto v_resetjp_6175_;
}
v_resetjp_6175_:
{
lean_object* v___x_6179_; 
if (v_isShared_6177_ == 0)
{
v___x_6179_ = v___x_6176_;
goto v_reusejp_6178_;
}
else
{
lean_object* v_reuseFailAlloc_6180_; 
v_reuseFailAlloc_6180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6180_, 0, v_a_6174_);
v___x_6179_ = v_reuseFailAlloc_6180_;
goto v_reusejp_6178_;
}
v_reusejp_6178_:
{
return v___x_6179_;
}
}
}
}
else
{
lean_dec(v_a_6169_);
lean_dec_ref_known(v___x_6155_, 7);
lean_dec(v_pre_6131_);
lean_dec_ref_known(v_name_6119_, 2);
v_a_6162_ = v___x_6137_;
goto v___jp_6161_;
}
}
else
{
lean_object* v_a_6182_; lean_object* v___x_6184_; uint8_t v_isShared_6185_; uint8_t v_isSharedCheck_6189_; 
lean_dec(v___x_6160_);
lean_dec_ref_known(v___x_6155_, 7);
lean_del_object(v___x_6142_);
lean_dec(v_pre_6131_);
lean_dec_ref_known(v_name_6119_, 2);
v_a_6182_ = lean_ctor_get(v___x_6168_, 0);
v_isSharedCheck_6189_ = !lean_is_exclusive(v___x_6168_);
if (v_isSharedCheck_6189_ == 0)
{
v___x_6184_ = v___x_6168_;
v_isShared_6185_ = v_isSharedCheck_6189_;
goto v_resetjp_6183_;
}
else
{
lean_inc(v_a_6182_);
lean_dec(v___x_6168_);
v___x_6184_ = lean_box(0);
v_isShared_6185_ = v_isSharedCheck_6189_;
goto v_resetjp_6183_;
}
v_resetjp_6183_:
{
lean_object* v___x_6187_; 
if (v_isShared_6185_ == 0)
{
v___x_6187_ = v___x_6184_;
goto v_reusejp_6186_;
}
else
{
lean_object* v_reuseFailAlloc_6188_; 
v_reuseFailAlloc_6188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6188_, 0, v_a_6182_);
v___x_6187_ = v_reuseFailAlloc_6188_;
goto v_reusejp_6186_;
}
v_reusejp_6186_:
{
return v___x_6187_;
}
}
}
v___jp_6161_:
{
lean_object* v___x_6163_; lean_object* v___x_6164_; lean_object* v___x_6166_; 
v___x_6163_ = lean_st_ref_get(v___x_6160_);
lean_dec(v___x_6160_);
lean_dec(v___x_6163_);
v___x_6164_ = lean_box(v_a_6162_);
if (v_isShared_6143_ == 0)
{
lean_ctor_set_tag(v___x_6142_, 0);
lean_ctor_set(v___x_6142_, 0, v___x_6164_);
v___x_6166_ = v___x_6142_;
goto v_reusejp_6165_;
}
else
{
lean_object* v_reuseFailAlloc_6167_; 
v_reuseFailAlloc_6167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6167_, 0, v___x_6164_);
v___x_6166_ = v_reuseFailAlloc_6167_;
goto v_reusejp_6165_;
}
v_reusejp_6165_:
{
return v___x_6166_;
}
}
}
}
else
{
lean_dec(v_val_6139_);
lean_dec_ref_known(v_name_6119_, 2);
lean_dec(v_pre_6131_);
lean_dec(v___x_6118_);
goto v___jp_6123_;
}
}
else
{
lean_dec(v___x_6138_);
lean_dec_ref_known(v_name_6119_, 2);
lean_dec(v_pre_6131_);
lean_dec(v___x_6118_);
goto v___jp_6123_;
}
}
}
else
{
lean_dec(v_name_6119_);
lean_dec(v___x_6118_);
goto v___jp_6127_;
}
v___jp_6123_:
{
uint8_t v___x_6124_; lean_object* v___x_6125_; lean_object* v___x_6126_; 
v___x_6124_ = 0;
v___x_6125_ = lean_box(v___x_6124_);
v___x_6126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6126_, 0, v___x_6125_);
return v___x_6126_;
}
v___jp_6127_:
{
uint8_t v___x_6128_; lean_object* v___x_6129_; lean_object* v___x_6130_; 
v___x_6128_ = 0;
v___x_6129_ = lean_box(v___x_6128_);
v___x_6130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6130_, 0, v___x_6129_);
return v___x_6130_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object* v___x_6191_, lean_object* v_name_6192_, lean_object* v___y_6193_, lean_object* v___y_6194_, lean_object* v___y_6195_){
_start:
{
lean_object* v_res_6196_; 
v_res_6196_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(v___x_6191_, v_name_6192_, v___y_6193_, v___y_6194_);
lean_dec(v___y_6194_);
lean_dec_ref(v___y_6193_);
return v_res_6196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_6200_; lean_object* v___x_6201_; 
v___f_6200_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_));
v___x_6201_ = l_Lean_registerReservedNameAction(v___f_6200_);
return v___x_6201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object* v_a_6202_){
_start:
{
lean_object* v_res_6203_; 
v_res_6203_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_();
return v_res_6203_;
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
