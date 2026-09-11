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
v___x_213_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6___redArg(v___x_212_, v_e_209_, v_a_210_);
v___x_214_ = lean_st_ref_put(v_a_208_, v___x_213_);
v___x_215_ = lean_box(0);
return v___x_215_;
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
lean_object* v___y_255_; uint8_t v___y_265_; lean_object* v___y_266_; lean_object* v___y_267_; lean_object* v___y_268_; uint8_t v___y_269_; lean_object* v_toCold_274_; lean_object* v_currRecDepth_275_; lean_object* v_ref_276_; uint8_t v_diag_277_; uint8_t v_suppressElabErrors_278_; lean_object* v_maxRecDepth_279_; lean_object* v_cancelTk_x3f_280_; 
v_toCold_274_ = lean_ctor_get(v___y_251_, 0);
v_currRecDepth_275_ = lean_ctor_get(v___y_251_, 1);
v_ref_276_ = lean_ctor_get(v___y_251_, 2);
v_diag_277_ = lean_ctor_get_uint8(v___y_251_, sizeof(void*)*3);
v_suppressElabErrors_278_ = lean_ctor_get_uint8(v___y_251_, sizeof(void*)*3 + 1);
v_maxRecDepth_279_ = lean_ctor_get(v_toCold_274_, 3);
v_cancelTk_x3f_280_ = lean_ctor_get(v_toCold_274_, 10);
if (lean_obj_tag(v_cancelTk_x3f_280_) == 1)
{
lean_object* v_val_286_; uint8_t v___x_287_; 
v_val_286_ = lean_ctor_get(v_cancelTk_x3f_280_, 0);
v___x_287_ = l_IO_CancelToken_isSet(v_val_286_);
if (v___x_287_ == 0)
{
goto v___jp_281_;
}
else
{
lean_object* v___x_288_; lean_object* v_a_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_296_; 
lean_dec_ref(v_x_249_);
v___x_288_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg();
v_a_289_ = lean_ctor_get(v___x_288_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_296_ == 0)
{
v___x_291_ = v___x_288_;
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_a_289_);
lean_dec(v___x_288_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_294_; 
if (v_isShared_292_ == 0)
{
v___x_294_ = v___x_291_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_a_289_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
}
else
{
goto v___jp_281_;
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
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_270_ = lean_unsigned_to_nat(1u);
v___x_271_ = lean_nat_add(v___y_267_, v___x_270_);
lean_inc_ref(v___y_266_);
v___x_272_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_272_, 0, v___y_266_);
lean_ctor_set(v___x_272_, 1, v___x_271_);
lean_ctor_set(v___x_272_, 2, v___y_268_);
lean_ctor_set_uint8(v___x_272_, sizeof(void*)*3, v___y_269_);
lean_ctor_set_uint8(v___x_272_, sizeof(void*)*3 + 1, v___y_265_);
lean_inc(v___y_252_);
lean_inc(v___y_250_);
v___x_273_ = lean_apply_4(v_x_249_, v___y_250_, v___x_272_, v___y_252_, lean_box(0));
v___y_255_ = v___x_273_;
goto v___jp_254_;
}
v___jp_281_:
{
lean_object* v___x_282_; uint8_t v___x_283_; 
v___x_282_ = lean_unsigned_to_nat(0u);
v___x_283_ = lean_nat_dec_eq(v_maxRecDepth_279_, v___x_282_);
if (v___x_283_ == 0)
{
uint8_t v___x_284_; 
v___x_284_ = lean_nat_dec_eq(v_currRecDepth_275_, v_maxRecDepth_279_);
if (v___x_284_ == 0)
{
lean_inc(v_ref_276_);
v___y_265_ = v_suppressElabErrors_278_;
v___y_266_ = v_toCold_274_;
v___y_267_ = v_currRecDepth_275_;
v___y_268_ = v_ref_276_;
v___y_269_ = v_diag_277_;
goto v___jp_264_;
}
else
{
lean_object* v___x_285_; 
lean_dec_ref(v_x_249_);
lean_inc(v_ref_276_);
v___x_285_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_276_);
v___y_255_ = v___x_285_;
goto v___jp_254_;
}
}
else
{
lean_inc(v_ref_276_);
v___y_265_ = v_suppressElabErrors_278_;
v___y_266_ = v_toCold_274_;
v___y_267_ = v_currRecDepth_275_;
v___y_268_ = v_ref_276_;
v___y_269_ = v_diag_277_;
goto v___jp_264_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(v_x_297_, v___y_298_, v___y_299_, v___y_300_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
lean_dec(v___y_298_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_303_, lean_object* v_x_304_, lean_object* v___y_305_, lean_object* v___y_306_){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = lean_apply_1(v_x_304_, lean_box(0));
v___x_309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_310_, lean_object* v_x_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(v_00_u03b1_310_, v_x_311_, v___y_312_, v___y_313_);
lean_dec(v___y_313_);
lean_dec_ref(v___y_312_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_a_316_, lean_object* v_x_317_){
_start:
{
if (lean_obj_tag(v_x_317_) == 0)
{
lean_object* v___x_318_; 
v___x_318_ = lean_box(0);
return v___x_318_;
}
else
{
lean_object* v_key_319_; lean_object* v_value_320_; lean_object* v_tail_321_; uint8_t v___x_322_; 
v_key_319_ = lean_ctor_get(v_x_317_, 0);
v_value_320_ = lean_ctor_get(v_x_317_, 1);
v_tail_321_ = lean_ctor_get(v_x_317_, 2);
v___x_322_ = l_Lean_ExprStructEq_beq(v_key_319_, v_a_316_);
if (v___x_322_ == 0)
{
v_x_317_ = v_tail_321_;
goto _start;
}
else
{
lean_object* v___x_324_; 
lean_inc(v_value_320_);
v___x_324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_324_, 0, v_value_320_);
return v___x_324_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_a_325_, lean_object* v_x_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(v_a_325_, v_x_326_);
lean_dec(v_x_326_);
lean_dec_ref(v_a_325_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(lean_object* v_m_328_, lean_object* v_a_329_){
_start:
{
lean_object* v_buckets_330_; lean_object* v___x_331_; uint64_t v___x_332_; uint64_t v___x_333_; uint64_t v___x_334_; uint64_t v_fold_335_; uint64_t v___x_336_; uint64_t v___x_337_; uint64_t v___x_338_; size_t v___x_339_; size_t v___x_340_; size_t v___x_341_; size_t v___x_342_; size_t v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v_buckets_330_ = lean_ctor_get(v_m_328_, 1);
v___x_331_ = lean_array_get_size(v_buckets_330_);
v___x_332_ = l_Lean_ExprStructEq_hash(v_a_329_);
v___x_333_ = 32ULL;
v___x_334_ = lean_uint64_shift_right(v___x_332_, v___x_333_);
v_fold_335_ = lean_uint64_xor(v___x_332_, v___x_334_);
v___x_336_ = 16ULL;
v___x_337_ = lean_uint64_shift_right(v_fold_335_, v___x_336_);
v___x_338_ = lean_uint64_xor(v_fold_335_, v___x_337_);
v___x_339_ = lean_uint64_to_usize(v___x_338_);
v___x_340_ = lean_usize_of_nat(v___x_331_);
v___x_341_ = ((size_t)1ULL);
v___x_342_ = lean_usize_sub(v___x_340_, v___x_341_);
v___x_343_ = lean_usize_land(v___x_339_, v___x_342_);
v___x_344_ = lean_array_uget_borrowed(v_buckets_330_, v___x_343_);
v___x_345_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(v_a_329_, v___x_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_346_, lean_object* v_a_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(v_m_346_, v_a_347_);
lean_dec_ref(v_a_347_);
lean_dec_ref(v_m_346_);
return v_res_348_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0(void){
_start:
{
lean_object* v___x_350_; lean_object* v_dummy_351_; 
v___x_350_ = lean_box(0);
v_dummy_351_ = l_Lean_Expr_sort___override(v___x_350_);
return v_dummy_351_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1(lean_object* v_pre_352_, lean_object* v_post_353_, size_t v_sz_354_, size_t v_i_355_, lean_object* v_bs_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
uint8_t v___x_361_; 
v___x_361_ = lean_usize_dec_lt(v_i_355_, v_sz_354_);
if (v___x_361_ == 0)
{
lean_object* v___x_362_; 
lean_dec_ref(v_post_353_);
lean_dec_ref(v_pre_352_);
v___x_362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_362_, 0, v_bs_356_);
return v___x_362_;
}
else
{
lean_object* v_v_363_; lean_object* v___x_364_; 
v_v_363_ = lean_array_uget_borrowed(v_bs_356_, v_i_355_);
lean_inc(v_v_363_);
lean_inc_ref(v_post_353_);
lean_inc_ref(v_pre_352_);
v___x_364_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_352_, v_post_353_, v_v_363_, v___y_357_, v___y_358_, v___y_359_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_object* v_a_365_; lean_object* v___x_366_; lean_object* v_bs_x27_367_; size_t v___x_368_; size_t v___x_369_; lean_object* v___x_370_; 
v_a_365_ = lean_ctor_get(v___x_364_, 0);
lean_inc(v_a_365_);
lean_dec_ref_known(v___x_364_, 1);
v___x_366_ = lean_unsigned_to_nat(0u);
v_bs_x27_367_ = lean_array_uset(v_bs_356_, v_i_355_, v___x_366_);
v___x_368_ = ((size_t)1ULL);
v___x_369_ = lean_usize_add(v_i_355_, v___x_368_);
v___x_370_ = lean_array_uset(v_bs_x27_367_, v_i_355_, v_a_365_);
v_i_355_ = v___x_369_;
v_bs_356_ = v___x_370_;
goto _start;
}
else
{
lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_379_; 
lean_dec_ref(v_bs_356_);
lean_dec_ref(v_post_353_);
lean_dec_ref(v_pre_352_);
v_a_372_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_379_ == 0)
{
v___x_374_ = v___x_364_;
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v___x_364_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_377_; 
if (v_isShared_375_ == 0)
{
v___x_377_ = v___x_374_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_a_372_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4(lean_object* v_pre_380_, lean_object* v_post_381_, lean_object* v_x_382_, lean_object* v_x_383_, lean_object* v_x_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
if (lean_obj_tag(v_x_382_) == 5)
{
lean_object* v_fn_389_; lean_object* v_arg_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v_fn_389_ = lean_ctor_get(v_x_382_, 0);
lean_inc_ref(v_fn_389_);
v_arg_390_ = lean_ctor_get(v_x_382_, 1);
lean_inc_ref(v_arg_390_);
lean_dec_ref_known(v_x_382_, 2);
v___x_391_ = lean_array_set(v_x_383_, v_x_384_, v_arg_390_);
v___x_392_ = lean_unsigned_to_nat(1u);
v___x_393_ = lean_nat_sub(v_x_384_, v___x_392_);
lean_dec(v_x_384_);
v_x_382_ = v_fn_389_;
v_x_383_ = v___x_391_;
v_x_384_ = v___x_393_;
goto _start;
}
else
{
lean_object* v___x_395_; 
lean_dec(v_x_384_);
lean_inc_ref(v_post_381_);
lean_inc_ref(v_pre_380_);
v___x_395_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_380_, v_post_381_, v_x_382_, v___y_385_, v___y_386_, v___y_387_);
if (lean_obj_tag(v___x_395_) == 0)
{
lean_object* v_a_396_; size_t v_sz_397_; size_t v___x_398_; lean_object* v___x_399_; 
v_a_396_ = lean_ctor_get(v___x_395_, 0);
lean_inc(v_a_396_);
lean_dec_ref_known(v___x_395_, 1);
v_sz_397_ = lean_array_size(v_x_383_);
v___x_398_ = ((size_t)0ULL);
lean_inc_ref(v_post_381_);
lean_inc_ref(v_pre_380_);
v___x_399_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1(v_pre_380_, v_post_381_, v_sz_397_, v___x_398_, v_x_383_, v___y_385_, v___y_386_, v___y_387_);
if (lean_obj_tag(v___x_399_) == 0)
{
lean_object* v_a_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v_a_400_ = lean_ctor_get(v___x_399_, 0);
lean_inc(v_a_400_);
lean_dec_ref_known(v___x_399_, 1);
v___x_401_ = l_Lean_mkAppN(v_a_396_, v_a_400_);
lean_dec(v_a_400_);
v___x_402_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_380_, v_post_381_, v___x_401_, v___y_385_, v___y_386_, v___y_387_);
return v___x_402_;
}
else
{
lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_410_; 
lean_dec(v_a_396_);
lean_dec_ref(v_post_381_);
lean_dec_ref(v_pre_380_);
v_a_403_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_410_ == 0)
{
v___x_405_ = v___x_399_;
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_dec(v___x_399_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_408_; 
if (v_isShared_406_ == 0)
{
v___x_408_ = v___x_405_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_a_403_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
}
else
{
lean_dec_ref(v_x_383_);
lean_dec_ref(v_post_381_);
lean_dec_ref(v_pre_380_);
return v___x_395_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1(lean_object* v___x_411_, lean_object* v_pre_412_, lean_object* v_e_413_, lean_object* v_post_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Lean_Core_checkSystem(v___x_411_, v___y_416_, v___y_417_);
if (lean_obj_tag(v___x_419_) == 0)
{
lean_object* v___x_420_; 
lean_dec_ref_known(v___x_419_, 1);
lean_inc_ref(v_pre_412_);
lean_inc(v___y_417_);
lean_inc_ref(v___y_416_);
lean_inc_ref(v_e_413_);
v___x_420_ = lean_apply_4(v_pre_412_, v_e_413_, v___y_416_, v___y_417_, lean_box(0));
if (lean_obj_tag(v___x_420_) == 0)
{
lean_object* v_a_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_536_; 
v_a_421_ = lean_ctor_get(v___x_420_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_536_ == 0)
{
v___x_423_ = v___x_420_;
v_isShared_424_ = v_isSharedCheck_536_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_a_421_);
lean_dec(v___x_420_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_536_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___y_426_; 
switch(lean_obj_tag(v_a_421_))
{
case 0:
{
lean_object* v_e_526_; lean_object* v___x_528_; 
lean_dec_ref(v_post_414_);
lean_dec_ref(v_e_413_);
lean_dec_ref(v_pre_412_);
v_e_526_ = lean_ctor_get(v_a_421_, 0);
lean_inc_ref(v_e_526_);
lean_dec_ref_known(v_a_421_, 1);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 0, v_e_526_);
v___x_528_ = v___x_423_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_e_526_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
case 1:
{
lean_object* v_e_530_; lean_object* v___x_531_; 
lean_del_object(v___x_423_);
lean_dec_ref(v_e_413_);
v_e_530_ = lean_ctor_get(v_a_421_, 0);
lean_inc_ref(v_e_530_);
lean_dec_ref_known(v_a_421_, 1);
lean_inc_ref(v_post_414_);
lean_inc_ref(v_pre_412_);
v___x_531_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_412_, v_post_414_, v_e_530_, v___y_415_, v___y_416_, v___y_417_);
if (lean_obj_tag(v___x_531_) == 0)
{
lean_object* v_a_532_; lean_object* v___x_533_; 
v_a_532_ = lean_ctor_get(v___x_531_, 0);
lean_inc(v_a_532_);
lean_dec_ref_known(v___x_531_, 1);
v___x_533_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_412_, v_post_414_, v_a_532_, v___y_415_, v___y_416_, v___y_417_);
return v___x_533_;
}
else
{
lean_dec_ref(v_post_414_);
lean_dec_ref(v_pre_412_);
return v___x_531_;
}
}
default: 
{
lean_object* v_e_x3f_534_; 
lean_del_object(v___x_423_);
v_e_x3f_534_ = lean_ctor_get(v_a_421_, 0);
lean_inc(v_e_x3f_534_);
lean_dec_ref_known(v_a_421_, 1);
if (lean_obj_tag(v_e_x3f_534_) == 0)
{
v___y_426_ = v_e_413_;
goto v___jp_425_;
}
else
{
lean_object* v_val_535_; 
lean_dec_ref(v_e_413_);
v_val_535_ = lean_ctor_get(v_e_x3f_534_, 0);
lean_inc(v_val_535_);
lean_dec_ref_known(v_e_x3f_534_, 1);
v___y_426_ = v_val_535_;
goto v___jp_425_;
}
}
}
v___jp_425_:
{
switch(lean_obj_tag(v___y_426_))
{
case 7:
{
lean_object* v_binderName_427_; lean_object* v_binderType_428_; lean_object* v_body_429_; uint8_t v_binderInfo_430_; lean_object* v___x_431_; 
v_binderName_427_ = lean_ctor_get(v___y_426_, 0);
v_binderType_428_ = lean_ctor_get(v___y_426_, 1);
v_body_429_ = lean_ctor_get(v___y_426_, 2);
v_binderInfo_430_ = lean_ctor_get_uint8(v___y_426_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_428_);
lean_inc_ref(v_post_414_);
lean_inc_ref(v_pre_412_);
v___x_431_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_412_, v_post_414_, v_binderType_428_, v___y_415_, v___y_416_, v___y_417_);
if (lean_obj_tag(v___x_431_) == 0)
{
lean_object* v_a_432_; lean_object* v___x_433_; 
v_a_432_ = lean_ctor_get(v___x_431_, 0);
lean_inc(v_a_432_);
lean_dec_ref_known(v___x_431_, 1);
lean_inc_ref(v_body_429_);
lean_inc_ref(v_post_414_);
lean_inc_ref(v_pre_412_);
v___x_433_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_412_, v_post_414_, v_body_429_, v___y_415_, v___y_416_, v___y_417_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v_a_434_; size_t v___x_435_; size_t v___x_436_; uint8_t v___x_437_; 
v_a_434_ = lean_ctor_get(v___x_433_, 0);
lean_inc(v_a_434_);
lean_dec_ref_known(v___x_433_, 1);
v___x_435_ = lean_ptr_addr(v_binderType_428_);
v___x_436_ = lean_ptr_addr(v_a_432_);
v___x_437_ = lean_usize_dec_eq(v___x_435_, v___x_436_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; lean_object* v___x_439_; 
lean_inc(v_binderName_427_);
lean_dec_ref_known(v___y_426_, 3);
v___x_438_ = l_Lean_Expr_forallE___override(v_binderName_427_, v_a_432_, v_a_434_, v_binderInfo_430_);
v___x_439_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_412_, v_post_414_, v___x_438_, v___y_415_, v___y_416_, v___y_417_);
return v___x_439_;
}
else
{
size_t v___x_440_; size_t v___x_441_; uint8_t v___x_442_; 
v___x_440_ = lean_ptr_addr(v_body_429_);
v___x_441_ = lean_ptr_addr(v_a_434_);
v___x_442_ = lean_usize_dec_eq(v___x_440_, v___x_441_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; lean_object* v___x_444_; 
lean_inc(v_binderName_427_);
lean_dec_ref_known(v___y_426_, 3);
v___x_443_ = l_Lean_Expr_forallE___override(v_binderName_427_, v_a_432_, v_a_434_, v_binderInfo_430_);
v___x_444_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_412_, v_post_414_, v___x_443_, v___y_415_, v___y_416_, v___y_417_);
return v___x_444_;
}
else
{
uint8_t v___x_445_; 
v___x_445_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_430_, v_binderInfo_430_);
if (v___x_445_ == 0)
{
lean_object* v___x_446_; lean_object* v___x_447_; 
lean_inc(v_binderName_427_);
lean_dec_ref_known(v___y_426_, 3);
v___x_446_ = l_Lean_Expr_forallE___override(v_binderName_427_, v_a_432_, v_a_434_, v_binderInfo_430_);
v___x_447_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_412_, v_post_414_, v___x_446_, v___y_415_, v___y_416_, v___y_417_);
return v___x_447_;
}
else
{
lean_object* v___x_448_; 
lean_dec(v_a_434_);
lean_dec(v_a_432_);
v___x_448_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_412_, v_post_414_, v___y_426_, v___y_415_, v___y_416_, v___y_417_);
return v___x_448_;
}
}
}
}
else
{
lean_dec(v_a_432_);
lean_dec_ref_known(v___y_426_, 3);
lean_dec_ref(v_post_414_);
lean_dec_ref(v_pre_412_);
return v___x_433_;
}
}
else
{
lean_dec_ref_known(v___y_426_, 3);
lean_dec_ref(v_post_414_);
lean_dec_ref(v_pre_412_);
return v___x_431_;
}
}
case 6:
{
lean_object* v_binderName_449_; lean_object* v_binderType_450_; lean_object* v_body_451_; uint8_t v_binderInfo_452_; lean_object* v___x_453_; 
v_binderName_449_ = lean_ctor_get(v___y_426_, 0);
v_binderType_450_ = lean_ctor_get(v___y_426_, 1);
v_body_451_ = lean_ctor_get(v___y_426_, 2);
v_binderInfo_452_ = lean_ctor_get_uint8(v___y_426_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_450_);
lean_inc_ref(v_post_414_);
lean_inc_ref(v_pre_412_);
v___x_453_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_412_, v_post_414_, v_binderType_450_, v___y_415_, v___y_416_, v___y_417_);
if (lean_obj_tag(v___x_453_) == 0)
{
lean_object* v_a_454_; lean_object* v___x_455_; 
v_a_454_ = lean_ctor_get(v___x_453_, 0);
lean_inc(v_a_454_);
lean_dec_ref_known(v___x_453_, 1);
lean_inc_ref(v_body_451_);
lean_inc_ref(v_post_414_);
lean_inc_ref(v_pre_412_);
v___x_455_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_412_, v_post_414_, v_body_451_, v___y_415_, v___y_416_, v___y_417_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v_a_456_; size_t v___x_457_; size_t v___x_458_; uint8_t v___x_459_; 
v_a_456_ = lean_ctor_get(v___x_455_, 0);
lean_inc(v_a_456_);
lean_dec_ref_known(v___x_455_, 1);
v___x_457_ = lean_ptr_addr(v_binderType_450_);
v___x_458_ = lean_ptr_addr(v_a_454_);
v___x_459_ = lean_usize_dec_eq(v___x_457_, v___x_458_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; lean_object* v___x_461_; 
lean_inc(v_binderName_449_);
lean_dec_ref_known(v___y_426_, 3);
v___x_460_ = l_Lean_Expr_lam___override(v_binderName_449_, v_a_454_, v_a_456_, v_binderInfo_452_);
v___x_461_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_412_, v_post_414_, v___x_460_, v___y_415_, v___y_416_, v___y_417_);
return v___x_461_;
}
else
{
size_t v___x_462_; size_t v___x_463_; uint8_t v___x_464_; 
v___x_462_ = lean_ptr_addr(v_body_451_);
v___x_463_ = lean_ptr_addr(v_a_456_);
v___x_464_ = lean_usize_dec_eq(v___x_462_, v___x_463_);
if (v___x_464_ == 0)
{
lean_object* v___x_465_; lean_object* v___x_466_; 
lean_inc(v_binderName_449_);
lean_dec_ref_known(v___y_426_, 3);
v___x_465_ = l_Lean_Expr_lam___override(v_binderName_449_, v_a_454_, v_a_456_, v_binderInfo_452_);
v___x_466_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_412_, v_post_414_, v___x_465_, v___y_415_, v___y_416_, v___y_417_);
return v___x_466_;
}
else
{
uint8_t v___x_467_; 
v___x_467_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_452_, v_binderInfo_452_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; lean_object* v___x_469_; 
lean_inc(v_binderName_449_);
lean_dec_ref_known(v___y_426_, 3);
v___x_468_ = l_Lean_Expr_lam___override(v_binderName_449_, v_a_454_, v_a_456_, v_binderInfo_452_);
v___x_469_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_412_, v_post_414_, v___x_468_, v___y_415_, v___y_416_, v___y_417_);
return v___x_469_;
}
else
{
lean_object* v___x_470_; 
lean_dec(v_a_456_);
lean_dec(v_a_454_);
v___x_470_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_412_, v_post_414_, v___y_426_, v___y_415_, v___y_416_, v___y_417_);
return v___x_470_;
}
}
}
}
else
{
lean_dec(v_a_454_);
lean_dec_ref_known(v___y_426_, 3);
lean_dec_ref(v_post_414_);
lean_dec_ref(v_pre_412_);
return v___x_455_;
}
}
else
{
lean_dec_ref_known(v___y_426_, 3);
lean_dec_ref(v_post_414_);
lean_dec_ref(v_pre_412_);
return v___x_453_;
}
}
case 8:
{
lean_object* v_declName_471_; lean_object* v_type_472_; lean_object* v_value_473_; lean_object* v_body_474_; uint8_t v_nondep_475_; lean_object* v___x_476_; 
v_declName_471_ = lean_ctor_get(v___y_426_, 0);
v_type_472_ = lean_ctor_get(v___y_426_, 1);
v_value_473_ = lean_ctor_get(v___y_426_, 2);
v_body_474_ = lean_ctor_get(v___y_426_, 3);
v_nondep_475_ = lean_ctor_get_uint8(v___y_426_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_472_);
lean_inc_ref(v_post_414_);
lean_inc_ref(v_pre_412_);
v___x_476_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_412_, v_post_414_, v_type_472_, v___y_415_, v___y_416_, v___y_417_);
if (lean_obj_tag(v___x_476_) == 0)
{
lean_object* v_a_477_; lean_object* v___x_478_; 
v_a_477_ = lean_ctor_get(v___x_476_, 0);
lean_inc(v_a_477_);
lean_dec_ref_known(v___x_476_, 1);
lean_inc_ref(v_value_473_);
lean_inc_ref(v_post_414_);
lean_inc_ref(v_pre_412_);
v___x_478_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_412_, v_post_414_, v_value_473_, v___y_415_, v___y_416_, v___y_417_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v_a_479_; lean_object* v___x_480_; 
v_a_479_ = lean_ctor_get(v___x_478_, 0);
lean_inc(v_a_479_);
lean_dec_ref_known(v___x_478_, 1);
lean_inc_ref(v_body_474_);
lean_inc_ref(v_post_414_);
lean_inc_ref(v_pre_412_);
v___x_480_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_412_, v_post_414_, v_body_474_, v___y_415_, v___y_416_, v___y_417_);
if (lean_obj_tag(v___x_480_) == 0)
{
lean_object* v_a_481_; size_t v___x_482_; size_t v___x_483_; uint8_t v___x_484_; 
v_a_481_ = lean_ctor_get(v___x_480_, 0);
lean_inc(v_a_481_);
lean_dec_ref_known(v___x_480_, 1);
v___x_482_ = lean_ptr_addr(v_type_472_);
v___x_483_ = lean_ptr_addr(v_a_477_);
v___x_484_ = lean_usize_dec_eq(v___x_482_, v___x_483_);
if (v___x_484_ == 0)
{
lean_object* v___x_485_; lean_object* v___x_486_; 
lean_inc(v_declName_471_);
lean_dec_ref_known(v___y_426_, 4);
v___x_485_ = l_Lean_Expr_letE___override(v_declName_471_, v_a_477_, v_a_479_, v_a_481_, v_nondep_475_);
v___x_486_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_412_, v_post_414_, v___x_485_, v___y_415_, v___y_416_, v___y_417_);
return v___x_486_;
}
else
{
size_t v___x_487_; size_t v___x_488_; uint8_t v___x_489_; 
v___x_487_ = lean_ptr_addr(v_value_473_);
v___x_488_ = lean_ptr_addr(v_a_479_);
v___x_489_ = lean_usize_dec_eq(v___x_487_, v___x_488_);
if (v___x_489_ == 0)
{
lean_object* v___x_490_; lean_object* v___x_491_; 
lean_inc(v_declName_471_);
lean_dec_ref_known(v___y_426_, 4);
v___x_490_ = l_Lean_Expr_letE___override(v_declName_471_, v_a_477_, v_a_479_, v_a_481_, v_nondep_475_);
v___x_491_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_412_, v_post_414_, v___x_490_, v___y_415_, v___y_416_, v___y_417_);
return v___x_491_;
}
else
{
size_t v___x_492_; size_t v___x_493_; uint8_t v___x_494_; 
v___x_492_ = lean_ptr_addr(v_body_474_);
v___x_493_ = lean_ptr_addr(v_a_481_);
v___x_494_ = lean_usize_dec_eq(v___x_492_, v___x_493_);
if (v___x_494_ == 0)
{
lean_object* v___x_495_; lean_object* v___x_496_; 
lean_inc(v_declName_471_);
lean_dec_ref_known(v___y_426_, 4);
v___x_495_ = l_Lean_Expr_letE___override(v_declName_471_, v_a_477_, v_a_479_, v_a_481_, v_nondep_475_);
v___x_496_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_412_, v_post_414_, v___x_495_, v___y_415_, v___y_416_, v___y_417_);
return v___x_496_;
}
else
{
lean_object* v___x_497_; 
lean_dec(v_a_481_);
lean_dec(v_a_479_);
lean_dec(v_a_477_);
v___x_497_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_412_, v_post_414_, v___y_426_, v___y_415_, v___y_416_, v___y_417_);
return v___x_497_;
}
}
}
}
else
{
lean_dec(v_a_479_);
lean_dec(v_a_477_);
lean_dec_ref_known(v___y_426_, 4);
lean_dec_ref(v_post_414_);
lean_dec_ref(v_pre_412_);
return v___x_480_;
}
}
else
{
lean_dec(v_a_477_);
lean_dec_ref_known(v___y_426_, 4);
lean_dec_ref(v_post_414_);
lean_dec_ref(v_pre_412_);
return v___x_478_;
}
}
else
{
lean_dec_ref_known(v___y_426_, 4);
lean_dec_ref(v_post_414_);
lean_dec_ref(v_pre_412_);
return v___x_476_;
}
}
case 5:
{
lean_object* v_dummy_498_; lean_object* v_nargs_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v_dummy_498_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0);
v_nargs_499_ = l_Lean_Expr_getAppNumArgs(v___y_426_);
lean_inc(v_nargs_499_);
v___x_500_ = lean_mk_array(v_nargs_499_, v_dummy_498_);
v___x_501_ = lean_unsigned_to_nat(1u);
v___x_502_ = lean_nat_sub(v_nargs_499_, v___x_501_);
lean_dec(v_nargs_499_);
v___x_503_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4(v_pre_412_, v_post_414_, v___y_426_, v___x_500_, v___x_502_, v___y_415_, v___y_416_, v___y_417_);
return v___x_503_;
}
case 10:
{
lean_object* v_data_504_; lean_object* v_expr_505_; lean_object* v___x_506_; 
v_data_504_ = lean_ctor_get(v___y_426_, 0);
v_expr_505_ = lean_ctor_get(v___y_426_, 1);
lean_inc_ref(v_expr_505_);
lean_inc_ref(v_post_414_);
lean_inc_ref(v_pre_412_);
v___x_506_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_412_, v_post_414_, v_expr_505_, v___y_415_, v___y_416_, v___y_417_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v_a_507_; size_t v___x_508_; size_t v___x_509_; uint8_t v___x_510_; 
v_a_507_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_a_507_);
lean_dec_ref_known(v___x_506_, 1);
v___x_508_ = lean_ptr_addr(v_expr_505_);
v___x_509_ = lean_ptr_addr(v_a_507_);
v___x_510_ = lean_usize_dec_eq(v___x_508_, v___x_509_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; lean_object* v___x_512_; 
lean_inc(v_data_504_);
lean_dec_ref_known(v___y_426_, 2);
v___x_511_ = l_Lean_Expr_mdata___override(v_data_504_, v_a_507_);
v___x_512_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_412_, v_post_414_, v___x_511_, v___y_415_, v___y_416_, v___y_417_);
return v___x_512_;
}
else
{
lean_object* v___x_513_; 
lean_dec(v_a_507_);
v___x_513_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_412_, v_post_414_, v___y_426_, v___y_415_, v___y_416_, v___y_417_);
return v___x_513_;
}
}
else
{
lean_dec_ref_known(v___y_426_, 2);
lean_dec_ref(v_post_414_);
lean_dec_ref(v_pre_412_);
return v___x_506_;
}
}
case 11:
{
lean_object* v_typeName_514_; lean_object* v_idx_515_; lean_object* v_struct_516_; lean_object* v___x_517_; 
v_typeName_514_ = lean_ctor_get(v___y_426_, 0);
v_idx_515_ = lean_ctor_get(v___y_426_, 1);
v_struct_516_ = lean_ctor_get(v___y_426_, 2);
lean_inc_ref(v_struct_516_);
lean_inc_ref(v_post_414_);
lean_inc_ref(v_pre_412_);
v___x_517_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_412_, v_post_414_, v_struct_516_, v___y_415_, v___y_416_, v___y_417_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v_a_518_; size_t v___x_519_; size_t v___x_520_; uint8_t v___x_521_; 
v_a_518_ = lean_ctor_get(v___x_517_, 0);
lean_inc(v_a_518_);
lean_dec_ref_known(v___x_517_, 1);
v___x_519_ = lean_ptr_addr(v_struct_516_);
v___x_520_ = lean_ptr_addr(v_a_518_);
v___x_521_ = lean_usize_dec_eq(v___x_519_, v___x_520_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; lean_object* v___x_523_; 
lean_inc(v_idx_515_);
lean_inc(v_typeName_514_);
lean_dec_ref_known(v___y_426_, 3);
v___x_522_ = l_Lean_Expr_proj___override(v_typeName_514_, v_idx_515_, v_a_518_);
v___x_523_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_412_, v_post_414_, v___x_522_, v___y_415_, v___y_416_, v___y_417_);
return v___x_523_;
}
else
{
lean_object* v___x_524_; 
lean_dec(v_a_518_);
v___x_524_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_412_, v_post_414_, v___y_426_, v___y_415_, v___y_416_, v___y_417_);
return v___x_524_;
}
}
else
{
lean_dec_ref_known(v___y_426_, 3);
lean_dec_ref(v_post_414_);
lean_dec_ref(v_pre_412_);
return v___x_517_;
}
}
default: 
{
lean_object* v___x_525_; 
v___x_525_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_412_, v_post_414_, v___y_426_, v___y_415_, v___y_416_, v___y_417_);
return v___x_525_;
}
}
}
}
}
else
{
lean_object* v_a_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_544_; 
lean_dec_ref(v_post_414_);
lean_dec_ref(v_e_413_);
lean_dec_ref(v_pre_412_);
v_a_537_ = lean_ctor_get(v___x_420_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_544_ == 0)
{
v___x_539_ = v___x_420_;
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_a_537_);
lean_dec(v___x_420_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_542_; 
if (v_isShared_540_ == 0)
{
v___x_542_ = v___x_539_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_a_537_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
}
else
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_552_; 
lean_dec_ref(v_post_414_);
lean_dec_ref(v_e_413_);
lean_dec_ref(v_pre_412_);
v_a_545_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_552_ == 0)
{
v___x_547_ = v___x_419_;
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___x_419_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
if (v_isShared_548_ == 0)
{
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_a_545_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___boxed(lean_object* v___x_553_, lean_object* v_pre_554_, lean_object* v_e_555_, lean_object* v_post_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1(v___x_553_, v_pre_554_, v_e_555_, v_post_556_, v___y_557_, v___y_558_, v___y_559_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
lean_dec(v___y_557_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(lean_object* v_pre_562_, lean_object* v_post_563_, lean_object* v_e_564_, lean_object* v_a_565_, lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; 
lean_inc(v_a_565_);
v___x_569_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_569_, 0, lean_box(0));
lean_closure_set(v___x_569_, 1, lean_box(0));
lean_closure_set(v___x_569_, 2, v_a_565_);
v___x_570_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(lean_box(0), v___x_569_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v_a_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_602_; 
v_a_571_ = lean_ctor_get(v___x_570_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_602_ == 0)
{
v___x_573_ = v___x_570_;
v_isShared_574_ = v_isSharedCheck_602_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_a_571_);
lean_dec(v___x_570_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_602_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_575_; 
v___x_575_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(v_a_571_, v_e_564_);
lean_dec(v_a_571_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v___x_576_; lean_object* v___f_577_; lean_object* v___x_578_; 
lean_del_object(v___x_573_);
v___x_576_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___closed__0));
lean_inc_ref(v_e_564_);
v___f_577_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___boxed), 8, 4);
lean_closure_set(v___f_577_, 0, v___x_576_);
lean_closure_set(v___f_577_, 1, v_pre_562_);
lean_closure_set(v___f_577_, 2, v_e_564_);
lean_closure_set(v___f_577_, 3, v_post_563_);
v___x_578_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(v___f_577_, v_a_565_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v_a_579_; lean_object* v___f_580_; lean_object* v___x_581_; 
v_a_579_ = lean_ctor_get(v___x_578_, 0);
lean_inc_n(v_a_579_, 2);
lean_dec_ref_known(v___x_578_, 1);
lean_inc(v_a_565_);
v___f_580_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_580_, 0, v_a_565_);
lean_closure_set(v___f_580_, 1, v_e_564_);
lean_closure_set(v___f_580_, 2, v_a_579_);
v___x_581_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(lean_box(0), v___f_580_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_588_; 
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_588_ == 0)
{
lean_object* v_unused_589_; 
v_unused_589_ = lean_ctor_get(v___x_581_, 0);
lean_dec(v_unused_589_);
v___x_583_ = v___x_581_;
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
else
{
lean_dec(v___x_581_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_586_; 
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 0, v_a_579_);
v___x_586_ = v___x_583_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_a_579_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
else
{
lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_597_; 
lean_dec(v_a_579_);
v_a_590_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_597_ == 0)
{
v___x_592_ = v___x_581_;
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_581_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_595_; 
if (v_isShared_593_ == 0)
{
v___x_595_ = v___x_592_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_a_590_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
}
else
{
lean_dec_ref(v_e_564_);
return v___x_578_;
}
}
else
{
lean_object* v_val_598_; lean_object* v___x_600_; 
lean_dec_ref(v_e_564_);
lean_dec_ref(v_post_563_);
lean_dec_ref(v_pre_562_);
v_val_598_ = lean_ctor_get(v___x_575_, 0);
lean_inc(v_val_598_);
lean_dec_ref_known(v___x_575_, 1);
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 0, v_val_598_);
v___x_600_ = v___x_573_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_val_598_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
else
{
lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_610_; 
lean_dec_ref(v_e_564_);
lean_dec_ref(v_post_563_);
lean_dec_ref(v_pre_562_);
v_a_603_ = lean_ctor_get(v___x_570_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_610_ == 0)
{
v___x_605_ = v___x_570_;
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v___x_570_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(lean_object* v_pre_611_, lean_object* v_post_612_, lean_object* v_e_613_, lean_object* v_a_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
lean_object* v___x_618_; 
lean_inc_ref(v_post_612_);
lean_inc(v___y_616_);
lean_inc_ref(v___y_615_);
lean_inc_ref(v_e_613_);
v___x_618_ = lean_apply_4(v_post_612_, v_e_613_, v___y_615_, v___y_616_, lean_box(0));
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v_a_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_637_; 
v_a_619_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_637_ == 0)
{
v___x_621_ = v___x_618_;
v_isShared_622_ = v_isSharedCheck_637_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_a_619_);
lean_dec(v___x_618_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_637_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
switch(lean_obj_tag(v_a_619_))
{
case 0:
{
lean_object* v_e_623_; lean_object* v___x_625_; 
lean_dec_ref(v_e_613_);
lean_dec_ref(v_post_612_);
lean_dec_ref(v_pre_611_);
v_e_623_ = lean_ctor_get(v_a_619_, 0);
lean_inc_ref(v_e_623_);
lean_dec_ref_known(v_a_619_, 1);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v_e_623_);
v___x_625_ = v___x_621_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_e_623_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
case 1:
{
lean_object* v_e_627_; lean_object* v___x_628_; 
lean_del_object(v___x_621_);
lean_dec_ref(v_e_613_);
v_e_627_ = lean_ctor_get(v_a_619_, 0);
lean_inc_ref(v_e_627_);
lean_dec_ref_known(v_a_619_, 1);
v___x_628_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_611_, v_post_612_, v_e_627_, v_a_614_, v___y_615_, v___y_616_);
return v___x_628_;
}
default: 
{
lean_object* v_e_x3f_629_; 
lean_dec_ref(v_post_612_);
lean_dec_ref(v_pre_611_);
v_e_x3f_629_ = lean_ctor_get(v_a_619_, 0);
lean_inc(v_e_x3f_629_);
lean_dec_ref_known(v_a_619_, 1);
if (lean_obj_tag(v_e_x3f_629_) == 0)
{
lean_object* v___x_631_; 
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v_e_613_);
v___x_631_ = v___x_621_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_e_613_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
else
{
lean_object* v_val_633_; lean_object* v___x_635_; 
lean_dec_ref(v_e_613_);
v_val_633_ = lean_ctor_get(v_e_x3f_629_, 0);
lean_inc(v_val_633_);
lean_dec_ref_known(v_e_x3f_629_, 1);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v_val_633_);
v___x_635_ = v___x_621_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_val_633_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
}
}
}
else
{
lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_645_; 
lean_dec_ref(v_e_613_);
lean_dec_ref(v_post_612_);
lean_dec_ref(v_pre_611_);
v_a_638_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_645_ == 0)
{
v___x_640_ = v___x_618_;
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_dec(v___x_618_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_643_; 
if (v_isShared_641_ == 0)
{
v___x_643_ = v___x_640_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_a_638_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_646_, lean_object* v_post_647_, lean_object* v_e_648_, lean_object* v_a_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_646_, v_post_647_, v_e_648_, v_a_649_, v___y_650_, v___y_651_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
lean_dec(v_a_649_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_654_, lean_object* v_post_655_, lean_object* v_sz_656_, lean_object* v_i_657_, lean_object* v_bs_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
size_t v_sz_boxed_663_; size_t v_i_boxed_664_; lean_object* v_res_665_; 
v_sz_boxed_663_ = lean_unbox_usize(v_sz_656_);
lean_dec(v_sz_656_);
v_i_boxed_664_ = lean_unbox_usize(v_i_657_);
lean_dec(v_i_657_);
v_res_665_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1(v_pre_654_, v_post_655_, v_sz_boxed_663_, v_i_boxed_664_, v_bs_658_, v___y_659_, v___y_660_, v___y_661_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_666_, lean_object* v_post_667_, lean_object* v_x_668_, lean_object* v_x_669_, lean_object* v_x_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4(v_pre_666_, v_post_667_, v_x_668_, v_x_669_, v_x_670_, v___y_671_, v___y_672_, v___y_673_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___boxed(lean_object* v_pre_676_, lean_object* v_post_677_, lean_object* v_e_678_, lean_object* v_a_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_676_, v_post_677_, v_e_678_, v_a_679_, v___y_680_, v___y_681_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v_a_679_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(lean_object* v_00_u03b1_684_, lean_object* v_x_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_689_ = lean_apply_1(v_x_685_, lean_box(0));
v___x_690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0___boxed(lean_object* v_00_u03b1_691_, lean_object* v_x_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(v_00_u03b1_691_, v_x_692_, v___y_693_, v___y_694_);
lean_dec(v___y_694_);
lean_dec_ref(v___y_693_);
return v_res_696_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0(void){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_697_ = lean_box(0);
v___x_698_ = lean_unsigned_to_nat(16u);
v___x_699_ = lean_mk_array(v___x_698_, v___x_697_);
return v___x_699_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1(void){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_700_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0);
v___x_701_ = lean_unsigned_to_nat(0u);
v___x_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_702_, 0, v___x_701_);
lean_ctor_set(v___x_702_, 1, v___x_700_);
return v___x_702_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2(void){
_start:
{
lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_703_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1, &l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1);
v___x_704_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_704_, 0, lean_box(0));
lean_closure_set(v___x_704_, 1, lean_box(0));
lean_closure_set(v___x_704_, 2, v___x_703_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0(lean_object* v_input_705_, lean_object* v_pre_706_, lean_object* v_post_707_, lean_object* v___y_708_, lean_object* v___y_709_){
_start:
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v_a_713_; lean_object* v___x_714_; 
v___x_711_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2);
v___x_712_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(lean_box(0), v___x_711_, v___y_708_, v___y_709_);
v_a_713_ = lean_ctor_get(v___x_712_, 0);
lean_inc(v_a_713_);
lean_dec_ref(v___x_712_);
v___x_714_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_706_, v_post_707_, v_input_705_, v_a_713_, v___y_708_, v___y_709_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v_a_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_724_; 
v_a_715_ = lean_ctor_get(v___x_714_, 0);
lean_inc(v_a_715_);
lean_dec_ref_known(v___x_714_, 1);
v___x_716_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_716_, 0, lean_box(0));
lean_closure_set(v___x_716_, 1, lean_box(0));
lean_closure_set(v___x_716_, 2, v_a_713_);
v___x_717_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(lean_box(0), v___x_716_, v___y_708_, v___y_709_);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_724_ == 0)
{
lean_object* v_unused_725_; 
v_unused_725_ = lean_ctor_get(v___x_717_, 0);
lean_dec(v_unused_725_);
v___x_719_ = v___x_717_;
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
else
{
lean_dec(v___x_717_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_722_; 
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 0, v_a_715_);
v___x_722_ = v___x_719_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_a_715_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
else
{
lean_dec(v_a_713_);
return v___x_714_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___boxed(lean_object* v_input_726_, lean_object* v_pre_727_, lean_object* v_post_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0(v_input_726_, v_pre_727_, v_post_728_, v___y_729_, v___y_730_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam(lean_object* v_type_735_, lean_object* v_a_736_, lean_object* v_a_737_){
_start:
{
lean_object* v___f_739_; lean_object* v___f_740_; lean_object* v___x_741_; 
v___f_739_ = ((lean_object*)(l_Lean_Meta_elimOptParam___closed__0));
v___f_740_ = ((lean_object*)(l_Lean_Meta_elimOptParam___closed__1));
v___x_741_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0(v_type_735_, v___f_739_, v___f_740_, v_a_736_, v_a_737_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam___boxed(lean_object* v_type_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_Lean_Meta_elimOptParam(v_type_742_, v_a_743_, v_a_744_);
lean_dec(v_a_744_);
lean_dec_ref(v_a_743_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_747_, lean_object* v_m_748_, lean_object* v_a_749_){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(v_m_748_, v_a_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_751_, lean_object* v_m_752_, lean_object* v_a_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(v_00_u03b2_751_, v_m_752_, v_a_753_);
lean_dec_ref(v_a_753_);
lean_dec_ref(v_m_752_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_755_, lean_object* v_ref_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_756_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_761_, lean_object* v_ref_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_761_, v_ref_762_, v___y_763_, v___y_764_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8(lean_object* v_00_u03b1_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___redArg();
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8___boxed(lean_object* v_00_u03b1_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_772_, v___y_773_, v___y_774_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_777_, lean_object* v_x_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
lean_object* v___x_783_; 
v___x_783_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(v_x_778_, v___y_779_, v___y_780_, v___y_781_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_784_, lean_object* v_x_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5(v_00_u03b1_784_, v_x_785_, v___y_786_, v___y_787_, v___y_788_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec(v___y_786_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_791_, lean_object* v_m_792_, lean_object* v_a_793_, lean_object* v_b_794_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6___redArg(v_m_792_, v_a_793_, v_b_794_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_796_, lean_object* v_a_797_, lean_object* v_x_798_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(v_a_797_, v_x_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_800_, lean_object* v_a_801_, lean_object* v_x_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_800_, v_a_801_, v_x_802_);
lean_dec(v_x_802_);
lean_dec_ref(v_a_801_);
return v_res_803_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_804_, lean_object* v_a_805_, lean_object* v_x_806_){
_start:
{
uint8_t v___x_807_; 
v___x_807_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___redArg(v_a_805_, v_x_806_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___boxed(lean_object* v_00_u03b2_808_, lean_object* v_a_809_, lean_object* v_x_810_){
_start:
{
uint8_t v_res_811_; lean_object* v_r_812_; 
v_res_811_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_808_, v_a_809_, v_x_810_);
lean_dec(v_x_810_);
lean_dec_ref(v_a_809_);
v_r_812_ = lean_box(v_res_811_);
return v_r_812_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_813_, lean_object* v_data_814_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11___redArg(v_data_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__12(lean_object* v_00_u03b2_816_, lean_object* v_a_817_, lean_object* v_b_818_, lean_object* v_x_819_){
_start:
{
lean_object* v___x_820_; 
v___x_820_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__12___redArg(v_a_817_, v_b_818_, v_x_819_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12(lean_object* v_00_u03b2_821_, lean_object* v_i_822_, lean_object* v_source_823_, lean_object* v_target_824_){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v_i_822_, v_source_823_, v_target_824_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_826_, lean_object* v_x_827_, lean_object* v_x_828_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_x_827_, v_x_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0(uint8_t v_skipIfPropOrEq_830_, lean_object* v_as_831_, size_t v_sz_832_, size_t v_i_833_, lean_object* v_b_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
lean_object* v_a_841_; uint8_t v___x_845_; 
v___x_845_ = lean_usize_dec_lt(v_i_833_, v_sz_832_);
if (v___x_845_ == 0)
{
lean_object* v___x_846_; 
v___x_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_846_, 0, v_b_834_);
return v___x_846_;
}
else
{
lean_object* v_snd_847_; lean_object* v_fst_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_926_; 
v_snd_847_ = lean_ctor_get(v_b_834_, 1);
v_fst_848_ = lean_ctor_get(v_b_834_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v_b_834_);
if (v_isSharedCheck_926_ == 0)
{
v___x_850_ = v_b_834_;
v_isShared_851_ = v_isSharedCheck_926_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_snd_847_);
lean_inc(v_fst_848_);
lean_dec(v_b_834_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_926_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v_array_852_; lean_object* v_start_853_; lean_object* v_stop_854_; uint8_t v___x_855_; 
v_array_852_ = lean_ctor_get(v_snd_847_, 0);
v_start_853_ = lean_ctor_get(v_snd_847_, 1);
v_stop_854_ = lean_ctor_get(v_snd_847_, 2);
v___x_855_ = lean_nat_dec_lt(v_start_853_, v_stop_854_);
if (v___x_855_ == 0)
{
lean_object* v___x_857_; 
if (v_isShared_851_ == 0)
{
v___x_857_ = v___x_850_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_fst_848_);
lean_ctor_set(v_reuseFailAlloc_859_, 1, v_snd_847_);
v___x_857_ = v_reuseFailAlloc_859_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
lean_object* v___x_858_; 
v___x_858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_858_, 0, v___x_857_);
return v___x_858_;
}
}
else
{
lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_922_; 
lean_inc(v_stop_854_);
lean_inc(v_start_853_);
lean_inc_ref(v_array_852_);
v_isSharedCheck_922_ = !lean_is_exclusive(v_snd_847_);
if (v_isSharedCheck_922_ == 0)
{
lean_object* v_unused_923_; lean_object* v_unused_924_; lean_object* v_unused_925_; 
v_unused_923_ = lean_ctor_get(v_snd_847_, 2);
lean_dec(v_unused_923_);
v_unused_924_ = lean_ctor_get(v_snd_847_, 1);
lean_dec(v_unused_924_);
v_unused_925_ = lean_ctor_get(v_snd_847_, 0);
lean_dec(v_unused_925_);
v___x_861_ = v_snd_847_;
v_isShared_862_ = v_isSharedCheck_922_;
goto v_resetjp_860_;
}
else
{
lean_dec(v_snd_847_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_922_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v_a_863_; lean_object* v___x_864_; 
v_a_863_ = lean_array_uget_borrowed(v_as_831_, v_i_833_);
lean_inc(v___y_838_);
lean_inc_ref(v___y_837_);
lean_inc(v___y_836_);
lean_inc_ref(v___y_835_);
lean_inc(v_a_863_);
v___x_864_ = lean_infer_type(v_a_863_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_a_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_870_; 
v_a_865_ = lean_ctor_get(v___x_864_, 0);
lean_inc(v_a_865_);
lean_dec_ref_known(v___x_864_, 1);
v___x_866_ = lean_array_fget(v_array_852_, v_start_853_);
v___x_867_ = lean_unsigned_to_nat(1u);
v___x_868_ = lean_nat_add(v_start_853_, v___x_867_);
lean_dec(v_start_853_);
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 1, v___x_868_);
v___x_870_ = v___x_861_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_array_852_);
lean_ctor_set(v_reuseFailAlloc_913_, 1, v___x_868_);
lean_ctor_set(v_reuseFailAlloc_913_, 2, v_stop_854_);
v___x_870_ = v_reuseFailAlloc_913_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
if (v_skipIfPropOrEq_830_ == 0)
{
lean_object* v___x_871_; 
lean_dec(v_a_865_);
lean_inc(v_a_863_);
v___x_871_ = l_Lean_Meta_mkEqHEq(v_a_863_, v___x_866_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; lean_object* v___x_873_; lean_object* v___x_875_; 
v_a_872_ = lean_ctor_get(v___x_871_, 0);
lean_inc(v_a_872_);
lean_dec_ref_known(v___x_871_, 1);
v___x_873_ = lean_array_push(v_fst_848_, v_a_872_);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 1, v___x_870_);
lean_ctor_set(v___x_850_, 0, v___x_873_);
v___x_875_ = v___x_850_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_873_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v___x_870_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
v_a_841_ = v___x_875_;
goto v___jp_840_;
}
}
else
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_884_; 
lean_dec_ref(v___x_870_);
lean_del_object(v___x_850_);
lean_dec(v_fst_848_);
v_a_877_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_884_ == 0)
{
v___x_879_ = v___x_871_;
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_871_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_882_; 
if (v_isShared_880_ == 0)
{
v___x_882_ = v___x_879_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_a_877_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
else
{
lean_object* v___x_885_; 
v___x_885_ = l_Lean_Meta_isProp(v_a_865_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; uint8_t v___x_891_; 
v_a_886_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_a_886_);
lean_dec_ref_known(v___x_885_, 1);
v___x_891_ = lean_unbox(v_a_886_);
lean_dec(v_a_886_);
if (v___x_891_ == 0)
{
uint8_t v___x_892_; 
v___x_892_ = lean_expr_eqv(v_a_863_, v___x_866_);
if (v___x_892_ == 0)
{
lean_object* v___x_893_; 
lean_del_object(v___x_850_);
lean_inc(v_a_863_);
v___x_893_ = l_Lean_Meta_mkEqHEq(v_a_863_, v___x_866_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
if (lean_obj_tag(v___x_893_) == 0)
{
lean_object* v_a_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v_a_894_ = lean_ctor_get(v___x_893_, 0);
lean_inc(v_a_894_);
lean_dec_ref_known(v___x_893_, 1);
v___x_895_ = lean_array_push(v_fst_848_, v_a_894_);
v___x_896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_895_);
lean_ctor_set(v___x_896_, 1, v___x_870_);
v_a_841_ = v___x_896_;
goto v___jp_840_;
}
else
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_904_; 
lean_dec_ref(v___x_870_);
lean_dec(v_fst_848_);
v_a_897_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_904_ == 0)
{
v___x_899_ = v___x_893_;
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_893_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_902_; 
if (v_isShared_900_ == 0)
{
v___x_902_ = v___x_899_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_a_897_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
else
{
lean_dec(v___x_866_);
goto v___jp_887_;
}
}
else
{
lean_dec(v___x_866_);
goto v___jp_887_;
}
v___jp_887_:
{
lean_object* v___x_889_; 
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 1, v___x_870_);
v___x_889_ = v___x_850_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_fst_848_);
lean_ctor_set(v_reuseFailAlloc_890_, 1, v___x_870_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
v_a_841_ = v___x_889_;
goto v___jp_840_;
}
}
}
else
{
lean_object* v_a_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_912_; 
lean_dec_ref(v___x_870_);
lean_dec(v___x_866_);
lean_del_object(v___x_850_);
lean_dec(v_fst_848_);
v_a_905_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_912_ == 0)
{
v___x_907_ = v___x_885_;
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_a_905_);
lean_dec(v___x_885_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_910_; 
if (v_isShared_908_ == 0)
{
v___x_910_ = v___x_907_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_905_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
}
}
}
else
{
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_921_; 
lean_del_object(v___x_861_);
lean_dec(v_stop_854_);
lean_dec(v_start_853_);
lean_dec_ref(v_array_852_);
lean_del_object(v___x_850_);
lean_dec(v_fst_848_);
v_a_914_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_921_ == 0)
{
v___x_916_ = v___x_864_;
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_864_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_919_; 
if (v_isShared_917_ == 0)
{
v___x_919_ = v___x_916_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_a_914_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
}
}
}
}
v___jp_840_:
{
size_t v___x_842_; size_t v___x_843_; 
v___x_842_ = ((size_t)1ULL);
v___x_843_ = lean_usize_add(v_i_833_, v___x_842_);
v_i_833_ = v___x_843_;
v_b_834_ = v_a_841_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0___boxed(lean_object* v_skipIfPropOrEq_927_, lean_object* v_as_928_, lean_object* v_sz_929_, lean_object* v_i_930_, lean_object* v_b_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
uint8_t v_skipIfPropOrEq_boxed_937_; size_t v_sz_boxed_938_; size_t v_i_boxed_939_; lean_object* v_res_940_; 
v_skipIfPropOrEq_boxed_937_ = lean_unbox(v_skipIfPropOrEq_927_);
v_sz_boxed_938_ = lean_unbox_usize(v_sz_929_);
lean_dec(v_sz_929_);
v_i_boxed_939_ = lean_unbox_usize(v_i_930_);
lean_dec(v_i_930_);
v_res_940_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0(v_skipIfPropOrEq_boxed_937_, v_as_928_, v_sz_boxed_938_, v_i_boxed_939_, v_b_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec_ref(v_as_928_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(lean_object* v_args1_943_, lean_object* v_args2_944_, uint8_t v_skipIfPropOrEq_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_){
_start:
{
lean_object* v___x_951_; lean_object* v_eqs_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; size_t v_sz_956_; size_t v___x_957_; lean_object* v___x_958_; 
v___x_951_ = lean_unsigned_to_nat(0u);
v_eqs_952_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_953_ = lean_array_get_size(v_args2_944_);
v___x_954_ = l_Array_toSubarray___redArg(v_args2_944_, v___x_951_, v___x_953_);
v___x_955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_955_, 0, v_eqs_952_);
lean_ctor_set(v___x_955_, 1, v___x_954_);
v_sz_956_ = lean_array_size(v_args1_943_);
v___x_957_ = ((size_t)0ULL);
v___x_958_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0(v_skipIfPropOrEq_945_, v_args1_943_, v_sz_956_, v___x_957_, v___x_955_, v_a_946_, v_a_947_, v_a_948_, v_a_949_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v_a_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_967_; 
v_a_959_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_967_ == 0)
{
v___x_961_ = v___x_958_;
v_isShared_962_ = v_isSharedCheck_967_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_a_959_);
lean_dec(v___x_958_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_967_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v_fst_963_; lean_object* v___x_965_; 
v_fst_963_ = lean_ctor_get(v_a_959_, 0);
lean_inc(v_fst_963_);
lean_dec(v_a_959_);
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 0, v_fst_963_);
v___x_965_ = v___x_961_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_fst_963_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
else
{
lean_object* v_a_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_975_; 
v_a_968_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_975_ == 0)
{
v___x_970_ = v___x_958_;
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_a_968_);
lean_dec(v___x_958_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_973_; 
if (v_isShared_971_ == 0)
{
v___x_973_ = v___x_970_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_a_968_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___boxed(lean_object* v_args1_976_, lean_object* v_args2_977_, lean_object* v_skipIfPropOrEq_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_){
_start:
{
uint8_t v_skipIfPropOrEq_boxed_984_; lean_object* v_res_985_; 
v_skipIfPropOrEq_boxed_984_ = lean_unbox(v_skipIfPropOrEq_978_);
v_res_985_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v_args1_976_, v_args2_977_, v_skipIfPropOrEq_boxed_984_, v_a_979_, v_a_980_, v_a_981_, v_a_982_);
lean_dec(v_a_982_);
lean_dec_ref(v_a_981_);
lean_dec(v_a_980_);
lean_dec_ref(v_a_979_);
lean_dec_ref(v_args1_976_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0(lean_object* v_k_986_, lean_object* v_b_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_){
_start:
{
lean_object* v___x_993_; 
lean_inc(v___y_991_);
lean_inc_ref(v___y_990_);
lean_inc(v___y_989_);
lean_inc_ref(v___y_988_);
v___x_993_ = lean_apply_6(v_k_986_, v_b_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, lean_box(0));
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0___boxed(lean_object* v_k_994_, lean_object* v_b_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0(v_k_994_, v_b_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(lean_object* v_name_1002_, uint8_t v_bi_1003_, lean_object* v_type_1004_, lean_object* v_k_1005_, uint8_t v_kind_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v___f_1012_; lean_object* v___x_1013_; 
v___f_1012_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1012_, 0, v_k_1005_);
v___x_1013_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1002_, v_bi_1003_, v_type_1004_, v___f_1012_, v_kind_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
if (lean_obj_tag(v___x_1013_) == 0)
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1021_; 
v_a_1014_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1016_ = v___x_1013_;
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_1013_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1019_; 
if (v_isShared_1017_ == 0)
{
v___x_1019_ = v___x_1016_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_a_1014_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
else
{
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1029_; 
v_a_1022_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1024_ = v___x_1013_;
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_1013_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1027_; 
if (v_isShared_1025_ == 0)
{
v___x_1027_ = v___x_1024_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_a_1022_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___boxed(lean_object* v_name_1030_, lean_object* v_bi_1031_, lean_object* v_type_1032_, lean_object* v_k_1033_, lean_object* v_kind_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
uint8_t v_bi_boxed_1040_; uint8_t v_kind_boxed_1041_; lean_object* v_res_1042_; 
v_bi_boxed_1040_ = lean_unbox(v_bi_1031_);
v_kind_boxed_1041_ = lean_unbox(v_kind_1034_);
v_res_1042_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_name_1030_, v_bi_boxed_1040_, v_type_1032_, v_k_1033_, v_kind_boxed_1041_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0(lean_object* v_00_u03b1_1043_, lean_object* v_name_1044_, uint8_t v_bi_1045_, lean_object* v_type_1046_, lean_object* v_k_1047_, uint8_t v_kind_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_name_1044_, v_bi_1045_, v_type_1046_, v_k_1047_, v_kind_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___boxed(lean_object* v_00_u03b1_1055_, lean_object* v_name_1056_, lean_object* v_bi_1057_, lean_object* v_type_1058_, lean_object* v_k_1059_, lean_object* v_kind_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
uint8_t v_bi_boxed_1066_; uint8_t v_kind_boxed_1067_; lean_object* v_res_1068_; 
v_bi_boxed_1066_ = lean_unbox(v_bi_1057_);
v_kind_boxed_1067_ = lean_unbox(v_kind_1060_);
v_res_1068_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0(v_00_u03b1_1055_, v_name_1056_, v_bi_boxed_1066_, v_type_1058_, v_k_1059_, v_kind_boxed_1067_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
lean_dec(v___y_1064_);
lean_dec_ref(v___y_1063_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(lean_object* v_msgData_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
lean_object* v___x_1075_; lean_object* v_env_1076_; lean_object* v___x_1077_; lean_object* v_toCold_1078_; lean_object* v_mctx_1079_; lean_object* v_lctx_1080_; lean_object* v_options_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1075_ = lean_st_ref_get(v___y_1073_);
v_env_1076_ = lean_ctor_get(v___x_1075_, 0);
lean_inc_ref(v_env_1076_);
lean_dec(v___x_1075_);
v___x_1077_ = lean_st_ref_get(v___y_1071_);
v_toCold_1078_ = lean_ctor_get(v___y_1072_, 0);
v_mctx_1079_ = lean_ctor_get(v___x_1077_, 0);
lean_inc_ref(v_mctx_1079_);
lean_dec(v___x_1077_);
v_lctx_1080_ = lean_ctor_get(v___y_1070_, 2);
v_options_1081_ = lean_ctor_get(v_toCold_1078_, 2);
lean_inc_ref(v_options_1081_);
lean_inc_ref(v_lctx_1080_);
v___x_1082_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1082_, 0, v_env_1076_);
lean_ctor_set(v___x_1082_, 1, v_mctx_1079_);
lean_ctor_set(v___x_1082_, 2, v_lctx_1080_);
lean_ctor_set(v___x_1082_, 3, v_options_1081_);
v___x_1083_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1082_);
lean_ctor_set(v___x_1083_, 1, v_msgData_1069_);
v___x_1084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1___boxed(lean_object* v_msgData_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msgData_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(lean_object* v_msg_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v_ref_1098_; lean_object* v___x_1099_; lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1108_; 
v_ref_1098_ = lean_ctor_get(v___y_1095_, 2);
v___x_1099_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msg_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_);
v_a_1100_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1102_ = v___x_1099_;
v_isShared_1103_ = v_isSharedCheck_1108_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1099_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1108_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1104_; lean_object* v___x_1106_; 
lean_inc(v_ref_1098_);
v___x_1104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1104_, 0, v_ref_1098_);
lean_ctor_set(v___x_1104_, 1, v_a_1100_);
if (v_isShared_1103_ == 0)
{
lean_ctor_set_tag(v___x_1102_, 1);
lean_ctor_set(v___x_1102_, 0, v___x_1104_);
v___x_1106_ = v___x_1102_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_1104_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg___boxed(lean_object* v_msg_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v_msg_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
lean_dec(v___y_1111_);
lean_dec_ref(v___y_1110_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0___boxed(lean_object* v_i_1116_, lean_object* v_body_1117_, lean_object* v_args2_1118_, lean_object* v_args2New_1119_, lean_object* v_ctorVal_1120_, lean_object* v_useEq_1121_, lean_object* v_args1_1122_, lean_object* v_resultType_1123_, lean_object* v_k_1124_, lean_object* v_arg2_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
uint8_t v_useEq_boxed_1131_; lean_object* v_res_1132_; 
v_useEq_boxed_1131_ = lean_unbox(v_useEq_1121_);
v_res_1132_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0(v_i_1116_, v_body_1117_, v_args2_1118_, v_args2New_1119_, v_ctorVal_1120_, v_useEq_boxed_1131_, v_args1_1122_, v_resultType_1123_, v_k_1124_, v_arg2_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec_ref(v_body_1117_);
lean_dec(v_i_1116_);
return v_res_1132_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1(void){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1134_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__0));
v___x_1135_ = l_Lean_stringToMessageData(v___x_1134_);
return v___x_1135_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3(void){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__2));
v___x_1138_ = l_Lean_stringToMessageData(v___x_1137_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(lean_object* v_ctorVal_1139_, uint8_t v_useEq_1140_, lean_object* v_args1_1141_, lean_object* v_resultType_1142_, lean_object* v_k_1143_, lean_object* v_i_1144_, lean_object* v_type_1145_, lean_object* v_args2_1146_, lean_object* v_args2New_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_){
_start:
{
lean_object* v___x_1153_; uint8_t v___x_1154_; 
v___x_1153_ = lean_array_get_size(v_args1_1141_);
v___x_1154_ = lean_nat_dec_lt(v_i_1144_, v___x_1153_);
if (v___x_1154_ == 0)
{
lean_object* v___x_1155_; 
lean_dec_ref(v_type_1145_);
lean_dec(v_i_1144_);
lean_dec_ref(v_resultType_1142_);
lean_dec_ref(v_args1_1141_);
lean_dec_ref(v_ctorVal_1139_);
lean_inc(v_a_1151_);
lean_inc_ref(v_a_1150_);
lean_inc(v_a_1149_);
lean_inc_ref(v_a_1148_);
v___x_1155_ = lean_apply_7(v_k_1143_, v_args2_1146_, v_args2New_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, lean_box(0));
return v___x_1155_;
}
else
{
lean_object* v___x_1156_; 
lean_inc(v_a_1151_);
lean_inc_ref(v_a_1150_);
lean_inc(v_a_1149_);
lean_inc_ref(v_a_1148_);
v___x_1156_ = lean_whnf(v_type_1145_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_a_1157_; 
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
lean_inc(v_a_1157_);
lean_dec_ref_known(v___x_1156_, 1);
if (lean_obj_tag(v_a_1157_) == 7)
{
lean_object* v_binderName_1158_; lean_object* v_binderType_1159_; lean_object* v_body_1160_; lean_object* v_lctx_1161_; lean_object* v___x_1162_; uint8_t v___x_1163_; 
v_binderName_1158_ = lean_ctor_get(v_a_1157_, 0);
lean_inc(v_binderName_1158_);
v_binderType_1159_ = lean_ctor_get(v_a_1157_, 1);
lean_inc_ref(v_binderType_1159_);
v_body_1160_ = lean_ctor_get(v_a_1157_, 2);
lean_inc_ref(v_body_1160_);
lean_dec_ref_known(v_a_1157_, 3);
v_lctx_1161_ = lean_ctor_get(v_a_1148_, 2);
v___x_1162_ = lean_array_fget_borrowed(v_args1_1141_, v_i_1144_);
lean_inc(v___x_1162_);
lean_inc_ref(v_lctx_1161_);
v___x_1163_ = l_Lean_Meta_occursOrInType(v_lctx_1161_, v___x_1162_, v_resultType_1142_);
if (v___x_1163_ == 0)
{
lean_object* v___x_1164_; lean_object* v___f_1165_; uint8_t v___y_1167_; 
v___x_1164_ = lean_box(v_useEq_1140_);
v___f_1165_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0___boxed), 15, 9);
lean_closure_set(v___f_1165_, 0, v_i_1144_);
lean_closure_set(v___f_1165_, 1, v_body_1160_);
lean_closure_set(v___f_1165_, 2, v_args2_1146_);
lean_closure_set(v___f_1165_, 3, v_args2New_1147_);
lean_closure_set(v___f_1165_, 4, v_ctorVal_1139_);
lean_closure_set(v___f_1165_, 5, v___x_1164_);
lean_closure_set(v___f_1165_, 6, v_args1_1141_);
lean_closure_set(v___f_1165_, 7, v_resultType_1142_);
lean_closure_set(v___f_1165_, 8, v_k_1143_);
if (v_useEq_1140_ == 0)
{
uint8_t v___x_1170_; 
v___x_1170_ = 1;
v___y_1167_ = v___x_1170_;
goto v___jp_1166_;
}
else
{
uint8_t v___x_1171_; 
v___x_1171_ = 0;
v___y_1167_ = v___x_1171_;
goto v___jp_1166_;
}
v___jp_1166_:
{
uint8_t v___x_1168_; lean_object* v___x_1169_; 
v___x_1168_ = 0;
v___x_1169_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_binderName_1158_, v___y_1167_, v_binderType_1159_, v___f_1165_, v___x_1168_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_);
return v___x_1169_;
}
}
else
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
lean_dec_ref(v_binderType_1159_);
lean_dec(v_binderName_1158_);
v___x_1172_ = lean_unsigned_to_nat(1u);
v___x_1173_ = lean_nat_add(v_i_1144_, v___x_1172_);
lean_dec(v_i_1144_);
v___x_1174_ = lean_expr_instantiate1(v_body_1160_, v___x_1162_);
lean_dec_ref(v_body_1160_);
lean_inc(v___x_1162_);
v___x_1175_ = lean_array_push(v_args2_1146_, v___x_1162_);
v_i_1144_ = v___x_1173_;
v_type_1145_ = v___x_1174_;
v_args2_1146_ = v___x_1175_;
goto _start;
}
}
else
{
lean_object* v_toConstantVal_1177_; lean_object* v_name_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
lean_dec(v_a_1157_);
lean_dec_ref(v_args2New_1147_);
lean_dec_ref(v_args2_1146_);
lean_dec(v_i_1144_);
lean_dec_ref(v_k_1143_);
lean_dec_ref(v_resultType_1142_);
lean_dec_ref(v_args1_1141_);
v_toConstantVal_1177_ = lean_ctor_get(v_ctorVal_1139_, 0);
lean_inc_ref(v_toConstantVal_1177_);
lean_dec_ref(v_ctorVal_1139_);
v_name_1178_ = lean_ctor_get(v_toConstantVal_1177_, 0);
lean_inc(v_name_1178_);
lean_dec_ref(v_toConstantVal_1177_);
v___x_1179_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1);
v___x_1180_ = l_Lean_MessageData_ofName(v_name_1178_);
v___x_1181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1179_);
lean_ctor_set(v___x_1181_, 1, v___x_1180_);
v___x_1182_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_1183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1181_);
lean_ctor_set(v___x_1183_, 1, v___x_1182_);
v___x_1184_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_1183_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_);
return v___x_1184_;
}
}
else
{
lean_object* v_a_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1192_; 
lean_dec_ref(v_args2New_1147_);
lean_dec_ref(v_args2_1146_);
lean_dec(v_i_1144_);
lean_dec_ref(v_k_1143_);
lean_dec_ref(v_resultType_1142_);
lean_dec_ref(v_args1_1141_);
lean_dec_ref(v_ctorVal_1139_);
v_a_1185_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1187_ = v___x_1156_;
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_a_1185_);
lean_dec(v___x_1156_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1190_; 
if (v_isShared_1188_ == 0)
{
v___x_1190_ = v___x_1187_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_a_1185_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0(lean_object* v_i_1193_, lean_object* v_body_1194_, lean_object* v_args2_1195_, lean_object* v_args2New_1196_, lean_object* v_ctorVal_1197_, uint8_t v_useEq_1198_, lean_object* v_args1_1199_, lean_object* v_resultType_1200_, lean_object* v_k_1201_, lean_object* v_arg2_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1208_ = lean_unsigned_to_nat(1u);
v___x_1209_ = lean_nat_add(v_i_1193_, v___x_1208_);
v___x_1210_ = lean_expr_instantiate1(v_body_1194_, v_arg2_1202_);
lean_inc_ref(v_arg2_1202_);
v___x_1211_ = lean_array_push(v_args2_1195_, v_arg2_1202_);
v___x_1212_ = lean_array_push(v_args2New_1196_, v_arg2_1202_);
v___x_1213_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(v_ctorVal_1197_, v_useEq_1198_, v_args1_1199_, v_resultType_1200_, v_k_1201_, v___x_1209_, v___x_1210_, v___x_1211_, v___x_1212_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___boxed(lean_object* v_ctorVal_1214_, lean_object* v_useEq_1215_, lean_object* v_args1_1216_, lean_object* v_resultType_1217_, lean_object* v_k_1218_, lean_object* v_i_1219_, lean_object* v_type_1220_, lean_object* v_args2_1221_, lean_object* v_args2New_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_){
_start:
{
uint8_t v_useEq_boxed_1228_; lean_object* v_res_1229_; 
v_useEq_boxed_1228_ = lean_unbox(v_useEq_1215_);
v_res_1229_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(v_ctorVal_1214_, v_useEq_boxed_1228_, v_args1_1216_, v_resultType_1217_, v_k_1218_, v_i_1219_, v_type_1220_, v_args2_1221_, v_args2New_1222_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_);
lean_dec(v_a_1226_);
lean_dec_ref(v_a_1225_);
lean_dec(v_a_1224_);
lean_dec_ref(v_a_1223_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1(lean_object* v_00_u03b1_1230_, lean_object* v_msg_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
lean_object* v___x_1237_; 
v___x_1237_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v_msg_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___boxed(lean_object* v_00_u03b1_1238_, lean_object* v_msg_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1(v_00_u03b1_1238_, v_msg_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_match__1_splitter___redArg(lean_object* v_____x_1246_, lean_object* v_h__1_1247_, lean_object* v_h__2_1248_){
_start:
{
if (lean_obj_tag(v_____x_1246_) == 7)
{
lean_object* v_binderName_1249_; lean_object* v_binderType_1250_; lean_object* v_body_1251_; uint8_t v_binderInfo_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
lean_dec(v_h__2_1248_);
v_binderName_1249_ = lean_ctor_get(v_____x_1246_, 0);
lean_inc(v_binderName_1249_);
v_binderType_1250_ = lean_ctor_get(v_____x_1246_, 1);
lean_inc_ref(v_binderType_1250_);
v_body_1251_ = lean_ctor_get(v_____x_1246_, 2);
lean_inc_ref(v_body_1251_);
v_binderInfo_1252_ = lean_ctor_get_uint8(v_____x_1246_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_____x_1246_, 3);
v___x_1253_ = lean_box(v_binderInfo_1252_);
v___x_1254_ = lean_apply_4(v_h__1_1247_, v_binderName_1249_, v_binderType_1250_, v_body_1251_, v___x_1253_);
return v___x_1254_;
}
else
{
lean_object* v___x_1255_; 
lean_dec(v_h__1_1247_);
v___x_1255_ = lean_apply_2(v_h__2_1248_, v_____x_1246_, lean_box(0));
return v___x_1255_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_match__1_splitter(lean_object* v_motive_1256_, lean_object* v_____x_1257_, lean_object* v_h__1_1258_, lean_object* v_h__2_1259_){
_start:
{
if (lean_obj_tag(v_____x_1257_) == 7)
{
lean_object* v_binderName_1260_; lean_object* v_binderType_1261_; lean_object* v_body_1262_; uint8_t v_binderInfo_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
lean_dec(v_h__2_1259_);
v_binderName_1260_ = lean_ctor_get(v_____x_1257_, 0);
lean_inc(v_binderName_1260_);
v_binderType_1261_ = lean_ctor_get(v_____x_1257_, 1);
lean_inc_ref(v_binderType_1261_);
v_body_1262_ = lean_ctor_get(v_____x_1257_, 2);
lean_inc_ref(v_body_1262_);
v_binderInfo_1263_ = lean_ctor_get_uint8(v_____x_1257_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_____x_1257_, 3);
v___x_1264_ = lean_box(v_binderInfo_1263_);
v___x_1265_ = lean_apply_4(v_h__1_1258_, v_binderName_1260_, v_binderType_1261_, v_body_1262_, v___x_1264_);
return v___x_1265_;
}
else
{
lean_object* v___x_1266_; 
lean_dec(v_h__1_1258_);
v___x_1266_ = lean_apply_2(v_h__2_1259_, v_____x_1257_, lean_box(0));
return v___x_1266_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0(lean_object* v_k_1267_, lean_object* v_b_1268_, lean_object* v_c_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v___x_1275_; 
lean_inc(v___y_1273_);
lean_inc_ref(v___y_1272_);
lean_inc(v___y_1271_);
lean_inc_ref(v___y_1270_);
v___x_1275_ = lean_apply_7(v_k_1267_, v_b_1268_, v_c_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, lean_box(0));
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed(lean_object* v_k_1276_, lean_object* v_b_1277_, lean_object* v_c_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0(v_k_1276_, v_b_1277_, v_c_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(lean_object* v_type_1285_, lean_object* v_k_1286_, uint8_t v_cleanupAnnotations_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_){
_start:
{
lean_object* v___f_1293_; uint8_t v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___f_1293_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1293_, 0, v_k_1286_);
v___x_1294_ = 0;
v___x_1295_ = lean_box(0);
v___x_1296_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_1294_, v___x_1295_, v_type_1285_, v___f_1293_, v_cleanupAnnotations_1287_, v___x_1294_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1304_; 
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1299_ = v___x_1296_;
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v___x_1296_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1302_; 
if (v_isShared_1300_ == 0)
{
v___x_1302_ = v___x_1299_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_a_1297_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
else
{
lean_object* v_a_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1312_; 
v_a_1305_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1307_ = v___x_1296_;
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_a_1305_);
lean_dec(v___x_1296_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1310_; 
if (v_isShared_1308_ == 0)
{
v___x_1310_ = v___x_1307_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_a_1305_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___boxed(lean_object* v_type_1313_, lean_object* v_k_1314_, lean_object* v_cleanupAnnotations_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1321_; lean_object* v_res_1322_; 
v_cleanupAnnotations_boxed_1321_ = lean_unbox(v_cleanupAnnotations_1315_);
v_res_1322_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_type_1313_, v_k_1314_, v_cleanupAnnotations_boxed_1321_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
return v_res_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2(lean_object* v_00_u03b1_1323_, lean_object* v_type_1324_, lean_object* v_k_1325_, uint8_t v_cleanupAnnotations_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
lean_object* v___x_1332_; 
v___x_1332_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_type_1324_, v_k_1325_, v_cleanupAnnotations_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___boxed(lean_object* v_00_u03b1_1333_, lean_object* v_type_1334_, lean_object* v_k_1335_, lean_object* v_cleanupAnnotations_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1342_; lean_object* v_res_1343_; 
v_cleanupAnnotations_boxed_1342_ = lean_unbox(v_cleanupAnnotations_1336_);
v_res_1343_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2(v_00_u03b1_1333_, v_type_1334_, v_k_1335_, v_cleanupAnnotations_boxed_1342_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(lean_object* v_type_1344_, lean_object* v_maxFVars_x3f_1345_, lean_object* v_k_1346_, uint8_t v_cleanupAnnotations_1347_, uint8_t v_whnfType_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
lean_object* v___f_1354_; lean_object* v___x_1355_; 
v___f_1354_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1354_, 0, v_k_1346_);
v___x_1355_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_1344_, v_maxFVars_x3f_1345_, v___f_1354_, v_cleanupAnnotations_1347_, v_whnfType_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_object* v_a_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1363_; 
v_a_1356_ = lean_ctor_get(v___x_1355_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1358_ = v___x_1355_;
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_a_1356_);
lean_dec(v___x_1355_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1361_; 
if (v_isShared_1359_ == 0)
{
v___x_1361_ = v___x_1358_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_a_1356_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
else
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1371_; 
v_a_1364_ = lean_ctor_get(v___x_1355_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1366_ = v___x_1355_;
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v___x_1355_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1369_; 
if (v_isShared_1367_ == 0)
{
v___x_1369_ = v___x_1366_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_a_1364_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg___boxed(lean_object* v_type_1372_, lean_object* v_maxFVars_x3f_1373_, lean_object* v_k_1374_, lean_object* v_cleanupAnnotations_1375_, lean_object* v_whnfType_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1382_; uint8_t v_whnfType_boxed_1383_; lean_object* v_res_1384_; 
v_cleanupAnnotations_boxed_1382_ = lean_unbox(v_cleanupAnnotations_1375_);
v_whnfType_boxed_1383_ = lean_unbox(v_whnfType_1376_);
v_res_1384_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(v_type_1372_, v_maxFVars_x3f_1373_, v_k_1374_, v_cleanupAnnotations_boxed_1382_, v_whnfType_boxed_1383_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
lean_dec(v___y_1380_);
lean_dec_ref(v___y_1379_);
lean_dec(v___y_1378_);
lean_dec_ref(v___y_1377_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3(lean_object* v_00_u03b1_1385_, lean_object* v_type_1386_, lean_object* v_maxFVars_x3f_1387_, lean_object* v_k_1388_, uint8_t v_cleanupAnnotations_1389_, uint8_t v_whnfType_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
lean_object* v___x_1396_; 
v___x_1396_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(v_type_1386_, v_maxFVars_x3f_1387_, v_k_1388_, v_cleanupAnnotations_1389_, v_whnfType_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___boxed(lean_object* v_00_u03b1_1397_, lean_object* v_type_1398_, lean_object* v_maxFVars_x3f_1399_, lean_object* v_k_1400_, lean_object* v_cleanupAnnotations_1401_, lean_object* v_whnfType_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1408_; uint8_t v_whnfType_boxed_1409_; lean_object* v_res_1410_; 
v_cleanupAnnotations_boxed_1408_ = lean_unbox(v_cleanupAnnotations_1401_);
v_whnfType_boxed_1409_ = lean_unbox(v_whnfType_1402_);
v_res_1410_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3(v_00_u03b1_1397_, v_type_1398_, v_maxFVars_x3f_1399_, v_k_1400_, v_cleanupAnnotations_boxed_1408_, v_whnfType_boxed_1409_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0(lean_object* v_name_1411_, lean_object* v_us_1412_, lean_object* v_params_1413_, lean_object* v_args1_1414_, uint8_t v_useEq_1415_, lean_object* v_args2_1416_, lean_object* v_args2New_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1423_ = l_Lean_mkConst(v_name_1411_, v_us_1412_);
v___x_1424_ = l_Lean_mkAppN(v___x_1423_, v_params_1413_);
lean_inc_ref(v___x_1424_);
v___x_1425_ = l_Lean_mkAppN(v___x_1424_, v_args1_1414_);
v___x_1426_ = l_Lean_mkAppN(v___x_1424_, v_args2_1416_);
v___x_1427_ = l_Lean_Meta_mkEq(v___x_1425_, v___x_1426_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v_a_1428_; uint8_t v___x_1429_; lean_object* v_result_1431_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___x_1476_; 
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
lean_inc(v_a_1428_);
lean_dec_ref_known(v___x_1427_, 1);
v___x_1429_ = 1;
v___x_1476_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v_args1_1414_, v_args2_1416_, v___x_1429_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
if (lean_obj_tag(v___x_1476_) == 0)
{
lean_object* v_a_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1508_; 
v_a_1477_ = lean_ctor_get(v___x_1476_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1476_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1479_ = v___x_1476_;
v_isShared_1480_ = v_isSharedCheck_1508_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_a_1477_);
lean_dec(v___x_1476_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1508_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1481_; 
v___x_1481_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f(v_a_1477_);
if (lean_obj_tag(v___x_1481_) == 1)
{
lean_del_object(v___x_1479_);
if (v_useEq_1415_ == 0)
{
lean_object* v_val_1482_; lean_object* v___x_1483_; 
v_val_1482_ = lean_ctor_get(v___x_1481_, 0);
lean_inc(v_val_1482_);
lean_dec_ref_known(v___x_1481_, 1);
v___x_1483_ = l_Lean_mkArrow(v_a_1428_, v_val_1482_, v___y_1420_, v___y_1421_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_object* v_a_1484_; 
v_a_1484_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_a_1484_);
lean_dec_ref_known(v___x_1483_, 1);
v_result_1431_ = v_a_1484_;
v___y_1432_ = v___y_1418_;
v___y_1433_ = v___y_1419_;
v___y_1434_ = v___y_1420_;
v___y_1435_ = v___y_1421_;
goto v___jp_1430_;
}
else
{
lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1492_; 
v_a_1485_ = lean_ctor_get(v___x_1483_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1483_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1487_ = v___x_1483_;
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v___x_1483_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1490_; 
if (v_isShared_1488_ == 0)
{
v___x_1490_ = v___x_1487_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_a_1485_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
}
else
{
lean_object* v_val_1493_; lean_object* v___x_1494_; 
v_val_1493_ = lean_ctor_get(v___x_1481_, 0);
lean_inc(v_val_1493_);
lean_dec_ref_known(v___x_1481_, 1);
v___x_1494_ = l_Lean_Meta_mkEq(v_a_1428_, v_val_1493_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_object* v_a_1495_; 
v_a_1495_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_a_1495_);
lean_dec_ref_known(v___x_1494_, 1);
v_result_1431_ = v_a_1495_;
v___y_1432_ = v___y_1418_;
v___y_1433_ = v___y_1419_;
v___y_1434_ = v___y_1420_;
v___y_1435_ = v___y_1421_;
goto v___jp_1430_;
}
else
{
lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1503_; 
v_a_1496_ = lean_ctor_get(v___x_1494_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1498_ = v___x_1494_;
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_a_1496_);
lean_dec(v___x_1494_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1501_; 
if (v_isShared_1499_ == 0)
{
v___x_1501_ = v___x_1498_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_a_1496_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
}
}
else
{
lean_object* v___x_1504_; lean_object* v___x_1506_; 
lean_dec(v___x_1481_);
lean_dec(v_a_1428_);
v___x_1504_ = lean_box(0);
if (v_isShared_1480_ == 0)
{
lean_ctor_set(v___x_1479_, 0, v___x_1504_);
v___x_1506_ = v___x_1479_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1504_);
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
lean_object* v_a_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1516_; 
lean_dec(v_a_1428_);
v_a_1509_ = lean_ctor_get(v___x_1476_, 0);
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1476_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1511_ = v___x_1476_;
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_a_1509_);
lean_dec(v___x_1476_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1514_; 
if (v_isShared_1512_ == 0)
{
v___x_1514_ = v___x_1511_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_a_1509_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
}
}
}
v___jp_1430_:
{
uint8_t v___x_1436_; uint8_t v___x_1437_; lean_object* v___x_1438_; 
v___x_1436_ = 0;
v___x_1437_ = 1;
v___x_1438_ = l_Lean_Meta_mkForallFVars(v_args2New_1417_, v_result_1431_, v___x_1436_, v___x_1429_, v___x_1429_, v___x_1437_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_);
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_object* v_a_1439_; lean_object* v___x_1440_; 
v_a_1439_ = lean_ctor_get(v___x_1438_, 0);
lean_inc(v_a_1439_);
lean_dec_ref_known(v___x_1438_, 1);
v___x_1440_ = l_Lean_Meta_mkForallFVars(v_args1_1414_, v_a_1439_, v___x_1436_, v___x_1429_, v___x_1429_, v___x_1437_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_object* v_a_1441_; lean_object* v___x_1442_; 
v_a_1441_ = lean_ctor_get(v___x_1440_, 0);
lean_inc(v_a_1441_);
lean_dec_ref_known(v___x_1440_, 1);
v___x_1442_ = l_Lean_Meta_mkForallFVars(v_params_1413_, v_a_1441_, v___x_1436_, v___x_1429_, v___x_1429_, v___x_1437_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_);
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1451_; 
v_a_1443_ = lean_ctor_get(v___x_1442_, 0);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1445_ = v___x_1442_;
v_isShared_1446_ = v_isSharedCheck_1451_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1442_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1451_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1447_; lean_object* v___x_1449_; 
v___x_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1447_, 0, v_a_1443_);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 0, v___x_1447_);
v___x_1449_ = v___x_1445_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v___x_1447_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
}
else
{
lean_object* v_a_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1459_; 
v_a_1452_ = lean_ctor_get(v___x_1442_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1454_ = v___x_1442_;
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_a_1452_);
lean_dec(v___x_1442_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1457_; 
if (v_isShared_1455_ == 0)
{
v___x_1457_ = v___x_1454_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_a_1452_);
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
else
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1467_; 
v_a_1460_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1462_ = v___x_1440_;
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1440_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1465_; 
if (v_isShared_1463_ == 0)
{
v___x_1465_ = v___x_1462_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_a_1460_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
}
else
{
lean_object* v_a_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1475_; 
v_a_1468_ = lean_ctor_get(v___x_1438_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1470_ = v___x_1438_;
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_a_1468_);
lean_dec(v___x_1438_);
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
}
else
{
lean_object* v_a_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1524_; 
lean_dec_ref(v_args2_1416_);
v_a_1517_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1524_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1519_ = v___x_1427_;
v_isShared_1520_ = v_isSharedCheck_1524_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_a_1517_);
lean_dec(v___x_1427_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1524_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v___x_1522_; 
if (v_isShared_1520_ == 0)
{
v___x_1522_ = v___x_1519_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_a_1517_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0___boxed(lean_object* v_name_1525_, lean_object* v_us_1526_, lean_object* v_params_1527_, lean_object* v_args1_1528_, lean_object* v_useEq_1529_, lean_object* v_args2_1530_, lean_object* v_args2New_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
uint8_t v_useEq_boxed_1537_; lean_object* v_res_1538_; 
v_useEq_boxed_1537_ = lean_unbox(v_useEq_1529_);
v_res_1538_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0(v_name_1525_, v_us_1526_, v_params_1527_, v_args1_1528_, v_useEq_boxed_1537_, v_args2_1530_, v_args2New_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
lean_dec_ref(v_args2New_1531_);
lean_dec_ref(v_args1_1528_);
lean_dec_ref(v_params_1527_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1(size_t v_sz_1539_, size_t v_i_1540_, lean_object* v_bs_1541_){
_start:
{
uint8_t v___x_1542_; 
v___x_1542_ = lean_usize_dec_lt(v_i_1540_, v_sz_1539_);
if (v___x_1542_ == 0)
{
return v_bs_1541_;
}
else
{
lean_object* v_v_1543_; lean_object* v___x_1544_; lean_object* v_bs_x27_1545_; lean_object* v___x_1546_; uint8_t v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; size_t v___x_1550_; size_t v___x_1551_; lean_object* v___x_1552_; 
v_v_1543_ = lean_array_uget(v_bs_1541_, v_i_1540_);
v___x_1544_ = lean_unsigned_to_nat(0u);
v_bs_x27_1545_ = lean_array_uset(v_bs_1541_, v_i_1540_, v___x_1544_);
v___x_1546_ = l_Lean_Expr_fvarId_x21(v_v_1543_);
lean_dec(v_v_1543_);
v___x_1547_ = 1;
v___x_1548_ = lean_box(v___x_1547_);
v___x_1549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1546_);
lean_ctor_set(v___x_1549_, 1, v___x_1548_);
v___x_1550_ = ((size_t)1ULL);
v___x_1551_ = lean_usize_add(v_i_1540_, v___x_1550_);
v___x_1552_ = lean_array_uset(v_bs_x27_1545_, v_i_1540_, v___x_1549_);
v_i_1540_ = v___x_1551_;
v_bs_1541_ = v___x_1552_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1___boxed(lean_object* v_sz_1554_, lean_object* v_i_1555_, lean_object* v_bs_1556_){
_start:
{
size_t v_sz_boxed_1557_; size_t v_i_boxed_1558_; lean_object* v_res_1559_; 
v_sz_boxed_1557_ = lean_unbox_usize(v_sz_1554_);
lean_dec(v_sz_1554_);
v_i_boxed_1558_ = lean_unbox_usize(v_i_1555_);
lean_dec(v_i_1555_);
v_res_1559_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1(v_sz_boxed_1557_, v_i_boxed_1558_, v_bs_1556_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(lean_object* v_bs_1560_, lean_object* v_k_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_){
_start:
{
lean_object* v___x_1567_; 
v___x_1567_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_box(0), v_bs_1560_, v_k_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1575_; 
v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1570_ = v___x_1567_;
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v___x_1567_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1573_; 
if (v_isShared_1571_ == 0)
{
v___x_1573_ = v___x_1570_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_a_1568_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
else
{
lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1583_; 
v_a_1576_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1578_ = v___x_1567_;
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v___x_1567_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1581_; 
if (v_isShared_1579_ == 0)
{
v___x_1581_ = v___x_1578_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_a_1576_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_bs_1584_, lean_object* v_k_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
lean_object* v_res_1591_; 
v_res_1591_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(v_bs_1584_, v_k_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec_ref(v_bs_1584_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(lean_object* v_bs_1592_, lean_object* v_k_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_){
_start:
{
size_t v_sz_1599_; size_t v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
v_sz_1599_ = lean_array_size(v_bs_1592_);
v___x_1600_ = ((size_t)0ULL);
v___x_1601_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1(v_sz_1599_, v___x_1600_, v_bs_1592_);
v___x_1602_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(v___x_1601_, v_k_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
lean_dec_ref(v___x_1601_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg___boxed(lean_object* v_bs_1603_, lean_object* v_k_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v_bs_1603_, v_k_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
lean_dec(v___y_1606_);
lean_dec_ref(v___y_1605_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1(lean_object* v_name_1611_, lean_object* v_us_1612_, lean_object* v_params_1613_, uint8_t v_useEq_1614_, lean_object* v_ctorVal_1615_, lean_object* v_type_1616_, lean_object* v_args1_1617_, lean_object* v_resultType_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_){
_start:
{
lean_object* v___x_1624_; lean_object* v___f_1625_; 
v___x_1624_ = lean_box(v_useEq_1614_);
lean_inc_ref(v_args1_1617_);
lean_inc_ref(v_params_1613_);
v___f_1625_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1625_, 0, v_name_1611_);
lean_closure_set(v___f_1625_, 1, v_us_1612_);
lean_closure_set(v___f_1625_, 2, v_params_1613_);
lean_closure_set(v___f_1625_, 3, v_args1_1617_);
lean_closure_set(v___f_1625_, 4, v___x_1624_);
if (v_useEq_1614_ == 0)
{
lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1626_ = l_Array_append___redArg(v_params_1613_, v_args1_1617_);
v___x_1627_ = lean_unsigned_to_nat(0u);
v___x_1628_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_1629_ = lean_box(v_useEq_1614_);
v___x_1630_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___boxed), 14, 9);
lean_closure_set(v___x_1630_, 0, v_ctorVal_1615_);
lean_closure_set(v___x_1630_, 1, v___x_1629_);
lean_closure_set(v___x_1630_, 2, v_args1_1617_);
lean_closure_set(v___x_1630_, 3, v_resultType_1618_);
lean_closure_set(v___x_1630_, 4, v___f_1625_);
lean_closure_set(v___x_1630_, 5, v___x_1627_);
lean_closure_set(v___x_1630_, 6, v_type_1616_);
lean_closure_set(v___x_1630_, 7, v___x_1628_);
lean_closure_set(v___x_1630_, 8, v___x_1628_);
v___x_1631_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v___x_1626_, v___x_1630_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_);
return v___x_1631_;
}
else
{
lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
lean_dec_ref(v_params_1613_);
v___x_1632_ = lean_unsigned_to_nat(0u);
v___x_1633_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_1634_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(v_ctorVal_1615_, v_useEq_1614_, v_args1_1617_, v_resultType_1618_, v___f_1625_, v___x_1632_, v_type_1616_, v___x_1633_, v___x_1633_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_);
return v___x_1634_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1___boxed(lean_object* v_name_1635_, lean_object* v_us_1636_, lean_object* v_params_1637_, lean_object* v_useEq_1638_, lean_object* v_ctorVal_1639_, lean_object* v_type_1640_, lean_object* v_args1_1641_, lean_object* v_resultType_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_){
_start:
{
uint8_t v_useEq_boxed_1648_; lean_object* v_res_1649_; 
v_useEq_boxed_1648_ = lean_unbox(v_useEq_1638_);
v_res_1649_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1(v_name_1635_, v_us_1636_, v_params_1637_, v_useEq_boxed_1648_, v_ctorVal_1639_, v_type_1640_, v_args1_1641_, v_resultType_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_);
lean_dec(v___y_1646_);
lean_dec_ref(v___y_1645_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2(lean_object* v_name_1650_, lean_object* v_us_1651_, uint8_t v_useEq_1652_, lean_object* v_ctorVal_1653_, lean_object* v_params_1654_, lean_object* v_type_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
lean_object* v___x_1661_; lean_object* v___f_1662_; uint8_t v___x_1663_; lean_object* v___x_1664_; 
v___x_1661_ = lean_box(v_useEq_1652_);
lean_inc_ref(v_type_1655_);
v___f_1662_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1___boxed), 13, 6);
lean_closure_set(v___f_1662_, 0, v_name_1650_);
lean_closure_set(v___f_1662_, 1, v_us_1651_);
lean_closure_set(v___f_1662_, 2, v_params_1654_);
lean_closure_set(v___f_1662_, 3, v___x_1661_);
lean_closure_set(v___f_1662_, 4, v_ctorVal_1653_);
lean_closure_set(v___f_1662_, 5, v_type_1655_);
v___x_1663_ = 0;
v___x_1664_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_type_1655_, v___f_1662_, v___x_1663_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2___boxed(lean_object* v_name_1665_, lean_object* v_us_1666_, lean_object* v_useEq_1667_, lean_object* v_ctorVal_1668_, lean_object* v_params_1669_, lean_object* v_type_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_){
_start:
{
uint8_t v_useEq_boxed_1676_; lean_object* v_res_1677_; 
v_useEq_boxed_1676_ = lean_unbox(v_useEq_1667_);
v_res_1677_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2(v_name_1665_, v_us_1666_, v_useEq_boxed_1676_, v_ctorVal_1668_, v_params_1669_, v_type_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(lean_object* v_a_1678_, lean_object* v_a_1679_){
_start:
{
if (lean_obj_tag(v_a_1678_) == 0)
{
lean_object* v___x_1680_; 
v___x_1680_ = l_List_reverse___redArg(v_a_1679_);
return v___x_1680_;
}
else
{
lean_object* v_head_1681_; lean_object* v_tail_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1691_; 
v_head_1681_ = lean_ctor_get(v_a_1678_, 0);
v_tail_1682_ = lean_ctor_get(v_a_1678_, 1);
v_isSharedCheck_1691_ = !lean_is_exclusive(v_a_1678_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1684_ = v_a_1678_;
v_isShared_1685_ = v_isSharedCheck_1691_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_tail_1682_);
lean_inc(v_head_1681_);
lean_dec(v_a_1678_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1691_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1686_; lean_object* v___x_1688_; 
v___x_1686_ = l_Lean_mkLevelParam(v_head_1681_);
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 1, v_a_1679_);
lean_ctor_set(v___x_1684_, 0, v___x_1686_);
v___x_1688_ = v___x_1684_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v___x_1686_);
lean_ctor_set(v_reuseFailAlloc_1690_, 1, v_a_1679_);
v___x_1688_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
v_a_1678_ = v_tail_1682_;
v_a_1679_ = v___x_1688_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(lean_object* v_ctorVal_1692_, uint8_t v_useEq_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_){
_start:
{
lean_object* v_toConstantVal_1699_; lean_object* v_numParams_1700_; lean_object* v_name_1701_; lean_object* v_levelParams_1702_; lean_object* v_type_1703_; lean_object* v___x_1704_; 
v_toConstantVal_1699_ = lean_ctor_get(v_ctorVal_1692_, 0);
v_numParams_1700_ = lean_ctor_get(v_ctorVal_1692_, 3);
lean_inc(v_numParams_1700_);
v_name_1701_ = lean_ctor_get(v_toConstantVal_1699_, 0);
lean_inc(v_name_1701_);
v_levelParams_1702_ = lean_ctor_get(v_toConstantVal_1699_, 1);
v_type_1703_ = lean_ctor_get(v_toConstantVal_1699_, 2);
lean_inc_ref(v_type_1703_);
v___x_1704_ = l_Lean_Meta_elimOptParam(v_type_1703_, v_a_1696_, v_a_1697_);
if (lean_obj_tag(v___x_1704_) == 0)
{
lean_object* v_a_1705_; lean_object* v___x_1706_; lean_object* v_us_1707_; lean_object* v___x_1708_; lean_object* v___f_1709_; lean_object* v___x_1710_; uint8_t v___x_1711_; lean_object* v___x_1712_; 
v_a_1705_ = lean_ctor_get(v___x_1704_, 0);
lean_inc(v_a_1705_);
lean_dec_ref_known(v___x_1704_, 1);
v___x_1706_ = lean_box(0);
lean_inc(v_levelParams_1702_);
v_us_1707_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(v_levelParams_1702_, v___x_1706_);
v___x_1708_ = lean_box(v_useEq_1693_);
v___f_1709_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2___boxed), 11, 4);
lean_closure_set(v___f_1709_, 0, v_name_1701_);
lean_closure_set(v___f_1709_, 1, v_us_1707_);
lean_closure_set(v___f_1709_, 2, v___x_1708_);
lean_closure_set(v___f_1709_, 3, v_ctorVal_1692_);
v___x_1710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1710_, 0, v_numParams_1700_);
v___x_1711_ = 0;
v___x_1712_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(v_a_1705_, v___x_1710_, v___f_1709_, v___x_1711_, v___x_1711_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_);
return v___x_1712_;
}
else
{
lean_object* v_a_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1720_; 
lean_dec(v_name_1701_);
lean_dec(v_numParams_1700_);
lean_dec_ref(v_ctorVal_1692_);
v_a_1713_ = lean_ctor_get(v___x_1704_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1704_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1715_ = v___x_1704_;
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_a_1713_);
lean_dec(v___x_1704_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1718_; 
if (v_isShared_1716_ == 0)
{
v___x_1718_ = v___x_1715_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_a_1713_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___boxed(lean_object* v_ctorVal_1721_, lean_object* v_useEq_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_){
_start:
{
uint8_t v_useEq_boxed_1728_; lean_object* v_res_1729_; 
v_useEq_boxed_1728_ = lean_unbox(v_useEq_1722_);
v_res_1729_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(v_ctorVal_1721_, v_useEq_boxed_1728_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_);
lean_dec(v_a_1726_);
lean_dec_ref(v_a_1725_);
lean_dec(v_a_1724_);
lean_dec_ref(v_a_1723_);
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2(lean_object* v_00_u03b1_1730_, lean_object* v_bs_1731_, lean_object* v_k_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
lean_object* v___x_1738_; 
v___x_1738_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(v_bs_1731_, v_k_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
return v___x_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1739_, lean_object* v_bs_1740_, lean_object* v_k_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2(v_00_u03b1_1739_, v_bs_1740_, v_k_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1744_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec_ref(v_bs_1740_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1(lean_object* v_00_u03b1_1748_, lean_object* v_bs_1749_, lean_object* v_k_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
lean_object* v___x_1756_; 
v___x_1756_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v_bs_1749_, v_k_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___boxed(lean_object* v_00_u03b1_1757_, lean_object* v_bs_1758_, lean_object* v_k_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_){
_start:
{
lean_object* v_res_1765_; 
v_res_1765_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1(v_00_u03b1_1757_, v_bs_1758_, v_k_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_);
lean_dec(v___y_1763_);
lean_dec_ref(v___y_1762_);
lean_dec(v___y_1761_);
lean_dec_ref(v___y_1760_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(lean_object* v_ctorVal_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_){
_start:
{
uint8_t v___x_1772_; lean_object* v___x_1773_; 
v___x_1772_ = 0;
v___x_1773_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(v_ctorVal_1766_, v___x_1772_, v_a_1767_, v_a_1768_, v_a_1769_, v_a_1770_);
return v___x_1773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f___boxed(lean_object* v_ctorVal_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_1774_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_);
lean_dec(v_a_1778_);
lean_dec_ref(v_a_1777_);
lean_dec(v_a_1776_);
lean_dec_ref(v_a_1775_);
return v_res_1780_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1(void){
_start:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1782_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__0));
v___x_1783_ = l_Lean_stringToMessageData(v___x_1782_);
return v___x_1783_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3(void){
_start:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1785_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__2));
v___x_1786_ = l_Lean_stringToMessageData(v___x_1785_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(lean_object* v_ctorName_1787_){
_start:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1788_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1);
v___x_1789_ = l_Lean_MessageData_ofName(v_ctorName_1787_);
v___x_1790_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1788_);
lean_ctor_set(v___x_1790_, 1, v___x_1789_);
v___x_1791_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3);
v___x_1792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1792_, 0, v___x_1790_);
lean_ctor_set(v___x_1792_, 1, v___x_1791_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(lean_object* v_ctorName_1793_, lean_object* v_mvarId_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_){
_start:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1800_ = l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(v_ctorName_1793_);
v___x_1801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1801_, 0, v_mvarId_1794_);
v___x_1802_ = l_Lean_indentD(v___x_1801_);
v___x_1803_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1800_);
lean_ctor_set(v___x_1803_, 1, v___x_1802_);
v___x_1804_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_1803_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg___boxed(lean_object* v_ctorName_1805_, lean_object* v_mvarId_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(v_ctorName_1805_, v_mvarId_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_);
lean_dec(v_a_1810_);
lean_dec_ref(v_a_1809_);
lean_dec(v_a_1808_);
lean_dec_ref(v_a_1807_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure(lean_object* v_00_u03b1_1813_, lean_object* v_ctorName_1814_, lean_object* v_mvarId_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_){
_start:
{
lean_object* v___x_1821_; 
v___x_1821_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(v_ctorName_1814_, v_mvarId_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___boxed(lean_object* v_00_u03b1_1822_, lean_object* v_ctorName_1823_, lean_object* v_mvarId_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_){
_start:
{
lean_object* v_res_1830_; 
v_res_1830_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure(v_00_u03b1_1822_, v_ctorName_1823_, v_mvarId_1824_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_);
lean_dec(v_a_1828_);
lean_dec_ref(v_a_1827_);
lean_dec(v_a_1826_);
lean_dec_ref(v_a_1825_);
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0(lean_object* v_ctorName_1831_, lean_object* v_as_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_){
_start:
{
if (lean_obj_tag(v_as_1832_) == 0)
{
lean_object* v___x_1838_; lean_object* v___x_1839_; 
lean_dec(v_ctorName_1831_);
v___x_1838_ = lean_box(0);
v___x_1839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1838_);
return v___x_1839_;
}
else
{
lean_object* v_head_1840_; lean_object* v_tail_1841_; lean_object* v___x_1842_; 
v_head_1840_ = lean_ctor_get(v_as_1832_, 0);
lean_inc_n(v_head_1840_, 2);
v_tail_1841_ = lean_ctor_get(v_as_1832_, 1);
lean_inc(v_tail_1841_);
lean_dec_ref_known(v_as_1832_, 2);
v___x_1842_ = l_Lean_MVarId_assumptionCore(v_head_1840_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_);
if (lean_obj_tag(v___x_1842_) == 0)
{
lean_object* v_a_1843_; uint8_t v___x_1844_; 
v_a_1843_ = lean_ctor_get(v___x_1842_, 0);
lean_inc(v_a_1843_);
lean_dec_ref_known(v___x_1842_, 1);
v___x_1844_ = lean_unbox(v_a_1843_);
lean_dec(v_a_1843_);
if (v___x_1844_ == 0)
{
lean_object* v___x_1845_; 
lean_dec(v_tail_1841_);
v___x_1845_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(v_ctorName_1831_, v_head_1840_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_);
return v___x_1845_;
}
else
{
lean_dec(v_head_1840_);
v_as_1832_ = v_tail_1841_;
goto _start;
}
}
else
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1854_; 
lean_dec(v_tail_1841_);
lean_dec(v_head_1840_);
lean_dec(v_ctorName_1831_);
v_a_1847_ = lean_ctor_get(v___x_1842_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1849_ = v___x_1842_;
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1842_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1852_; 
if (v_isShared_1850_ == 0)
{
v___x_1852_ = v___x_1849_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_a_1847_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0___boxed(lean_object* v_ctorName_1855_, lean_object* v_as_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0(v_ctorName_1855_, v_as_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(lean_object* v_mvarId_1863_, lean_object* v_ctorName_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_){
_start:
{
lean_object* v___x_1870_; 
v___x_1870_ = l_Lean_MVarId_splitAndCore(v_mvarId_1863_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_a_1871_; lean_object* v___x_1872_; 
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
lean_inc(v_a_1871_);
lean_dec_ref_known(v___x_1870_, 1);
v___x_1872_ = l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0(v_ctorName_1864_, v_a_1871_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_);
return v___x_1872_;
}
else
{
lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1880_; 
lean_dec(v_ctorName_1864_);
v_a_1873_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1875_ = v___x_1870_;
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___x_1870_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1878_; 
if (v_isShared_1876_ == 0)
{
v___x_1878_ = v___x_1875_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_a_1873_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption___boxed(lean_object* v_mvarId_1881_, lean_object* v_ctorName_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_){
_start:
{
lean_object* v_res_1888_; 
v_res_1888_ = l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(v_mvarId_1881_, v_ctorName_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_);
lean_dec(v_a_1886_);
lean_dec_ref(v_a_1885_);
lean_dec(v_a_1884_);
lean_dec_ref(v_a_1883_);
return v_res_1888_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0(lean_object* v_msg_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_){
_start:
{
lean_object* v___f_1896_; lean_object* v___x_905__overap_1897_; lean_object* v___x_1898_; 
v___f_1896_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0___closed__0));
v___x_905__overap_1897_ = lean_panic_fn_borrowed(v___f_1896_, v_msg_1890_);
lean_inc(v___y_1894_);
lean_inc_ref(v___y_1893_);
lean_inc(v___y_1892_);
lean_inc_ref(v___y_1891_);
v___x_1898_ = lean_apply_5(v___x_905__overap_1897_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, lean_box(0));
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0___boxed(lean_object* v_msg_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0(v_msg_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
return v_res_1905_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1906_; double v___x_1907_; 
v___x_1906_ = lean_unsigned_to_nat(0u);
v___x_1907_ = lean_float_of_nat(v___x_1906_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(lean_object* v_cls_1911_, lean_object* v_msg_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
lean_object* v_ref_1918_; lean_object* v___x_1919_; lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1964_; 
v_ref_1918_ = lean_ctor_get(v___y_1915_, 2);
v___x_1919_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msg_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1922_ = v___x_1919_;
v_isShared_1923_ = v_isSharedCheck_1964_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1919_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1964_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1924_; lean_object* v_traceState_1925_; lean_object* v_env_1926_; lean_object* v_nextMacroScope_1927_; lean_object* v_ngen_1928_; lean_object* v_auxDeclNGen_1929_; lean_object* v_cache_1930_; lean_object* v_messages_1931_; lean_object* v_infoState_1932_; lean_object* v_snapshotTasks_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1963_; 
v___x_1924_ = lean_st_ref_take(v___y_1916_);
v_traceState_1925_ = lean_ctor_get(v___x_1924_, 4);
v_env_1926_ = lean_ctor_get(v___x_1924_, 0);
v_nextMacroScope_1927_ = lean_ctor_get(v___x_1924_, 1);
v_ngen_1928_ = lean_ctor_get(v___x_1924_, 2);
v_auxDeclNGen_1929_ = lean_ctor_get(v___x_1924_, 3);
v_cache_1930_ = lean_ctor_get(v___x_1924_, 5);
v_messages_1931_ = lean_ctor_get(v___x_1924_, 6);
v_infoState_1932_ = lean_ctor_get(v___x_1924_, 7);
v_snapshotTasks_1933_ = lean_ctor_get(v___x_1924_, 8);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1935_ = v___x_1924_;
v_isShared_1936_ = v_isSharedCheck_1963_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_snapshotTasks_1933_);
lean_inc(v_infoState_1932_);
lean_inc(v_messages_1931_);
lean_inc(v_cache_1930_);
lean_inc(v_traceState_1925_);
lean_inc(v_auxDeclNGen_1929_);
lean_inc(v_ngen_1928_);
lean_inc(v_nextMacroScope_1927_);
lean_inc(v_env_1926_);
lean_dec(v___x_1924_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1963_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
uint64_t v_tid_1937_; lean_object* v_traces_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1962_; 
v_tid_1937_ = lean_ctor_get_uint64(v_traceState_1925_, sizeof(void*)*1);
v_traces_1938_ = lean_ctor_get(v_traceState_1925_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v_traceState_1925_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1940_ = v_traceState_1925_;
v_isShared_1941_ = v_isSharedCheck_1962_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_traces_1938_);
lean_dec(v_traceState_1925_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1962_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1942_; double v___x_1943_; uint8_t v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1952_; 
v___x_1942_ = lean_box(0);
v___x_1943_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0);
v___x_1944_ = 0;
v___x_1945_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_1946_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1946_, 0, v_cls_1911_);
lean_ctor_set(v___x_1946_, 1, v___x_1942_);
lean_ctor_set(v___x_1946_, 2, v___x_1945_);
lean_ctor_set_float(v___x_1946_, sizeof(void*)*3, v___x_1943_);
lean_ctor_set_float(v___x_1946_, sizeof(void*)*3 + 8, v___x_1943_);
lean_ctor_set_uint8(v___x_1946_, sizeof(void*)*3 + 16, v___x_1944_);
v___x_1947_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__2));
v___x_1948_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1946_);
lean_ctor_set(v___x_1948_, 1, v_a_1920_);
lean_ctor_set(v___x_1948_, 2, v___x_1947_);
lean_inc(v_ref_1918_);
v___x_1949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1949_, 0, v_ref_1918_);
lean_ctor_set(v___x_1949_, 1, v___x_1948_);
v___x_1950_ = l_Lean_PersistentArray_push___redArg(v_traces_1938_, v___x_1949_);
if (v_isShared_1941_ == 0)
{
lean_ctor_set(v___x_1940_, 0, v___x_1950_);
v___x_1952_ = v___x_1940_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v___x_1950_);
lean_ctor_set_uint64(v_reuseFailAlloc_1961_, sizeof(void*)*1, v_tid_1937_);
v___x_1952_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
lean_object* v___x_1954_; 
if (v_isShared_1936_ == 0)
{
lean_ctor_set(v___x_1935_, 4, v___x_1952_);
v___x_1954_ = v___x_1935_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_env_1926_);
lean_ctor_set(v_reuseFailAlloc_1960_, 1, v_nextMacroScope_1927_);
lean_ctor_set(v_reuseFailAlloc_1960_, 2, v_ngen_1928_);
lean_ctor_set(v_reuseFailAlloc_1960_, 3, v_auxDeclNGen_1929_);
lean_ctor_set(v_reuseFailAlloc_1960_, 4, v___x_1952_);
lean_ctor_set(v_reuseFailAlloc_1960_, 5, v_cache_1930_);
lean_ctor_set(v_reuseFailAlloc_1960_, 6, v_messages_1931_);
lean_ctor_set(v_reuseFailAlloc_1960_, 7, v_infoState_1932_);
lean_ctor_set(v_reuseFailAlloc_1960_, 8, v_snapshotTasks_1933_);
v___x_1954_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1958_; 
v___x_1955_ = lean_st_ref_put(v___y_1916_, v___x_1954_);
v___x_1956_ = lean_box(0);
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 0, v___x_1956_);
v___x_1958_ = v___x_1922_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v___x_1956_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___boxed(lean_object* v_cls_1965_, lean_object* v_msg_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
lean_object* v_res_1972_; 
v_res_1972_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_1965_, v_msg_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
return v_res_1972_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3(void){
_start:
{
lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; 
v___x_1976_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__2));
v___x_1977_ = lean_unsigned_to_nat(30u);
v___x_1978_ = lean_unsigned_to_nat(96u);
v___x_1979_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__1));
v___x_1980_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__0));
v___x_1981_ = l_mkPanicMessageWithDecl(v___x_1980_, v___x_1979_, v___x_1978_, v___x_1977_, v___x_1976_);
return v___x_1981_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9(void){
_start:
{
lean_object* v_cls_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; 
v_cls_1990_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_1991_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__8));
v___x_1992_ = l_Lean_Name_append(v___x_1991_, v_cls_1990_);
return v___x_1992_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11(void){
_start:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___x_1994_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__10));
v___x_1995_ = l_Lean_stringToMessageData(v___x_1994_);
return v___x_1995_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13(void){
_start:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1997_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__12));
v___x_1998_ = l_Lean_stringToMessageData(v___x_1997_);
return v___x_1998_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15(void){
_start:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_2000_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__14));
v___x_2001_ = l_Lean_stringToMessageData(v___x_2000_);
return v___x_2001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(lean_object* v_ctorName_2002_, lean_object* v_mvarId_2003_, lean_object* v_h_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_){
_start:
{
lean_object* v___y_2011_; lean_object* v___y_2012_; lean_object* v___y_2013_; lean_object* v___y_2014_; lean_object* v_toCold_2030_; lean_object* v_options_2031_; uint8_t v_hasTrace_2032_; 
v_toCold_2030_ = lean_ctor_get(v_a_2007_, 0);
v_options_2031_ = lean_ctor_get(v_toCold_2030_, 2);
v_hasTrace_2032_ = lean_ctor_get_uint8(v_options_2031_, sizeof(void*)*1);
if (v_hasTrace_2032_ == 0)
{
v___y_2011_ = v_a_2005_;
v___y_2012_ = v_a_2006_;
v___y_2013_ = v_a_2007_;
v___y_2014_ = v_a_2008_;
goto v___jp_2010_;
}
else
{
lean_object* v_inheritedTraceOptions_2033_; lean_object* v_cls_2034_; lean_object* v___x_2035_; uint8_t v___x_2036_; 
v_inheritedTraceOptions_2033_ = lean_ctor_get(v_toCold_2030_, 11);
v_cls_2034_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_2035_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_2036_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2033_, v_options_2031_, v___x_2035_);
if (v___x_2036_ == 0)
{
v___y_2011_ = v_a_2005_;
v___y_2012_ = v_a_2006_;
v___y_2013_ = v_a_2007_;
v___y_2014_ = v_a_2008_;
goto v___jp_2010_;
}
else
{
lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2037_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11);
lean_inc(v_ctorName_2002_);
v___x_2038_ = l_Lean_MessageData_ofName(v_ctorName_2002_);
v___x_2039_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2039_, 0, v___x_2037_);
lean_ctor_set(v___x_2039_, 1, v___x_2038_);
v___x_2040_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13);
v___x_2041_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2041_, 0, v___x_2039_);
lean_ctor_set(v___x_2041_, 1, v___x_2040_);
lean_inc(v_h_2004_);
v___x_2042_ = l_Lean_mkFVar(v_h_2004_);
v___x_2043_ = l_Lean_MessageData_ofExpr(v___x_2042_);
v___x_2044_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2041_);
lean_ctor_set(v___x_2044_, 1, v___x_2043_);
v___x_2045_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15);
v___x_2046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2044_);
lean_ctor_set(v___x_2046_, 1, v___x_2045_);
lean_inc(v_mvarId_2003_);
v___x_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2047_, 0, v_mvarId_2003_);
v___x_2048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2046_);
lean_ctor_set(v___x_2048_, 1, v___x_2047_);
v___x_2049_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2034_, v___x_2048_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_dec_ref_known(v___x_2049_, 1);
v___y_2011_ = v_a_2005_;
v___y_2012_ = v_a_2006_;
v___y_2013_ = v_a_2007_;
v___y_2014_ = v_a_2008_;
goto v___jp_2010_;
}
else
{
lean_dec(v_h_2004_);
lean_dec(v_mvarId_2003_);
lean_dec(v_ctorName_2002_);
return v___x_2049_;
}
}
}
v___jp_2010_:
{
lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2015_ = lean_box(0);
v___x_2016_ = l_Lean_Meta_injection(v_mvarId_2003_, v_h_2004_, v___x_2015_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v_a_2017_; 
v_a_2017_ = lean_ctor_get(v___x_2016_, 0);
lean_inc(v_a_2017_);
lean_dec_ref_known(v___x_2016_, 1);
if (lean_obj_tag(v_a_2017_) == 0)
{
lean_object* v___x_2018_; lean_object* v___x_2019_; 
lean_dec(v_ctorName_2002_);
v___x_2018_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3);
v___x_2019_ = l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0(v___x_2018_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_);
return v___x_2019_;
}
else
{
lean_object* v_mvarId_2020_; lean_object* v___x_2021_; 
v_mvarId_2020_ = lean_ctor_get(v_a_2017_, 0);
lean_inc(v_mvarId_2020_);
lean_dec_ref_known(v_a_2017_, 3);
v___x_2021_ = l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(v_mvarId_2020_, v_ctorName_2002_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_);
return v___x_2021_;
}
}
else
{
lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2029_; 
lean_dec(v_ctorName_2002_);
v_a_2022_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2024_ = v___x_2016_;
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v___x_2016_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2027_; 
if (v_isShared_2025_ == 0)
{
v___x_2027_ = v___x_2024_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_a_2022_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___boxed(lean_object* v_ctorName_2050_, lean_object* v_mvarId_2051_, lean_object* v_h_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_){
_start:
{
lean_object* v_res_2058_; 
v_res_2058_ = l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(v_ctorName_2050_, v_mvarId_2051_, v_h_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_);
lean_dec(v_a_2056_);
lean_dec_ref(v_a_2055_);
lean_dec(v_a_2054_);
lean_dec_ref(v_a_2053_);
return v_res_2058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(lean_object* v_type_2059_, lean_object* v_k_2060_, uint8_t v_cleanupAnnotations_2061_, uint8_t v_whnfType_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
lean_object* v___f_2068_; lean_object* v___x_2069_; 
v___f_2068_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2068_, 0, v_k_2060_);
v___x_2069_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_2059_, v___f_2068_, v_cleanupAnnotations_2061_, v_whnfType_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_);
if (lean_obj_tag(v___x_2069_) == 0)
{
lean_object* v_a_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2077_; 
v_a_2070_ = lean_ctor_get(v___x_2069_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2072_ = v___x_2069_;
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_a_2070_);
lean_dec(v___x_2069_);
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
v_reuseFailAlloc_2076_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2085_; 
v_a_2078_ = lean_ctor_get(v___x_2069_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2080_ = v___x_2069_;
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_a_2078_);
lean_dec(v___x_2069_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg___boxed(lean_object* v_type_2086_, lean_object* v_k_2087_, lean_object* v_cleanupAnnotations_2088_, lean_object* v_whnfType_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2095_; uint8_t v_whnfType_boxed_2096_; lean_object* v_res_2097_; 
v_cleanupAnnotations_boxed_2095_ = lean_unbox(v_cleanupAnnotations_2088_);
v_whnfType_boxed_2096_ = lean_unbox(v_whnfType_2089_);
v_res_2097_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_type_2086_, v_k_2087_, v_cleanupAnnotations_boxed_2095_, v_whnfType_boxed_2096_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
lean_dec(v___y_2091_);
lean_dec_ref(v___y_2090_);
return v_res_2097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0(lean_object* v_00_u03b1_2098_, lean_object* v_type_2099_, lean_object* v_k_2100_, uint8_t v_cleanupAnnotations_2101_, uint8_t v_whnfType_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_){
_start:
{
lean_object* v___x_2108_; 
v___x_2108_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_type_2099_, v_k_2100_, v_cleanupAnnotations_2101_, v_whnfType_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_);
return v___x_2108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___boxed(lean_object* v_00_u03b1_2109_, lean_object* v_type_2110_, lean_object* v_k_2111_, lean_object* v_cleanupAnnotations_2112_, lean_object* v_whnfType_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2119_; uint8_t v_whnfType_boxed_2120_; lean_object* v_res_2121_; 
v_cleanupAnnotations_boxed_2119_ = lean_unbox(v_cleanupAnnotations_2112_);
v_whnfType_boxed_2120_ = lean_unbox(v_whnfType_2113_);
v_res_2121_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0(v_00_u03b1_2109_, v_type_2110_, v_k_2111_, v_cleanupAnnotations_boxed_2119_, v_whnfType_boxed_2120_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_);
lean_dec(v___y_2117_);
lean_dec_ref(v___y_2116_);
lean_dec(v___y_2115_);
lean_dec_ref(v___y_2114_);
return v_res_2121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0(lean_object* v___x_2122_, lean_object* v_ctorName_2123_, lean_object* v_xs_2124_, lean_object* v_type_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_){
_start:
{
lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2131_ = lean_box(0);
v___x_2132_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_2125_, v___x_2131_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; 
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
lean_inc(v_a_2133_);
lean_dec_ref_known(v___x_2132_, 1);
v___x_2134_ = l_Lean_Expr_mvarId_x21(v_a_2133_);
v___x_2135_ = lean_array_get_size(v_xs_2124_);
v___x_2136_ = lean_unsigned_to_nat(1u);
v___x_2137_ = lean_nat_sub(v___x_2135_, v___x_2136_);
v___x_2138_ = lean_array_get_borrowed(v___x_2122_, v_xs_2124_, v___x_2137_);
lean_dec(v___x_2137_);
v___x_2139_ = l_Lean_Expr_fvarId_x21(v___x_2138_);
v___x_2140_ = l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(v_ctorName_2123_, v___x_2134_, v___x_2139_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
if (lean_obj_tag(v___x_2140_) == 0)
{
uint8_t v___x_2141_; uint8_t v___x_2142_; uint8_t v___x_2143_; lean_object* v___x_2144_; 
lean_dec_ref_known(v___x_2140_, 1);
v___x_2141_ = 0;
v___x_2142_ = 1;
v___x_2143_ = 1;
v___x_2144_ = l_Lean_Meta_mkLambdaFVars(v_xs_2124_, v_a_2133_, v___x_2141_, v___x_2142_, v___x_2141_, v___x_2142_, v___x_2143_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
return v___x_2144_;
}
else
{
lean_object* v_a_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2152_; 
lean_dec(v_a_2133_);
v_a_2145_ = lean_ctor_get(v___x_2140_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2147_ = v___x_2140_;
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_a_2145_);
lean_dec(v___x_2140_);
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
}
else
{
lean_dec(v_ctorName_2123_);
return v___x_2132_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0___boxed(lean_object* v___x_2153_, lean_object* v_ctorName_2154_, lean_object* v_xs_2155_, lean_object* v_type_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_){
_start:
{
lean_object* v_res_2162_; 
v_res_2162_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0(v___x_2153_, v_ctorName_2154_, v_xs_2155_, v_type_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
lean_dec_ref(v_xs_2155_);
lean_dec_ref(v___x_2153_);
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(lean_object* v_ctorName_2163_, lean_object* v_targetType_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_){
_start:
{
lean_object* v___x_2170_; lean_object* v___f_2171_; uint8_t v___x_2172_; lean_object* v___x_2173_; 
v___x_2170_ = l_Lean_instInhabitedExpr;
v___f_2171_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2171_, 0, v___x_2170_);
lean_closure_set(v___f_2171_, 1, v_ctorName_2163_);
v___x_2172_ = 0;
v___x_2173_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_targetType_2164_, v___f_2171_, v___x_2172_, v___x_2172_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_);
return v___x_2173_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___boxed(lean_object* v_ctorName_2174_, lean_object* v_targetType_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_){
_start:
{
lean_object* v_res_2181_; 
v_res_2181_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_ctorName_2174_, v_targetType_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_);
lean_dec(v_a_2179_);
lean_dec_ref(v_a_2178_);
lean_dec(v_a_2177_);
lean_dec_ref(v_a_2176_);
return v_res_2181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheoremNameFor(lean_object* v_ctorName_2185_){
_start:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2186_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheoremNameFor___closed__1));
v___x_2187_ = l_Lean_Name_append(v_ctorName_2185_, v___x_2186_);
return v___x_2187_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(lean_object* v_e_2188_, lean_object* v___y_2189_){
_start:
{
uint8_t v___x_2191_; 
v___x_2191_ = l_Lean_Expr_hasMVar(v_e_2188_);
if (v___x_2191_ == 0)
{
lean_object* v___x_2192_; 
v___x_2192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2192_, 0, v_e_2188_);
return v___x_2192_;
}
else
{
lean_object* v___x_2193_; lean_object* v_mctx_2194_; lean_object* v___x_2195_; lean_object* v_fst_2196_; lean_object* v_snd_2197_; lean_object* v___x_2198_; lean_object* v_cache_2199_; lean_object* v_zetaDeltaFVarIds_2200_; lean_object* v_postponed_2201_; lean_object* v_diag_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2211_; 
v___x_2193_ = lean_st_ref_get(v___y_2189_);
v_mctx_2194_ = lean_ctor_get(v___x_2193_, 0);
lean_inc_ref(v_mctx_2194_);
lean_dec(v___x_2193_);
v___x_2195_ = l_Lean_instantiateMVarsCore(v_mctx_2194_, v_e_2188_);
v_fst_2196_ = lean_ctor_get(v___x_2195_, 0);
lean_inc(v_fst_2196_);
v_snd_2197_ = lean_ctor_get(v___x_2195_, 1);
lean_inc(v_snd_2197_);
lean_dec_ref(v___x_2195_);
v___x_2198_ = lean_st_ref_take(v___y_2189_);
v_cache_2199_ = lean_ctor_get(v___x_2198_, 1);
v_zetaDeltaFVarIds_2200_ = lean_ctor_get(v___x_2198_, 2);
v_postponed_2201_ = lean_ctor_get(v___x_2198_, 3);
v_diag_2202_ = lean_ctor_get(v___x_2198_, 4);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2211_ == 0)
{
lean_object* v_unused_2212_; 
v_unused_2212_ = lean_ctor_get(v___x_2198_, 0);
lean_dec(v_unused_2212_);
v___x_2204_ = v___x_2198_;
v_isShared_2205_ = v_isSharedCheck_2211_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_diag_2202_);
lean_inc(v_postponed_2201_);
lean_inc(v_zetaDeltaFVarIds_2200_);
lean_inc(v_cache_2199_);
lean_dec(v___x_2198_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2211_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2207_; 
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 0, v_snd_2197_);
v___x_2207_ = v___x_2204_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_snd_2197_);
lean_ctor_set(v_reuseFailAlloc_2210_, 1, v_cache_2199_);
lean_ctor_set(v_reuseFailAlloc_2210_, 2, v_zetaDeltaFVarIds_2200_);
lean_ctor_set(v_reuseFailAlloc_2210_, 3, v_postponed_2201_);
lean_ctor_set(v_reuseFailAlloc_2210_, 4, v_diag_2202_);
v___x_2207_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2208_ = lean_st_ref_put(v___y_2189_, v___x_2207_);
v___x_2209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2209_, 0, v_fst_2196_);
return v___x_2209_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg___boxed(lean_object* v_e_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_){
_start:
{
lean_object* v_res_2216_; 
v_res_2216_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_e_2213_, v___y_2214_);
lean_dec(v___y_2214_);
return v_res_2216_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0(lean_object* v_e_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_){
_start:
{
lean_object* v___x_2223_; 
v___x_2223_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_e_2217_, v___y_2219_);
return v___x_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___boxed(lean_object* v_e_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_){
_start:
{
lean_object* v_res_2230_; 
v_res_2230_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0(v_e_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2225_);
return v_res_2230_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2231_ = lean_unsigned_to_nat(32u);
v___x_2232_ = lean_mk_empty_array_with_capacity(v___x_2231_);
v___x_2233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2233_, 0, v___x_2232_);
return v___x_2233_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
v___x_2234_ = ((size_t)5ULL);
v___x_2235_ = lean_unsigned_to_nat(0u);
v___x_2236_ = lean_unsigned_to_nat(32u);
v___x_2237_ = lean_mk_empty_array_with_capacity(v___x_2236_);
v___x_2238_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0);
v___x_2239_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2239_, 0, v___x_2238_);
lean_ctor_set(v___x_2239_, 1, v___x_2237_);
lean_ctor_set(v___x_2239_, 2, v___x_2235_);
lean_ctor_set(v___x_2239_, 3, v___x_2235_);
lean_ctor_set_usize(v___x_2239_, 4, v___x_2234_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(lean_object* v___y_2240_){
_start:
{
lean_object* v___x_2242_; lean_object* v_traceState_2243_; lean_object* v_traces_2244_; lean_object* v___x_2245_; lean_object* v_traceState_2246_; lean_object* v_env_2247_; lean_object* v_nextMacroScope_2248_; lean_object* v_ngen_2249_; lean_object* v_auxDeclNGen_2250_; lean_object* v_cache_2251_; lean_object* v_messages_2252_; lean_object* v_infoState_2253_; lean_object* v_snapshotTasks_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2273_; 
v___x_2242_ = lean_st_ref_get(v___y_2240_);
v_traceState_2243_ = lean_ctor_get(v___x_2242_, 4);
lean_inc_ref(v_traceState_2243_);
lean_dec(v___x_2242_);
v_traces_2244_ = lean_ctor_get(v_traceState_2243_, 0);
lean_inc_ref(v_traces_2244_);
lean_dec_ref(v_traceState_2243_);
v___x_2245_ = lean_st_ref_take(v___y_2240_);
v_traceState_2246_ = lean_ctor_get(v___x_2245_, 4);
v_env_2247_ = lean_ctor_get(v___x_2245_, 0);
v_nextMacroScope_2248_ = lean_ctor_get(v___x_2245_, 1);
v_ngen_2249_ = lean_ctor_get(v___x_2245_, 2);
v_auxDeclNGen_2250_ = lean_ctor_get(v___x_2245_, 3);
v_cache_2251_ = lean_ctor_get(v___x_2245_, 5);
v_messages_2252_ = lean_ctor_get(v___x_2245_, 6);
v_infoState_2253_ = lean_ctor_get(v___x_2245_, 7);
v_snapshotTasks_2254_ = lean_ctor_get(v___x_2245_, 8);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2245_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2256_ = v___x_2245_;
v_isShared_2257_ = v_isSharedCheck_2273_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_snapshotTasks_2254_);
lean_inc(v_infoState_2253_);
lean_inc(v_messages_2252_);
lean_inc(v_cache_2251_);
lean_inc(v_traceState_2246_);
lean_inc(v_auxDeclNGen_2250_);
lean_inc(v_ngen_2249_);
lean_inc(v_nextMacroScope_2248_);
lean_inc(v_env_2247_);
lean_dec(v___x_2245_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2273_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
uint64_t v_tid_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2271_; 
v_tid_2258_ = lean_ctor_get_uint64(v_traceState_2246_, sizeof(void*)*1);
v_isSharedCheck_2271_ = !lean_is_exclusive(v_traceState_2246_);
if (v_isSharedCheck_2271_ == 0)
{
lean_object* v_unused_2272_; 
v_unused_2272_ = lean_ctor_get(v_traceState_2246_, 0);
lean_dec(v_unused_2272_);
v___x_2260_ = v_traceState_2246_;
v_isShared_2261_ = v_isSharedCheck_2271_;
goto v_resetjp_2259_;
}
else
{
lean_dec(v_traceState_2246_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2271_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
lean_object* v___x_2262_; lean_object* v___x_2264_; 
v___x_2262_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1);
if (v_isShared_2261_ == 0)
{
lean_ctor_set(v___x_2260_, 0, v___x_2262_);
v___x_2264_ = v___x_2260_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v___x_2262_);
lean_ctor_set_uint64(v_reuseFailAlloc_2270_, sizeof(void*)*1, v_tid_2258_);
v___x_2264_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
lean_object* v___x_2266_; 
if (v_isShared_2257_ == 0)
{
lean_ctor_set(v___x_2256_, 4, v___x_2264_);
v___x_2266_ = v___x_2256_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_env_2247_);
lean_ctor_set(v_reuseFailAlloc_2269_, 1, v_nextMacroScope_2248_);
lean_ctor_set(v_reuseFailAlloc_2269_, 2, v_ngen_2249_);
lean_ctor_set(v_reuseFailAlloc_2269_, 3, v_auxDeclNGen_2250_);
lean_ctor_set(v_reuseFailAlloc_2269_, 4, v___x_2264_);
lean_ctor_set(v_reuseFailAlloc_2269_, 5, v_cache_2251_);
lean_ctor_set(v_reuseFailAlloc_2269_, 6, v_messages_2252_);
lean_ctor_set(v_reuseFailAlloc_2269_, 7, v_infoState_2253_);
lean_ctor_set(v_reuseFailAlloc_2269_, 8, v_snapshotTasks_2254_);
v___x_2266_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
lean_object* v___x_2267_; lean_object* v___x_2268_; 
v___x_2267_ = lean_st_ref_put(v___y_2240_, v___x_2266_);
v___x_2268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2268_, 0, v_traces_2244_);
return v___x_2268_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___boxed(lean_object* v___y_2274_, lean_object* v___y_2275_){
_start:
{
lean_object* v_res_2276_; 
v_res_2276_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v___y_2274_);
lean_dec(v___y_2274_);
return v_res_2276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1(lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_){
_start:
{
lean_object* v___x_2282_; 
v___x_2282_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v___y_2280_);
return v___x_2282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___boxed(lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_){
_start:
{
lean_object* v_res_2288_; 
v_res_2288_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1(v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_);
lean_dec(v___y_2286_);
lean_dec_ref(v___y_2285_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
return v_res_2288_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(lean_object* v_opts_2289_, lean_object* v_opt_2290_){
_start:
{
lean_object* v_name_2291_; lean_object* v_defValue_2292_; lean_object* v_map_2293_; lean_object* v___x_2294_; 
v_name_2291_ = lean_ctor_get(v_opt_2290_, 0);
v_defValue_2292_ = lean_ctor_get(v_opt_2290_, 1);
v_map_2293_ = lean_ctor_get(v_opts_2289_, 0);
v___x_2294_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2293_, v_name_2291_);
if (lean_obj_tag(v___x_2294_) == 0)
{
uint8_t v___x_2295_; 
v___x_2295_ = lean_unbox(v_defValue_2292_);
return v___x_2295_;
}
else
{
lean_object* v_val_2296_; 
v_val_2296_ = lean_ctor_get(v___x_2294_, 0);
lean_inc(v_val_2296_);
lean_dec_ref_known(v___x_2294_, 1);
if (lean_obj_tag(v_val_2296_) == 1)
{
uint8_t v_v_2297_; 
v_v_2297_ = lean_ctor_get_uint8(v_val_2296_, 0);
lean_dec_ref_known(v_val_2296_, 0);
return v_v_2297_;
}
else
{
uint8_t v___x_2298_; 
lean_dec(v_val_2296_);
v___x_2298_ = lean_unbox(v_defValue_2292_);
return v___x_2298_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2___boxed(lean_object* v_opts_2299_, lean_object* v_opt_2300_){
_start:
{
uint8_t v_res_2301_; lean_object* v_r_2302_; 
v_res_2301_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_opts_2299_, v_opt_2300_);
lean_dec_ref(v_opt_2300_);
lean_dec_ref(v_opts_2299_);
v_r_2302_ = lean_box(v_res_2301_);
return v_r_2302_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2304_; lean_object* v___x_2305_; 
v___x_2304_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__0));
v___x_2305_ = l_Lean_stringToMessageData(v___x_2304_);
return v___x_2305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0(lean_object* v_name_2306_, lean_object* v_x_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2313_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1);
v___x_2314_ = l_Lean_MessageData_ofName(v_name_2306_);
v___x_2315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2313_);
lean_ctor_set(v___x_2315_, 1, v___x_2314_);
v___x_2316_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_2317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2315_);
lean_ctor_set(v___x_2317_, 1, v___x_2316_);
v___x_2318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2317_);
return v___x_2318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed(lean_object* v_name_2319_, lean_object* v_x_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_){
_start:
{
lean_object* v_res_2326_; 
v_res_2326_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0(v_name_2319_, v_x_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_);
lean_dec(v___y_2324_);
lean_dec_ref(v___y_2323_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
lean_dec_ref(v_x_2320_);
return v_res_2326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(lean_object* v_name_2327_, lean_object* v_val_2328_, lean_object* v_name_2329_, lean_object* v_levelParams_2330_, uint8_t v___x_2331_, lean_object* v_____r_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
lean_object* v___x_2338_; 
lean_inc_ref(v_val_2328_);
v___x_2338_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2327_, v_val_2328_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
if (lean_obj_tag(v___x_2338_) == 0)
{
lean_object* v_a_2339_; lean_object* v___x_2340_; lean_object* v_a_2341_; lean_object* v___x_2342_; lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2355_; 
v_a_2339_ = lean_ctor_get(v___x_2338_, 0);
lean_inc(v_a_2339_);
lean_dec_ref_known(v___x_2338_, 1);
v___x_2340_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2328_, v___y_2334_);
v_a_2341_ = lean_ctor_get(v___x_2340_, 0);
lean_inc(v_a_2341_);
lean_dec_ref(v___x_2340_);
v___x_2342_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2339_, v___y_2334_);
v_a_2343_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2355_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2355_ == 0)
{
v___x_2345_ = v___x_2342_;
v_isShared_2346_ = v_isSharedCheck_2355_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_a_2343_);
lean_dec(v___x_2342_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2355_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2352_; 
lean_inc(v_name_2329_);
v___x_2347_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2347_, 0, v_name_2329_);
lean_ctor_set(v___x_2347_, 1, v_levelParams_2330_);
lean_ctor_set(v___x_2347_, 2, v_a_2341_);
v___x_2348_ = lean_box(0);
v___x_2349_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2349_, 0, v_name_2329_);
lean_ctor_set(v___x_2349_, 1, v___x_2348_);
v___x_2350_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2347_);
lean_ctor_set(v___x_2350_, 1, v_a_2343_);
lean_ctor_set(v___x_2350_, 2, v___x_2349_);
if (v_isShared_2346_ == 0)
{
lean_ctor_set_tag(v___x_2345_, 2);
lean_ctor_set(v___x_2345_, 0, v___x_2350_);
v___x_2352_ = v___x_2345_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v___x_2350_);
v___x_2352_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
lean_object* v___x_2353_; 
v___x_2353_ = l_Lean_addDecl(v___x_2352_, v___x_2331_, v___y_2335_, v___y_2336_);
return v___x_2353_;
}
}
}
else
{
lean_object* v_a_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2363_; 
lean_dec(v_levelParams_2330_);
lean_dec(v_name_2329_);
lean_dec_ref(v_val_2328_);
v_a_2356_ = lean_ctor_get(v___x_2338_, 0);
v_isSharedCheck_2363_ = !lean_is_exclusive(v___x_2338_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2358_ = v___x_2338_;
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_a_2356_);
lean_dec(v___x_2338_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v___x_2361_; 
if (v_isShared_2359_ == 0)
{
v___x_2361_ = v___x_2358_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_a_2356_);
v___x_2361_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
return v___x_2361_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1___boxed(lean_object* v_name_2364_, lean_object* v_val_2365_, lean_object* v_name_2366_, lean_object* v_levelParams_2367_, lean_object* v___x_2368_, lean_object* v_____r_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_){
_start:
{
uint8_t v___x_12398__boxed_2375_; lean_object* v_res_2376_; 
v___x_12398__boxed_2375_ = lean_unbox(v___x_2368_);
v_res_2376_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(v_name_2364_, v_val_2365_, v_name_2366_, v_levelParams_2367_, v___x_12398__boxed_2375_, v_____r_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_);
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
lean_dec(v___y_2371_);
lean_dec_ref(v___y_2370_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(lean_object* v_name_2377_, lean_object* v_val_2378_, lean_object* v_name_2379_, lean_object* v_levelParams_2380_, lean_object* v_____r_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_){
_start:
{
lean_object* v___x_2387_; 
lean_inc_ref(v_val_2378_);
v___x_2387_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2377_, v_val_2378_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_);
if (lean_obj_tag(v___x_2387_) == 0)
{
lean_object* v_a_2388_; lean_object* v___x_2389_; lean_object* v_a_2390_; lean_object* v___x_2391_; lean_object* v_a_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2405_; 
v_a_2388_ = lean_ctor_get(v___x_2387_, 0);
lean_inc(v_a_2388_);
lean_dec_ref_known(v___x_2387_, 1);
v___x_2389_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2378_, v___y_2383_);
v_a_2390_ = lean_ctor_get(v___x_2389_, 0);
lean_inc(v_a_2390_);
lean_dec_ref(v___x_2389_);
v___x_2391_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2388_, v___y_2383_);
v_a_2392_ = lean_ctor_get(v___x_2391_, 0);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2394_ = v___x_2391_;
v_isShared_2395_ = v_isSharedCheck_2405_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_a_2392_);
lean_dec(v___x_2391_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2405_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2401_; 
lean_inc(v_name_2379_);
v___x_2396_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2396_, 0, v_name_2379_);
lean_ctor_set(v___x_2396_, 1, v_levelParams_2380_);
lean_ctor_set(v___x_2396_, 2, v_a_2390_);
v___x_2397_ = lean_box(0);
v___x_2398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2398_, 0, v_name_2379_);
lean_ctor_set(v___x_2398_, 1, v___x_2397_);
v___x_2399_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2396_);
lean_ctor_set(v___x_2399_, 1, v_a_2392_);
lean_ctor_set(v___x_2399_, 2, v___x_2398_);
if (v_isShared_2395_ == 0)
{
lean_ctor_set_tag(v___x_2394_, 2);
lean_ctor_set(v___x_2394_, 0, v___x_2399_);
v___x_2401_ = v___x_2394_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v___x_2399_);
v___x_2401_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
uint8_t v___x_2402_; lean_object* v___x_2403_; 
v___x_2402_ = 0;
v___x_2403_ = l_Lean_addDecl(v___x_2401_, v___x_2402_, v___y_2384_, v___y_2385_);
return v___x_2403_;
}
}
}
else
{
lean_object* v_a_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2413_; 
lean_dec(v_levelParams_2380_);
lean_dec(v_name_2379_);
lean_dec_ref(v_val_2378_);
v_a_2406_ = lean_ctor_get(v___x_2387_, 0);
v_isSharedCheck_2413_ = !lean_is_exclusive(v___x_2387_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2408_ = v___x_2387_;
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_a_2406_);
lean_dec(v___x_2387_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v___x_2411_; 
if (v_isShared_2409_ == 0)
{
v___x_2411_ = v___x_2408_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v_a_2406_);
v___x_2411_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
return v___x_2411_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2___boxed(lean_object* v_name_2414_, lean_object* v_val_2415_, lean_object* v_name_2416_, lean_object* v_levelParams_2417_, lean_object* v_____r_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_){
_start:
{
lean_object* v_res_2424_; 
v_res_2424_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(v_name_2414_, v_val_2415_, v_name_2416_, v_levelParams_2417_, v_____r_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_);
lean_dec(v___y_2422_);
lean_dec_ref(v___y_2421_);
lean_dec(v___y_2420_);
lean_dec_ref(v___y_2419_);
return v_res_2424_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3_spec__4(size_t v_sz_2425_, size_t v_i_2426_, lean_object* v_bs_2427_){
_start:
{
uint8_t v___x_2428_; 
v___x_2428_ = lean_usize_dec_lt(v_i_2426_, v_sz_2425_);
if (v___x_2428_ == 0)
{
return v_bs_2427_;
}
else
{
lean_object* v_v_2429_; lean_object* v_msg_2430_; lean_object* v___x_2431_; lean_object* v_bs_x27_2432_; size_t v___x_2433_; size_t v___x_2434_; lean_object* v___x_2435_; 
v_v_2429_ = lean_array_uget_borrowed(v_bs_2427_, v_i_2426_);
v_msg_2430_ = lean_ctor_get(v_v_2429_, 1);
lean_inc_ref(v_msg_2430_);
v___x_2431_ = lean_unsigned_to_nat(0u);
v_bs_x27_2432_ = lean_array_uset(v_bs_2427_, v_i_2426_, v___x_2431_);
v___x_2433_ = ((size_t)1ULL);
v___x_2434_ = lean_usize_add(v_i_2426_, v___x_2433_);
v___x_2435_ = lean_array_uset(v_bs_x27_2432_, v_i_2426_, v_msg_2430_);
v_i_2426_ = v___x_2434_;
v_bs_2427_ = v___x_2435_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_2437_, lean_object* v_i_2438_, lean_object* v_bs_2439_){
_start:
{
size_t v_sz_boxed_2440_; size_t v_i_boxed_2441_; lean_object* v_res_2442_; 
v_sz_boxed_2440_ = lean_unbox_usize(v_sz_2437_);
lean_dec(v_sz_2437_);
v_i_boxed_2441_ = lean_unbox_usize(v_i_2438_);
lean_dec(v_i_2438_);
v_res_2442_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3_spec__4(v_sz_boxed_2440_, v_i_boxed_2441_, v_bs_2439_);
return v_res_2442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(lean_object* v_oldTraces_2443_, lean_object* v_data_2444_, lean_object* v_ref_2445_, lean_object* v_msg_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_){
_start:
{
lean_object* v_toCold_2452_; lean_object* v_currRecDepth_2453_; lean_object* v_ref_2454_; uint8_t v_diag_2455_; uint8_t v_suppressElabErrors_2456_; lean_object* v___x_2457_; lean_object* v_traceState_2458_; lean_object* v_traces_2459_; lean_object* v_ref_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; size_t v_sz_2463_; size_t v___x_2464_; lean_object* v___x_2465_; lean_object* v_msg_2466_; lean_object* v___x_2467_; lean_object* v_a_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2505_; 
v_toCold_2452_ = lean_ctor_get(v___y_2449_, 0);
v_currRecDepth_2453_ = lean_ctor_get(v___y_2449_, 1);
v_ref_2454_ = lean_ctor_get(v___y_2449_, 2);
v_diag_2455_ = lean_ctor_get_uint8(v___y_2449_, sizeof(void*)*3);
v_suppressElabErrors_2456_ = lean_ctor_get_uint8(v___y_2449_, sizeof(void*)*3 + 1);
v___x_2457_ = lean_st_ref_get(v___y_2450_);
v_traceState_2458_ = lean_ctor_get(v___x_2457_, 4);
lean_inc_ref(v_traceState_2458_);
lean_dec(v___x_2457_);
v_traces_2459_ = lean_ctor_get(v_traceState_2458_, 0);
lean_inc_ref(v_traces_2459_);
lean_dec_ref(v_traceState_2458_);
v_ref_2460_ = l_Lean_replaceRef(v_ref_2445_, v_ref_2454_);
lean_inc(v_currRecDepth_2453_);
lean_inc_ref(v_toCold_2452_);
v___x_2461_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2461_, 0, v_toCold_2452_);
lean_ctor_set(v___x_2461_, 1, v_currRecDepth_2453_);
lean_ctor_set(v___x_2461_, 2, v_ref_2460_);
lean_ctor_set_uint8(v___x_2461_, sizeof(void*)*3, v_diag_2455_);
lean_ctor_set_uint8(v___x_2461_, sizeof(void*)*3 + 1, v_suppressElabErrors_2456_);
v___x_2462_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2459_);
lean_dec_ref(v_traces_2459_);
v_sz_2463_ = lean_array_size(v___x_2462_);
v___x_2464_ = ((size_t)0ULL);
v___x_2465_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3_spec__4(v_sz_2463_, v___x_2464_, v___x_2462_);
v_msg_2466_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2466_, 0, v_data_2444_);
lean_ctor_set(v_msg_2466_, 1, v_msg_2446_);
lean_ctor_set(v_msg_2466_, 2, v___x_2465_);
v___x_2467_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msg_2466_, v___y_2447_, v___y_2448_, v___x_2461_, v___y_2450_);
lean_dec_ref_known(v___x_2461_, 3);
v_a_2468_ = lean_ctor_get(v___x_2467_, 0);
v_isSharedCheck_2505_ = !lean_is_exclusive(v___x_2467_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2470_ = v___x_2467_;
v_isShared_2471_ = v_isSharedCheck_2505_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_a_2468_);
lean_dec(v___x_2467_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2505_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2472_; lean_object* v_traceState_2473_; lean_object* v_env_2474_; lean_object* v_nextMacroScope_2475_; lean_object* v_ngen_2476_; lean_object* v_auxDeclNGen_2477_; lean_object* v_cache_2478_; lean_object* v_messages_2479_; lean_object* v_infoState_2480_; lean_object* v_snapshotTasks_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2504_; 
v___x_2472_ = lean_st_ref_take(v___y_2450_);
v_traceState_2473_ = lean_ctor_get(v___x_2472_, 4);
v_env_2474_ = lean_ctor_get(v___x_2472_, 0);
v_nextMacroScope_2475_ = lean_ctor_get(v___x_2472_, 1);
v_ngen_2476_ = lean_ctor_get(v___x_2472_, 2);
v_auxDeclNGen_2477_ = lean_ctor_get(v___x_2472_, 3);
v_cache_2478_ = lean_ctor_get(v___x_2472_, 5);
v_messages_2479_ = lean_ctor_get(v___x_2472_, 6);
v_infoState_2480_ = lean_ctor_get(v___x_2472_, 7);
v_snapshotTasks_2481_ = lean_ctor_get(v___x_2472_, 8);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2472_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2483_ = v___x_2472_;
v_isShared_2484_ = v_isSharedCheck_2504_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_snapshotTasks_2481_);
lean_inc(v_infoState_2480_);
lean_inc(v_messages_2479_);
lean_inc(v_cache_2478_);
lean_inc(v_traceState_2473_);
lean_inc(v_auxDeclNGen_2477_);
lean_inc(v_ngen_2476_);
lean_inc(v_nextMacroScope_2475_);
lean_inc(v_env_2474_);
lean_dec(v___x_2472_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2504_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
uint64_t v_tid_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2502_; 
v_tid_2485_ = lean_ctor_get_uint64(v_traceState_2473_, sizeof(void*)*1);
v_isSharedCheck_2502_ = !lean_is_exclusive(v_traceState_2473_);
if (v_isSharedCheck_2502_ == 0)
{
lean_object* v_unused_2503_; 
v_unused_2503_ = lean_ctor_get(v_traceState_2473_, 0);
lean_dec(v_unused_2503_);
v___x_2487_ = v_traceState_2473_;
v_isShared_2488_ = v_isSharedCheck_2502_;
goto v_resetjp_2486_;
}
else
{
lean_dec(v_traceState_2473_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2502_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2492_; 
v___x_2489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2489_, 0, v_ref_2445_);
lean_ctor_set(v___x_2489_, 1, v_a_2468_);
v___x_2490_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2443_, v___x_2489_);
if (v_isShared_2488_ == 0)
{
lean_ctor_set(v___x_2487_, 0, v___x_2490_);
v___x_2492_ = v___x_2487_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v___x_2490_);
lean_ctor_set_uint64(v_reuseFailAlloc_2501_, sizeof(void*)*1, v_tid_2485_);
v___x_2492_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
lean_object* v___x_2494_; 
if (v_isShared_2484_ == 0)
{
lean_ctor_set(v___x_2483_, 4, v___x_2492_);
v___x_2494_ = v___x_2483_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_env_2474_);
lean_ctor_set(v_reuseFailAlloc_2500_, 1, v_nextMacroScope_2475_);
lean_ctor_set(v_reuseFailAlloc_2500_, 2, v_ngen_2476_);
lean_ctor_set(v_reuseFailAlloc_2500_, 3, v_auxDeclNGen_2477_);
lean_ctor_set(v_reuseFailAlloc_2500_, 4, v___x_2492_);
lean_ctor_set(v_reuseFailAlloc_2500_, 5, v_cache_2478_);
lean_ctor_set(v_reuseFailAlloc_2500_, 6, v_messages_2479_);
lean_ctor_set(v_reuseFailAlloc_2500_, 7, v_infoState_2480_);
lean_ctor_set(v_reuseFailAlloc_2500_, 8, v_snapshotTasks_2481_);
v___x_2494_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2498_; 
v___x_2495_ = lean_st_ref_put(v___y_2450_, v___x_2494_);
v___x_2496_ = lean_box(0);
if (v_isShared_2471_ == 0)
{
lean_ctor_set(v___x_2470_, 0, v___x_2496_);
v___x_2498_ = v___x_2470_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v___x_2496_);
v___x_2498_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
return v___x_2498_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3___boxed(lean_object* v_oldTraces_2506_, lean_object* v_data_2507_, lean_object* v_ref_2508_, lean_object* v_msg_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_){
_start:
{
lean_object* v_res_2515_; 
v_res_2515_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(v_oldTraces_2506_, v_data_2507_, v_ref_2508_, v_msg_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_);
lean_dec(v___y_2513_);
lean_dec_ref(v___y_2512_);
lean_dec(v___y_2511_);
lean_dec_ref(v___y_2510_);
return v_res_2515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(lean_object* v_opts_2516_, lean_object* v_opt_2517_){
_start:
{
lean_object* v_name_2518_; lean_object* v_defValue_2519_; lean_object* v_map_2520_; lean_object* v___x_2521_; 
v_name_2518_ = lean_ctor_get(v_opt_2517_, 0);
v_defValue_2519_ = lean_ctor_get(v_opt_2517_, 1);
v_map_2520_ = lean_ctor_get(v_opts_2516_, 0);
v___x_2521_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2520_, v_name_2518_);
if (lean_obj_tag(v___x_2521_) == 0)
{
lean_inc(v_defValue_2519_);
return v_defValue_2519_;
}
else
{
lean_object* v_val_2522_; 
v_val_2522_ = lean_ctor_get(v___x_2521_, 0);
lean_inc(v_val_2522_);
lean_dec_ref_known(v___x_2521_, 1);
if (lean_obj_tag(v_val_2522_) == 3)
{
lean_object* v_v_2523_; 
v_v_2523_ = lean_ctor_get(v_val_2522_, 0);
lean_inc(v_v_2523_);
lean_dec_ref_known(v_val_2522_, 1);
return v_v_2523_;
}
else
{
lean_dec(v_val_2522_);
lean_inc(v_defValue_2519_);
return v_defValue_2519_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6___boxed(lean_object* v_opts_2524_, lean_object* v_opt_2525_){
_start:
{
lean_object* v_res_2526_; 
v_res_2526_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(v_opts_2524_, v_opt_2525_);
lean_dec_ref(v_opt_2525_);
lean_dec_ref(v_opts_2524_);
return v_res_2526_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5(lean_object* v_e_2527_){
_start:
{
if (lean_obj_tag(v_e_2527_) == 0)
{
uint8_t v___x_2528_; 
v___x_2528_ = 2;
return v___x_2528_;
}
else
{
uint8_t v___x_2529_; 
v___x_2529_ = 0;
return v___x_2529_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___boxed(lean_object* v_e_2530_){
_start:
{
uint8_t v_res_2531_; lean_object* v_r_2532_; 
v_res_2531_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5(v_e_2530_);
lean_dec_ref(v_e_2530_);
v_r_2532_ = lean_box(v_res_2531_);
return v_r_2532_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg(lean_object* v_x_2533_){
_start:
{
if (lean_obj_tag(v_x_2533_) == 0)
{
lean_object* v_a_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2542_; 
v_a_2535_ = lean_ctor_get(v_x_2533_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v_x_2533_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2537_ = v_x_2533_;
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_a_2535_);
lean_dec(v_x_2533_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v___x_2540_; 
if (v_isShared_2538_ == 0)
{
lean_ctor_set_tag(v___x_2537_, 1);
v___x_2540_ = v___x_2537_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_a_2535_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
}
else
{
lean_object* v_a_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2550_; 
v_a_2543_ = lean_ctor_get(v_x_2533_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v_x_2533_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2545_ = v_x_2533_;
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_a_2543_);
lean_dec(v_x_2533_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___x_2548_; 
if (v_isShared_2546_ == 0)
{
lean_ctor_set_tag(v___x_2545_, 0);
v___x_2548_ = v___x_2545_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_a_2543_);
v___x_2548_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
return v___x_2548_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg___boxed(lean_object* v_x_2551_, lean_object* v___y_2552_){
_start:
{
lean_object* v_res_2553_; 
v_res_2553_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg(v_x_2551_);
return v_res_2553_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2555_; lean_object* v___x_2556_; 
v___x_2555_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__0));
v___x_2556_ = l_Lean_stringToMessageData(v___x_2555_);
return v___x_2556_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2557_; double v___x_2558_; 
v___x_2557_ = lean_unsigned_to_nat(1000u);
v___x_2558_ = lean_float_of_nat(v___x_2557_);
return v___x_2558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(lean_object* v_cls_2559_, uint8_t v_collapsed_2560_, lean_object* v_tag_2561_, lean_object* v_opts_2562_, uint8_t v_clsEnabled_2563_, lean_object* v_oldTraces_2564_, lean_object* v_msg_2565_, lean_object* v_resStartStop_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_){
_start:
{
lean_object* v_fst_2572_; lean_object* v_snd_2573_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v_data_2577_; lean_object* v_fst_2580_; lean_object* v_snd_2581_; lean_object* v___x_2582_; uint8_t v___x_2583_; lean_object* v___y_2585_; lean_object* v_a_2586_; uint8_t v___y_2601_; double v___y_2632_; 
v_fst_2572_ = lean_ctor_get(v_resStartStop_2566_, 0);
lean_inc(v_fst_2572_);
v_snd_2573_ = lean_ctor_get(v_resStartStop_2566_, 1);
lean_inc(v_snd_2573_);
lean_dec_ref(v_resStartStop_2566_);
v_fst_2580_ = lean_ctor_get(v_snd_2573_, 0);
lean_inc(v_fst_2580_);
v_snd_2581_ = lean_ctor_get(v_snd_2573_, 1);
lean_inc(v_snd_2581_);
lean_dec(v_snd_2573_);
v___x_2582_ = l_Lean_trace_profiler;
v___x_2583_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_opts_2562_, v___x_2582_);
if (v___x_2583_ == 0)
{
v___y_2601_ = v___x_2583_;
goto v___jp_2600_;
}
else
{
lean_object* v___x_2637_; uint8_t v___x_2638_; 
v___x_2637_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2638_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_opts_2562_, v___x_2637_);
if (v___x_2638_ == 0)
{
lean_object* v___x_2639_; lean_object* v___x_2640_; double v___x_2641_; double v___x_2642_; double v___x_2643_; 
v___x_2639_ = l_Lean_trace_profiler_threshold;
v___x_2640_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(v_opts_2562_, v___x_2639_);
v___x_2641_ = lean_float_of_nat(v___x_2640_);
v___x_2642_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2);
v___x_2643_ = lean_float_div(v___x_2641_, v___x_2642_);
v___y_2632_ = v___x_2643_;
goto v___jp_2631_;
}
else
{
lean_object* v___x_2644_; lean_object* v___x_2645_; double v___x_2646_; 
v___x_2644_ = l_Lean_trace_profiler_threshold;
v___x_2645_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(v_opts_2562_, v___x_2644_);
v___x_2646_ = lean_float_of_nat(v___x_2645_);
v___y_2632_ = v___x_2646_;
goto v___jp_2631_;
}
}
v___jp_2574_:
{
lean_object* v___x_2578_; 
lean_inc(v___y_2576_);
v___x_2578_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(v_oldTraces_2564_, v_data_2577_, v___y_2576_, v___y_2575_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_);
if (lean_obj_tag(v___x_2578_) == 0)
{
lean_object* v___x_2579_; 
lean_dec_ref_known(v___x_2578_, 1);
v___x_2579_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg(v_fst_2572_);
return v___x_2579_;
}
else
{
lean_dec(v_fst_2572_);
return v___x_2578_;
}
}
v___jp_2584_:
{
uint8_t v_result_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; double v___x_2590_; lean_object* v_data_2591_; 
v_result_2587_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5(v_fst_2572_);
v___x_2588_ = lean_box(v_result_2587_);
v___x_2589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2589_, 0, v___x_2588_);
v___x_2590_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0);
lean_inc_ref(v_tag_2561_);
lean_inc_ref(v___x_2589_);
lean_inc(v_cls_2559_);
v_data_2591_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2591_, 0, v_cls_2559_);
lean_ctor_set(v_data_2591_, 1, v___x_2589_);
lean_ctor_set(v_data_2591_, 2, v_tag_2561_);
lean_ctor_set_float(v_data_2591_, sizeof(void*)*3, v___x_2590_);
lean_ctor_set_float(v_data_2591_, sizeof(void*)*3 + 8, v___x_2590_);
lean_ctor_set_uint8(v_data_2591_, sizeof(void*)*3 + 16, v_collapsed_2560_);
if (v___x_2583_ == 0)
{
lean_dec_ref_known(v___x_2589_, 1);
lean_dec(v_snd_2581_);
lean_dec(v_fst_2580_);
lean_dec_ref(v_tag_2561_);
lean_dec(v_cls_2559_);
v___y_2575_ = v_a_2586_;
v___y_2576_ = v___y_2585_;
v_data_2577_ = v_data_2591_;
goto v___jp_2574_;
}
else
{
lean_object* v_data_2592_; double v___x_2593_; double v___x_2594_; 
lean_dec_ref_known(v_data_2591_, 3);
v_data_2592_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2592_, 0, v_cls_2559_);
lean_ctor_set(v_data_2592_, 1, v___x_2589_);
lean_ctor_set(v_data_2592_, 2, v_tag_2561_);
v___x_2593_ = lean_unbox_float(v_fst_2580_);
lean_dec(v_fst_2580_);
lean_ctor_set_float(v_data_2592_, sizeof(void*)*3, v___x_2593_);
v___x_2594_ = lean_unbox_float(v_snd_2581_);
lean_dec(v_snd_2581_);
lean_ctor_set_float(v_data_2592_, sizeof(void*)*3 + 8, v___x_2594_);
lean_ctor_set_uint8(v_data_2592_, sizeof(void*)*3 + 16, v_collapsed_2560_);
v___y_2575_ = v_a_2586_;
v___y_2576_ = v___y_2585_;
v_data_2577_ = v_data_2592_;
goto v___jp_2574_;
}
}
v___jp_2595_:
{
lean_object* v_ref_2596_; lean_object* v___x_2597_; 
v_ref_2596_ = lean_ctor_get(v___y_2569_, 2);
lean_inc(v___y_2570_);
lean_inc_ref(v___y_2569_);
lean_inc(v___y_2568_);
lean_inc_ref(v___y_2567_);
lean_inc(v_fst_2572_);
v___x_2597_ = lean_apply_6(v_msg_2565_, v_fst_2572_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, lean_box(0));
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_object* v_a_2598_; 
v_a_2598_ = lean_ctor_get(v___x_2597_, 0);
lean_inc(v_a_2598_);
lean_dec_ref_known(v___x_2597_, 1);
v___y_2585_ = v_ref_2596_;
v_a_2586_ = v_a_2598_;
goto v___jp_2584_;
}
else
{
lean_object* v___x_2599_; 
lean_dec_ref_known(v___x_2597_, 1);
v___x_2599_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1);
v___y_2585_ = v_ref_2596_;
v_a_2586_ = v___x_2599_;
goto v___jp_2584_;
}
}
v___jp_2600_:
{
if (v_clsEnabled_2563_ == 0)
{
if (v___y_2601_ == 0)
{
lean_object* v___x_2602_; lean_object* v_traceState_2603_; lean_object* v_env_2604_; lean_object* v_nextMacroScope_2605_; lean_object* v_ngen_2606_; lean_object* v_auxDeclNGen_2607_; lean_object* v_cache_2608_; lean_object* v_messages_2609_; lean_object* v_infoState_2610_; lean_object* v_snapshotTasks_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2630_; 
lean_dec(v_snd_2581_);
lean_dec(v_fst_2580_);
lean_dec_ref(v_msg_2565_);
lean_dec_ref(v_tag_2561_);
lean_dec(v_cls_2559_);
v___x_2602_ = lean_st_ref_take(v___y_2570_);
v_traceState_2603_ = lean_ctor_get(v___x_2602_, 4);
v_env_2604_ = lean_ctor_get(v___x_2602_, 0);
v_nextMacroScope_2605_ = lean_ctor_get(v___x_2602_, 1);
v_ngen_2606_ = lean_ctor_get(v___x_2602_, 2);
v_auxDeclNGen_2607_ = lean_ctor_get(v___x_2602_, 3);
v_cache_2608_ = lean_ctor_get(v___x_2602_, 5);
v_messages_2609_ = lean_ctor_get(v___x_2602_, 6);
v_infoState_2610_ = lean_ctor_get(v___x_2602_, 7);
v_snapshotTasks_2611_ = lean_ctor_get(v___x_2602_, 8);
v_isSharedCheck_2630_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2613_ = v___x_2602_;
v_isShared_2614_ = v_isSharedCheck_2630_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_snapshotTasks_2611_);
lean_inc(v_infoState_2610_);
lean_inc(v_messages_2609_);
lean_inc(v_cache_2608_);
lean_inc(v_traceState_2603_);
lean_inc(v_auxDeclNGen_2607_);
lean_inc(v_ngen_2606_);
lean_inc(v_nextMacroScope_2605_);
lean_inc(v_env_2604_);
lean_dec(v___x_2602_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2630_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
uint64_t v_tid_2615_; lean_object* v_traces_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2629_; 
v_tid_2615_ = lean_ctor_get_uint64(v_traceState_2603_, sizeof(void*)*1);
v_traces_2616_ = lean_ctor_get(v_traceState_2603_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v_traceState_2603_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2618_ = v_traceState_2603_;
v_isShared_2619_ = v_isSharedCheck_2629_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_traces_2616_);
lean_dec(v_traceState_2603_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2629_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
lean_object* v___x_2620_; lean_object* v___x_2622_; 
v___x_2620_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2564_, v_traces_2616_);
lean_dec_ref(v_traces_2616_);
if (v_isShared_2619_ == 0)
{
lean_ctor_set(v___x_2618_, 0, v___x_2620_);
v___x_2622_ = v___x_2618_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v___x_2620_);
lean_ctor_set_uint64(v_reuseFailAlloc_2628_, sizeof(void*)*1, v_tid_2615_);
v___x_2622_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
lean_object* v___x_2624_; 
if (v_isShared_2614_ == 0)
{
lean_ctor_set(v___x_2613_, 4, v___x_2622_);
v___x_2624_ = v___x_2613_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_env_2604_);
lean_ctor_set(v_reuseFailAlloc_2627_, 1, v_nextMacroScope_2605_);
lean_ctor_set(v_reuseFailAlloc_2627_, 2, v_ngen_2606_);
lean_ctor_set(v_reuseFailAlloc_2627_, 3, v_auxDeclNGen_2607_);
lean_ctor_set(v_reuseFailAlloc_2627_, 4, v___x_2622_);
lean_ctor_set(v_reuseFailAlloc_2627_, 5, v_cache_2608_);
lean_ctor_set(v_reuseFailAlloc_2627_, 6, v_messages_2609_);
lean_ctor_set(v_reuseFailAlloc_2627_, 7, v_infoState_2610_);
lean_ctor_set(v_reuseFailAlloc_2627_, 8, v_snapshotTasks_2611_);
v___x_2624_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
lean_object* v___x_2625_; lean_object* v___x_2626_; 
v___x_2625_ = lean_st_ref_put(v___y_2570_, v___x_2624_);
v___x_2626_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg(v_fst_2572_);
return v___x_2626_;
}
}
}
}
}
else
{
goto v___jp_2595_;
}
}
else
{
goto v___jp_2595_;
}
}
v___jp_2631_:
{
double v___x_2633_; double v___x_2634_; double v___x_2635_; uint8_t v___x_2636_; 
v___x_2633_ = lean_unbox_float(v_snd_2581_);
v___x_2634_ = lean_unbox_float(v_fst_2580_);
v___x_2635_ = lean_float_sub(v___x_2633_, v___x_2634_);
v___x_2636_ = lean_float_decLt(v___y_2632_, v___x_2635_);
v___y_2601_ = v___x_2636_;
goto v___jp_2600_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___boxed(lean_object* v_cls_2647_, lean_object* v_collapsed_2648_, lean_object* v_tag_2649_, lean_object* v_opts_2650_, lean_object* v_clsEnabled_2651_, lean_object* v_oldTraces_2652_, lean_object* v_msg_2653_, lean_object* v_resStartStop_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_){
_start:
{
uint8_t v_collapsed_boxed_2660_; uint8_t v_clsEnabled_boxed_2661_; lean_object* v_res_2662_; 
v_collapsed_boxed_2660_ = lean_unbox(v_collapsed_2648_);
v_clsEnabled_boxed_2661_ = lean_unbox(v_clsEnabled_2651_);
v_res_2662_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_2647_, v_collapsed_boxed_2660_, v_tag_2649_, v_opts_2650_, v_clsEnabled_boxed_2661_, v_oldTraces_2652_, v_msg_2653_, v_resStartStop_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_);
lean_dec(v___y_2658_);
lean_dec_ref(v___y_2657_);
lean_dec(v___y_2656_);
lean_dec_ref(v___y_2655_);
lean_dec_ref(v_opts_2650_);
return v_res_2662_;
}
}
static double _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0(void){
_start:
{
lean_object* v___x_2663_; double v___x_2664_; 
v___x_2663_ = lean_unsigned_to_nat(1000000000u);
v___x_2664_ = lean_float_of_nat(v___x_2663_);
return v___x_2664_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2(void){
_start:
{
lean_object* v___x_2666_; lean_object* v___x_2667_; 
v___x_2666_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1));
v___x_2667_ = l_Lean_stringToMessageData(v___x_2666_);
return v___x_2667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(lean_object* v_ctorVal_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_){
_start:
{
lean_object* v_toConstantVal_2674_; lean_object* v_toCold_2675_; lean_object* v_options_2676_; lean_object* v_name_2677_; lean_object* v_levelParams_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2889_; 
v_toConstantVal_2674_ = lean_ctor_get(v_ctorVal_2668_, 0);
lean_inc_ref(v_toConstantVal_2674_);
v_toCold_2675_ = lean_ctor_get(v_a_2671_, 0);
v_options_2676_ = lean_ctor_get(v_toCold_2675_, 2);
v_name_2677_ = lean_ctor_get(v_toConstantVal_2674_, 0);
v_levelParams_2678_ = lean_ctor_get(v_toConstantVal_2674_, 1);
v_isSharedCheck_2889_ = !lean_is_exclusive(v_toConstantVal_2674_);
if (v_isSharedCheck_2889_ == 0)
{
lean_object* v_unused_2890_; 
v_unused_2890_ = lean_ctor_get(v_toConstantVal_2674_, 2);
lean_dec(v_unused_2890_);
v___x_2680_ = v_toConstantVal_2674_;
v_isShared_2681_ = v_isSharedCheck_2889_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_levelParams_2678_);
lean_inc(v_name_2677_);
lean_dec(v_toConstantVal_2674_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2889_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v_inheritedTraceOptions_2682_; uint8_t v_hasTrace_2683_; lean_object* v_name_2684_; 
v_inheritedTraceOptions_2682_ = lean_ctor_get(v_toCold_2675_, 11);
v_hasTrace_2683_ = lean_ctor_get_uint8(v_options_2676_, sizeof(void*)*1);
lean_inc(v_name_2677_);
v_name_2684_ = l_Lean_Meta_mkInjectiveTheoremNameFor(v_name_2677_);
if (v_hasTrace_2683_ == 0)
{
lean_object* v___x_2685_; 
v___x_2685_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_);
if (lean_obj_tag(v___x_2685_) == 0)
{
lean_object* v_a_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2723_; 
v_a_2686_ = lean_ctor_get(v___x_2685_, 0);
v_isSharedCheck_2723_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2688_ = v___x_2685_;
v_isShared_2689_ = v_isSharedCheck_2723_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_a_2686_);
lean_dec(v___x_2685_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2723_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
if (lean_obj_tag(v_a_2686_) == 1)
{
lean_object* v_val_2690_; lean_object* v___x_2691_; 
lean_del_object(v___x_2688_);
v_val_2690_ = lean_ctor_get(v_a_2686_, 0);
lean_inc_n(v_val_2690_, 2);
lean_dec_ref_known(v_a_2686_, 1);
v___x_2691_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2677_, v_val_2690_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_);
if (lean_obj_tag(v___x_2691_) == 0)
{
lean_object* v_a_2692_; lean_object* v___x_2693_; lean_object* v_a_2694_; lean_object* v___x_2695_; lean_object* v_a_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2710_; 
v_a_2692_ = lean_ctor_get(v___x_2691_, 0);
lean_inc(v_a_2692_);
lean_dec_ref_known(v___x_2691_, 1);
v___x_2693_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2690_, v_a_2670_);
v_a_2694_ = lean_ctor_get(v___x_2693_, 0);
lean_inc(v_a_2694_);
lean_dec_ref(v___x_2693_);
v___x_2695_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2692_, v_a_2670_);
v_a_2696_ = lean_ctor_get(v___x_2695_, 0);
v_isSharedCheck_2710_ = !lean_is_exclusive(v___x_2695_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2698_ = v___x_2695_;
v_isShared_2699_ = v_isSharedCheck_2710_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_a_2696_);
lean_dec(v___x_2695_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2710_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2701_; 
lean_inc(v_name_2684_);
if (v_isShared_2681_ == 0)
{
lean_ctor_set(v___x_2680_, 2, v_a_2694_);
lean_ctor_set(v___x_2680_, 0, v_name_2684_);
v___x_2701_ = v___x_2680_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_name_2684_);
lean_ctor_set(v_reuseFailAlloc_2709_, 1, v_levelParams_2678_);
lean_ctor_set(v_reuseFailAlloc_2709_, 2, v_a_2694_);
v___x_2701_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2706_; 
v___x_2702_ = lean_box(0);
v___x_2703_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2703_, 0, v_name_2684_);
lean_ctor_set(v___x_2703_, 1, v___x_2702_);
v___x_2704_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2701_);
lean_ctor_set(v___x_2704_, 1, v_a_2696_);
lean_ctor_set(v___x_2704_, 2, v___x_2703_);
if (v_isShared_2699_ == 0)
{
lean_ctor_set_tag(v___x_2698_, 2);
lean_ctor_set(v___x_2698_, 0, v___x_2704_);
v___x_2706_ = v___x_2698_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v___x_2704_);
v___x_2706_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
lean_object* v___x_2707_; 
v___x_2707_ = l_Lean_addDecl(v___x_2706_, v_hasTrace_2683_, v_a_2671_, v_a_2672_);
return v___x_2707_;
}
}
}
}
else
{
lean_object* v_a_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2718_; 
lean_dec(v_val_2690_);
lean_dec(v_name_2684_);
lean_del_object(v___x_2680_);
lean_dec(v_levelParams_2678_);
v_a_2711_ = lean_ctor_get(v___x_2691_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___x_2691_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2713_ = v___x_2691_;
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_a_2711_);
lean_dec(v___x_2691_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v___x_2716_; 
if (v_isShared_2714_ == 0)
{
v___x_2716_ = v___x_2713_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_a_2711_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
return v___x_2716_;
}
}
}
}
else
{
lean_object* v___x_2719_; lean_object* v___x_2721_; 
lean_dec(v_a_2686_);
lean_dec(v_name_2684_);
lean_del_object(v___x_2680_);
lean_dec(v_levelParams_2678_);
lean_dec(v_name_2677_);
v___x_2719_ = lean_box(0);
if (v_isShared_2689_ == 0)
{
lean_ctor_set(v___x_2688_, 0, v___x_2719_);
v___x_2721_ = v___x_2688_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v___x_2719_);
v___x_2721_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
return v___x_2721_;
}
}
}
}
else
{
lean_object* v_a_2724_; lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2731_; 
lean_dec(v_name_2684_);
lean_del_object(v___x_2680_);
lean_dec(v_levelParams_2678_);
lean_dec(v_name_2677_);
v_a_2724_ = lean_ctor_get(v___x_2685_, 0);
v_isSharedCheck_2731_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2726_ = v___x_2685_;
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
else
{
lean_inc(v_a_2724_);
lean_dec(v___x_2685_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
lean_object* v___x_2729_; 
if (v_isShared_2727_ == 0)
{
v___x_2729_ = v___x_2726_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_a_2724_);
v___x_2729_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
return v___x_2729_;
}
}
}
}
else
{
lean_object* v___f_2732_; lean_object* v_cls_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; uint8_t v___x_2736_; lean_object* v___y_2738_; lean_object* v___y_2739_; lean_object* v_a_2740_; lean_object* v___y_2750_; lean_object* v___y_2751_; lean_object* v_a_2752_; lean_object* v___y_2755_; lean_object* v___y_2756_; lean_object* v_a_2757_; lean_object* v___y_2760_; lean_object* v___y_2761_; lean_object* v___y_2762_; lean_object* v___y_2766_; lean_object* v___y_2767_; lean_object* v_a_2768_; lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v_a_2783_; lean_object* v___y_2786_; lean_object* v___y_2787_; lean_object* v_a_2788_; lean_object* v___y_2791_; lean_object* v___y_2792_; lean_object* v___y_2793_; 
lean_inc(v_name_2684_);
v___f_2732_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2732_, 0, v_name_2684_);
v_cls_2733_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_2734_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_2735_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_2736_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2682_, v_options_2676_, v___x_2735_);
if (v___x_2736_ == 0)
{
lean_object* v___x_2831_; uint8_t v___x_2832_; 
v___x_2831_ = l_Lean_trace_profiler;
v___x_2832_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_2676_, v___x_2831_);
if (v___x_2832_ == 0)
{
lean_object* v___x_2833_; 
lean_dec_ref(v___f_2732_);
v___x_2833_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_);
if (lean_obj_tag(v___x_2833_) == 0)
{
lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2880_; 
v_a_2834_ = lean_ctor_get(v___x_2833_, 0);
v_isSharedCheck_2880_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2880_ == 0)
{
v___x_2836_ = v___x_2833_;
v_isShared_2837_ = v_isSharedCheck_2880_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v___x_2833_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2880_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
if (lean_obj_tag(v_a_2834_) == 1)
{
lean_object* v_val_2838_; lean_object* v___y_2840_; lean_object* v___y_2841_; lean_object* v___y_2842_; lean_object* v___y_2843_; 
lean_del_object(v___x_2836_);
v_val_2838_ = lean_ctor_get(v_a_2834_, 0);
lean_inc(v_val_2838_);
lean_dec_ref_known(v_a_2834_, 1);
if (v___x_2736_ == 0)
{
v___y_2840_ = v_a_2669_;
v___y_2841_ = v_a_2670_;
v___y_2842_ = v_a_2671_;
v___y_2843_ = v_a_2672_;
goto v___jp_2839_;
}
else
{
lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; 
v___x_2872_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
lean_inc(v_val_2838_);
v___x_2873_ = l_Lean_MessageData_ofExpr(v_val_2838_);
v___x_2874_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2874_, 0, v___x_2872_);
lean_ctor_set(v___x_2874_, 1, v___x_2873_);
v___x_2875_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2733_, v___x_2874_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_);
if (lean_obj_tag(v___x_2875_) == 0)
{
lean_dec_ref_known(v___x_2875_, 1);
v___y_2840_ = v_a_2669_;
v___y_2841_ = v_a_2670_;
v___y_2842_ = v_a_2671_;
v___y_2843_ = v_a_2672_;
goto v___jp_2839_;
}
else
{
lean_dec(v_val_2838_);
lean_dec(v_name_2684_);
lean_del_object(v___x_2680_);
lean_dec(v_levelParams_2678_);
lean_dec(v_name_2677_);
return v___x_2875_;
}
}
v___jp_2839_:
{
lean_object* v___x_2844_; 
lean_inc(v_val_2838_);
v___x_2844_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2677_, v_val_2838_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_);
if (lean_obj_tag(v___x_2844_) == 0)
{
lean_object* v_a_2845_; lean_object* v___x_2846_; lean_object* v_a_2847_; lean_object* v___x_2848_; lean_object* v_a_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2863_; 
v_a_2845_ = lean_ctor_get(v___x_2844_, 0);
lean_inc(v_a_2845_);
lean_dec_ref_known(v___x_2844_, 1);
v___x_2846_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2838_, v___y_2841_);
v_a_2847_ = lean_ctor_get(v___x_2846_, 0);
lean_inc(v_a_2847_);
lean_dec_ref(v___x_2846_);
v___x_2848_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2845_, v___y_2841_);
v_a_2849_ = lean_ctor_get(v___x_2848_, 0);
v_isSharedCheck_2863_ = !lean_is_exclusive(v___x_2848_);
if (v_isSharedCheck_2863_ == 0)
{
v___x_2851_ = v___x_2848_;
v_isShared_2852_ = v_isSharedCheck_2863_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_a_2849_);
lean_dec(v___x_2848_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2863_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2854_; 
lean_inc(v_name_2684_);
if (v_isShared_2681_ == 0)
{
lean_ctor_set(v___x_2680_, 2, v_a_2847_);
lean_ctor_set(v___x_2680_, 0, v_name_2684_);
v___x_2854_ = v___x_2680_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v_name_2684_);
lean_ctor_set(v_reuseFailAlloc_2862_, 1, v_levelParams_2678_);
lean_ctor_set(v_reuseFailAlloc_2862_, 2, v_a_2847_);
v___x_2854_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2859_; 
v___x_2855_ = lean_box(0);
v___x_2856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2856_, 0, v_name_2684_);
lean_ctor_set(v___x_2856_, 1, v___x_2855_);
v___x_2857_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2857_, 0, v___x_2854_);
lean_ctor_set(v___x_2857_, 1, v_a_2849_);
lean_ctor_set(v___x_2857_, 2, v___x_2856_);
if (v_isShared_2852_ == 0)
{
lean_ctor_set_tag(v___x_2851_, 2);
lean_ctor_set(v___x_2851_, 0, v___x_2857_);
v___x_2859_ = v___x_2851_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v___x_2857_);
v___x_2859_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
lean_object* v___x_2860_; 
v___x_2860_ = l_Lean_addDecl(v___x_2859_, v___x_2832_, v___y_2842_, v___y_2843_);
return v___x_2860_;
}
}
}
}
else
{
lean_object* v_a_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2871_; 
lean_dec(v_val_2838_);
lean_dec(v_name_2684_);
lean_del_object(v___x_2680_);
lean_dec(v_levelParams_2678_);
v_a_2864_ = lean_ctor_get(v___x_2844_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2844_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2866_ = v___x_2844_;
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_a_2864_);
lean_dec(v___x_2844_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2869_; 
if (v_isShared_2867_ == 0)
{
v___x_2869_ = v___x_2866_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_a_2864_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
}
}
}
else
{
lean_object* v___x_2876_; lean_object* v___x_2878_; 
lean_dec(v_a_2834_);
lean_dec(v_name_2684_);
lean_del_object(v___x_2680_);
lean_dec(v_levelParams_2678_);
lean_dec(v_name_2677_);
v___x_2876_ = lean_box(0);
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 0, v___x_2876_);
v___x_2878_ = v___x_2836_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v___x_2876_);
v___x_2878_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
return v___x_2878_;
}
}
}
}
else
{
lean_object* v_a_2881_; lean_object* v___x_2883_; uint8_t v_isShared_2884_; uint8_t v_isSharedCheck_2888_; 
lean_dec(v_name_2684_);
lean_del_object(v___x_2680_);
lean_dec(v_levelParams_2678_);
lean_dec(v_name_2677_);
v_a_2881_ = lean_ctor_get(v___x_2833_, 0);
v_isSharedCheck_2888_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2888_ == 0)
{
v___x_2883_ = v___x_2833_;
v_isShared_2884_ = v_isSharedCheck_2888_;
goto v_resetjp_2882_;
}
else
{
lean_inc(v_a_2881_);
lean_dec(v___x_2833_);
v___x_2883_ = lean_box(0);
v_isShared_2884_ = v_isSharedCheck_2888_;
goto v_resetjp_2882_;
}
v_resetjp_2882_:
{
lean_object* v___x_2886_; 
if (v_isShared_2884_ == 0)
{
v___x_2886_ = v___x_2883_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_a_2881_);
v___x_2886_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
return v___x_2886_;
}
}
}
}
else
{
lean_del_object(v___x_2680_);
goto v___jp_2796_;
}
}
else
{
lean_del_object(v___x_2680_);
goto v___jp_2796_;
}
v___jp_2737_:
{
lean_object* v___x_2741_; double v___x_2742_; double v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; 
v___x_2741_ = lean_io_get_num_heartbeats();
v___x_2742_ = lean_float_of_nat(v___y_2738_);
v___x_2743_ = lean_float_of_nat(v___x_2741_);
v___x_2744_ = lean_box_float(v___x_2742_);
v___x_2745_ = lean_box_float(v___x_2743_);
v___x_2746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2746_, 0, v___x_2744_);
lean_ctor_set(v___x_2746_, 1, v___x_2745_);
v___x_2747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2747_, 0, v_a_2740_);
lean_ctor_set(v___x_2747_, 1, v___x_2746_);
v___x_2748_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_2733_, v_hasTrace_2683_, v___x_2734_, v_options_2676_, v___x_2736_, v___y_2739_, v___f_2732_, v___x_2747_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_);
return v___x_2748_;
}
v___jp_2749_:
{
lean_object* v___x_2753_; 
v___x_2753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2753_, 0, v_a_2752_);
v___y_2738_ = v___y_2750_;
v___y_2739_ = v___y_2751_;
v_a_2740_ = v___x_2753_;
goto v___jp_2737_;
}
v___jp_2754_:
{
lean_object* v___x_2758_; 
v___x_2758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2758_, 0, v_a_2757_);
v___y_2738_ = v___y_2755_;
v___y_2739_ = v___y_2756_;
v_a_2740_ = v___x_2758_;
goto v___jp_2737_;
}
v___jp_2759_:
{
if (lean_obj_tag(v___y_2762_) == 0)
{
lean_object* v_a_2763_; 
v_a_2763_ = lean_ctor_get(v___y_2762_, 0);
lean_inc(v_a_2763_);
lean_dec_ref_known(v___y_2762_, 1);
v___y_2755_ = v___y_2760_;
v___y_2756_ = v___y_2761_;
v_a_2757_ = v_a_2763_;
goto v___jp_2754_;
}
else
{
lean_object* v_a_2764_; 
v_a_2764_ = lean_ctor_get(v___y_2762_, 0);
lean_inc(v_a_2764_);
lean_dec_ref_known(v___y_2762_, 1);
v___y_2750_ = v___y_2760_;
v___y_2751_ = v___y_2761_;
v_a_2752_ = v_a_2764_;
goto v___jp_2749_;
}
}
v___jp_2765_:
{
lean_object* v___x_2769_; double v___x_2770_; double v___x_2771_; double v___x_2772_; double v___x_2773_; double v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; 
v___x_2769_ = lean_io_mono_nanos_now();
v___x_2770_ = lean_float_of_nat(v___y_2767_);
v___x_2771_ = lean_float_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0);
v___x_2772_ = lean_float_div(v___x_2770_, v___x_2771_);
v___x_2773_ = lean_float_of_nat(v___x_2769_);
v___x_2774_ = lean_float_div(v___x_2773_, v___x_2771_);
v___x_2775_ = lean_box_float(v___x_2772_);
v___x_2776_ = lean_box_float(v___x_2774_);
v___x_2777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2777_, 0, v___x_2775_);
lean_ctor_set(v___x_2777_, 1, v___x_2776_);
v___x_2778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2778_, 0, v_a_2768_);
lean_ctor_set(v___x_2778_, 1, v___x_2777_);
v___x_2779_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_2733_, v_hasTrace_2683_, v___x_2734_, v_options_2676_, v___x_2736_, v___y_2766_, v___f_2732_, v___x_2778_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_);
return v___x_2779_;
}
v___jp_2780_:
{
lean_object* v___x_2784_; 
v___x_2784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2784_, 0, v_a_2783_);
v___y_2766_ = v___y_2782_;
v___y_2767_ = v___y_2781_;
v_a_2768_ = v___x_2784_;
goto v___jp_2765_;
}
v___jp_2785_:
{
lean_object* v___x_2789_; 
v___x_2789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2789_, 0, v_a_2788_);
v___y_2766_ = v___y_2787_;
v___y_2767_ = v___y_2786_;
v_a_2768_ = v___x_2789_;
goto v___jp_2765_;
}
v___jp_2790_:
{
if (lean_obj_tag(v___y_2793_) == 0)
{
lean_object* v_a_2794_; 
v_a_2794_ = lean_ctor_get(v___y_2793_, 0);
lean_inc(v_a_2794_);
lean_dec_ref_known(v___y_2793_, 1);
v___y_2781_ = v___y_2792_;
v___y_2782_ = v___y_2791_;
v_a_2783_ = v_a_2794_;
goto v___jp_2780_;
}
else
{
lean_object* v_a_2795_; 
v_a_2795_ = lean_ctor_get(v___y_2793_, 0);
lean_inc(v_a_2795_);
lean_dec_ref_known(v___y_2793_, 1);
v___y_2786_ = v___y_2792_;
v___y_2787_ = v___y_2791_;
v_a_2788_ = v_a_2795_;
goto v___jp_2785_;
}
}
v___jp_2796_:
{
lean_object* v___x_2797_; lean_object* v_a_2798_; lean_object* v___x_2799_; uint8_t v___x_2800_; 
v___x_2797_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v_a_2672_);
v_a_2798_ = lean_ctor_get(v___x_2797_, 0);
lean_inc(v_a_2798_);
lean_dec_ref(v___x_2797_);
v___x_2799_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2800_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_2676_, v___x_2799_);
if (v___x_2800_ == 0)
{
lean_object* v___x_2801_; lean_object* v___x_2802_; 
v___x_2801_ = lean_io_mono_nanos_now();
v___x_2802_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_);
if (lean_obj_tag(v___x_2802_) == 0)
{
lean_object* v_a_2803_; 
v_a_2803_ = lean_ctor_get(v___x_2802_, 0);
lean_inc(v_a_2803_);
lean_dec_ref_known(v___x_2802_, 1);
if (lean_obj_tag(v_a_2803_) == 1)
{
if (v___x_2736_ == 0)
{
lean_object* v_val_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; 
v_val_2804_ = lean_ctor_get(v_a_2803_, 0);
lean_inc(v_val_2804_);
lean_dec_ref_known(v_a_2803_, 1);
v___x_2805_ = lean_box(0);
v___x_2806_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(v_name_2677_, v_val_2804_, v_name_2684_, v_levelParams_2678_, v___x_2800_, v___x_2805_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_);
v___y_2791_ = v_a_2798_;
v___y_2792_ = v___x_2801_;
v___y_2793_ = v___x_2806_;
goto v___jp_2790_;
}
else
{
lean_object* v_val_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; 
v_val_2807_ = lean_ctor_get(v_a_2803_, 0);
lean_inc_n(v_val_2807_, 2);
lean_dec_ref_known(v_a_2803_, 1);
v___x_2808_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_2809_ = l_Lean_MessageData_ofExpr(v_val_2807_);
v___x_2810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2810_, 0, v___x_2808_);
lean_ctor_set(v___x_2810_, 1, v___x_2809_);
v___x_2811_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2733_, v___x_2810_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_);
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_object* v_a_2812_; lean_object* v___x_2813_; 
v_a_2812_ = lean_ctor_get(v___x_2811_, 0);
lean_inc(v_a_2812_);
lean_dec_ref_known(v___x_2811_, 1);
v___x_2813_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(v_name_2677_, v_val_2807_, v_name_2684_, v_levelParams_2678_, v___x_2800_, v_a_2812_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_);
v___y_2791_ = v_a_2798_;
v___y_2792_ = v___x_2801_;
v___y_2793_ = v___x_2813_;
goto v___jp_2790_;
}
else
{
lean_dec(v_val_2807_);
lean_dec(v_name_2684_);
lean_dec(v_levelParams_2678_);
lean_dec(v_name_2677_);
v___y_2791_ = v_a_2798_;
v___y_2792_ = v___x_2801_;
v___y_2793_ = v___x_2811_;
goto v___jp_2790_;
}
}
}
else
{
lean_object* v___x_2814_; 
lean_dec(v_a_2803_);
lean_dec(v_name_2684_);
lean_dec(v_levelParams_2678_);
lean_dec(v_name_2677_);
v___x_2814_ = lean_box(0);
v___y_2781_ = v___x_2801_;
v___y_2782_ = v_a_2798_;
v_a_2783_ = v___x_2814_;
goto v___jp_2780_;
}
}
else
{
lean_object* v_a_2815_; 
lean_dec(v_name_2684_);
lean_dec(v_levelParams_2678_);
lean_dec(v_name_2677_);
v_a_2815_ = lean_ctor_get(v___x_2802_, 0);
lean_inc(v_a_2815_);
lean_dec_ref_known(v___x_2802_, 1);
v___y_2786_ = v___x_2801_;
v___y_2787_ = v_a_2798_;
v_a_2788_ = v_a_2815_;
goto v___jp_2785_;
}
}
else
{
lean_object* v___x_2816_; lean_object* v___x_2817_; 
v___x_2816_ = lean_io_get_num_heartbeats();
v___x_2817_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_);
if (lean_obj_tag(v___x_2817_) == 0)
{
lean_object* v_a_2818_; 
v_a_2818_ = lean_ctor_get(v___x_2817_, 0);
lean_inc(v_a_2818_);
lean_dec_ref_known(v___x_2817_, 1);
if (lean_obj_tag(v_a_2818_) == 1)
{
if (v___x_2736_ == 0)
{
lean_object* v_val_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; 
v_val_2819_ = lean_ctor_get(v_a_2818_, 0);
lean_inc(v_val_2819_);
lean_dec_ref_known(v_a_2818_, 1);
v___x_2820_ = lean_box(0);
v___x_2821_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(v_name_2677_, v_val_2819_, v_name_2684_, v_levelParams_2678_, v___x_2820_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_);
v___y_2760_ = v___x_2816_;
v___y_2761_ = v_a_2798_;
v___y_2762_ = v___x_2821_;
goto v___jp_2759_;
}
else
{
lean_object* v_val_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; 
v_val_2822_ = lean_ctor_get(v_a_2818_, 0);
lean_inc_n(v_val_2822_, 2);
lean_dec_ref_known(v_a_2818_, 1);
v___x_2823_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_2824_ = l_Lean_MessageData_ofExpr(v_val_2822_);
v___x_2825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2825_, 0, v___x_2823_);
lean_ctor_set(v___x_2825_, 1, v___x_2824_);
v___x_2826_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2733_, v___x_2825_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_);
if (lean_obj_tag(v___x_2826_) == 0)
{
lean_object* v_a_2827_; lean_object* v___x_2828_; 
v_a_2827_ = lean_ctor_get(v___x_2826_, 0);
lean_inc(v_a_2827_);
lean_dec_ref_known(v___x_2826_, 1);
v___x_2828_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(v_name_2677_, v_val_2822_, v_name_2684_, v_levelParams_2678_, v_a_2827_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_);
v___y_2760_ = v___x_2816_;
v___y_2761_ = v_a_2798_;
v___y_2762_ = v___x_2828_;
goto v___jp_2759_;
}
else
{
lean_dec(v_val_2822_);
lean_dec(v_name_2684_);
lean_dec(v_levelParams_2678_);
lean_dec(v_name_2677_);
v___y_2760_ = v___x_2816_;
v___y_2761_ = v_a_2798_;
v___y_2762_ = v___x_2826_;
goto v___jp_2759_;
}
}
}
else
{
lean_object* v___x_2829_; 
lean_dec(v_a_2818_);
lean_dec(v_name_2684_);
lean_dec(v_levelParams_2678_);
lean_dec(v_name_2677_);
v___x_2829_ = lean_box(0);
v___y_2755_ = v___x_2816_;
v___y_2756_ = v_a_2798_;
v_a_2757_ = v___x_2829_;
goto v___jp_2754_;
}
}
else
{
lean_object* v_a_2830_; 
lean_dec(v_name_2684_);
lean_dec(v_levelParams_2678_);
lean_dec(v_name_2677_);
v_a_2830_ = lean_ctor_get(v___x_2817_, 0);
lean_inc(v_a_2830_);
lean_dec_ref_known(v___x_2817_, 1);
v___y_2750_ = v___x_2816_;
v___y_2751_ = v_a_2798_;
v_a_2752_ = v_a_2830_;
goto v___jp_2749_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___boxed(lean_object* v_ctorVal_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_){
_start:
{
lean_object* v_res_2897_; 
v_res_2897_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(v_ctorVal_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_);
lean_dec(v_a_2895_);
lean_dec_ref(v_a_2894_);
lean_dec(v_a_2893_);
lean_dec_ref(v_a_2892_);
return v_res_2897_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4(lean_object* v_00_u03b1_2898_, lean_object* v_x_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_){
_start:
{
lean_object* v___x_2905_; 
v___x_2905_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___redArg(v_x_2899_);
return v___x_2905_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2906_, lean_object* v_x_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_){
_start:
{
lean_object* v_res_2913_; 
v_res_2913_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4(v_00_u03b1_2906_, v_x_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_);
lean_dec(v___y_2911_);
lean_dec_ref(v___y_2910_);
lean_dec(v___y_2909_);
lean_dec_ref(v___y_2908_);
return v_res_2913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveEqTheoremNameFor(lean_object* v_ctorName_2917_){
_start:
{
lean_object* v___x_2918_; lean_object* v___x_2919_; 
v___x_2918_ = ((lean_object*)(l_Lean_Meta_mkInjectiveEqTheoremNameFor___closed__1));
v___x_2919_ = l_Lean_Name_append(v_ctorName_2917_, v___x_2918_);
return v___x_2919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(lean_object* v_ctorVal_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_){
_start:
{
uint8_t v___x_2926_; lean_object* v___x_2927_; 
v___x_2926_ = 1;
v___x_2927_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(v_ctorVal_2920_, v___x_2926_, v_a_2921_, v_a_2922_, v_a_2923_, v_a_2924_);
return v___x_2927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f___boxed(lean_object* v_ctorVal_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_){
_start:
{
lean_object* v_res_2934_; 
v_res_2934_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_2928_, v_a_2929_, v_a_2930_, v_a_2931_, v_a_2932_);
lean_dec(v_a_2932_);
lean_dec_ref(v_a_2931_);
lean_dec(v_a_2930_);
lean_dec_ref(v_a_2929_);
return v_res_2934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(lean_object* v_e_2935_, lean_object* v_t_2936_, lean_object* v_acc_2937_, lean_object* v_a_2938_){
_start:
{
lean_object* v___x_2940_; 
v___x_2940_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_t_2936_, v_a_2938_);
if (lean_obj_tag(v___x_2940_) == 0)
{
lean_object* v_a_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2964_; 
v_a_2941_ = lean_ctor_get(v___x_2940_, 0);
v_isSharedCheck_2964_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_2964_ == 0)
{
v___x_2943_ = v___x_2940_;
v_isShared_2944_ = v_isSharedCheck_2964_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_a_2941_);
lean_dec(v___x_2940_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2964_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2950_; uint8_t v___x_2951_; 
v___x_2950_ = l_Lean_Expr_cleanupAnnotations(v_a_2941_);
v___x_2951_ = l_Lean_Expr_isApp(v___x_2950_);
if (v___x_2951_ == 0)
{
lean_dec_ref(v___x_2950_);
goto v___jp_2945_;
}
else
{
lean_object* v_arg_2952_; lean_object* v___x_2953_; uint8_t v___x_2954_; 
v_arg_2952_ = lean_ctor_get(v___x_2950_, 1);
lean_inc_ref(v_arg_2952_);
v___x_2953_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2950_);
v___x_2954_ = l_Lean_Expr_isApp(v___x_2953_);
if (v___x_2954_ == 0)
{
lean_dec_ref(v___x_2953_);
lean_dec_ref(v_arg_2952_);
goto v___jp_2945_;
}
else
{
lean_object* v_arg_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; uint8_t v___x_2958_; 
v_arg_2955_ = lean_ctor_get(v___x_2953_, 1);
lean_inc_ref(v_arg_2955_);
v___x_2956_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2953_);
v___x_2957_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__1));
v___x_2958_ = l_Lean_Expr_isConstOf(v___x_2956_, v___x_2957_);
lean_dec_ref(v___x_2956_);
if (v___x_2958_ == 0)
{
lean_dec_ref(v_arg_2955_);
lean_dec_ref(v_arg_2952_);
goto v___jp_2945_;
}
else
{
lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; 
lean_del_object(v___x_2943_);
v___x_2959_ = lean_unsigned_to_nat(0u);
v___x_2960_ = l_Lean_mkProj(v___x_2957_, v___x_2959_, v_e_2935_);
lean_inc_ref(v___x_2960_);
v___x_2961_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v___x_2960_, v_arg_2955_, v_acc_2937_, v_a_2938_);
if (lean_obj_tag(v___x_2961_) == 0)
{
lean_object* v_a_2962_; 
v_a_2962_ = lean_ctor_get(v___x_2961_, 0);
lean_inc(v_a_2962_);
lean_dec_ref_known(v___x_2961_, 1);
v_e_2935_ = v___x_2960_;
v_t_2936_ = v_arg_2952_;
v_acc_2937_ = v_a_2962_;
goto _start;
}
else
{
lean_dec_ref(v___x_2960_);
lean_dec_ref(v_arg_2952_);
return v___x_2961_;
}
}
}
}
v___jp_2945_:
{
lean_object* v___x_2946_; lean_object* v___x_2948_; 
v___x_2946_ = lean_array_push(v_acc_2937_, v_e_2935_);
if (v_isShared_2944_ == 0)
{
lean_ctor_set(v___x_2943_, 0, v___x_2946_);
v___x_2948_ = v___x_2943_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v___x_2946_);
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
lean_object* v_a_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_2972_; 
lean_dec_ref(v_acc_2937_);
lean_dec_ref(v_e_2935_);
v_a_2965_ = lean_ctor_get(v___x_2940_, 0);
v_isSharedCheck_2972_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_2972_ == 0)
{
v___x_2967_ = v___x_2940_;
v_isShared_2968_ = v_isSharedCheck_2972_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_a_2965_);
lean_dec(v___x_2940_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_2972_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___x_2970_; 
if (v_isShared_2968_ == 0)
{
v___x_2970_ = v___x_2967_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v_a_2965_);
v___x_2970_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
return v___x_2970_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg___boxed(lean_object* v_e_2973_, lean_object* v_t_2974_, lean_object* v_acc_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_){
_start:
{
lean_object* v_res_2978_; 
v_res_2978_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v_e_2973_, v_t_2974_, v_acc_2975_, v_a_2976_);
lean_dec(v_a_2976_);
return v_res_2978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go(lean_object* v_e_2979_, lean_object* v_t_2980_, lean_object* v_acc_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_){
_start:
{
lean_object* v___x_2987_; 
v___x_2987_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v_e_2979_, v_t_2980_, v_acc_2981_, v_a_2983_);
return v___x_2987_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___boxed(lean_object* v_e_2988_, lean_object* v_t_2989_, lean_object* v_acc_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_){
_start:
{
lean_object* v_res_2996_; 
v_res_2996_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go(v_e_2988_, v_t_2989_, v_acc_2990_, v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_);
lean_dec(v_a_2994_);
lean_dec_ref(v_a_2993_);
lean_dec(v_a_2992_);
lean_dec_ref(v_a_2991_);
return v_res_2996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections(lean_object* v_e_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_){
_start:
{
lean_object* v___x_3003_; 
lean_inc(v_a_3001_);
lean_inc_ref(v_a_3000_);
lean_inc(v_a_2999_);
lean_inc_ref(v_a_2998_);
lean_inc_ref(v_e_2997_);
v___x_3003_ = lean_infer_type(v_e_2997_, v_a_2998_, v_a_2999_, v_a_3000_, v_a_3001_);
if (lean_obj_tag(v___x_3003_) == 0)
{
lean_object* v_a_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; 
v_a_3004_ = lean_ctor_get(v___x_3003_, 0);
lean_inc(v_a_3004_);
lean_dec_ref_known(v___x_3003_, 1);
v___x_3005_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_3006_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v_e_2997_, v_a_3004_, v___x_3005_, v_a_2999_);
return v___x_3006_;
}
else
{
lean_object* v_a_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3014_; 
lean_dec_ref(v_e_2997_);
v_a_3007_ = lean_ctor_get(v___x_3003_, 0);
v_isSharedCheck_3014_ = !lean_is_exclusive(v___x_3003_);
if (v_isSharedCheck_3014_ == 0)
{
v___x_3009_ = v___x_3003_;
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_a_3007_);
lean_dec(v___x_3003_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v___x_3012_; 
if (v_isShared_3010_ == 0)
{
v___x_3012_ = v___x_3009_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_a_3007_);
v___x_3012_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
return v___x_3012_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections___boxed(lean_object* v_e_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_){
_start:
{
lean_object* v_res_3021_; 
v_res_3021_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections(v_e_3015_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_);
lean_dec(v_a_3019_);
lean_dec_ref(v_a_3018_);
lean_dec(v_a_3017_);
lean_dec_ref(v_a_3016_);
return v_res_3021_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_x_3022_, lean_object* v_x_3023_, lean_object* v_x_3024_, lean_object* v_x_3025_){
_start:
{
lean_object* v_ks_3026_; lean_object* v_vs_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3051_; 
v_ks_3026_ = lean_ctor_get(v_x_3022_, 0);
v_vs_3027_ = lean_ctor_get(v_x_3022_, 1);
v_isSharedCheck_3051_ = !lean_is_exclusive(v_x_3022_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3029_ = v_x_3022_;
v_isShared_3030_ = v_isSharedCheck_3051_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_vs_3027_);
lean_inc(v_ks_3026_);
lean_dec(v_x_3022_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3051_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v___x_3031_; uint8_t v___x_3032_; 
v___x_3031_ = lean_array_get_size(v_ks_3026_);
v___x_3032_ = lean_nat_dec_lt(v_x_3023_, v___x_3031_);
if (v___x_3032_ == 0)
{
lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3036_; 
lean_dec(v_x_3023_);
v___x_3033_ = lean_array_push(v_ks_3026_, v_x_3024_);
v___x_3034_ = lean_array_push(v_vs_3027_, v_x_3025_);
if (v_isShared_3030_ == 0)
{
lean_ctor_set(v___x_3029_, 1, v___x_3034_);
lean_ctor_set(v___x_3029_, 0, v___x_3033_);
v___x_3036_ = v___x_3029_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v___x_3033_);
lean_ctor_set(v_reuseFailAlloc_3037_, 1, v___x_3034_);
v___x_3036_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
return v___x_3036_;
}
}
else
{
lean_object* v_k_x27_3038_; uint8_t v___x_3039_; 
v_k_x27_3038_ = lean_array_fget_borrowed(v_ks_3026_, v_x_3023_);
v___x_3039_ = l_Lean_instBEqMVarId_beq(v_x_3024_, v_k_x27_3038_);
if (v___x_3039_ == 0)
{
lean_object* v___x_3041_; 
if (v_isShared_3030_ == 0)
{
v___x_3041_ = v___x_3029_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v_ks_3026_);
lean_ctor_set(v_reuseFailAlloc_3045_, 1, v_vs_3027_);
v___x_3041_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
lean_object* v___x_3042_; lean_object* v___x_3043_; 
v___x_3042_ = lean_unsigned_to_nat(1u);
v___x_3043_ = lean_nat_add(v_x_3023_, v___x_3042_);
lean_dec(v_x_3023_);
v_x_3022_ = v___x_3041_;
v_x_3023_ = v___x_3043_;
goto _start;
}
}
else
{
lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3049_; 
v___x_3046_ = lean_array_fset(v_ks_3026_, v_x_3023_, v_x_3024_);
v___x_3047_ = lean_array_fset(v_vs_3027_, v_x_3023_, v_x_3025_);
lean_dec(v_x_3023_);
if (v_isShared_3030_ == 0)
{
lean_ctor_set(v___x_3029_, 1, v___x_3047_);
lean_ctor_set(v___x_3029_, 0, v___x_3046_);
v___x_3049_ = v___x_3029_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v___x_3046_);
lean_ctor_set(v_reuseFailAlloc_3050_, 1, v___x_3047_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_n_3052_, lean_object* v_k_3053_, lean_object* v_v_3054_){
_start:
{
lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3055_ = lean_unsigned_to_nat(0u);
v___x_3056_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_n_3052_, v___x_3055_, v_k_3053_, v_v_3054_);
return v___x_3056_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_3057_; 
v___x_3057_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_3057_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(lean_object* v_x_3058_, size_t v_x_3059_, size_t v_x_3060_, lean_object* v_x_3061_, lean_object* v_x_3062_){
_start:
{
if (lean_obj_tag(v_x_3058_) == 0)
{
lean_object* v_es_3063_; size_t v___x_3064_; size_t v___x_3065_; lean_object* v_j_3066_; lean_object* v___x_3067_; uint8_t v___x_3068_; 
v_es_3063_ = lean_ctor_get(v_x_3058_, 0);
v___x_3064_ = ((size_t)31ULL);
v___x_3065_ = lean_usize_land(v_x_3059_, v___x_3064_);
v_j_3066_ = lean_usize_to_nat(v___x_3065_);
v___x_3067_ = lean_array_get_size(v_es_3063_);
v___x_3068_ = lean_nat_dec_lt(v_j_3066_, v___x_3067_);
if (v___x_3068_ == 0)
{
lean_dec(v_j_3066_);
lean_dec(v_x_3062_);
lean_dec(v_x_3061_);
return v_x_3058_;
}
else
{
lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3107_; 
lean_inc_ref(v_es_3063_);
v_isSharedCheck_3107_ = !lean_is_exclusive(v_x_3058_);
if (v_isSharedCheck_3107_ == 0)
{
lean_object* v_unused_3108_; 
v_unused_3108_ = lean_ctor_get(v_x_3058_, 0);
lean_dec(v_unused_3108_);
v___x_3070_ = v_x_3058_;
v_isShared_3071_ = v_isSharedCheck_3107_;
goto v_resetjp_3069_;
}
else
{
lean_dec(v_x_3058_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3107_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
lean_object* v_v_3072_; lean_object* v___x_3073_; lean_object* v_xs_x27_3074_; lean_object* v___y_3076_; 
v_v_3072_ = lean_array_fget(v_es_3063_, v_j_3066_);
v___x_3073_ = lean_box(0);
v_xs_x27_3074_ = lean_array_fset(v_es_3063_, v_j_3066_, v___x_3073_);
switch(lean_obj_tag(v_v_3072_))
{
case 0:
{
lean_object* v_key_3081_; lean_object* v_val_3082_; lean_object* v___x_3084_; uint8_t v_isShared_3085_; uint8_t v_isSharedCheck_3092_; 
v_key_3081_ = lean_ctor_get(v_v_3072_, 0);
v_val_3082_ = lean_ctor_get(v_v_3072_, 1);
v_isSharedCheck_3092_ = !lean_is_exclusive(v_v_3072_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3084_ = v_v_3072_;
v_isShared_3085_ = v_isSharedCheck_3092_;
goto v_resetjp_3083_;
}
else
{
lean_inc(v_val_3082_);
lean_inc(v_key_3081_);
lean_dec(v_v_3072_);
v___x_3084_ = lean_box(0);
v_isShared_3085_ = v_isSharedCheck_3092_;
goto v_resetjp_3083_;
}
v_resetjp_3083_:
{
uint8_t v___x_3086_; 
v___x_3086_ = l_Lean_instBEqMVarId_beq(v_x_3061_, v_key_3081_);
if (v___x_3086_ == 0)
{
lean_object* v___x_3087_; lean_object* v___x_3088_; 
lean_del_object(v___x_3084_);
v___x_3087_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3081_, v_val_3082_, v_x_3061_, v_x_3062_);
v___x_3088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3088_, 0, v___x_3087_);
v___y_3076_ = v___x_3088_;
goto v___jp_3075_;
}
else
{
lean_object* v___x_3090_; 
lean_dec(v_val_3082_);
lean_dec(v_key_3081_);
if (v_isShared_3085_ == 0)
{
lean_ctor_set(v___x_3084_, 1, v_x_3062_);
lean_ctor_set(v___x_3084_, 0, v_x_3061_);
v___x_3090_ = v___x_3084_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v_x_3061_);
lean_ctor_set(v_reuseFailAlloc_3091_, 1, v_x_3062_);
v___x_3090_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
v___y_3076_ = v___x_3090_;
goto v___jp_3075_;
}
}
}
}
case 1:
{
lean_object* v_node_3093_; lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3105_; 
v_node_3093_ = lean_ctor_get(v_v_3072_, 0);
v_isSharedCheck_3105_ = !lean_is_exclusive(v_v_3072_);
if (v_isSharedCheck_3105_ == 0)
{
v___x_3095_ = v_v_3072_;
v_isShared_3096_ = v_isSharedCheck_3105_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_node_3093_);
lean_dec(v_v_3072_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3105_;
goto v_resetjp_3094_;
}
v_resetjp_3094_:
{
size_t v___x_3097_; size_t v___x_3098_; size_t v___x_3099_; size_t v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3103_; 
v___x_3097_ = ((size_t)5ULL);
v___x_3098_ = lean_usize_shift_right(v_x_3059_, v___x_3097_);
v___x_3099_ = ((size_t)1ULL);
v___x_3100_ = lean_usize_add(v_x_3060_, v___x_3099_);
v___x_3101_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_node_3093_, v___x_3098_, v___x_3100_, v_x_3061_, v_x_3062_);
if (v_isShared_3096_ == 0)
{
lean_ctor_set(v___x_3095_, 0, v___x_3101_);
v___x_3103_ = v___x_3095_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v___x_3101_);
v___x_3103_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
v___y_3076_ = v___x_3103_;
goto v___jp_3075_;
}
}
}
default: 
{
lean_object* v___x_3106_; 
v___x_3106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3106_, 0, v_x_3061_);
lean_ctor_set(v___x_3106_, 1, v_x_3062_);
v___y_3076_ = v___x_3106_;
goto v___jp_3075_;
}
}
v___jp_3075_:
{
lean_object* v___x_3077_; lean_object* v___x_3079_; 
v___x_3077_ = lean_array_fset(v_xs_x27_3074_, v_j_3066_, v___y_3076_);
lean_dec(v_j_3066_);
if (v_isShared_3071_ == 0)
{
lean_ctor_set(v___x_3070_, 0, v___x_3077_);
v___x_3079_ = v___x_3070_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v___x_3077_);
v___x_3079_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
return v___x_3079_;
}
}
}
}
}
else
{
lean_object* v_ks_3109_; lean_object* v_vs_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3128_; 
v_ks_3109_ = lean_ctor_get(v_x_3058_, 0);
v_vs_3110_ = lean_ctor_get(v_x_3058_, 1);
v_isSharedCheck_3128_ = !lean_is_exclusive(v_x_3058_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3112_ = v_x_3058_;
v_isShared_3113_ = v_isSharedCheck_3128_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_vs_3110_);
lean_inc(v_ks_3109_);
lean_dec(v_x_3058_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3128_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___x_3115_; 
if (v_isShared_3113_ == 0)
{
v___x_3115_ = v___x_3112_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v_ks_3109_);
lean_ctor_set(v_reuseFailAlloc_3127_, 1, v_vs_3110_);
v___x_3115_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
lean_object* v_newNode_3116_; size_t v___x_3117_; uint8_t v___x_3118_; 
v_newNode_3116_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(v___x_3115_, v_x_3061_, v_x_3062_);
v___x_3117_ = ((size_t)7ULL);
v___x_3118_ = lean_usize_dec_le(v___x_3117_, v_x_3060_);
if (v___x_3118_ == 0)
{
lean_object* v___x_3119_; lean_object* v___x_3120_; uint8_t v___x_3121_; 
v___x_3119_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3116_);
v___x_3120_ = lean_unsigned_to_nat(4u);
v___x_3121_ = lean_nat_dec_lt(v___x_3119_, v___x_3120_);
lean_dec(v___x_3119_);
if (v___x_3121_ == 0)
{
lean_object* v_ks_3122_; lean_object* v_vs_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; 
v_ks_3122_ = lean_ctor_get(v_newNode_3116_, 0);
lean_inc_ref(v_ks_3122_);
v_vs_3123_ = lean_ctor_get(v_newNode_3116_, 1);
lean_inc_ref(v_vs_3123_);
lean_dec_ref(v_newNode_3116_);
v___x_3124_ = lean_unsigned_to_nat(0u);
v___x_3125_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_3126_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(v_x_3060_, v_ks_3122_, v_vs_3123_, v___x_3124_, v___x_3125_);
lean_dec_ref(v_vs_3123_);
lean_dec_ref(v_ks_3122_);
return v___x_3126_;
}
else
{
return v_newNode_3116_;
}
}
else
{
return v_newNode_3116_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(size_t v_depth_3129_, lean_object* v_keys_3130_, lean_object* v_vals_3131_, lean_object* v_i_3132_, lean_object* v_entries_3133_){
_start:
{
lean_object* v___x_3134_; uint8_t v___x_3135_; 
v___x_3134_ = lean_array_get_size(v_keys_3130_);
v___x_3135_ = lean_nat_dec_lt(v_i_3132_, v___x_3134_);
if (v___x_3135_ == 0)
{
lean_dec(v_i_3132_);
return v_entries_3133_;
}
else
{
lean_object* v_k_3136_; lean_object* v_v_3137_; uint64_t v___x_3138_; size_t v_h_3139_; size_t v___x_3140_; lean_object* v___x_3141_; size_t v___x_3142_; size_t v___x_3143_; size_t v___x_3144_; size_t v_h_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; 
v_k_3136_ = lean_array_fget_borrowed(v_keys_3130_, v_i_3132_);
v_v_3137_ = lean_array_fget_borrowed(v_vals_3131_, v_i_3132_);
v___x_3138_ = l_Lean_instHashableMVarId_hash(v_k_3136_);
v_h_3139_ = lean_uint64_to_usize(v___x_3138_);
v___x_3140_ = ((size_t)5ULL);
v___x_3141_ = lean_unsigned_to_nat(1u);
v___x_3142_ = ((size_t)1ULL);
v___x_3143_ = lean_usize_sub(v_depth_3129_, v___x_3142_);
v___x_3144_ = lean_usize_mul(v___x_3140_, v___x_3143_);
v_h_3145_ = lean_usize_shift_right(v_h_3139_, v___x_3144_);
v___x_3146_ = lean_nat_add(v_i_3132_, v___x_3141_);
lean_dec(v_i_3132_);
lean_inc(v_v_3137_);
lean_inc(v_k_3136_);
v___x_3147_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_entries_3133_, v_h_3145_, v_depth_3129_, v_k_3136_, v_v_3137_);
v_i_3132_ = v___x_3146_;
v_entries_3133_ = v___x_3147_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_depth_3149_, lean_object* v_keys_3150_, lean_object* v_vals_3151_, lean_object* v_i_3152_, lean_object* v_entries_3153_){
_start:
{
size_t v_depth_boxed_3154_; lean_object* v_res_3155_; 
v_depth_boxed_3154_ = lean_unbox_usize(v_depth_3149_);
lean_dec(v_depth_3149_);
v_res_3155_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_boxed_3154_, v_keys_3150_, v_vals_3151_, v_i_3152_, v_entries_3153_);
lean_dec_ref(v_vals_3151_);
lean_dec_ref(v_keys_3150_);
return v_res_3155_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_3156_, lean_object* v_x_3157_, lean_object* v_x_3158_, lean_object* v_x_3159_, lean_object* v_x_3160_){
_start:
{
size_t v_x_4985__boxed_3161_; size_t v_x_4986__boxed_3162_; lean_object* v_res_3163_; 
v_x_4985__boxed_3161_ = lean_unbox_usize(v_x_3157_);
lean_dec(v_x_3157_);
v_x_4986__boxed_3162_ = lean_unbox_usize(v_x_3158_);
lean_dec(v_x_3158_);
v_res_3163_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_x_3156_, v_x_4985__boxed_3161_, v_x_4986__boxed_3162_, v_x_3159_, v_x_3160_);
return v_res_3163_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(lean_object* v_x_3164_, lean_object* v_x_3165_, lean_object* v_x_3166_){
_start:
{
uint64_t v___x_3167_; size_t v___x_3168_; size_t v___x_3169_; lean_object* v___x_3170_; 
v___x_3167_ = l_Lean_instHashableMVarId_hash(v_x_3165_);
v___x_3168_ = lean_uint64_to_usize(v___x_3167_);
v___x_3169_ = ((size_t)1ULL);
v___x_3170_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_x_3164_, v___x_3168_, v___x_3169_, v_x_3165_, v_x_3166_);
return v___x_3170_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(lean_object* v_mvarId_3171_, lean_object* v_val_3172_, lean_object* v___y_3173_){
_start:
{
lean_object* v___x_3175_; lean_object* v_mctx_3176_; lean_object* v_cache_3177_; lean_object* v_zetaDeltaFVarIds_3178_; lean_object* v_postponed_3179_; lean_object* v_diag_3180_; lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3209_; 
v___x_3175_ = lean_st_ref_take(v___y_3173_);
v_mctx_3176_ = lean_ctor_get(v___x_3175_, 0);
v_cache_3177_ = lean_ctor_get(v___x_3175_, 1);
v_zetaDeltaFVarIds_3178_ = lean_ctor_get(v___x_3175_, 2);
v_postponed_3179_ = lean_ctor_get(v___x_3175_, 3);
v_diag_3180_ = lean_ctor_get(v___x_3175_, 4);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___x_3175_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3182_ = v___x_3175_;
v_isShared_3183_ = v_isSharedCheck_3209_;
goto v_resetjp_3181_;
}
else
{
lean_inc(v_diag_3180_);
lean_inc(v_postponed_3179_);
lean_inc(v_zetaDeltaFVarIds_3178_);
lean_inc(v_cache_3177_);
lean_inc(v_mctx_3176_);
lean_dec(v___x_3175_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3209_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
lean_object* v_depth_3184_; lean_object* v_levelAssignDepth_3185_; lean_object* v_lmvarCounter_3186_; lean_object* v_mvarCounter_3187_; lean_object* v_lDecls_3188_; lean_object* v_decls_3189_; lean_object* v_userNames_3190_; lean_object* v_lAssignment_3191_; lean_object* v_eAssignment_3192_; lean_object* v_dAssignment_3193_; lean_object* v_instanceTypedMVars_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3208_; 
v_depth_3184_ = lean_ctor_get(v_mctx_3176_, 0);
v_levelAssignDepth_3185_ = lean_ctor_get(v_mctx_3176_, 1);
v_lmvarCounter_3186_ = lean_ctor_get(v_mctx_3176_, 2);
v_mvarCounter_3187_ = lean_ctor_get(v_mctx_3176_, 3);
v_lDecls_3188_ = lean_ctor_get(v_mctx_3176_, 4);
v_decls_3189_ = lean_ctor_get(v_mctx_3176_, 5);
v_userNames_3190_ = lean_ctor_get(v_mctx_3176_, 6);
v_lAssignment_3191_ = lean_ctor_get(v_mctx_3176_, 7);
v_eAssignment_3192_ = lean_ctor_get(v_mctx_3176_, 8);
v_dAssignment_3193_ = lean_ctor_get(v_mctx_3176_, 9);
v_instanceTypedMVars_3194_ = lean_ctor_get(v_mctx_3176_, 10);
v_isSharedCheck_3208_ = !lean_is_exclusive(v_mctx_3176_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_3196_ = v_mctx_3176_;
v_isShared_3197_ = v_isSharedCheck_3208_;
goto v_resetjp_3195_;
}
else
{
lean_inc(v_instanceTypedMVars_3194_);
lean_inc(v_dAssignment_3193_);
lean_inc(v_eAssignment_3192_);
lean_inc(v_lAssignment_3191_);
lean_inc(v_userNames_3190_);
lean_inc(v_decls_3189_);
lean_inc(v_lDecls_3188_);
lean_inc(v_mvarCounter_3187_);
lean_inc(v_lmvarCounter_3186_);
lean_inc(v_levelAssignDepth_3185_);
lean_inc(v_depth_3184_);
lean_dec(v_mctx_3176_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3208_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v___x_3198_; lean_object* v___x_3200_; 
v___x_3198_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(v_eAssignment_3192_, v_mvarId_3171_, v_val_3172_);
if (v_isShared_3197_ == 0)
{
lean_ctor_set(v___x_3196_, 8, v___x_3198_);
v___x_3200_ = v___x_3196_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v_depth_3184_);
lean_ctor_set(v_reuseFailAlloc_3207_, 1, v_levelAssignDepth_3185_);
lean_ctor_set(v_reuseFailAlloc_3207_, 2, v_lmvarCounter_3186_);
lean_ctor_set(v_reuseFailAlloc_3207_, 3, v_mvarCounter_3187_);
lean_ctor_set(v_reuseFailAlloc_3207_, 4, v_lDecls_3188_);
lean_ctor_set(v_reuseFailAlloc_3207_, 5, v_decls_3189_);
lean_ctor_set(v_reuseFailAlloc_3207_, 6, v_userNames_3190_);
lean_ctor_set(v_reuseFailAlloc_3207_, 7, v_lAssignment_3191_);
lean_ctor_set(v_reuseFailAlloc_3207_, 8, v___x_3198_);
lean_ctor_set(v_reuseFailAlloc_3207_, 9, v_dAssignment_3193_);
lean_ctor_set(v_reuseFailAlloc_3207_, 10, v_instanceTypedMVars_3194_);
v___x_3200_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
lean_object* v___x_3202_; 
if (v_isShared_3183_ == 0)
{
lean_ctor_set(v___x_3182_, 0, v___x_3200_);
v___x_3202_ = v___x_3182_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v___x_3200_);
lean_ctor_set(v_reuseFailAlloc_3206_, 1, v_cache_3177_);
lean_ctor_set(v_reuseFailAlloc_3206_, 2, v_zetaDeltaFVarIds_3178_);
lean_ctor_set(v_reuseFailAlloc_3206_, 3, v_postponed_3179_);
lean_ctor_set(v_reuseFailAlloc_3206_, 4, v_diag_3180_);
v___x_3202_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; 
v___x_3203_ = lean_st_ref_put(v___y_3173_, v___x_3202_);
v___x_3204_ = lean_box(0);
v___x_3205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3205_, 0, v___x_3204_);
return v___x_3205_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg___boxed(lean_object* v_mvarId_3210_, lean_object* v_val_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_){
_start:
{
lean_object* v_res_3214_; 
v_res_3214_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(v_mvarId_3210_, v_val_3211_, v___y_3212_);
lean_dec(v___y_3212_);
return v_res_3214_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(lean_object* v___f_3215_, lean_object* v_a_3216_, lean_object* v_x_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_){
_start:
{
lean_object* v___x_3223_; lean_object* v___x_3224_; 
v___x_3223_ = lean_box(0);
lean_inc(v___y_3221_);
lean_inc_ref(v___y_3220_);
lean_inc(v___y_3219_);
lean_inc_ref(v___y_3218_);
v___x_3224_ = lean_apply_7(v___f_3215_, v___x_3223_, v_a_3216_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, lean_box(0));
return v___x_3224_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1___boxed(lean_object* v___f_3225_, lean_object* v_a_3226_, lean_object* v_x_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_){
_start:
{
lean_object* v_res_3233_; 
v_res_3233_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(v___f_3225_, v_a_3226_, v_x_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_);
lean_dec(v___y_3231_);
lean_dec_ref(v___y_3230_);
lean_dec(v___y_3229_);
lean_dec_ref(v___y_3228_);
return v_res_3233_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3235_; lean_object* v___x_3236_; 
v___x_3235_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___closed__0));
v___x_3236_ = l_Lean_stringToMessageData(v___x_3235_);
return v___x_3236_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(lean_object* v___f_3237_, lean_object* v_a_3238_, lean_object* v_x_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_){
_start:
{
lean_object* v___x_3245_; lean_object* v___x_3246_; 
v___x_3245_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___closed__1, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___closed__1);
v___x_3246_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_3245_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_);
if (lean_obj_tag(v___x_3246_) == 0)
{
lean_object* v_a_3247_; lean_object* v___x_3248_; 
v_a_3247_ = lean_ctor_get(v___x_3246_, 0);
lean_inc(v_a_3247_);
lean_dec_ref_known(v___x_3246_, 1);
lean_inc(v___y_3243_);
lean_inc_ref(v___y_3242_);
lean_inc(v___y_3241_);
lean_inc_ref(v___y_3240_);
v___x_3248_ = lean_apply_7(v___f_3237_, v_a_3247_, v_a_3238_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, lean_box(0));
return v___x_3248_;
}
else
{
lean_object* v_a_3249_; lean_object* v___x_3251_; uint8_t v_isShared_3252_; uint8_t v_isSharedCheck_3256_; 
lean_dec(v_a_3238_);
lean_dec_ref(v___f_3237_);
v_a_3249_ = lean_ctor_get(v___x_3246_, 0);
v_isSharedCheck_3256_ = !lean_is_exclusive(v___x_3246_);
if (v_isSharedCheck_3256_ == 0)
{
v___x_3251_ = v___x_3246_;
v_isShared_3252_ = v_isSharedCheck_3256_;
goto v_resetjp_3250_;
}
else
{
lean_inc(v_a_3249_);
lean_dec(v___x_3246_);
v___x_3251_ = lean_box(0);
v_isShared_3252_ = v_isSharedCheck_3256_;
goto v_resetjp_3250_;
}
v_resetjp_3250_:
{
lean_object* v___x_3254_; 
if (v_isShared_3252_ == 0)
{
v___x_3254_ = v___x_3251_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v_a_3249_);
v___x_3254_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
return v___x_3254_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2___boxed(lean_object* v___f_3257_, lean_object* v_a_3258_, lean_object* v_x_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_){
_start:
{
lean_object* v_res_3265_; 
v_res_3265_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(v___f_3257_, v_a_3258_, v_x_3259_, v___y_3260_, v___y_3261_, v___y_3262_, v___y_3263_);
lean_dec(v___y_3263_);
lean_dec_ref(v___y_3262_);
lean_dec(v___y_3261_);
lean_dec_ref(v___y_3260_);
lean_dec(v_x_3259_);
return v_res_3265_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0(uint8_t v___x_3266_, lean_object* v_____r_3267_, lean_object* v_mvarId_u2082_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_){
_start:
{
lean_object* v___x_3274_; 
v___x_3274_ = l_Lean_Meta_introSubstEq(v_mvarId_u2082_3268_, v___x_3266_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_object* v_a_3275_; lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3284_; 
v_a_3275_ = lean_ctor_get(v___x_3274_, 0);
v_isSharedCheck_3284_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3284_ == 0)
{
v___x_3277_ = v___x_3274_;
v_isShared_3278_ = v_isSharedCheck_3284_;
goto v_resetjp_3276_;
}
else
{
lean_inc(v_a_3275_);
lean_dec(v___x_3274_);
v___x_3277_ = lean_box(0);
v_isShared_3278_ = v_isSharedCheck_3284_;
goto v_resetjp_3276_;
}
v_resetjp_3276_:
{
lean_object* v_snd_3279_; lean_object* v___x_3280_; lean_object* v___x_3282_; 
v_snd_3279_ = lean_ctor_get(v_a_3275_, 1);
lean_inc(v_snd_3279_);
lean_dec(v_a_3275_);
v___x_3280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3280_, 0, v_snd_3279_);
if (v_isShared_3278_ == 0)
{
lean_ctor_set(v___x_3277_, 0, v___x_3280_);
v___x_3282_ = v___x_3277_;
goto v_reusejp_3281_;
}
else
{
lean_object* v_reuseFailAlloc_3283_; 
v_reuseFailAlloc_3283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3283_, 0, v___x_3280_);
v___x_3282_ = v_reuseFailAlloc_3283_;
goto v_reusejp_3281_;
}
v_reusejp_3281_:
{
return v___x_3282_;
}
}
}
else
{
lean_object* v_a_3285_; lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3292_; 
v_a_3285_ = lean_ctor_get(v___x_3274_, 0);
v_isSharedCheck_3292_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3292_ == 0)
{
v___x_3287_ = v___x_3274_;
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
else
{
lean_inc(v_a_3285_);
lean_dec(v___x_3274_);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0___boxed(lean_object* v___x_3293_, lean_object* v_____r_3294_, lean_object* v_mvarId_u2082_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_){
_start:
{
uint8_t v___x_5273__boxed_3301_; lean_object* v_res_3302_; 
v___x_5273__boxed_3301_ = lean_unbox(v___x_3293_);
v_res_3302_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0(v___x_5273__boxed_3301_, v_____r_3294_, v_mvarId_u2082_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_);
lean_dec(v___y_3299_);
lean_dec_ref(v___y_3298_);
lean_dec(v___y_3297_);
lean_dec_ref(v___y_3296_);
return v_res_3302_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; 
v___x_3308_ = lean_box(0);
v___x_3309_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__2));
v___x_3310_ = l_Lean_mkConst(v___x_3309_, v___x_3308_);
return v___x_3310_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg(lean_object* v_a_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_){
_start:
{
lean_object* v___y_3318_; lean_object* v___x_3338_; 
lean_inc(v_a_3311_);
v___x_3338_ = l_Lean_MVarId_getType(v_a_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_);
if (lean_obj_tag(v___x_3338_) == 0)
{
lean_object* v_a_3339_; lean_object* v___x_3341_; uint8_t v_isShared_3342_; uint8_t v_isSharedCheck_3398_; 
v_a_3339_ = lean_ctor_get(v___x_3338_, 0);
v_isSharedCheck_3398_ = !lean_is_exclusive(v___x_3338_);
if (v_isSharedCheck_3398_ == 0)
{
v___x_3341_ = v___x_3338_;
v_isShared_3342_ = v_isSharedCheck_3398_;
goto v_resetjp_3340_;
}
else
{
lean_inc(v_a_3339_);
lean_dec(v___x_3338_);
v___x_3341_ = lean_box(0);
v_isShared_3342_ = v_isSharedCheck_3398_;
goto v_resetjp_3340_;
}
v_resetjp_3340_:
{
if (lean_obj_tag(v_a_3339_) == 7)
{
lean_object* v_binderType_3343_; lean_object* v_body_3344_; uint8_t v___x_3345_; 
v_binderType_3343_ = lean_ctor_get(v_a_3339_, 1);
lean_inc_ref(v_binderType_3343_);
v_body_3344_ = lean_ctor_get(v_a_3339_, 2);
lean_inc_ref(v_body_3344_);
lean_dec_ref_known(v_a_3339_, 3);
v___x_3345_ = l_Lean_Expr_hasLooseBVars(v_body_3344_);
if (v___x_3345_ == 0)
{
lean_object* v___x_3346_; 
lean_del_object(v___x_3341_);
v___x_3346_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_3343_, v___y_3313_);
if (lean_obj_tag(v___x_3346_) == 0)
{
lean_object* v_a_3347_; lean_object* v___x_3348_; lean_object* v___f_3349_; lean_object* v___x_3350_; uint8_t v___x_3351_; 
v_a_3347_ = lean_ctor_get(v___x_3346_, 0);
lean_inc(v_a_3347_);
lean_dec_ref_known(v___x_3346_, 1);
v___x_3348_ = lean_box(v___x_3345_);
v___f_3349_ = lean_alloc_closure((void*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3349_, 0, v___x_3348_);
v___x_3350_ = l_Lean_Expr_cleanupAnnotations(v_a_3347_);
v___x_3351_ = l_Lean_Expr_isApp(v___x_3350_);
if (v___x_3351_ == 0)
{
lean_object* v___x_3352_; lean_object* v___x_3353_; 
lean_dec_ref(v___x_3350_);
lean_dec_ref(v_body_3344_);
v___x_3352_ = lean_box(0);
v___x_3353_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(v___f_3349_, v_a_3311_, v___x_3352_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_);
v___y_3318_ = v___x_3353_;
goto v___jp_3317_;
}
else
{
lean_object* v_arg_3354_; lean_object* v___x_3355_; uint8_t v___x_3356_; 
v_arg_3354_ = lean_ctor_get(v___x_3350_, 1);
lean_inc_ref(v_arg_3354_);
v___x_3355_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3350_);
v___x_3356_ = l_Lean_Expr_isApp(v___x_3355_);
if (v___x_3356_ == 0)
{
lean_object* v___x_3357_; lean_object* v___x_3358_; 
lean_dec_ref(v___x_3355_);
lean_dec_ref(v_arg_3354_);
lean_dec_ref(v_body_3344_);
v___x_3357_ = lean_box(0);
v___x_3358_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(v___f_3349_, v_a_3311_, v___x_3357_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_);
v___y_3318_ = v___x_3358_;
goto v___jp_3317_;
}
else
{
lean_object* v_arg_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; uint8_t v___x_3362_; 
v_arg_3359_ = lean_ctor_get(v___x_3355_, 1);
lean_inc_ref(v_arg_3359_);
v___x_3360_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3355_);
v___x_3361_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__1));
v___x_3362_ = l_Lean_Expr_isConstOf(v___x_3360_, v___x_3361_);
lean_dec_ref(v___x_3360_);
if (v___x_3362_ == 0)
{
lean_object* v___x_3363_; lean_object* v___x_3364_; 
lean_dec_ref(v_arg_3359_);
lean_dec_ref(v_arg_3354_);
lean_dec_ref(v_body_3344_);
v___x_3363_ = lean_box(0);
v___x_3364_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__1(v___f_3349_, v_a_3311_, v___x_3363_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_);
v___y_3318_ = v___x_3364_;
goto v___jp_3317_;
}
else
{
lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; 
v___x_3365_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__3, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__3_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___closed__3);
v___x_3366_ = l_Lean_mkApp3(v___x_3365_, v_arg_3359_, v_arg_3354_, v_body_3344_);
v___x_3367_ = lean_unsigned_to_nat(1u);
lean_inc(v_a_3311_);
v___x_3368_ = l_Lean_MVarId_applyN(v_a_3311_, v___x_3366_, v___x_3367_, v___x_3362_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_);
if (lean_obj_tag(v___x_3368_) == 0)
{
lean_object* v_a_3369_; 
v_a_3369_ = lean_ctor_get(v___x_3368_, 0);
lean_inc(v_a_3369_);
lean_dec_ref_known(v___x_3368_, 1);
if (lean_obj_tag(v_a_3369_) == 1)
{
lean_object* v_tail_3370_; 
v_tail_3370_ = lean_ctor_get(v_a_3369_, 1);
if (lean_obj_tag(v_tail_3370_) == 0)
{
lean_object* v_head_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; 
lean_dec_ref(v___f_3349_);
lean_dec(v_a_3311_);
v_head_3371_ = lean_ctor_get(v_a_3369_, 0);
lean_inc(v_head_3371_);
lean_dec_ref_known(v_a_3369_, 2);
v___x_3372_ = lean_box(0);
v___x_3373_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__0(v___x_3345_, v___x_3372_, v_head_3371_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_);
v___y_3318_ = v___x_3373_;
goto v___jp_3317_;
}
else
{
lean_object* v___x_3374_; 
v___x_3374_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(v___f_3349_, v_a_3311_, v_a_3369_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_);
lean_dec_ref_known(v_a_3369_, 2);
v___y_3318_ = v___x_3374_;
goto v___jp_3317_;
}
}
else
{
lean_object* v___x_3375_; 
v___x_3375_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___lam__2(v___f_3349_, v_a_3311_, v_a_3369_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_);
lean_dec(v_a_3369_);
v___y_3318_ = v___x_3375_;
goto v___jp_3317_;
}
}
else
{
lean_object* v_a_3376_; lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3383_; 
lean_dec_ref(v___f_3349_);
lean_dec(v_a_3311_);
v_a_3376_ = lean_ctor_get(v___x_3368_, 0);
v_isSharedCheck_3383_ = !lean_is_exclusive(v___x_3368_);
if (v_isSharedCheck_3383_ == 0)
{
v___x_3378_ = v___x_3368_;
v_isShared_3379_ = v_isSharedCheck_3383_;
goto v_resetjp_3377_;
}
else
{
lean_inc(v_a_3376_);
lean_dec(v___x_3368_);
v___x_3378_ = lean_box(0);
v_isShared_3379_ = v_isSharedCheck_3383_;
goto v_resetjp_3377_;
}
v_resetjp_3377_:
{
lean_object* v___x_3381_; 
if (v_isShared_3379_ == 0)
{
v___x_3381_ = v___x_3378_;
goto v_reusejp_3380_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v_a_3376_);
v___x_3381_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3380_;
}
v_reusejp_3380_:
{
return v___x_3381_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3384_; lean_object* v___x_3386_; uint8_t v_isShared_3387_; uint8_t v_isSharedCheck_3391_; 
lean_dec_ref(v_body_3344_);
lean_dec(v_a_3311_);
v_a_3384_ = lean_ctor_get(v___x_3346_, 0);
v_isSharedCheck_3391_ = !lean_is_exclusive(v___x_3346_);
if (v_isSharedCheck_3391_ == 0)
{
v___x_3386_ = v___x_3346_;
v_isShared_3387_ = v_isSharedCheck_3391_;
goto v_resetjp_3385_;
}
else
{
lean_inc(v_a_3384_);
lean_dec(v___x_3346_);
v___x_3386_ = lean_box(0);
v_isShared_3387_ = v_isSharedCheck_3391_;
goto v_resetjp_3385_;
}
v_resetjp_3385_:
{
lean_object* v___x_3389_; 
if (v_isShared_3387_ == 0)
{
v___x_3389_ = v___x_3386_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3390_; 
v_reuseFailAlloc_3390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3390_, 0, v_a_3384_);
v___x_3389_ = v_reuseFailAlloc_3390_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
return v___x_3389_;
}
}
}
}
else
{
lean_object* v___x_3393_; 
lean_dec_ref(v_body_3344_);
lean_dec_ref(v_binderType_3343_);
if (v_isShared_3342_ == 0)
{
lean_ctor_set(v___x_3341_, 0, v_a_3311_);
v___x_3393_ = v___x_3341_;
goto v_reusejp_3392_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v_a_3311_);
v___x_3393_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3392_;
}
v_reusejp_3392_:
{
return v___x_3393_;
}
}
}
else
{
lean_object* v___x_3396_; 
lean_dec(v_a_3339_);
if (v_isShared_3342_ == 0)
{
lean_ctor_set(v___x_3341_, 0, v_a_3311_);
v___x_3396_ = v___x_3341_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3397_; 
v_reuseFailAlloc_3397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3397_, 0, v_a_3311_);
v___x_3396_ = v_reuseFailAlloc_3397_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
return v___x_3396_;
}
}
}
}
else
{
lean_object* v_a_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3406_; 
lean_dec(v_a_3311_);
v_a_3399_ = lean_ctor_get(v___x_3338_, 0);
v_isSharedCheck_3406_ = !lean_is_exclusive(v___x_3338_);
if (v_isSharedCheck_3406_ == 0)
{
v___x_3401_ = v___x_3338_;
v_isShared_3402_ = v_isSharedCheck_3406_;
goto v_resetjp_3400_;
}
else
{
lean_inc(v_a_3399_);
lean_dec(v___x_3338_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3406_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v___x_3404_; 
if (v_isShared_3402_ == 0)
{
v___x_3404_ = v___x_3401_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v_a_3399_);
v___x_3404_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
return v___x_3404_;
}
}
}
v___jp_3317_:
{
if (lean_obj_tag(v___y_3318_) == 0)
{
lean_object* v_a_3319_; lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3329_; 
v_a_3319_ = lean_ctor_get(v___y_3318_, 0);
v_isSharedCheck_3329_ = !lean_is_exclusive(v___y_3318_);
if (v_isSharedCheck_3329_ == 0)
{
v___x_3321_ = v___y_3318_;
v_isShared_3322_ = v_isSharedCheck_3329_;
goto v_resetjp_3320_;
}
else
{
lean_inc(v_a_3319_);
lean_dec(v___y_3318_);
v___x_3321_ = lean_box(0);
v_isShared_3322_ = v_isSharedCheck_3329_;
goto v_resetjp_3320_;
}
v_resetjp_3320_:
{
if (lean_obj_tag(v_a_3319_) == 0)
{
lean_object* v_a_3323_; lean_object* v___x_3325_; 
v_a_3323_ = lean_ctor_get(v_a_3319_, 0);
lean_inc(v_a_3323_);
lean_dec_ref_known(v_a_3319_, 1);
if (v_isShared_3322_ == 0)
{
lean_ctor_set(v___x_3321_, 0, v_a_3323_);
v___x_3325_ = v___x_3321_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3326_; 
v_reuseFailAlloc_3326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3326_, 0, v_a_3323_);
v___x_3325_ = v_reuseFailAlloc_3326_;
goto v_reusejp_3324_;
}
v_reusejp_3324_:
{
return v___x_3325_;
}
}
else
{
lean_object* v_a_3327_; 
lean_del_object(v___x_3321_);
v_a_3327_ = lean_ctor_get(v_a_3319_, 0);
lean_inc(v_a_3327_);
lean_dec_ref_known(v_a_3319_, 1);
v_a_3311_ = v_a_3327_;
goto _start;
}
}
}
else
{
lean_object* v_a_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3337_; 
v_a_3330_ = lean_ctor_get(v___y_3318_, 0);
v_isSharedCheck_3337_ = !lean_is_exclusive(v___y_3318_);
if (v_isSharedCheck_3337_ == 0)
{
v___x_3332_ = v___y_3318_;
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_a_3330_);
lean_dec(v___y_3318_);
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
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg___boxed(lean_object* v_a_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_){
_start:
{
lean_object* v_res_3413_; 
v_res_3413_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg(v_a_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_);
lean_dec(v___y_3411_);
lean_dec_ref(v___y_3410_);
lean_dec(v___y_3409_);
lean_dec_ref(v___y_3408_);
return v_res_3413_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; 
v___x_3419_ = lean_box(0);
v___x_3420_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__2));
v___x_3421_ = l_Lean_mkConst(v___x_3420_, v___x_3419_);
return v___x_3421_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6(void){
_start:
{
lean_object* v___x_3427_; lean_object* v___x_3428_; 
v___x_3427_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__5));
v___x_3428_ = l_Lean_stringToMessageData(v___x_3427_);
return v___x_3428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0(lean_object* v_ctorVal_3429_, lean_object* v_xs_3430_, lean_object* v_type_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_){
_start:
{
lean_object* v___x_3437_; lean_object* v___x_3438_; 
v___x_3437_ = lean_box(0);
v___x_3438_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_3431_, v___x_3437_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_);
if (lean_obj_tag(v___x_3438_) == 0)
{
lean_object* v_a_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; uint8_t v___x_3443_; uint8_t v___x_3444_; lean_object* v___y_3446_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; 
v_a_3439_ = lean_ctor_get(v___x_3438_, 0);
lean_inc(v_a_3439_);
lean_dec_ref_known(v___x_3438_, 1);
v___x_3440_ = l_Lean_Expr_mvarId_x21(v_a_3439_);
v___x_3441_ = lean_box(0);
v___x_3442_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3);
v___x_3443_ = 1;
v___x_3444_ = 0;
v___x_3457_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__4));
v___x_3458_ = lean_box(0);
v___x_3459_ = l_Lean_MVarId_apply(v___x_3440_, v___x_3442_, v___x_3457_, v___x_3458_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_);
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_object* v_a_3460_; lean_object* v___y_3462_; lean_object* v___y_3463_; lean_object* v___y_3464_; lean_object* v___y_3465_; 
v_a_3460_ = lean_ctor_get(v___x_3459_, 0);
lean_inc(v_a_3460_);
lean_dec_ref_known(v___x_3459_, 1);
if (lean_obj_tag(v_a_3460_) == 1)
{
lean_object* v_tail_3474_; 
v_tail_3474_ = lean_ctor_get(v_a_3460_, 1);
lean_inc(v_tail_3474_);
if (lean_obj_tag(v_tail_3474_) == 1)
{
lean_object* v_tail_3475_; 
v_tail_3475_ = lean_ctor_get(v_tail_3474_, 1);
if (lean_obj_tag(v_tail_3475_) == 0)
{
lean_object* v_toConstantVal_3476_; lean_object* v_head_3477_; lean_object* v_head_3478_; lean_object* v_name_3479_; lean_object* v_levelParams_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; 
v_toConstantVal_3476_ = lean_ctor_get(v_ctorVal_3429_, 0);
lean_inc_ref(v_toConstantVal_3476_);
lean_dec_ref(v_ctorVal_3429_);
v_head_3477_ = lean_ctor_get(v_a_3460_, 0);
lean_inc(v_head_3477_);
lean_dec_ref_known(v_a_3460_, 2);
v_head_3478_ = lean_ctor_get(v_tail_3474_, 0);
lean_inc(v_head_3478_);
lean_dec_ref_known(v_tail_3474_, 2);
v_name_3479_ = lean_ctor_get(v_toConstantVal_3476_, 0);
lean_inc_n(v_name_3479_, 2);
v_levelParams_3480_ = lean_ctor_get(v_toConstantVal_3476_, 1);
lean_inc(v_levelParams_3480_);
lean_dec_ref(v_toConstantVal_3476_);
v___x_3481_ = l_Lean_Meta_mkInjectiveTheoremNameFor(v_name_3479_);
v___x_3482_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(v_levelParams_3480_, v___x_3441_);
v___x_3483_ = l_Lean_mkConst(v___x_3481_, v___x_3482_);
v___x_3484_ = l_Lean_mkAppN(v___x_3483_, v_xs_3430_);
v___x_3485_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(v_head_3477_, v___x_3484_, v___y_3433_);
lean_dec_ref(v___x_3485_);
v___x_3486_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg(v_head_3478_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_);
if (lean_obj_tag(v___x_3486_) == 0)
{
lean_object* v_a_3487_; lean_object* v___x_3488_; 
v_a_3487_ = lean_ctor_get(v___x_3486_, 0);
lean_inc(v_a_3487_);
lean_dec_ref_known(v___x_3486_, 1);
v___x_3488_ = l_Lean_MVarId_refl(v_a_3487_, v___x_3443_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_);
if (lean_obj_tag(v___x_3488_) == 0)
{
lean_dec(v_name_3479_);
v___y_3446_ = v___x_3488_;
goto v___jp_3445_;
}
else
{
lean_object* v_a_3489_; uint8_t v___y_3491_; uint8_t v___x_3494_; 
v_a_3489_ = lean_ctor_get(v___x_3488_, 0);
lean_inc(v_a_3489_);
v___x_3494_ = l_Lean_Exception_isInterrupt(v_a_3489_);
if (v___x_3494_ == 0)
{
uint8_t v___x_3495_; 
v___x_3495_ = l_Lean_Exception_isRuntime(v_a_3489_);
v___y_3491_ = v___x_3495_;
goto v___jp_3490_;
}
else
{
lean_dec(v_a_3489_);
v___y_3491_ = v___x_3494_;
goto v___jp_3490_;
}
v___jp_3490_:
{
if (v___y_3491_ == 0)
{
lean_object* v___x_3492_; lean_object* v___x_3493_; 
lean_dec_ref_known(v___x_3488_, 1);
v___x_3492_ = l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(v_name_3479_);
v___x_3493_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_3492_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_);
v___y_3446_ = v___x_3493_;
goto v___jp_3445_;
}
else
{
lean_dec(v_name_3479_);
v___y_3446_ = v___x_3488_;
goto v___jp_3445_;
}
}
}
}
else
{
lean_object* v_a_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3503_; 
lean_dec(v_name_3479_);
lean_dec(v_a_3439_);
v_a_3496_ = lean_ctor_get(v___x_3486_, 0);
v_isSharedCheck_3503_ = !lean_is_exclusive(v___x_3486_);
if (v_isSharedCheck_3503_ == 0)
{
v___x_3498_ = v___x_3486_;
v_isShared_3499_ = v_isSharedCheck_3503_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_a_3496_);
lean_dec(v___x_3486_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3503_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
lean_object* v___x_3501_; 
if (v_isShared_3499_ == 0)
{
v___x_3501_ = v___x_3498_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v_a_3496_);
v___x_3501_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
return v___x_3501_;
}
}
}
}
else
{
lean_dec_ref_known(v_tail_3474_, 2);
lean_dec_ref_known(v_a_3460_, 2);
lean_dec(v_a_3439_);
v___y_3462_ = v___y_3432_;
v___y_3463_ = v___y_3433_;
v___y_3464_ = v___y_3434_;
v___y_3465_ = v___y_3435_;
goto v___jp_3461_;
}
}
else
{
lean_dec(v_tail_3474_);
lean_dec_ref_known(v_a_3460_, 2);
lean_dec(v_a_3439_);
v___y_3462_ = v___y_3432_;
v___y_3463_ = v___y_3433_;
v___y_3464_ = v___y_3434_;
v___y_3465_ = v___y_3435_;
goto v___jp_3461_;
}
}
else
{
lean_dec(v_a_3460_);
lean_dec(v_a_3439_);
v___y_3462_ = v___y_3432_;
v___y_3463_ = v___y_3433_;
v___y_3464_ = v___y_3434_;
v___y_3465_ = v___y_3435_;
goto v___jp_3461_;
}
v___jp_3461_:
{
lean_object* v_toConstantVal_3466_; lean_object* v_name_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; 
v_toConstantVal_3466_ = lean_ctor_get(v_ctorVal_3429_, 0);
lean_inc_ref(v_toConstantVal_3466_);
lean_dec_ref(v_ctorVal_3429_);
v_name_3467_ = lean_ctor_get(v_toConstantVal_3466_, 0);
lean_inc(v_name_3467_);
lean_dec_ref(v_toConstantVal_3466_);
v___x_3468_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6);
v___x_3469_ = l_Lean_MessageData_ofName(v_name_3467_);
v___x_3470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3470_, 0, v___x_3468_);
lean_ctor_set(v___x_3470_, 1, v___x_3469_);
v___x_3471_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_3472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3472_, 0, v___x_3470_);
lean_ctor_set(v___x_3472_, 1, v___x_3471_);
v___x_3473_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_3472_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_);
return v___x_3473_;
}
}
else
{
lean_object* v_a_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3511_; 
lean_dec(v_a_3439_);
lean_dec_ref(v_ctorVal_3429_);
v_a_3504_ = lean_ctor_get(v___x_3459_, 0);
v_isSharedCheck_3511_ = !lean_is_exclusive(v___x_3459_);
if (v_isSharedCheck_3511_ == 0)
{
v___x_3506_ = v___x_3459_;
v_isShared_3507_ = v_isSharedCheck_3511_;
goto v_resetjp_3505_;
}
else
{
lean_inc(v_a_3504_);
lean_dec(v___x_3459_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3511_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
lean_object* v___x_3509_; 
if (v_isShared_3507_ == 0)
{
v___x_3509_ = v___x_3506_;
goto v_reusejp_3508_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v_a_3504_);
v___x_3509_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3508_;
}
v_reusejp_3508_:
{
return v___x_3509_;
}
}
}
v___jp_3445_:
{
if (lean_obj_tag(v___y_3446_) == 0)
{
uint8_t v___x_3447_; lean_object* v___x_3448_; 
lean_dec_ref_known(v___y_3446_, 1);
v___x_3447_ = 1;
v___x_3448_ = l_Lean_Meta_mkLambdaFVars(v_xs_3430_, v_a_3439_, v___x_3444_, v___x_3443_, v___x_3444_, v___x_3443_, v___x_3447_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_);
return v___x_3448_;
}
else
{
lean_object* v_a_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3456_; 
lean_dec(v_a_3439_);
v_a_3449_ = lean_ctor_get(v___y_3446_, 0);
v_isSharedCheck_3456_ = !lean_is_exclusive(v___y_3446_);
if (v_isSharedCheck_3456_ == 0)
{
v___x_3451_ = v___y_3446_;
v_isShared_3452_ = v_isSharedCheck_3456_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_a_3449_);
lean_dec(v___y_3446_);
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
}
}
else
{
lean_dec_ref(v_ctorVal_3429_);
return v___x_3438_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___boxed(lean_object* v_ctorVal_3512_, lean_object* v_xs_3513_, lean_object* v_type_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_){
_start:
{
lean_object* v_res_3520_; 
v_res_3520_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0(v_ctorVal_3512_, v_xs_3513_, v_type_3514_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_);
lean_dec(v___y_3518_);
lean_dec_ref(v___y_3517_);
lean_dec(v___y_3516_);
lean_dec_ref(v___y_3515_);
lean_dec_ref(v_xs_3513_);
return v_res_3520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(lean_object* v_ctorVal_3521_, lean_object* v_targetType_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_){
_start:
{
lean_object* v___f_3528_; uint8_t v___x_3529_; lean_object* v___x_3530_; 
v___f_3528_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3528_, 0, v_ctorVal_3521_);
v___x_3529_ = 0;
v___x_3530_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_targetType_3522_, v___f_3528_, v___x_3529_, v___x_3529_, v_a_3523_, v_a_3524_, v_a_3525_, v_a_3526_);
return v___x_3530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___boxed(lean_object* v_ctorVal_3531_, lean_object* v_targetType_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_){
_start:
{
lean_object* v_res_3538_; 
v_res_3538_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3531_, v_targetType_3532_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_);
lean_dec(v_a_3536_);
lean_dec_ref(v_a_3535_);
lean_dec(v_a_3534_);
lean_dec_ref(v_a_3533_);
return v_res_3538_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0(lean_object* v_mvarId_3539_, lean_object* v_val_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_){
_start:
{
lean_object* v___x_3546_; 
v___x_3546_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(v_mvarId_3539_, v_val_3540_, v___y_3542_);
return v___x_3546_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___boxed(lean_object* v_mvarId_3547_, lean_object* v_val_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_){
_start:
{
lean_object* v_res_3554_; 
v_res_3554_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0(v_mvarId_3547_, v_val_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_);
lean_dec(v___y_3552_);
lean_dec_ref(v___y_3551_);
lean_dec(v___y_3550_);
lean_dec_ref(v___y_3549_);
return v_res_3554_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1(lean_object* v_inst_3555_, lean_object* v_a_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_){
_start:
{
lean_object* v___x_3562_; 
v___x_3562_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___redArg(v_a_3556_, v___y_3557_, v___y_3558_, v___y_3559_, v___y_3560_);
return v___x_3562_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___boxed(lean_object* v_inst_3563_, lean_object* v_a_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_){
_start:
{
lean_object* v_res_3570_; 
v_res_3570_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1(v_inst_3563_, v_a_3564_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_);
lean_dec(v___y_3568_);
lean_dec_ref(v___y_3567_);
lean_dec(v___y_3566_);
lean_dec_ref(v___y_3565_);
return v_res_3570_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0(lean_object* v_00_u03b2_3571_, lean_object* v_x_3572_, lean_object* v_x_3573_, lean_object* v_x_3574_){
_start:
{
lean_object* v___x_3575_; 
v___x_3575_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(v_x_3572_, v_x_3573_, v_x_3574_);
return v___x_3575_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3576_, lean_object* v_x_3577_, size_t v_x_3578_, size_t v_x_3579_, lean_object* v_x_3580_, lean_object* v_x_3581_){
_start:
{
lean_object* v___x_3582_; 
v___x_3582_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_x_3577_, v_x_3578_, v_x_3579_, v_x_3580_, v_x_3581_);
return v___x_3582_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3583_, lean_object* v_x_3584_, lean_object* v_x_3585_, lean_object* v_x_3586_, lean_object* v_x_3587_, lean_object* v_x_3588_){
_start:
{
size_t v_x_5824__boxed_3589_; size_t v_x_5825__boxed_3590_; lean_object* v_res_3591_; 
v_x_5824__boxed_3589_ = lean_unbox_usize(v_x_3585_);
lean_dec(v_x_3585_);
v_x_5825__boxed_3590_ = lean_unbox_usize(v_x_3586_);
lean_dec(v_x_3586_);
v_res_3591_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1(v_00_u03b2_3583_, v_x_3584_, v_x_5824__boxed_3589_, v_x_5825__boxed_3590_, v_x_3587_, v_x_3588_);
return v_res_3591_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_3592_, lean_object* v_n_3593_, lean_object* v_k_3594_, lean_object* v_v_3595_){
_start:
{
lean_object* v___x_3596_; 
v___x_3596_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(v_n_3593_, v_k_3594_, v_v_3595_);
return v___x_3596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_3597_, size_t v_depth_3598_, lean_object* v_keys_3599_, lean_object* v_vals_3600_, lean_object* v_heq_3601_, lean_object* v_i_3602_, lean_object* v_entries_3603_){
_start:
{
lean_object* v___x_3604_; 
v___x_3604_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_3598_, v_keys_3599_, v_vals_3600_, v_i_3602_, v_entries_3603_);
return v___x_3604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_3605_, lean_object* v_depth_3606_, lean_object* v_keys_3607_, lean_object* v_vals_3608_, lean_object* v_heq_3609_, lean_object* v_i_3610_, lean_object* v_entries_3611_){
_start:
{
size_t v_depth_boxed_3612_; lean_object* v_res_3613_; 
v_depth_boxed_3612_ = lean_unbox_usize(v_depth_3606_);
lean_dec(v_depth_3606_);
v_res_3613_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_3605_, v_depth_boxed_3612_, v_keys_3607_, v_vals_3608_, v_heq_3609_, v_i_3610_, v_entries_3611_);
lean_dec_ref(v_vals_3608_);
lean_dec_ref(v_keys_3607_);
return v_res_3613_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_3614_, lean_object* v_x_3615_, lean_object* v_x_3616_, lean_object* v_x_3617_, lean_object* v_x_3618_){
_start:
{
lean_object* v___x_3619_; 
v___x_3619_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_x_3615_, v_x_3616_, v_x_3617_, v_x_3618_);
return v___x_3619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(lean_object* v_ctorVal_3620_, lean_object* v_val_3621_, lean_object* v_name_3622_, lean_object* v_levelParams_3623_, uint8_t v___x_3624_, uint8_t v_hasTrace_3625_, lean_object* v_____r_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_){
_start:
{
lean_object* v___x_3632_; 
lean_inc_ref(v_val_3621_);
v___x_3632_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3620_, v_val_3621_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_);
if (lean_obj_tag(v___x_3632_) == 0)
{
lean_object* v_a_3633_; lean_object* v___x_3634_; lean_object* v_a_3635_; lean_object* v___x_3636_; lean_object* v_a_3637_; lean_object* v___x_3639_; uint8_t v_isShared_3640_; uint8_t v_isSharedCheck_3653_; 
v_a_3633_ = lean_ctor_get(v___x_3632_, 0);
lean_inc(v_a_3633_);
lean_dec_ref_known(v___x_3632_, 1);
v___x_3634_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3621_, v___y_3628_);
v_a_3635_ = lean_ctor_get(v___x_3634_, 0);
lean_inc(v_a_3635_);
lean_dec_ref(v___x_3634_);
v___x_3636_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3633_, v___y_3628_);
v_a_3637_ = lean_ctor_get(v___x_3636_, 0);
v_isSharedCheck_3653_ = !lean_is_exclusive(v___x_3636_);
if (v_isSharedCheck_3653_ == 0)
{
v___x_3639_ = v___x_3636_;
v_isShared_3640_ = v_isSharedCheck_3653_;
goto v_resetjp_3638_;
}
else
{
lean_inc(v_a_3637_);
lean_dec(v___x_3636_);
v___x_3639_ = lean_box(0);
v_isShared_3640_ = v_isSharedCheck_3653_;
goto v_resetjp_3638_;
}
v_resetjp_3638_:
{
lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3646_; 
lean_inc_n(v_name_3622_, 2);
v___x_3641_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3641_, 0, v_name_3622_);
lean_ctor_set(v___x_3641_, 1, v_levelParams_3623_);
lean_ctor_set(v___x_3641_, 2, v_a_3635_);
v___x_3642_ = lean_box(0);
v___x_3643_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3643_, 0, v_name_3622_);
lean_ctor_set(v___x_3643_, 1, v___x_3642_);
v___x_3644_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3644_, 0, v___x_3641_);
lean_ctor_set(v___x_3644_, 1, v_a_3637_);
lean_ctor_set(v___x_3644_, 2, v___x_3643_);
if (v_isShared_3640_ == 0)
{
lean_ctor_set_tag(v___x_3639_, 2);
lean_ctor_set(v___x_3639_, 0, v___x_3644_);
v___x_3646_ = v___x_3639_;
goto v_reusejp_3645_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v___x_3644_);
v___x_3646_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3645_;
}
v_reusejp_3645_:
{
lean_object* v___x_3647_; 
v___x_3647_ = l_Lean_addDecl(v___x_3646_, v___x_3624_, v___y_3629_, v___y_3630_);
if (lean_obj_tag(v___x_3647_) == 0)
{
lean_object* v___x_3648_; uint8_t v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; 
lean_dec_ref_known(v___x_3647_, 1);
v___x_3648_ = l_Lean_Meta_simpExtension;
v___x_3649_ = 0;
v___x_3650_ = lean_unsigned_to_nat(1000u);
v___x_3651_ = l_Lean_Meta_addSimpTheorem(v___x_3648_, v_name_3622_, v_hasTrace_3625_, v___x_3624_, v___x_3649_, v___x_3650_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_);
return v___x_3651_;
}
else
{
lean_dec(v_name_3622_);
return v___x_3647_;
}
}
}
}
else
{
lean_object* v_a_3654_; lean_object* v___x_3656_; uint8_t v_isShared_3657_; uint8_t v_isSharedCheck_3661_; 
lean_dec(v_levelParams_3623_);
lean_dec(v_name_3622_);
lean_dec_ref(v_val_3621_);
v_a_3654_ = lean_ctor_get(v___x_3632_, 0);
v_isSharedCheck_3661_ = !lean_is_exclusive(v___x_3632_);
if (v_isSharedCheck_3661_ == 0)
{
v___x_3656_ = v___x_3632_;
v_isShared_3657_ = v_isSharedCheck_3661_;
goto v_resetjp_3655_;
}
else
{
lean_inc(v_a_3654_);
lean_dec(v___x_3632_);
v___x_3656_ = lean_box(0);
v_isShared_3657_ = v_isSharedCheck_3661_;
goto v_resetjp_3655_;
}
v_resetjp_3655_:
{
lean_object* v___x_3659_; 
if (v_isShared_3657_ == 0)
{
v___x_3659_ = v___x_3656_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v_a_3654_);
v___x_3659_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3658_;
}
v_reusejp_3658_:
{
return v___x_3659_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1___boxed(lean_object* v_ctorVal_3662_, lean_object* v_val_3663_, lean_object* v_name_3664_, lean_object* v_levelParams_3665_, lean_object* v___x_3666_, lean_object* v_hasTrace_3667_, lean_object* v_____r_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_){
_start:
{
uint8_t v___x_8689__boxed_3674_; uint8_t v_hasTrace_boxed_3675_; lean_object* v_res_3676_; 
v___x_8689__boxed_3674_ = lean_unbox(v___x_3666_);
v_hasTrace_boxed_3675_ = lean_unbox(v_hasTrace_3667_);
v_res_3676_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(v_ctorVal_3662_, v_val_3663_, v_name_3664_, v_levelParams_3665_, v___x_8689__boxed_3674_, v_hasTrace_boxed_3675_, v_____r_3668_, v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_);
lean_dec(v___y_3672_);
lean_dec_ref(v___y_3671_);
lean_dec(v___y_3670_);
lean_dec_ref(v___y_3669_);
return v_res_3676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(lean_object* v_ctorVal_3677_, lean_object* v_val_3678_, lean_object* v_name_3679_, lean_object* v_levelParams_3680_, uint8_t v___x_3681_, lean_object* v_____r_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_){
_start:
{
lean_object* v___x_3688_; 
lean_inc_ref(v_val_3678_);
v___x_3688_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3677_, v_val_3678_, v___y_3683_, v___y_3684_, v___y_3685_, v___y_3686_);
if (lean_obj_tag(v___x_3688_) == 0)
{
lean_object* v_a_3689_; lean_object* v___x_3690_; lean_object* v_a_3691_; lean_object* v___x_3692_; lean_object* v_a_3693_; lean_object* v___x_3695_; uint8_t v_isShared_3696_; uint8_t v_isSharedCheck_3710_; 
v_a_3689_ = lean_ctor_get(v___x_3688_, 0);
lean_inc(v_a_3689_);
lean_dec_ref_known(v___x_3688_, 1);
v___x_3690_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3678_, v___y_3684_);
v_a_3691_ = lean_ctor_get(v___x_3690_, 0);
lean_inc(v_a_3691_);
lean_dec_ref(v___x_3690_);
v___x_3692_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3689_, v___y_3684_);
v_a_3693_ = lean_ctor_get(v___x_3692_, 0);
v_isSharedCheck_3710_ = !lean_is_exclusive(v___x_3692_);
if (v_isSharedCheck_3710_ == 0)
{
v___x_3695_ = v___x_3692_;
v_isShared_3696_ = v_isSharedCheck_3710_;
goto v_resetjp_3694_;
}
else
{
lean_inc(v_a_3693_);
lean_dec(v___x_3692_);
v___x_3695_ = lean_box(0);
v_isShared_3696_ = v_isSharedCheck_3710_;
goto v_resetjp_3694_;
}
v_resetjp_3694_:
{
lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3702_; 
lean_inc_n(v_name_3679_, 2);
v___x_3697_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3697_, 0, v_name_3679_);
lean_ctor_set(v___x_3697_, 1, v_levelParams_3680_);
lean_ctor_set(v___x_3697_, 2, v_a_3691_);
v___x_3698_ = lean_box(0);
v___x_3699_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3699_, 0, v_name_3679_);
lean_ctor_set(v___x_3699_, 1, v___x_3698_);
v___x_3700_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3700_, 0, v___x_3697_);
lean_ctor_set(v___x_3700_, 1, v_a_3693_);
lean_ctor_set(v___x_3700_, 2, v___x_3699_);
if (v_isShared_3696_ == 0)
{
lean_ctor_set_tag(v___x_3695_, 2);
lean_ctor_set(v___x_3695_, 0, v___x_3700_);
v___x_3702_ = v___x_3695_;
goto v_reusejp_3701_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v___x_3700_);
v___x_3702_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3701_;
}
v_reusejp_3701_:
{
uint8_t v___x_3703_; lean_object* v___x_3704_; 
v___x_3703_ = 0;
v___x_3704_ = l_Lean_addDecl(v___x_3702_, v___x_3703_, v___y_3685_, v___y_3686_);
if (lean_obj_tag(v___x_3704_) == 0)
{
lean_object* v___x_3705_; uint8_t v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; 
lean_dec_ref_known(v___x_3704_, 1);
v___x_3705_ = l_Lean_Meta_simpExtension;
v___x_3706_ = 0;
v___x_3707_ = lean_unsigned_to_nat(1000u);
v___x_3708_ = l_Lean_Meta_addSimpTheorem(v___x_3705_, v_name_3679_, v___x_3681_, v___x_3703_, v___x_3706_, v___x_3707_, v___y_3683_, v___y_3684_, v___y_3685_, v___y_3686_);
return v___x_3708_;
}
else
{
lean_dec(v_name_3679_);
return v___x_3704_;
}
}
}
}
else
{
lean_object* v_a_3711_; lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3718_; 
lean_dec(v_levelParams_3680_);
lean_dec(v_name_3679_);
lean_dec_ref(v_val_3678_);
v_a_3711_ = lean_ctor_get(v___x_3688_, 0);
v_isSharedCheck_3718_ = !lean_is_exclusive(v___x_3688_);
if (v_isSharedCheck_3718_ == 0)
{
v___x_3713_ = v___x_3688_;
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
else
{
lean_inc(v_a_3711_);
lean_dec(v___x_3688_);
v___x_3713_ = lean_box(0);
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
v_resetjp_3712_:
{
lean_object* v___x_3716_; 
if (v_isShared_3714_ == 0)
{
v___x_3716_ = v___x_3713_;
goto v_reusejp_3715_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v_a_3711_);
v___x_3716_ = v_reuseFailAlloc_3717_;
goto v_reusejp_3715_;
}
v_reusejp_3715_:
{
return v___x_3716_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0___boxed(lean_object* v_ctorVal_3719_, lean_object* v_val_3720_, lean_object* v_name_3721_, lean_object* v_levelParams_3722_, lean_object* v___x_3723_, lean_object* v_____r_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_){
_start:
{
uint8_t v___x_8777__boxed_3730_; lean_object* v_res_3731_; 
v___x_8777__boxed_3730_ = lean_unbox(v___x_3723_);
v_res_3731_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(v_ctorVal_3719_, v_val_3720_, v_name_3721_, v_levelParams_3722_, v___x_8777__boxed_3730_, v_____r_3724_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_);
lean_dec(v___y_3728_);
lean_dec_ref(v___y_3727_);
lean_dec(v___y_3726_);
lean_dec_ref(v___y_3725_);
return v_res_3731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(lean_object* v_ctorVal_3732_, lean_object* v_a_3733_, lean_object* v_a_3734_, lean_object* v_a_3735_, lean_object* v_a_3736_){
_start:
{
lean_object* v_toConstantVal_3738_; lean_object* v_toCold_3739_; lean_object* v_options_3740_; lean_object* v_name_3741_; lean_object* v_levelParams_3742_; lean_object* v___x_3744_; uint8_t v_isShared_3745_; uint8_t v_isSharedCheck_3962_; 
v_toConstantVal_3738_ = lean_ctor_get(v_ctorVal_3732_, 0);
lean_inc_ref(v_toConstantVal_3738_);
v_toCold_3739_ = lean_ctor_get(v_a_3735_, 0);
v_options_3740_ = lean_ctor_get(v_toCold_3739_, 2);
v_name_3741_ = lean_ctor_get(v_toConstantVal_3738_, 0);
v_levelParams_3742_ = lean_ctor_get(v_toConstantVal_3738_, 1);
v_isSharedCheck_3962_ = !lean_is_exclusive(v_toConstantVal_3738_);
if (v_isSharedCheck_3962_ == 0)
{
lean_object* v_unused_3963_; 
v_unused_3963_ = lean_ctor_get(v_toConstantVal_3738_, 2);
lean_dec(v_unused_3963_);
v___x_3744_ = v_toConstantVal_3738_;
v_isShared_3745_ = v_isSharedCheck_3962_;
goto v_resetjp_3743_;
}
else
{
lean_inc(v_levelParams_3742_);
lean_inc(v_name_3741_);
lean_dec(v_toConstantVal_3738_);
v___x_3744_ = lean_box(0);
v_isShared_3745_ = v_isSharedCheck_3962_;
goto v_resetjp_3743_;
}
v_resetjp_3743_:
{
lean_object* v_inheritedTraceOptions_3746_; uint8_t v_hasTrace_3747_; lean_object* v_name_3748_; 
v_inheritedTraceOptions_3746_ = lean_ctor_get(v_toCold_3739_, 11);
v_hasTrace_3747_ = lean_ctor_get_uint8(v_options_3740_, sizeof(void*)*1);
v_name_3748_ = l_Lean_Meta_mkInjectiveEqTheoremNameFor(v_name_3741_);
if (v_hasTrace_3747_ == 0)
{
lean_object* v___x_3749_; 
lean_inc_ref(v_ctorVal_3732_);
v___x_3749_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3732_, v_a_3733_, v_a_3734_, v_a_3735_, v_a_3736_);
if (lean_obj_tag(v___x_3749_) == 0)
{
lean_object* v_a_3750_; lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3792_; 
v_a_3750_ = lean_ctor_get(v___x_3749_, 0);
v_isSharedCheck_3792_ = !lean_is_exclusive(v___x_3749_);
if (v_isSharedCheck_3792_ == 0)
{
v___x_3752_ = v___x_3749_;
v_isShared_3753_ = v_isSharedCheck_3792_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_a_3750_);
lean_dec(v___x_3749_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3792_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
if (lean_obj_tag(v_a_3750_) == 1)
{
lean_object* v_val_3754_; lean_object* v___x_3755_; 
lean_del_object(v___x_3752_);
v_val_3754_ = lean_ctor_get(v_a_3750_, 0);
lean_inc_n(v_val_3754_, 2);
lean_dec_ref_known(v_a_3750_, 1);
v___x_3755_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3732_, v_val_3754_, v_a_3733_, v_a_3734_, v_a_3735_, v_a_3736_);
if (lean_obj_tag(v___x_3755_) == 0)
{
lean_object* v_a_3756_; lean_object* v___x_3757_; lean_object* v_a_3758_; lean_object* v___x_3759_; lean_object* v_a_3760_; lean_object* v___x_3762_; uint8_t v_isShared_3763_; uint8_t v_isSharedCheck_3779_; 
v_a_3756_ = lean_ctor_get(v___x_3755_, 0);
lean_inc(v_a_3756_);
lean_dec_ref_known(v___x_3755_, 1);
v___x_3757_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3754_, v_a_3734_);
v_a_3758_ = lean_ctor_get(v___x_3757_, 0);
lean_inc(v_a_3758_);
lean_dec_ref(v___x_3757_);
v___x_3759_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3756_, v_a_3734_);
v_a_3760_ = lean_ctor_get(v___x_3759_, 0);
v_isSharedCheck_3779_ = !lean_is_exclusive(v___x_3759_);
if (v_isSharedCheck_3779_ == 0)
{
v___x_3762_ = v___x_3759_;
v_isShared_3763_ = v_isSharedCheck_3779_;
goto v_resetjp_3761_;
}
else
{
lean_inc(v_a_3760_);
lean_dec(v___x_3759_);
v___x_3762_ = lean_box(0);
v_isShared_3763_ = v_isSharedCheck_3779_;
goto v_resetjp_3761_;
}
v_resetjp_3761_:
{
lean_object* v___x_3765_; 
lean_inc(v_name_3748_);
if (v_isShared_3745_ == 0)
{
lean_ctor_set(v___x_3744_, 2, v_a_3758_);
lean_ctor_set(v___x_3744_, 0, v_name_3748_);
v___x_3765_ = v___x_3744_;
goto v_reusejp_3764_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v_name_3748_);
lean_ctor_set(v_reuseFailAlloc_3778_, 1, v_levelParams_3742_);
lean_ctor_set(v_reuseFailAlloc_3778_, 2, v_a_3758_);
v___x_3765_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3764_;
}
v_reusejp_3764_:
{
lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3770_; 
v___x_3766_ = lean_box(0);
lean_inc(v_name_3748_);
v___x_3767_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3767_, 0, v_name_3748_);
lean_ctor_set(v___x_3767_, 1, v___x_3766_);
v___x_3768_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3768_, 0, v___x_3765_);
lean_ctor_set(v___x_3768_, 1, v_a_3760_);
lean_ctor_set(v___x_3768_, 2, v___x_3767_);
if (v_isShared_3763_ == 0)
{
lean_ctor_set_tag(v___x_3762_, 2);
lean_ctor_set(v___x_3762_, 0, v___x_3768_);
v___x_3770_ = v___x_3762_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3777_; 
v_reuseFailAlloc_3777_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3777_, 0, v___x_3768_);
v___x_3770_ = v_reuseFailAlloc_3777_;
goto v_reusejp_3769_;
}
v_reusejp_3769_:
{
lean_object* v___x_3771_; 
v___x_3771_ = l_Lean_addDecl(v___x_3770_, v_hasTrace_3747_, v_a_3735_, v_a_3736_);
if (lean_obj_tag(v___x_3771_) == 0)
{
lean_object* v___x_3772_; uint8_t v___x_3773_; uint8_t v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; 
lean_dec_ref_known(v___x_3771_, 1);
v___x_3772_ = l_Lean_Meta_simpExtension;
v___x_3773_ = 1;
v___x_3774_ = 0;
v___x_3775_ = lean_unsigned_to_nat(1000u);
v___x_3776_ = l_Lean_Meta_addSimpTheorem(v___x_3772_, v_name_3748_, v___x_3773_, v_hasTrace_3747_, v___x_3774_, v___x_3775_, v_a_3733_, v_a_3734_, v_a_3735_, v_a_3736_);
return v___x_3776_;
}
else
{
lean_dec(v_name_3748_);
return v___x_3771_;
}
}
}
}
}
else
{
lean_object* v_a_3780_; lean_object* v___x_3782_; uint8_t v_isShared_3783_; uint8_t v_isSharedCheck_3787_; 
lean_dec(v_val_3754_);
lean_dec(v_name_3748_);
lean_del_object(v___x_3744_);
lean_dec(v_levelParams_3742_);
v_a_3780_ = lean_ctor_get(v___x_3755_, 0);
v_isSharedCheck_3787_ = !lean_is_exclusive(v___x_3755_);
if (v_isSharedCheck_3787_ == 0)
{
v___x_3782_ = v___x_3755_;
v_isShared_3783_ = v_isSharedCheck_3787_;
goto v_resetjp_3781_;
}
else
{
lean_inc(v_a_3780_);
lean_dec(v___x_3755_);
v___x_3782_ = lean_box(0);
v_isShared_3783_ = v_isSharedCheck_3787_;
goto v_resetjp_3781_;
}
v_resetjp_3781_:
{
lean_object* v___x_3785_; 
if (v_isShared_3783_ == 0)
{
v___x_3785_ = v___x_3782_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v_a_3780_);
v___x_3785_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3784_;
}
v_reusejp_3784_:
{
return v___x_3785_;
}
}
}
}
else
{
lean_object* v___x_3788_; lean_object* v___x_3790_; 
lean_dec(v_a_3750_);
lean_dec(v_name_3748_);
lean_del_object(v___x_3744_);
lean_dec(v_levelParams_3742_);
lean_dec_ref(v_ctorVal_3732_);
v___x_3788_ = lean_box(0);
if (v_isShared_3753_ == 0)
{
lean_ctor_set(v___x_3752_, 0, v___x_3788_);
v___x_3790_ = v___x_3752_;
goto v_reusejp_3789_;
}
else
{
lean_object* v_reuseFailAlloc_3791_; 
v_reuseFailAlloc_3791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3791_, 0, v___x_3788_);
v___x_3790_ = v_reuseFailAlloc_3791_;
goto v_reusejp_3789_;
}
v_reusejp_3789_:
{
return v___x_3790_;
}
}
}
}
else
{
lean_object* v_a_3793_; lean_object* v___x_3795_; uint8_t v_isShared_3796_; uint8_t v_isSharedCheck_3800_; 
lean_dec(v_name_3748_);
lean_del_object(v___x_3744_);
lean_dec(v_levelParams_3742_);
lean_dec_ref(v_ctorVal_3732_);
v_a_3793_ = lean_ctor_get(v___x_3749_, 0);
v_isSharedCheck_3800_ = !lean_is_exclusive(v___x_3749_);
if (v_isSharedCheck_3800_ == 0)
{
v___x_3795_ = v___x_3749_;
v_isShared_3796_ = v_isSharedCheck_3800_;
goto v_resetjp_3794_;
}
else
{
lean_inc(v_a_3793_);
lean_dec(v___x_3749_);
v___x_3795_ = lean_box(0);
v_isShared_3796_ = v_isSharedCheck_3800_;
goto v_resetjp_3794_;
}
v_resetjp_3794_:
{
lean_object* v___x_3798_; 
if (v_isShared_3796_ == 0)
{
v___x_3798_ = v___x_3795_;
goto v_reusejp_3797_;
}
else
{
lean_object* v_reuseFailAlloc_3799_; 
v_reuseFailAlloc_3799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3799_, 0, v_a_3793_);
v___x_3798_ = v_reuseFailAlloc_3799_;
goto v_reusejp_3797_;
}
v_reusejp_3797_:
{
return v___x_3798_;
}
}
}
}
else
{
lean_object* v___f_3801_; lean_object* v_cls_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; uint8_t v___x_3805_; lean_object* v___y_3807_; lean_object* v___y_3808_; lean_object* v_a_3809_; lean_object* v___y_3819_; lean_object* v___y_3820_; lean_object* v_a_3821_; lean_object* v___y_3824_; lean_object* v___y_3825_; lean_object* v_a_3826_; lean_object* v___y_3829_; lean_object* v___y_3830_; lean_object* v___y_3831_; lean_object* v___y_3835_; lean_object* v___y_3836_; lean_object* v_a_3837_; lean_object* v___y_3850_; lean_object* v___y_3851_; lean_object* v_a_3852_; lean_object* v___y_3855_; lean_object* v___y_3856_; lean_object* v_a_3857_; lean_object* v___y_3860_; lean_object* v___y_3861_; lean_object* v___y_3862_; 
lean_inc(v_name_3748_);
v___f_3801_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3801_, 0, v_name_3748_);
v_cls_3802_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_3803_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_3804_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_3805_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3746_, v_options_3740_, v___x_3804_);
if (v___x_3805_ == 0)
{
lean_object* v___x_3900_; uint8_t v___x_3901_; 
v___x_3900_ = l_Lean_trace_profiler;
v___x_3901_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_3740_, v___x_3900_);
if (v___x_3901_ == 0)
{
lean_object* v___x_3902_; 
lean_dec_ref(v___f_3801_);
lean_inc_ref(v_ctorVal_3732_);
v___x_3902_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3732_, v_a_3733_, v_a_3734_, v_a_3735_, v_a_3736_);
if (lean_obj_tag(v___x_3902_) == 0)
{
lean_object* v_a_3903_; lean_object* v___x_3905_; uint8_t v_isShared_3906_; uint8_t v_isSharedCheck_3953_; 
v_a_3903_ = lean_ctor_get(v___x_3902_, 0);
v_isSharedCheck_3953_ = !lean_is_exclusive(v___x_3902_);
if (v_isSharedCheck_3953_ == 0)
{
v___x_3905_ = v___x_3902_;
v_isShared_3906_ = v_isSharedCheck_3953_;
goto v_resetjp_3904_;
}
else
{
lean_inc(v_a_3903_);
lean_dec(v___x_3902_);
v___x_3905_ = lean_box(0);
v_isShared_3906_ = v_isSharedCheck_3953_;
goto v_resetjp_3904_;
}
v_resetjp_3904_:
{
if (lean_obj_tag(v_a_3903_) == 1)
{
lean_object* v_val_3907_; lean_object* v___y_3909_; lean_object* v___y_3910_; lean_object* v___y_3911_; lean_object* v___y_3912_; 
lean_del_object(v___x_3905_);
v_val_3907_ = lean_ctor_get(v_a_3903_, 0);
lean_inc(v_val_3907_);
lean_dec_ref_known(v_a_3903_, 1);
if (v___x_3805_ == 0)
{
v___y_3909_ = v_a_3733_;
v___y_3910_ = v_a_3734_;
v___y_3911_ = v_a_3735_;
v___y_3912_ = v_a_3736_;
goto v___jp_3908_;
}
else
{
lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; 
v___x_3945_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
lean_inc(v_val_3907_);
v___x_3946_ = l_Lean_MessageData_ofExpr(v_val_3907_);
v___x_3947_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3947_, 0, v___x_3945_);
lean_ctor_set(v___x_3947_, 1, v___x_3946_);
v___x_3948_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_3802_, v___x_3947_, v_a_3733_, v_a_3734_, v_a_3735_, v_a_3736_);
if (lean_obj_tag(v___x_3948_) == 0)
{
lean_dec_ref_known(v___x_3948_, 1);
v___y_3909_ = v_a_3733_;
v___y_3910_ = v_a_3734_;
v___y_3911_ = v_a_3735_;
v___y_3912_ = v_a_3736_;
goto v___jp_3908_;
}
else
{
lean_dec(v_val_3907_);
lean_dec(v_name_3748_);
lean_del_object(v___x_3744_);
lean_dec(v_levelParams_3742_);
lean_dec_ref(v_ctorVal_3732_);
return v___x_3948_;
}
}
v___jp_3908_:
{
lean_object* v___x_3913_; 
lean_inc(v_val_3907_);
v___x_3913_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3732_, v_val_3907_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_);
if (lean_obj_tag(v___x_3913_) == 0)
{
lean_object* v_a_3914_; lean_object* v___x_3915_; lean_object* v_a_3916_; lean_object* v___x_3917_; lean_object* v_a_3918_; lean_object* v___x_3920_; uint8_t v_isShared_3921_; uint8_t v_isSharedCheck_3936_; 
v_a_3914_ = lean_ctor_get(v___x_3913_, 0);
lean_inc(v_a_3914_);
lean_dec_ref_known(v___x_3913_, 1);
v___x_3915_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3907_, v___y_3910_);
v_a_3916_ = lean_ctor_get(v___x_3915_, 0);
lean_inc(v_a_3916_);
lean_dec_ref(v___x_3915_);
v___x_3917_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3914_, v___y_3910_);
v_a_3918_ = lean_ctor_get(v___x_3917_, 0);
v_isSharedCheck_3936_ = !lean_is_exclusive(v___x_3917_);
if (v_isSharedCheck_3936_ == 0)
{
v___x_3920_ = v___x_3917_;
v_isShared_3921_ = v_isSharedCheck_3936_;
goto v_resetjp_3919_;
}
else
{
lean_inc(v_a_3918_);
lean_dec(v___x_3917_);
v___x_3920_ = lean_box(0);
v_isShared_3921_ = v_isSharedCheck_3936_;
goto v_resetjp_3919_;
}
v_resetjp_3919_:
{
lean_object* v___x_3923_; 
lean_inc(v_name_3748_);
if (v_isShared_3745_ == 0)
{
lean_ctor_set(v___x_3744_, 2, v_a_3916_);
lean_ctor_set(v___x_3744_, 0, v_name_3748_);
v___x_3923_ = v___x_3744_;
goto v_reusejp_3922_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v_name_3748_);
lean_ctor_set(v_reuseFailAlloc_3935_, 1, v_levelParams_3742_);
lean_ctor_set(v_reuseFailAlloc_3935_, 2, v_a_3916_);
v___x_3923_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3922_;
}
v_reusejp_3922_:
{
lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3928_; 
v___x_3924_ = lean_box(0);
lean_inc(v_name_3748_);
v___x_3925_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3925_, 0, v_name_3748_);
lean_ctor_set(v___x_3925_, 1, v___x_3924_);
v___x_3926_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3926_, 0, v___x_3923_);
lean_ctor_set(v___x_3926_, 1, v_a_3918_);
lean_ctor_set(v___x_3926_, 2, v___x_3925_);
if (v_isShared_3921_ == 0)
{
lean_ctor_set_tag(v___x_3920_, 2);
lean_ctor_set(v___x_3920_, 0, v___x_3926_);
v___x_3928_ = v___x_3920_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v___x_3926_);
v___x_3928_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
lean_object* v___x_3929_; 
v___x_3929_ = l_Lean_addDecl(v___x_3928_, v___x_3901_, v___y_3911_, v___y_3912_);
if (lean_obj_tag(v___x_3929_) == 0)
{
lean_object* v___x_3930_; uint8_t v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; 
lean_dec_ref_known(v___x_3929_, 1);
v___x_3930_ = l_Lean_Meta_simpExtension;
v___x_3931_ = 0;
v___x_3932_ = lean_unsigned_to_nat(1000u);
v___x_3933_ = l_Lean_Meta_addSimpTheorem(v___x_3930_, v_name_3748_, v_hasTrace_3747_, v___x_3901_, v___x_3931_, v___x_3932_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_);
return v___x_3933_;
}
else
{
lean_dec(v_name_3748_);
return v___x_3929_;
}
}
}
}
}
else
{
lean_object* v_a_3937_; lean_object* v___x_3939_; uint8_t v_isShared_3940_; uint8_t v_isSharedCheck_3944_; 
lean_dec(v_val_3907_);
lean_dec(v_name_3748_);
lean_del_object(v___x_3744_);
lean_dec(v_levelParams_3742_);
v_a_3937_ = lean_ctor_get(v___x_3913_, 0);
v_isSharedCheck_3944_ = !lean_is_exclusive(v___x_3913_);
if (v_isSharedCheck_3944_ == 0)
{
v___x_3939_ = v___x_3913_;
v_isShared_3940_ = v_isSharedCheck_3944_;
goto v_resetjp_3938_;
}
else
{
lean_inc(v_a_3937_);
lean_dec(v___x_3913_);
v___x_3939_ = lean_box(0);
v_isShared_3940_ = v_isSharedCheck_3944_;
goto v_resetjp_3938_;
}
v_resetjp_3938_:
{
lean_object* v___x_3942_; 
if (v_isShared_3940_ == 0)
{
v___x_3942_ = v___x_3939_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v_a_3937_);
v___x_3942_ = v_reuseFailAlloc_3943_;
goto v_reusejp_3941_;
}
v_reusejp_3941_:
{
return v___x_3942_;
}
}
}
}
}
else
{
lean_object* v___x_3949_; lean_object* v___x_3951_; 
lean_dec(v_a_3903_);
lean_dec(v_name_3748_);
lean_del_object(v___x_3744_);
lean_dec(v_levelParams_3742_);
lean_dec_ref(v_ctorVal_3732_);
v___x_3949_ = lean_box(0);
if (v_isShared_3906_ == 0)
{
lean_ctor_set(v___x_3905_, 0, v___x_3949_);
v___x_3951_ = v___x_3905_;
goto v_reusejp_3950_;
}
else
{
lean_object* v_reuseFailAlloc_3952_; 
v_reuseFailAlloc_3952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3952_, 0, v___x_3949_);
v___x_3951_ = v_reuseFailAlloc_3952_;
goto v_reusejp_3950_;
}
v_reusejp_3950_:
{
return v___x_3951_;
}
}
}
}
else
{
lean_object* v_a_3954_; lean_object* v___x_3956_; uint8_t v_isShared_3957_; uint8_t v_isSharedCheck_3961_; 
lean_dec(v_name_3748_);
lean_del_object(v___x_3744_);
lean_dec(v_levelParams_3742_);
lean_dec_ref(v_ctorVal_3732_);
v_a_3954_ = lean_ctor_get(v___x_3902_, 0);
v_isSharedCheck_3961_ = !lean_is_exclusive(v___x_3902_);
if (v_isSharedCheck_3961_ == 0)
{
v___x_3956_ = v___x_3902_;
v_isShared_3957_ = v_isSharedCheck_3961_;
goto v_resetjp_3955_;
}
else
{
lean_inc(v_a_3954_);
lean_dec(v___x_3902_);
v___x_3956_ = lean_box(0);
v_isShared_3957_ = v_isSharedCheck_3961_;
goto v_resetjp_3955_;
}
v_resetjp_3955_:
{
lean_object* v___x_3959_; 
if (v_isShared_3957_ == 0)
{
v___x_3959_ = v___x_3956_;
goto v_reusejp_3958_;
}
else
{
lean_object* v_reuseFailAlloc_3960_; 
v_reuseFailAlloc_3960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3960_, 0, v_a_3954_);
v___x_3959_ = v_reuseFailAlloc_3960_;
goto v_reusejp_3958_;
}
v_reusejp_3958_:
{
return v___x_3959_;
}
}
}
}
else
{
lean_del_object(v___x_3744_);
goto v___jp_3865_;
}
}
else
{
lean_del_object(v___x_3744_);
goto v___jp_3865_;
}
v___jp_3806_:
{
lean_object* v___x_3810_; double v___x_3811_; double v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; 
v___x_3810_ = lean_io_get_num_heartbeats();
v___x_3811_ = lean_float_of_nat(v___y_3808_);
v___x_3812_ = lean_float_of_nat(v___x_3810_);
v___x_3813_ = lean_box_float(v___x_3811_);
v___x_3814_ = lean_box_float(v___x_3812_);
v___x_3815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3815_, 0, v___x_3813_);
lean_ctor_set(v___x_3815_, 1, v___x_3814_);
v___x_3816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3816_, 0, v_a_3809_);
lean_ctor_set(v___x_3816_, 1, v___x_3815_);
v___x_3817_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_3802_, v_hasTrace_3747_, v___x_3803_, v_options_3740_, v___x_3805_, v___y_3807_, v___f_3801_, v___x_3816_, v_a_3733_, v_a_3734_, v_a_3735_, v_a_3736_);
return v___x_3817_;
}
v___jp_3818_:
{
lean_object* v___x_3822_; 
v___x_3822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3822_, 0, v_a_3821_);
v___y_3807_ = v___y_3819_;
v___y_3808_ = v___y_3820_;
v_a_3809_ = v___x_3822_;
goto v___jp_3806_;
}
v___jp_3823_:
{
lean_object* v___x_3827_; 
v___x_3827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3827_, 0, v_a_3826_);
v___y_3807_ = v___y_3824_;
v___y_3808_ = v___y_3825_;
v_a_3809_ = v___x_3827_;
goto v___jp_3806_;
}
v___jp_3828_:
{
if (lean_obj_tag(v___y_3831_) == 0)
{
lean_object* v_a_3832_; 
v_a_3832_ = lean_ctor_get(v___y_3831_, 0);
lean_inc(v_a_3832_);
lean_dec_ref_known(v___y_3831_, 1);
v___y_3824_ = v___y_3829_;
v___y_3825_ = v___y_3830_;
v_a_3826_ = v_a_3832_;
goto v___jp_3823_;
}
else
{
lean_object* v_a_3833_; 
v_a_3833_ = lean_ctor_get(v___y_3831_, 0);
lean_inc(v_a_3833_);
lean_dec_ref_known(v___y_3831_, 1);
v___y_3819_ = v___y_3829_;
v___y_3820_ = v___y_3830_;
v_a_3821_ = v_a_3833_;
goto v___jp_3818_;
}
}
v___jp_3834_:
{
lean_object* v___x_3838_; double v___x_3839_; double v___x_3840_; double v___x_3841_; double v___x_3842_; double v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; 
v___x_3838_ = lean_io_mono_nanos_now();
v___x_3839_ = lean_float_of_nat(v___y_3836_);
v___x_3840_ = lean_float_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0);
v___x_3841_ = lean_float_div(v___x_3839_, v___x_3840_);
v___x_3842_ = lean_float_of_nat(v___x_3838_);
v___x_3843_ = lean_float_div(v___x_3842_, v___x_3840_);
v___x_3844_ = lean_box_float(v___x_3841_);
v___x_3845_ = lean_box_float(v___x_3843_);
v___x_3846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3846_, 0, v___x_3844_);
lean_ctor_set(v___x_3846_, 1, v___x_3845_);
v___x_3847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3847_, 0, v_a_3837_);
lean_ctor_set(v___x_3847_, 1, v___x_3846_);
v___x_3848_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_3802_, v_hasTrace_3747_, v___x_3803_, v_options_3740_, v___x_3805_, v___y_3835_, v___f_3801_, v___x_3847_, v_a_3733_, v_a_3734_, v_a_3735_, v_a_3736_);
return v___x_3848_;
}
v___jp_3849_:
{
lean_object* v___x_3853_; 
v___x_3853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3853_, 0, v_a_3852_);
v___y_3835_ = v___y_3850_;
v___y_3836_ = v___y_3851_;
v_a_3837_ = v___x_3853_;
goto v___jp_3834_;
}
v___jp_3854_:
{
lean_object* v___x_3858_; 
v___x_3858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3858_, 0, v_a_3857_);
v___y_3835_ = v___y_3855_;
v___y_3836_ = v___y_3856_;
v_a_3837_ = v___x_3858_;
goto v___jp_3834_;
}
v___jp_3859_:
{
if (lean_obj_tag(v___y_3862_) == 0)
{
lean_object* v_a_3863_; 
v_a_3863_ = lean_ctor_get(v___y_3862_, 0);
lean_inc(v_a_3863_);
lean_dec_ref_known(v___y_3862_, 1);
v___y_3850_ = v___y_3860_;
v___y_3851_ = v___y_3861_;
v_a_3852_ = v_a_3863_;
goto v___jp_3849_;
}
else
{
lean_object* v_a_3864_; 
v_a_3864_ = lean_ctor_get(v___y_3862_, 0);
lean_inc(v_a_3864_);
lean_dec_ref_known(v___y_3862_, 1);
v___y_3855_ = v___y_3860_;
v___y_3856_ = v___y_3861_;
v_a_3857_ = v_a_3864_;
goto v___jp_3854_;
}
}
v___jp_3865_:
{
lean_object* v___x_3866_; lean_object* v_a_3867_; lean_object* v___x_3868_; uint8_t v___x_3869_; 
v___x_3866_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v_a_3736_);
v_a_3867_ = lean_ctor_get(v___x_3866_, 0);
lean_inc(v_a_3867_);
lean_dec_ref(v___x_3866_);
v___x_3868_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3869_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_3740_, v___x_3868_);
if (v___x_3869_ == 0)
{
lean_object* v___x_3870_; lean_object* v___x_3871_; 
v___x_3870_ = lean_io_mono_nanos_now();
lean_inc_ref(v_ctorVal_3732_);
v___x_3871_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3732_, v_a_3733_, v_a_3734_, v_a_3735_, v_a_3736_);
if (lean_obj_tag(v___x_3871_) == 0)
{
lean_object* v_a_3872_; 
v_a_3872_ = lean_ctor_get(v___x_3871_, 0);
lean_inc(v_a_3872_);
lean_dec_ref_known(v___x_3871_, 1);
if (lean_obj_tag(v_a_3872_) == 1)
{
if (v___x_3805_ == 0)
{
lean_object* v_val_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; 
v_val_3873_ = lean_ctor_get(v_a_3872_, 0);
lean_inc(v_val_3873_);
lean_dec_ref_known(v_a_3872_, 1);
v___x_3874_ = lean_box(0);
v___x_3875_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(v_ctorVal_3732_, v_val_3873_, v_name_3748_, v_levelParams_3742_, v___x_3869_, v_hasTrace_3747_, v___x_3874_, v_a_3733_, v_a_3734_, v_a_3735_, v_a_3736_);
v___y_3860_ = v_a_3867_;
v___y_3861_ = v___x_3870_;
v___y_3862_ = v___x_3875_;
goto v___jp_3859_;
}
else
{
lean_object* v_val_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; 
v_val_3876_ = lean_ctor_get(v_a_3872_, 0);
lean_inc_n(v_val_3876_, 2);
lean_dec_ref_known(v_a_3872_, 1);
v___x_3877_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_3878_ = l_Lean_MessageData_ofExpr(v_val_3876_);
v___x_3879_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3879_, 0, v___x_3877_);
lean_ctor_set(v___x_3879_, 1, v___x_3878_);
v___x_3880_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_3802_, v___x_3879_, v_a_3733_, v_a_3734_, v_a_3735_, v_a_3736_);
if (lean_obj_tag(v___x_3880_) == 0)
{
lean_object* v_a_3881_; lean_object* v___x_3882_; 
v_a_3881_ = lean_ctor_get(v___x_3880_, 0);
lean_inc(v_a_3881_);
lean_dec_ref_known(v___x_3880_, 1);
v___x_3882_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(v_ctorVal_3732_, v_val_3876_, v_name_3748_, v_levelParams_3742_, v___x_3869_, v_hasTrace_3747_, v_a_3881_, v_a_3733_, v_a_3734_, v_a_3735_, v_a_3736_);
v___y_3860_ = v_a_3867_;
v___y_3861_ = v___x_3870_;
v___y_3862_ = v___x_3882_;
goto v___jp_3859_;
}
else
{
lean_dec(v_val_3876_);
lean_dec(v_name_3748_);
lean_dec(v_levelParams_3742_);
lean_dec_ref(v_ctorVal_3732_);
v___y_3860_ = v_a_3867_;
v___y_3861_ = v___x_3870_;
v___y_3862_ = v___x_3880_;
goto v___jp_3859_;
}
}
}
else
{
lean_object* v___x_3883_; 
lean_dec(v_a_3872_);
lean_dec(v_name_3748_);
lean_dec(v_levelParams_3742_);
lean_dec_ref(v_ctorVal_3732_);
v___x_3883_ = lean_box(0);
v___y_3850_ = v_a_3867_;
v___y_3851_ = v___x_3870_;
v_a_3852_ = v___x_3883_;
goto v___jp_3849_;
}
}
else
{
lean_object* v_a_3884_; 
lean_dec(v_name_3748_);
lean_dec(v_levelParams_3742_);
lean_dec_ref(v_ctorVal_3732_);
v_a_3884_ = lean_ctor_get(v___x_3871_, 0);
lean_inc(v_a_3884_);
lean_dec_ref_known(v___x_3871_, 1);
v___y_3855_ = v_a_3867_;
v___y_3856_ = v___x_3870_;
v_a_3857_ = v_a_3884_;
goto v___jp_3854_;
}
}
else
{
lean_object* v___x_3885_; lean_object* v___x_3886_; 
v___x_3885_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_ctorVal_3732_);
v___x_3886_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3732_, v_a_3733_, v_a_3734_, v_a_3735_, v_a_3736_);
if (lean_obj_tag(v___x_3886_) == 0)
{
lean_object* v_a_3887_; 
v_a_3887_ = lean_ctor_get(v___x_3886_, 0);
lean_inc(v_a_3887_);
lean_dec_ref_known(v___x_3886_, 1);
if (lean_obj_tag(v_a_3887_) == 1)
{
if (v___x_3805_ == 0)
{
lean_object* v_val_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; 
v_val_3888_ = lean_ctor_get(v_a_3887_, 0);
lean_inc(v_val_3888_);
lean_dec_ref_known(v_a_3887_, 1);
v___x_3889_ = lean_box(0);
v___x_3890_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(v_ctorVal_3732_, v_val_3888_, v_name_3748_, v_levelParams_3742_, v___x_3869_, v___x_3889_, v_a_3733_, v_a_3734_, v_a_3735_, v_a_3736_);
v___y_3829_ = v_a_3867_;
v___y_3830_ = v___x_3885_;
v___y_3831_ = v___x_3890_;
goto v___jp_3828_;
}
else
{
lean_object* v_val_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; 
v_val_3891_ = lean_ctor_get(v_a_3887_, 0);
lean_inc_n(v_val_3891_, 2);
lean_dec_ref_known(v_a_3887_, 1);
v___x_3892_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_3893_ = l_Lean_MessageData_ofExpr(v_val_3891_);
v___x_3894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3894_, 0, v___x_3892_);
lean_ctor_set(v___x_3894_, 1, v___x_3893_);
v___x_3895_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_3802_, v___x_3894_, v_a_3733_, v_a_3734_, v_a_3735_, v_a_3736_);
if (lean_obj_tag(v___x_3895_) == 0)
{
lean_object* v_a_3896_; lean_object* v___x_3897_; 
v_a_3896_ = lean_ctor_get(v___x_3895_, 0);
lean_inc(v_a_3896_);
lean_dec_ref_known(v___x_3895_, 1);
v___x_3897_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(v_ctorVal_3732_, v_val_3891_, v_name_3748_, v_levelParams_3742_, v___x_3869_, v_a_3896_, v_a_3733_, v_a_3734_, v_a_3735_, v_a_3736_);
v___y_3829_ = v_a_3867_;
v___y_3830_ = v___x_3885_;
v___y_3831_ = v___x_3897_;
goto v___jp_3828_;
}
else
{
lean_dec(v_val_3891_);
lean_dec(v_name_3748_);
lean_dec(v_levelParams_3742_);
lean_dec_ref(v_ctorVal_3732_);
v___y_3829_ = v_a_3867_;
v___y_3830_ = v___x_3885_;
v___y_3831_ = v___x_3895_;
goto v___jp_3828_;
}
}
}
else
{
lean_object* v___x_3898_; 
lean_dec(v_a_3887_);
lean_dec(v_name_3748_);
lean_dec(v_levelParams_3742_);
lean_dec_ref(v_ctorVal_3732_);
v___x_3898_ = lean_box(0);
v___y_3824_ = v_a_3867_;
v___y_3825_ = v___x_3885_;
v_a_3826_ = v___x_3898_;
goto v___jp_3823_;
}
}
else
{
lean_object* v_a_3899_; 
lean_dec(v_name_3748_);
lean_dec(v_levelParams_3742_);
lean_dec_ref(v_ctorVal_3732_);
v_a_3899_ = lean_ctor_get(v___x_3886_, 0);
lean_inc(v_a_3899_);
lean_dec_ref_known(v___x_3886_, 1);
v___y_3819_ = v_a_3867_;
v___y_3820_ = v___x_3885_;
v_a_3821_ = v_a_3899_;
goto v___jp_3818_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___boxed(lean_object* v_ctorVal_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_, lean_object* v_a_3967_, lean_object* v_a_3968_, lean_object* v_a_3969_){
_start:
{
lean_object* v_res_3970_; 
v_res_3970_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(v_ctorVal_3964_, v_a_3965_, v_a_3966_, v_a_3967_, v_a_3968_);
lean_dec(v_a_3968_);
lean_dec_ref(v_a_3967_);
lean_dec(v_a_3966_);
lean_dec_ref(v_a_3965_);
return v_res_3970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(lean_object* v_name_3971_, lean_object* v_decl_3972_, lean_object* v_ref_3973_){
_start:
{
lean_object* v_defValue_3975_; lean_object* v_descr_3976_; lean_object* v_deprecation_x3f_3977_; lean_object* v___x_3978_; uint8_t v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; 
v_defValue_3975_ = lean_ctor_get(v_decl_3972_, 0);
v_descr_3976_ = lean_ctor_get(v_decl_3972_, 1);
v_deprecation_x3f_3977_ = lean_ctor_get(v_decl_3972_, 2);
v___x_3978_ = lean_alloc_ctor(1, 0, 1);
v___x_3979_ = lean_unbox(v_defValue_3975_);
lean_ctor_set_uint8(v___x_3978_, 0, v___x_3979_);
lean_inc(v_deprecation_x3f_3977_);
lean_inc_ref(v_descr_3976_);
lean_inc_n(v_name_3971_, 2);
v___x_3980_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3980_, 0, v_name_3971_);
lean_ctor_set(v___x_3980_, 1, v_ref_3973_);
lean_ctor_set(v___x_3980_, 2, v___x_3978_);
lean_ctor_set(v___x_3980_, 3, v_descr_3976_);
lean_ctor_set(v___x_3980_, 4, v_deprecation_x3f_3977_);
v___x_3981_ = lean_register_option(v_name_3971_, v___x_3980_);
if (lean_obj_tag(v___x_3981_) == 0)
{
lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_3989_; 
v_isSharedCheck_3989_ = !lean_is_exclusive(v___x_3981_);
if (v_isSharedCheck_3989_ == 0)
{
lean_object* v_unused_3990_; 
v_unused_3990_ = lean_ctor_get(v___x_3981_, 0);
lean_dec(v_unused_3990_);
v___x_3983_ = v___x_3981_;
v_isShared_3984_ = v_isSharedCheck_3989_;
goto v_resetjp_3982_;
}
else
{
lean_dec(v___x_3981_);
v___x_3983_ = lean_box(0);
v_isShared_3984_ = v_isSharedCheck_3989_;
goto v_resetjp_3982_;
}
v_resetjp_3982_:
{
lean_object* v___x_3985_; lean_object* v___x_3987_; 
lean_inc(v_defValue_3975_);
v___x_3985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3985_, 0, v_name_3971_);
lean_ctor_set(v___x_3985_, 1, v_defValue_3975_);
if (v_isShared_3984_ == 0)
{
lean_ctor_set(v___x_3983_, 0, v___x_3985_);
v___x_3987_ = v___x_3983_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_3988_; 
v_reuseFailAlloc_3988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3988_, 0, v___x_3985_);
v___x_3987_ = v_reuseFailAlloc_3988_;
goto v_reusejp_3986_;
}
v_reusejp_3986_:
{
return v___x_3987_;
}
}
}
else
{
lean_object* v_a_3991_; lean_object* v___x_3993_; uint8_t v_isShared_3994_; uint8_t v_isSharedCheck_3998_; 
lean_dec(v_name_3971_);
v_a_3991_ = lean_ctor_get(v___x_3981_, 0);
v_isSharedCheck_3998_ = !lean_is_exclusive(v___x_3981_);
if (v_isSharedCheck_3998_ == 0)
{
v___x_3993_ = v___x_3981_;
v_isShared_3994_ = v_isSharedCheck_3998_;
goto v_resetjp_3992_;
}
else
{
lean_inc(v_a_3991_);
lean_dec(v___x_3981_);
v___x_3993_ = lean_box(0);
v_isShared_3994_ = v_isSharedCheck_3998_;
goto v_resetjp_3992_;
}
v_resetjp_3992_:
{
lean_object* v___x_3996_; 
if (v_isShared_3994_ == 0)
{
v___x_3996_ = v___x_3993_;
goto v_reusejp_3995_;
}
else
{
lean_object* v_reuseFailAlloc_3997_; 
v_reuseFailAlloc_3997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3997_, 0, v_a_3991_);
v___x_3996_ = v_reuseFailAlloc_3997_;
goto v_reusejp_3995_;
}
v_reusejp_3995_:
{
return v___x_3996_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_3999_, lean_object* v_decl_4000_, lean_object* v_ref_4001_, lean_object* v_a_4002_){
_start:
{
lean_object* v_res_4003_; 
v_res_4003_ = l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(v_name_3999_, v_decl_4000_, v_ref_4001_);
lean_dec_ref(v_decl_4000_);
return v_res_4003_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; 
v___x_4018_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_));
v___x_4019_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_));
v___x_4020_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_));
v___x_4021_ = l_Lean_Option_register___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(v___x_4018_, v___x_4019_, v___x_4020_);
return v___x_4021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4____boxed(lean_object* v_a_4022_){
_start:
{
lean_object* v_res_4023_; 
v_res_4023_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_();
return v_res_4023_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(lean_object* v___y_4024_, uint8_t v_isExporting_4025_, lean_object* v___x_4026_, lean_object* v___y_4027_, lean_object* v___x_4028_, lean_object* v_a_x3f_4029_){
_start:
{
lean_object* v___x_4031_; lean_object* v_env_4032_; lean_object* v_nextMacroScope_4033_; lean_object* v_ngen_4034_; lean_object* v_auxDeclNGen_4035_; lean_object* v_traceState_4036_; lean_object* v_messages_4037_; lean_object* v_infoState_4038_; lean_object* v_snapshotTasks_4039_; lean_object* v___x_4041_; uint8_t v_isShared_4042_; uint8_t v_isSharedCheck_4064_; 
v___x_4031_ = lean_st_ref_take(v___y_4024_);
v_env_4032_ = lean_ctor_get(v___x_4031_, 0);
v_nextMacroScope_4033_ = lean_ctor_get(v___x_4031_, 1);
v_ngen_4034_ = lean_ctor_get(v___x_4031_, 2);
v_auxDeclNGen_4035_ = lean_ctor_get(v___x_4031_, 3);
v_traceState_4036_ = lean_ctor_get(v___x_4031_, 4);
v_messages_4037_ = lean_ctor_get(v___x_4031_, 6);
v_infoState_4038_ = lean_ctor_get(v___x_4031_, 7);
v_snapshotTasks_4039_ = lean_ctor_get(v___x_4031_, 8);
v_isSharedCheck_4064_ = !lean_is_exclusive(v___x_4031_);
if (v_isSharedCheck_4064_ == 0)
{
lean_object* v_unused_4065_; 
v_unused_4065_ = lean_ctor_get(v___x_4031_, 5);
lean_dec(v_unused_4065_);
v___x_4041_ = v___x_4031_;
v_isShared_4042_ = v_isSharedCheck_4064_;
goto v_resetjp_4040_;
}
else
{
lean_inc(v_snapshotTasks_4039_);
lean_inc(v_infoState_4038_);
lean_inc(v_messages_4037_);
lean_inc(v_traceState_4036_);
lean_inc(v_auxDeclNGen_4035_);
lean_inc(v_ngen_4034_);
lean_inc(v_nextMacroScope_4033_);
lean_inc(v_env_4032_);
lean_dec(v___x_4031_);
v___x_4041_ = lean_box(0);
v_isShared_4042_ = v_isSharedCheck_4064_;
goto v_resetjp_4040_;
}
v_resetjp_4040_:
{
lean_object* v___x_4043_; lean_object* v___x_4045_; 
v___x_4043_ = l_Lean_Environment_setExporting(v_env_4032_, v_isExporting_4025_);
if (v_isShared_4042_ == 0)
{
lean_ctor_set(v___x_4041_, 5, v___x_4026_);
lean_ctor_set(v___x_4041_, 0, v___x_4043_);
v___x_4045_ = v___x_4041_;
goto v_reusejp_4044_;
}
else
{
lean_object* v_reuseFailAlloc_4063_; 
v_reuseFailAlloc_4063_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4063_, 0, v___x_4043_);
lean_ctor_set(v_reuseFailAlloc_4063_, 1, v_nextMacroScope_4033_);
lean_ctor_set(v_reuseFailAlloc_4063_, 2, v_ngen_4034_);
lean_ctor_set(v_reuseFailAlloc_4063_, 3, v_auxDeclNGen_4035_);
lean_ctor_set(v_reuseFailAlloc_4063_, 4, v_traceState_4036_);
lean_ctor_set(v_reuseFailAlloc_4063_, 5, v___x_4026_);
lean_ctor_set(v_reuseFailAlloc_4063_, 6, v_messages_4037_);
lean_ctor_set(v_reuseFailAlloc_4063_, 7, v_infoState_4038_);
lean_ctor_set(v_reuseFailAlloc_4063_, 8, v_snapshotTasks_4039_);
v___x_4045_ = v_reuseFailAlloc_4063_;
goto v_reusejp_4044_;
}
v_reusejp_4044_:
{
lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v_mctx_4048_; lean_object* v_zetaDeltaFVarIds_4049_; lean_object* v_postponed_4050_; lean_object* v_diag_4051_; lean_object* v___x_4053_; uint8_t v_isShared_4054_; uint8_t v_isSharedCheck_4061_; 
v___x_4046_ = lean_st_ref_put(v___y_4024_, v___x_4045_);
v___x_4047_ = lean_st_ref_take(v___y_4027_);
v_mctx_4048_ = lean_ctor_get(v___x_4047_, 0);
v_zetaDeltaFVarIds_4049_ = lean_ctor_get(v___x_4047_, 2);
v_postponed_4050_ = lean_ctor_get(v___x_4047_, 3);
v_diag_4051_ = lean_ctor_get(v___x_4047_, 4);
v_isSharedCheck_4061_ = !lean_is_exclusive(v___x_4047_);
if (v_isSharedCheck_4061_ == 0)
{
lean_object* v_unused_4062_; 
v_unused_4062_ = lean_ctor_get(v___x_4047_, 1);
lean_dec(v_unused_4062_);
v___x_4053_ = v___x_4047_;
v_isShared_4054_ = v_isSharedCheck_4061_;
goto v_resetjp_4052_;
}
else
{
lean_inc(v_diag_4051_);
lean_inc(v_postponed_4050_);
lean_inc(v_zetaDeltaFVarIds_4049_);
lean_inc(v_mctx_4048_);
lean_dec(v___x_4047_);
v___x_4053_ = lean_box(0);
v_isShared_4054_ = v_isSharedCheck_4061_;
goto v_resetjp_4052_;
}
v_resetjp_4052_:
{
lean_object* v___x_4056_; 
if (v_isShared_4054_ == 0)
{
lean_ctor_set(v___x_4053_, 1, v___x_4028_);
v___x_4056_ = v___x_4053_;
goto v_reusejp_4055_;
}
else
{
lean_object* v_reuseFailAlloc_4060_; 
v_reuseFailAlloc_4060_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4060_, 0, v_mctx_4048_);
lean_ctor_set(v_reuseFailAlloc_4060_, 1, v___x_4028_);
lean_ctor_set(v_reuseFailAlloc_4060_, 2, v_zetaDeltaFVarIds_4049_);
lean_ctor_set(v_reuseFailAlloc_4060_, 3, v_postponed_4050_);
lean_ctor_set(v_reuseFailAlloc_4060_, 4, v_diag_4051_);
v___x_4056_ = v_reuseFailAlloc_4060_;
goto v_reusejp_4055_;
}
v_reusejp_4055_:
{
lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; 
v___x_4057_ = lean_st_ref_put(v___y_4027_, v___x_4056_);
v___x_4058_ = lean_box(0);
v___x_4059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4059_, 0, v___x_4058_);
return v___x_4059_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0___boxed(lean_object* v___y_4066_, lean_object* v_isExporting_4067_, lean_object* v___x_4068_, lean_object* v___y_4069_, lean_object* v___x_4070_, lean_object* v_a_x3f_4071_, lean_object* v___y_4072_){
_start:
{
uint8_t v_isExporting_boxed_4073_; lean_object* v_res_4074_; 
v_isExporting_boxed_4073_ = lean_unbox(v_isExporting_4067_);
v_res_4074_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(v___y_4066_, v_isExporting_boxed_4073_, v___x_4068_, v___y_4069_, v___x_4070_, v_a_x3f_4071_);
lean_dec(v_a_x3f_4071_);
lean_dec(v___y_4069_);
lean_dec(v___y_4066_);
return v_res_4074_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_4075_; 
v___x_4075_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4075_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4076_; lean_object* v___x_4077_; 
v___x_4076_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0);
v___x_4077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4077_, 0, v___x_4076_);
return v___x_4077_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_4078_; lean_object* v___x_4079_; 
v___x_4078_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1);
v___x_4079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4079_, 0, v___x_4078_);
lean_ctor_set(v___x_4079_, 1, v___x_4078_);
return v___x_4079_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_4080_; lean_object* v___x_4081_; 
v___x_4080_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1);
v___x_4081_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4081_, 0, v___x_4080_);
lean_ctor_set(v___x_4081_, 1, v___x_4080_);
lean_ctor_set(v___x_4081_, 2, v___x_4080_);
lean_ctor_set(v___x_4081_, 3, v___x_4080_);
lean_ctor_set(v___x_4081_, 4, v___x_4080_);
lean_ctor_set(v___x_4081_, 5, v___x_4080_);
return v___x_4081_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(lean_object* v_x_4082_, uint8_t v_isExporting_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_){
_start:
{
lean_object* v___x_4089_; lean_object* v_env_4090_; lean_object* v___x_4091_; uint8_t v_isModule_4092_; 
v___x_4089_ = lean_st_ref_get(v___y_4087_);
v_env_4090_ = lean_ctor_get(v___x_4089_, 0);
lean_inc_ref(v_env_4090_);
lean_dec(v___x_4089_);
v___x_4091_ = l_Lean_Environment_header(v_env_4090_);
v_isModule_4092_ = lean_ctor_get_uint8(v___x_4091_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4091_);
if (v_isModule_4092_ == 0)
{
lean_object* v___x_4093_; 
lean_dec_ref(v_env_4090_);
lean_inc(v___y_4087_);
lean_inc_ref(v___y_4086_);
lean_inc(v___y_4085_);
lean_inc_ref(v___y_4084_);
v___x_4093_ = lean_apply_5(v_x_4082_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, lean_box(0));
return v___x_4093_;
}
else
{
uint8_t v_isExporting_4094_; 
v_isExporting_4094_ = lean_ctor_get_uint8(v_env_4090_, sizeof(void*)*8);
lean_dec_ref(v_env_4090_);
if (v_isExporting_4083_ == 0)
{
if (v_isExporting_4094_ == 0)
{
lean_object* v___x_4160_; 
lean_inc(v___y_4087_);
lean_inc_ref(v___y_4086_);
lean_inc(v___y_4085_);
lean_inc_ref(v___y_4084_);
v___x_4160_ = lean_apply_5(v_x_4082_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, lean_box(0));
return v___x_4160_;
}
else
{
goto v___jp_4095_;
}
}
else
{
if (v_isExporting_4094_ == 0)
{
goto v___jp_4095_;
}
else
{
lean_object* v___x_4161_; 
lean_inc(v___y_4087_);
lean_inc_ref(v___y_4086_);
lean_inc(v___y_4085_);
lean_inc_ref(v___y_4084_);
v___x_4161_ = lean_apply_5(v_x_4082_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, lean_box(0));
return v___x_4161_;
}
}
v___jp_4095_:
{
lean_object* v___x_4096_; lean_object* v_env_4097_; lean_object* v_nextMacroScope_4098_; lean_object* v_ngen_4099_; lean_object* v_auxDeclNGen_4100_; lean_object* v_traceState_4101_; lean_object* v_messages_4102_; lean_object* v_infoState_4103_; lean_object* v_snapshotTasks_4104_; lean_object* v___x_4106_; uint8_t v_isShared_4107_; uint8_t v_isSharedCheck_4158_; 
v___x_4096_ = lean_st_ref_take(v___y_4087_);
v_env_4097_ = lean_ctor_get(v___x_4096_, 0);
v_nextMacroScope_4098_ = lean_ctor_get(v___x_4096_, 1);
v_ngen_4099_ = lean_ctor_get(v___x_4096_, 2);
v_auxDeclNGen_4100_ = lean_ctor_get(v___x_4096_, 3);
v_traceState_4101_ = lean_ctor_get(v___x_4096_, 4);
v_messages_4102_ = lean_ctor_get(v___x_4096_, 6);
v_infoState_4103_ = lean_ctor_get(v___x_4096_, 7);
v_snapshotTasks_4104_ = lean_ctor_get(v___x_4096_, 8);
v_isSharedCheck_4158_ = !lean_is_exclusive(v___x_4096_);
if (v_isSharedCheck_4158_ == 0)
{
lean_object* v_unused_4159_; 
v_unused_4159_ = lean_ctor_get(v___x_4096_, 5);
lean_dec(v_unused_4159_);
v___x_4106_ = v___x_4096_;
v_isShared_4107_ = v_isSharedCheck_4158_;
goto v_resetjp_4105_;
}
else
{
lean_inc(v_snapshotTasks_4104_);
lean_inc(v_infoState_4103_);
lean_inc(v_messages_4102_);
lean_inc(v_traceState_4101_);
lean_inc(v_auxDeclNGen_4100_);
lean_inc(v_ngen_4099_);
lean_inc(v_nextMacroScope_4098_);
lean_inc(v_env_4097_);
lean_dec(v___x_4096_);
v___x_4106_ = lean_box(0);
v_isShared_4107_ = v_isSharedCheck_4158_;
goto v_resetjp_4105_;
}
v_resetjp_4105_:
{
lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4111_; 
v___x_4108_ = l_Lean_Environment_setExporting(v_env_4097_, v_isExporting_4083_);
v___x_4109_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2);
if (v_isShared_4107_ == 0)
{
lean_ctor_set(v___x_4106_, 5, v___x_4109_);
lean_ctor_set(v___x_4106_, 0, v___x_4108_);
v___x_4111_ = v___x_4106_;
goto v_reusejp_4110_;
}
else
{
lean_object* v_reuseFailAlloc_4157_; 
v_reuseFailAlloc_4157_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4157_, 0, v___x_4108_);
lean_ctor_set(v_reuseFailAlloc_4157_, 1, v_nextMacroScope_4098_);
lean_ctor_set(v_reuseFailAlloc_4157_, 2, v_ngen_4099_);
lean_ctor_set(v_reuseFailAlloc_4157_, 3, v_auxDeclNGen_4100_);
lean_ctor_set(v_reuseFailAlloc_4157_, 4, v_traceState_4101_);
lean_ctor_set(v_reuseFailAlloc_4157_, 5, v___x_4109_);
lean_ctor_set(v_reuseFailAlloc_4157_, 6, v_messages_4102_);
lean_ctor_set(v_reuseFailAlloc_4157_, 7, v_infoState_4103_);
lean_ctor_set(v_reuseFailAlloc_4157_, 8, v_snapshotTasks_4104_);
v___x_4111_ = v_reuseFailAlloc_4157_;
goto v_reusejp_4110_;
}
v_reusejp_4110_:
{
lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v_mctx_4114_; lean_object* v_zetaDeltaFVarIds_4115_; lean_object* v_postponed_4116_; lean_object* v_diag_4117_; lean_object* v___x_4119_; uint8_t v_isShared_4120_; uint8_t v_isSharedCheck_4155_; 
v___x_4112_ = lean_st_ref_put(v___y_4087_, v___x_4111_);
v___x_4113_ = lean_st_ref_take(v___y_4085_);
v_mctx_4114_ = lean_ctor_get(v___x_4113_, 0);
v_zetaDeltaFVarIds_4115_ = lean_ctor_get(v___x_4113_, 2);
v_postponed_4116_ = lean_ctor_get(v___x_4113_, 3);
v_diag_4117_ = lean_ctor_get(v___x_4113_, 4);
v_isSharedCheck_4155_ = !lean_is_exclusive(v___x_4113_);
if (v_isSharedCheck_4155_ == 0)
{
lean_object* v_unused_4156_; 
v_unused_4156_ = lean_ctor_get(v___x_4113_, 1);
lean_dec(v_unused_4156_);
v___x_4119_ = v___x_4113_;
v_isShared_4120_ = v_isSharedCheck_4155_;
goto v_resetjp_4118_;
}
else
{
lean_inc(v_diag_4117_);
lean_inc(v_postponed_4116_);
lean_inc(v_zetaDeltaFVarIds_4115_);
lean_inc(v_mctx_4114_);
lean_dec(v___x_4113_);
v___x_4119_ = lean_box(0);
v_isShared_4120_ = v_isSharedCheck_4155_;
goto v_resetjp_4118_;
}
v_resetjp_4118_:
{
lean_object* v___x_4121_; lean_object* v___x_4123_; 
v___x_4121_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3);
if (v_isShared_4120_ == 0)
{
lean_ctor_set(v___x_4119_, 1, v___x_4121_);
v___x_4123_ = v___x_4119_;
goto v_reusejp_4122_;
}
else
{
lean_object* v_reuseFailAlloc_4154_; 
v_reuseFailAlloc_4154_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4154_, 0, v_mctx_4114_);
lean_ctor_set(v_reuseFailAlloc_4154_, 1, v___x_4121_);
lean_ctor_set(v_reuseFailAlloc_4154_, 2, v_zetaDeltaFVarIds_4115_);
lean_ctor_set(v_reuseFailAlloc_4154_, 3, v_postponed_4116_);
lean_ctor_set(v_reuseFailAlloc_4154_, 4, v_diag_4117_);
v___x_4123_ = v_reuseFailAlloc_4154_;
goto v_reusejp_4122_;
}
v_reusejp_4122_:
{
lean_object* v___x_4124_; lean_object* v_r_4125_; 
v___x_4124_ = lean_st_ref_put(v___y_4085_, v___x_4123_);
lean_inc(v___y_4087_);
lean_inc_ref(v___y_4086_);
lean_inc(v___y_4085_);
lean_inc_ref(v___y_4084_);
v_r_4125_ = lean_apply_5(v_x_4082_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, lean_box(0));
if (lean_obj_tag(v_r_4125_) == 0)
{
lean_object* v_a_4126_; lean_object* v___x_4128_; uint8_t v_isShared_4129_; uint8_t v_isSharedCheck_4142_; 
v_a_4126_ = lean_ctor_get(v_r_4125_, 0);
v_isSharedCheck_4142_ = !lean_is_exclusive(v_r_4125_);
if (v_isSharedCheck_4142_ == 0)
{
v___x_4128_ = v_r_4125_;
v_isShared_4129_ = v_isSharedCheck_4142_;
goto v_resetjp_4127_;
}
else
{
lean_inc(v_a_4126_);
lean_dec(v_r_4125_);
v___x_4128_ = lean_box(0);
v_isShared_4129_ = v_isSharedCheck_4142_;
goto v_resetjp_4127_;
}
v_resetjp_4127_:
{
lean_object* v___x_4131_; 
lean_inc(v_a_4126_);
if (v_isShared_4129_ == 0)
{
lean_ctor_set_tag(v___x_4128_, 1);
v___x_4131_ = v___x_4128_;
goto v_reusejp_4130_;
}
else
{
lean_object* v_reuseFailAlloc_4141_; 
v_reuseFailAlloc_4141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4141_, 0, v_a_4126_);
v___x_4131_ = v_reuseFailAlloc_4141_;
goto v_reusejp_4130_;
}
v_reusejp_4130_:
{
lean_object* v___x_4132_; lean_object* v___x_4134_; uint8_t v_isShared_4135_; uint8_t v_isSharedCheck_4139_; 
v___x_4132_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(v___y_4087_, v_isExporting_4094_, v___x_4109_, v___y_4085_, v___x_4121_, v___x_4131_);
lean_dec_ref(v___x_4131_);
v_isSharedCheck_4139_ = !lean_is_exclusive(v___x_4132_);
if (v_isSharedCheck_4139_ == 0)
{
lean_object* v_unused_4140_; 
v_unused_4140_ = lean_ctor_get(v___x_4132_, 0);
lean_dec(v_unused_4140_);
v___x_4134_ = v___x_4132_;
v_isShared_4135_ = v_isSharedCheck_4139_;
goto v_resetjp_4133_;
}
else
{
lean_dec(v___x_4132_);
v___x_4134_ = lean_box(0);
v_isShared_4135_ = v_isSharedCheck_4139_;
goto v_resetjp_4133_;
}
v_resetjp_4133_:
{
lean_object* v___x_4137_; 
if (v_isShared_4135_ == 0)
{
lean_ctor_set(v___x_4134_, 0, v_a_4126_);
v___x_4137_ = v___x_4134_;
goto v_reusejp_4136_;
}
else
{
lean_object* v_reuseFailAlloc_4138_; 
v_reuseFailAlloc_4138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4138_, 0, v_a_4126_);
v___x_4137_ = v_reuseFailAlloc_4138_;
goto v_reusejp_4136_;
}
v_reusejp_4136_:
{
return v___x_4137_;
}
}
}
}
}
else
{
lean_object* v_a_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4147_; uint8_t v_isShared_4148_; uint8_t v_isSharedCheck_4152_; 
v_a_4143_ = lean_ctor_get(v_r_4125_, 0);
lean_inc(v_a_4143_);
lean_dec_ref_known(v_r_4125_, 1);
v___x_4144_ = lean_box(0);
v___x_4145_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(v___y_4087_, v_isExporting_4094_, v___x_4109_, v___y_4085_, v___x_4121_, v___x_4144_);
v_isSharedCheck_4152_ = !lean_is_exclusive(v___x_4145_);
if (v_isSharedCheck_4152_ == 0)
{
lean_object* v_unused_4153_; 
v_unused_4153_ = lean_ctor_get(v___x_4145_, 0);
lean_dec(v_unused_4153_);
v___x_4147_ = v___x_4145_;
v_isShared_4148_ = v_isSharedCheck_4152_;
goto v_resetjp_4146_;
}
else
{
lean_dec(v___x_4145_);
v___x_4147_ = lean_box(0);
v_isShared_4148_ = v_isSharedCheck_4152_;
goto v_resetjp_4146_;
}
v_resetjp_4146_:
{
lean_object* v___x_4150_; 
if (v_isShared_4148_ == 0)
{
lean_ctor_set_tag(v___x_4147_, 1);
lean_ctor_set(v___x_4147_, 0, v_a_4143_);
v___x_4150_ = v___x_4147_;
goto v_reusejp_4149_;
}
else
{
lean_object* v_reuseFailAlloc_4151_; 
v_reuseFailAlloc_4151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4151_, 0, v_a_4143_);
v___x_4150_ = v_reuseFailAlloc_4151_;
goto v_reusejp_4149_;
}
v_reusejp_4149_:
{
return v___x_4150_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___boxed(lean_object* v_x_4162_, lean_object* v_isExporting_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_){
_start:
{
uint8_t v_isExporting_boxed_4169_; lean_object* v_res_4170_; 
v_isExporting_boxed_4169_ = lean_unbox(v_isExporting_4163_);
v_res_4170_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(v_x_4162_, v_isExporting_boxed_4169_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_);
lean_dec(v___y_4167_);
lean_dec_ref(v___y_4166_);
lean_dec(v___y_4165_);
lean_dec_ref(v___y_4164_);
return v_res_4170_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2(lean_object* v_00_u03b1_4171_, lean_object* v_x_4172_, uint8_t v_isExporting_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_){
_start:
{
lean_object* v___x_4179_; 
v___x_4179_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(v_x_4172_, v_isExporting_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_);
return v___x_4179_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___boxed(lean_object* v_00_u03b1_4180_, lean_object* v_x_4181_, lean_object* v_isExporting_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_){
_start:
{
uint8_t v_isExporting_boxed_4188_; lean_object* v_res_4189_; 
v_isExporting_boxed_4188_ = lean_unbox(v_isExporting_4182_);
v_res_4189_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2(v_00_u03b1_4180_, v_x_4181_, v_isExporting_boxed_4188_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_);
lean_dec(v___y_4186_);
lean_dec_ref(v___y_4185_);
lean_dec(v___y_4184_);
lean_dec_ref(v___y_4183_);
return v_res_4189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(lean_object* v_lctx_4190_, lean_object* v_localInsts_4191_, lean_object* v_x_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_){
_start:
{
lean_object* v___x_4198_; 
v___x_4198_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_4190_, v_localInsts_4191_, v_x_4192_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_);
if (lean_obj_tag(v___x_4198_) == 0)
{
lean_object* v_a_4199_; lean_object* v___x_4201_; uint8_t v_isShared_4202_; uint8_t v_isSharedCheck_4206_; 
v_a_4199_ = lean_ctor_get(v___x_4198_, 0);
v_isSharedCheck_4206_ = !lean_is_exclusive(v___x_4198_);
if (v_isSharedCheck_4206_ == 0)
{
v___x_4201_ = v___x_4198_;
v_isShared_4202_ = v_isSharedCheck_4206_;
goto v_resetjp_4200_;
}
else
{
lean_inc(v_a_4199_);
lean_dec(v___x_4198_);
v___x_4201_ = lean_box(0);
v_isShared_4202_ = v_isSharedCheck_4206_;
goto v_resetjp_4200_;
}
v_resetjp_4200_:
{
lean_object* v___x_4204_; 
if (v_isShared_4202_ == 0)
{
v___x_4204_ = v___x_4201_;
goto v_reusejp_4203_;
}
else
{
lean_object* v_reuseFailAlloc_4205_; 
v_reuseFailAlloc_4205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4205_, 0, v_a_4199_);
v___x_4204_ = v_reuseFailAlloc_4205_;
goto v_reusejp_4203_;
}
v_reusejp_4203_:
{
return v___x_4204_;
}
}
}
else
{
lean_object* v_a_4207_; lean_object* v___x_4209_; uint8_t v_isShared_4210_; uint8_t v_isSharedCheck_4214_; 
v_a_4207_ = lean_ctor_get(v___x_4198_, 0);
v_isSharedCheck_4214_ = !lean_is_exclusive(v___x_4198_);
if (v_isSharedCheck_4214_ == 0)
{
v___x_4209_ = v___x_4198_;
v_isShared_4210_ = v_isSharedCheck_4214_;
goto v_resetjp_4208_;
}
else
{
lean_inc(v_a_4207_);
lean_dec(v___x_4198_);
v___x_4209_ = lean_box(0);
v_isShared_4210_ = v_isSharedCheck_4214_;
goto v_resetjp_4208_;
}
v_resetjp_4208_:
{
lean_object* v___x_4212_; 
if (v_isShared_4210_ == 0)
{
v___x_4212_ = v___x_4209_;
goto v_reusejp_4211_;
}
else
{
lean_object* v_reuseFailAlloc_4213_; 
v_reuseFailAlloc_4213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4213_, 0, v_a_4207_);
v___x_4212_ = v_reuseFailAlloc_4213_;
goto v_reusejp_4211_;
}
v_reusejp_4211_:
{
return v___x_4212_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg___boxed(lean_object* v_lctx_4215_, lean_object* v_localInsts_4216_, lean_object* v_x_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_){
_start:
{
lean_object* v_res_4223_; 
v_res_4223_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v_lctx_4215_, v_localInsts_4216_, v_x_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_);
lean_dec(v___y_4221_);
lean_dec_ref(v___y_4220_);
lean_dec(v___y_4219_);
lean_dec_ref(v___y_4218_);
return v_res_4223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4(lean_object* v_00_u03b1_4224_, lean_object* v_lctx_4225_, lean_object* v_localInsts_4226_, lean_object* v_x_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_){
_start:
{
lean_object* v___x_4233_; 
v___x_4233_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v_lctx_4225_, v_localInsts_4226_, v_x_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_);
return v___x_4233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___boxed(lean_object* v_00_u03b1_4234_, lean_object* v_lctx_4235_, lean_object* v_localInsts_4236_, lean_object* v_x_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_){
_start:
{
lean_object* v_res_4243_; 
v_res_4243_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4(v_00_u03b1_4234_, v_lctx_4235_, v_localInsts_4236_, v_x_4237_, v___y_4238_, v___y_4239_, v___y_4240_, v___y_4241_);
lean_dec(v___y_4241_);
lean_dec_ref(v___y_4240_);
lean_dec(v___y_4239_);
lean_dec_ref(v___y_4238_);
return v_res_4243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__0(lean_object* v_declName_4244_, lean_object* v_x_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_){
_start:
{
lean_object* v___x_4251_; lean_object* v___x_4252_; 
v___x_4251_ = l_Lean_MessageData_ofName(v_declName_4244_);
v___x_4252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4252_, 0, v___x_4251_);
return v___x_4252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__0___boxed(lean_object* v_declName_4253_, lean_object* v_x_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_){
_start:
{
lean_object* v_res_4260_; 
v_res_4260_ = l_Lean_Meta_mkInjectiveTheorems___lam__0(v_declName_4253_, v_x_4254_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_);
lean_dec(v___y_4258_);
lean_dec_ref(v___y_4257_);
lean_dec(v___y_4256_);
lean_dec_ref(v___y_4255_);
lean_dec_ref(v_x_4254_);
return v_res_4260_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_4261_; 
v___x_4261_ = l_instMonadEIO(lean_box(0));
return v___x_4261_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(lean_object* v_msg_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_){
_start:
{
lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v_toApplicative_4274_; lean_object* v___x_4276_; uint8_t v_isShared_4277_; uint8_t v_isSharedCheck_4335_; 
v___x_4272_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0);
v___x_4273_ = l_StateRefT_x27_instMonad___redArg(v___x_4272_);
v_toApplicative_4274_ = lean_ctor_get(v___x_4273_, 0);
v_isSharedCheck_4335_ = !lean_is_exclusive(v___x_4273_);
if (v_isSharedCheck_4335_ == 0)
{
lean_object* v_unused_4336_; 
v_unused_4336_ = lean_ctor_get(v___x_4273_, 1);
lean_dec(v_unused_4336_);
v___x_4276_ = v___x_4273_;
v_isShared_4277_ = v_isSharedCheck_4335_;
goto v_resetjp_4275_;
}
else
{
lean_inc(v_toApplicative_4274_);
lean_dec(v___x_4273_);
v___x_4276_ = lean_box(0);
v_isShared_4277_ = v_isSharedCheck_4335_;
goto v_resetjp_4275_;
}
v_resetjp_4275_:
{
lean_object* v_toFunctor_4278_; lean_object* v_toSeq_4279_; lean_object* v_toSeqLeft_4280_; lean_object* v_toSeqRight_4281_; lean_object* v___x_4283_; uint8_t v_isShared_4284_; uint8_t v_isSharedCheck_4333_; 
v_toFunctor_4278_ = lean_ctor_get(v_toApplicative_4274_, 0);
v_toSeq_4279_ = lean_ctor_get(v_toApplicative_4274_, 2);
v_toSeqLeft_4280_ = lean_ctor_get(v_toApplicative_4274_, 3);
v_toSeqRight_4281_ = lean_ctor_get(v_toApplicative_4274_, 4);
v_isSharedCheck_4333_ = !lean_is_exclusive(v_toApplicative_4274_);
if (v_isSharedCheck_4333_ == 0)
{
lean_object* v_unused_4334_; 
v_unused_4334_ = lean_ctor_get(v_toApplicative_4274_, 1);
lean_dec(v_unused_4334_);
v___x_4283_ = v_toApplicative_4274_;
v_isShared_4284_ = v_isSharedCheck_4333_;
goto v_resetjp_4282_;
}
else
{
lean_inc(v_toSeqRight_4281_);
lean_inc(v_toSeqLeft_4280_);
lean_inc(v_toSeq_4279_);
lean_inc(v_toFunctor_4278_);
lean_dec(v_toApplicative_4274_);
v___x_4283_ = lean_box(0);
v_isShared_4284_ = v_isSharedCheck_4333_;
goto v_resetjp_4282_;
}
v_resetjp_4282_:
{
lean_object* v___f_4285_; lean_object* v___f_4286_; lean_object* v___f_4287_; lean_object* v___f_4288_; lean_object* v___x_4289_; lean_object* v___f_4290_; lean_object* v___f_4291_; lean_object* v___f_4292_; lean_object* v___x_4294_; 
v___f_4285_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__1));
v___f_4286_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__2));
lean_inc_ref(v_toFunctor_4278_);
v___f_4287_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4287_, 0, v_toFunctor_4278_);
v___f_4288_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4288_, 0, v_toFunctor_4278_);
v___x_4289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4289_, 0, v___f_4287_);
lean_ctor_set(v___x_4289_, 1, v___f_4288_);
v___f_4290_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4290_, 0, v_toSeqRight_4281_);
v___f_4291_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4291_, 0, v_toSeqLeft_4280_);
v___f_4292_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4292_, 0, v_toSeq_4279_);
if (v_isShared_4284_ == 0)
{
lean_ctor_set(v___x_4283_, 4, v___f_4290_);
lean_ctor_set(v___x_4283_, 3, v___f_4291_);
lean_ctor_set(v___x_4283_, 2, v___f_4292_);
lean_ctor_set(v___x_4283_, 1, v___f_4285_);
lean_ctor_set(v___x_4283_, 0, v___x_4289_);
v___x_4294_ = v___x_4283_;
goto v_reusejp_4293_;
}
else
{
lean_object* v_reuseFailAlloc_4332_; 
v_reuseFailAlloc_4332_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4332_, 0, v___x_4289_);
lean_ctor_set(v_reuseFailAlloc_4332_, 1, v___f_4285_);
lean_ctor_set(v_reuseFailAlloc_4332_, 2, v___f_4292_);
lean_ctor_set(v_reuseFailAlloc_4332_, 3, v___f_4291_);
lean_ctor_set(v_reuseFailAlloc_4332_, 4, v___f_4290_);
v___x_4294_ = v_reuseFailAlloc_4332_;
goto v_reusejp_4293_;
}
v_reusejp_4293_:
{
lean_object* v___x_4296_; 
if (v_isShared_4277_ == 0)
{
lean_ctor_set(v___x_4276_, 1, v___f_4286_);
lean_ctor_set(v___x_4276_, 0, v___x_4294_);
v___x_4296_ = v___x_4276_;
goto v_reusejp_4295_;
}
else
{
lean_object* v_reuseFailAlloc_4331_; 
v_reuseFailAlloc_4331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4331_, 0, v___x_4294_);
lean_ctor_set(v_reuseFailAlloc_4331_, 1, v___f_4286_);
v___x_4296_ = v_reuseFailAlloc_4331_;
goto v_reusejp_4295_;
}
v_reusejp_4295_:
{
lean_object* v___x_4297_; lean_object* v_toApplicative_4298_; lean_object* v___x_4300_; uint8_t v_isShared_4301_; uint8_t v_isSharedCheck_4329_; 
v___x_4297_ = l_StateRefT_x27_instMonad___redArg(v___x_4296_);
v_toApplicative_4298_ = lean_ctor_get(v___x_4297_, 0);
v_isSharedCheck_4329_ = !lean_is_exclusive(v___x_4297_);
if (v_isSharedCheck_4329_ == 0)
{
lean_object* v_unused_4330_; 
v_unused_4330_ = lean_ctor_get(v___x_4297_, 1);
lean_dec(v_unused_4330_);
v___x_4300_ = v___x_4297_;
v_isShared_4301_ = v_isSharedCheck_4329_;
goto v_resetjp_4299_;
}
else
{
lean_inc(v_toApplicative_4298_);
lean_dec(v___x_4297_);
v___x_4300_ = lean_box(0);
v_isShared_4301_ = v_isSharedCheck_4329_;
goto v_resetjp_4299_;
}
v_resetjp_4299_:
{
lean_object* v_toFunctor_4302_; lean_object* v_toSeq_4303_; lean_object* v_toSeqLeft_4304_; lean_object* v_toSeqRight_4305_; lean_object* v___x_4307_; uint8_t v_isShared_4308_; uint8_t v_isSharedCheck_4327_; 
v_toFunctor_4302_ = lean_ctor_get(v_toApplicative_4298_, 0);
v_toSeq_4303_ = lean_ctor_get(v_toApplicative_4298_, 2);
v_toSeqLeft_4304_ = lean_ctor_get(v_toApplicative_4298_, 3);
v_toSeqRight_4305_ = lean_ctor_get(v_toApplicative_4298_, 4);
v_isSharedCheck_4327_ = !lean_is_exclusive(v_toApplicative_4298_);
if (v_isSharedCheck_4327_ == 0)
{
lean_object* v_unused_4328_; 
v_unused_4328_ = lean_ctor_get(v_toApplicative_4298_, 1);
lean_dec(v_unused_4328_);
v___x_4307_ = v_toApplicative_4298_;
v_isShared_4308_ = v_isSharedCheck_4327_;
goto v_resetjp_4306_;
}
else
{
lean_inc(v_toSeqRight_4305_);
lean_inc(v_toSeqLeft_4304_);
lean_inc(v_toSeq_4303_);
lean_inc(v_toFunctor_4302_);
lean_dec(v_toApplicative_4298_);
v___x_4307_ = lean_box(0);
v_isShared_4308_ = v_isSharedCheck_4327_;
goto v_resetjp_4306_;
}
v_resetjp_4306_:
{
lean_object* v___f_4309_; lean_object* v___f_4310_; lean_object* v___f_4311_; lean_object* v___f_4312_; lean_object* v___x_4313_; lean_object* v___f_4314_; lean_object* v___f_4315_; lean_object* v___f_4316_; lean_object* v___x_4318_; 
v___f_4309_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__3));
v___f_4310_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__4));
lean_inc_ref(v_toFunctor_4302_);
v___f_4311_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4311_, 0, v_toFunctor_4302_);
v___f_4312_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4312_, 0, v_toFunctor_4302_);
v___x_4313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4313_, 0, v___f_4311_);
lean_ctor_set(v___x_4313_, 1, v___f_4312_);
v___f_4314_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4314_, 0, v_toSeqRight_4305_);
v___f_4315_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4315_, 0, v_toSeqLeft_4304_);
v___f_4316_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4316_, 0, v_toSeq_4303_);
if (v_isShared_4308_ == 0)
{
lean_ctor_set(v___x_4307_, 4, v___f_4314_);
lean_ctor_set(v___x_4307_, 3, v___f_4315_);
lean_ctor_set(v___x_4307_, 2, v___f_4316_);
lean_ctor_set(v___x_4307_, 1, v___f_4309_);
lean_ctor_set(v___x_4307_, 0, v___x_4313_);
v___x_4318_ = v___x_4307_;
goto v_reusejp_4317_;
}
else
{
lean_object* v_reuseFailAlloc_4326_; 
v_reuseFailAlloc_4326_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4326_, 0, v___x_4313_);
lean_ctor_set(v_reuseFailAlloc_4326_, 1, v___f_4309_);
lean_ctor_set(v_reuseFailAlloc_4326_, 2, v___f_4316_);
lean_ctor_set(v_reuseFailAlloc_4326_, 3, v___f_4315_);
lean_ctor_set(v_reuseFailAlloc_4326_, 4, v___f_4314_);
v___x_4318_ = v_reuseFailAlloc_4326_;
goto v_reusejp_4317_;
}
v_reusejp_4317_:
{
lean_object* v___x_4320_; 
if (v_isShared_4301_ == 0)
{
lean_ctor_set(v___x_4300_, 1, v___f_4310_);
lean_ctor_set(v___x_4300_, 0, v___x_4318_);
v___x_4320_ = v___x_4300_;
goto v_reusejp_4319_;
}
else
{
lean_object* v_reuseFailAlloc_4325_; 
v_reuseFailAlloc_4325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4325_, 0, v___x_4318_);
lean_ctor_set(v_reuseFailAlloc_4325_, 1, v___f_4310_);
v___x_4320_ = v_reuseFailAlloc_4325_;
goto v_reusejp_4319_;
}
v_reusejp_4319_:
{
lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_15665__overap_4323_; lean_object* v___x_4324_; 
v___x_4321_ = lean_box(0);
v___x_4322_ = l_instInhabitedOfMonad___redArg(v___x_4320_, v___x_4321_);
v___x_15665__overap_4323_ = lean_panic_fn_borrowed(v___x_4322_, v_msg_4266_);
lean_dec(v___x_4322_);
lean_inc(v___y_4270_);
lean_inc_ref(v___y_4269_);
lean_inc(v___y_4268_);
lean_inc_ref(v___y_4267_);
v___x_4324_ = lean_apply_5(v___x_15665__overap_4323_, v___y_4267_, v___y_4268_, v___y_4269_, v___y_4270_, lean_box(0));
return v___x_4324_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___boxed(lean_object* v_msg_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_){
_start:
{
lean_object* v_res_4343_; 
v_res_4343_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(v_msg_4337_, v___y_4338_, v___y_4339_, v___y_4340_, v___y_4341_);
lean_dec(v___y_4341_);
lean_dec_ref(v___y_4340_);
lean_dec(v___y_4339_);
lean_dec_ref(v___y_4338_);
return v_res_4343_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1(void){
_start:
{
lean_object* v___x_4345_; lean_object* v___x_4346_; 
v___x_4345_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__0));
v___x_4346_ = l_Lean_stringToMessageData(v___x_4345_);
return v___x_4346_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4(void){
_start:
{
lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; 
v___x_4349_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__2));
v___x_4350_ = lean_unsigned_to_nat(11u);
v___x_4351_ = lean_unsigned_to_nat(122u);
v___x_4352_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__3));
v___x_4353_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__2));
v___x_4354_ = l_mkPanicMessageWithDecl(v___x_4353_, v___x_4352_, v___x_4351_, v___x_4350_, v___x_4349_);
return v___x_4354_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(lean_object* v_constName_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_){
_start:
{
lean_object* v___x_4369_; lean_object* v_env_4370_; uint8_t v___x_4371_; lean_object* v___x_4372_; 
v___x_4369_ = lean_st_ref_get(v___y_4359_);
v_env_4370_ = lean_ctor_get(v___x_4369_, 0);
lean_inc_ref(v_env_4370_);
lean_dec(v___x_4369_);
v___x_4371_ = 0;
lean_inc(v_constName_4355_);
v___x_4372_ = l_Lean_Environment_findAsync_x3f(v_env_4370_, v_constName_4355_, v___x_4371_);
if (lean_obj_tag(v___x_4372_) == 1)
{
lean_object* v_val_4373_; uint8_t v_kind_4374_; 
v_val_4373_ = lean_ctor_get(v___x_4372_, 0);
lean_inc(v_val_4373_);
lean_dec_ref_known(v___x_4372_, 1);
v_kind_4374_ = lean_ctor_get_uint8(v_val_4373_, sizeof(void*)*3);
if (v_kind_4374_ == 6)
{
lean_object* v___x_4375_; 
v___x_4375_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_4373_);
if (lean_obj_tag(v___x_4375_) == 6)
{
lean_object* v_val_4376_; lean_object* v___x_4378_; uint8_t v_isShared_4379_; uint8_t v_isSharedCheck_4383_; 
lean_dec(v_constName_4355_);
v_val_4376_ = lean_ctor_get(v___x_4375_, 0);
v_isSharedCheck_4383_ = !lean_is_exclusive(v___x_4375_);
if (v_isSharedCheck_4383_ == 0)
{
v___x_4378_ = v___x_4375_;
v_isShared_4379_ = v_isSharedCheck_4383_;
goto v_resetjp_4377_;
}
else
{
lean_inc(v_val_4376_);
lean_dec(v___x_4375_);
v___x_4378_ = lean_box(0);
v_isShared_4379_ = v_isSharedCheck_4383_;
goto v_resetjp_4377_;
}
v_resetjp_4377_:
{
lean_object* v___x_4381_; 
if (v_isShared_4379_ == 0)
{
lean_ctor_set_tag(v___x_4378_, 0);
v___x_4381_ = v___x_4378_;
goto v_reusejp_4380_;
}
else
{
lean_object* v_reuseFailAlloc_4382_; 
v_reuseFailAlloc_4382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4382_, 0, v_val_4376_);
v___x_4381_ = v_reuseFailAlloc_4382_;
goto v_reusejp_4380_;
}
v_reusejp_4380_:
{
return v___x_4381_;
}
}
}
else
{
lean_object* v___x_4384_; lean_object* v___x_4385_; 
lean_dec_ref(v___x_4375_);
v___x_4384_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4);
v___x_4385_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(v___x_4384_, v___y_4356_, v___y_4357_, v___y_4358_, v___y_4359_);
if (lean_obj_tag(v___x_4385_) == 0)
{
lean_object* v_a_4386_; lean_object* v___x_4388_; uint8_t v_isShared_4389_; uint8_t v_isSharedCheck_4394_; 
v_a_4386_ = lean_ctor_get(v___x_4385_, 0);
v_isSharedCheck_4394_ = !lean_is_exclusive(v___x_4385_);
if (v_isSharedCheck_4394_ == 0)
{
v___x_4388_ = v___x_4385_;
v_isShared_4389_ = v_isSharedCheck_4394_;
goto v_resetjp_4387_;
}
else
{
lean_inc(v_a_4386_);
lean_dec(v___x_4385_);
v___x_4388_ = lean_box(0);
v_isShared_4389_ = v_isSharedCheck_4394_;
goto v_resetjp_4387_;
}
v_resetjp_4387_:
{
if (lean_obj_tag(v_a_4386_) == 0)
{
lean_del_object(v___x_4388_);
goto v___jp_4361_;
}
else
{
lean_object* v_val_4390_; lean_object* v___x_4392_; 
lean_dec(v_constName_4355_);
v_val_4390_ = lean_ctor_get(v_a_4386_, 0);
lean_inc(v_val_4390_);
lean_dec_ref_known(v_a_4386_, 1);
if (v_isShared_4389_ == 0)
{
lean_ctor_set(v___x_4388_, 0, v_val_4390_);
v___x_4392_ = v___x_4388_;
goto v_reusejp_4391_;
}
else
{
lean_object* v_reuseFailAlloc_4393_; 
v_reuseFailAlloc_4393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4393_, 0, v_val_4390_);
v___x_4392_ = v_reuseFailAlloc_4393_;
goto v_reusejp_4391_;
}
v_reusejp_4391_:
{
return v___x_4392_;
}
}
}
}
else
{
lean_object* v_a_4395_; lean_object* v___x_4397_; uint8_t v_isShared_4398_; uint8_t v_isSharedCheck_4402_; 
lean_dec(v_constName_4355_);
v_a_4395_ = lean_ctor_get(v___x_4385_, 0);
v_isSharedCheck_4402_ = !lean_is_exclusive(v___x_4385_);
if (v_isSharedCheck_4402_ == 0)
{
v___x_4397_ = v___x_4385_;
v_isShared_4398_ = v_isSharedCheck_4402_;
goto v_resetjp_4396_;
}
else
{
lean_inc(v_a_4395_);
lean_dec(v___x_4385_);
v___x_4397_ = lean_box(0);
v_isShared_4398_ = v_isSharedCheck_4402_;
goto v_resetjp_4396_;
}
v_resetjp_4396_:
{
lean_object* v___x_4400_; 
if (v_isShared_4398_ == 0)
{
v___x_4400_ = v___x_4397_;
goto v_reusejp_4399_;
}
else
{
lean_object* v_reuseFailAlloc_4401_; 
v_reuseFailAlloc_4401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4401_, 0, v_a_4395_);
v___x_4400_ = v_reuseFailAlloc_4401_;
goto v_reusejp_4399_;
}
v_reusejp_4399_:
{
return v___x_4400_;
}
}
}
}
}
else
{
lean_dec(v_val_4373_);
goto v___jp_4361_;
}
}
else
{
lean_dec(v___x_4372_);
goto v___jp_4361_;
}
v___jp_4361_:
{
lean_object* v___x_4362_; uint8_t v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; 
v___x_4362_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_4363_ = 0;
v___x_4364_ = l_Lean_MessageData_ofConstName(v_constName_4355_, v___x_4363_);
v___x_4365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4365_, 0, v___x_4362_);
lean_ctor_set(v___x_4365_, 1, v___x_4364_);
v___x_4366_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1);
v___x_4367_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4367_, 0, v___x_4365_);
lean_ctor_set(v___x_4367_, 1, v___x_4366_);
v___x_4368_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_4367_, v___y_4356_, v___y_4357_, v___y_4358_, v___y_4359_);
return v___x_4368_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___boxed(lean_object* v_constName_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_){
_start:
{
lean_object* v_res_4409_; 
v_res_4409_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(v_constName_4403_, v___y_4404_, v___y_4405_, v___y_4406_, v___y_4407_);
lean_dec(v___y_4407_);
lean_dec_ref(v___y_4406_);
lean_dec(v___y_4405_);
lean_dec_ref(v___y_4404_);
return v_res_4409_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0(lean_object* v_head_4410_, lean_object* v___x_4411_, lean_object* v___x_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_){
_start:
{
lean_object* v___x_4418_; 
v___x_4418_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(v_head_4410_, v___y_4413_, v___y_4414_, v___y_4415_, v___y_4416_);
if (lean_obj_tag(v___x_4418_) == 0)
{
lean_object* v_a_4419_; lean_object* v___x_4421_; uint8_t v_isShared_4422_; uint8_t v_isSharedCheck_4430_; 
v_a_4419_ = lean_ctor_get(v___x_4418_, 0);
v_isSharedCheck_4430_ = !lean_is_exclusive(v___x_4418_);
if (v_isSharedCheck_4430_ == 0)
{
v___x_4421_ = v___x_4418_;
v_isShared_4422_ = v_isSharedCheck_4430_;
goto v_resetjp_4420_;
}
else
{
lean_inc(v_a_4419_);
lean_dec(v___x_4418_);
v___x_4421_ = lean_box(0);
v_isShared_4422_ = v_isSharedCheck_4430_;
goto v_resetjp_4420_;
}
v_resetjp_4420_:
{
lean_object* v_numFields_4423_; uint8_t v___x_4424_; 
v_numFields_4423_ = lean_ctor_get(v_a_4419_, 4);
v___x_4424_ = lean_nat_dec_lt(v___x_4411_, v_numFields_4423_);
if (v___x_4424_ == 0)
{
lean_object* v___x_4426_; 
lean_dec(v_a_4419_);
if (v_isShared_4422_ == 0)
{
lean_ctor_set(v___x_4421_, 0, v___x_4412_);
v___x_4426_ = v___x_4421_;
goto v_reusejp_4425_;
}
else
{
lean_object* v_reuseFailAlloc_4427_; 
v_reuseFailAlloc_4427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4427_, 0, v___x_4412_);
v___x_4426_ = v_reuseFailAlloc_4427_;
goto v_reusejp_4425_;
}
v_reusejp_4425_:
{
return v___x_4426_;
}
}
else
{
lean_object* v___x_4428_; 
lean_del_object(v___x_4421_);
lean_inc(v_a_4419_);
v___x_4428_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(v_a_4419_, v___y_4413_, v___y_4414_, v___y_4415_, v___y_4416_);
if (lean_obj_tag(v___x_4428_) == 0)
{
lean_object* v___x_4429_; 
lean_dec_ref_known(v___x_4428_, 1);
v___x_4429_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(v_a_4419_, v___y_4413_, v___y_4414_, v___y_4415_, v___y_4416_);
return v___x_4429_;
}
else
{
lean_dec(v_a_4419_);
return v___x_4428_;
}
}
}
}
else
{
lean_object* v_a_4431_; lean_object* v___x_4433_; uint8_t v_isShared_4434_; uint8_t v_isSharedCheck_4438_; 
v_a_4431_ = lean_ctor_get(v___x_4418_, 0);
v_isSharedCheck_4438_ = !lean_is_exclusive(v___x_4418_);
if (v_isSharedCheck_4438_ == 0)
{
v___x_4433_ = v___x_4418_;
v_isShared_4434_ = v_isSharedCheck_4438_;
goto v_resetjp_4432_;
}
else
{
lean_inc(v_a_4431_);
lean_dec(v___x_4418_);
v___x_4433_ = lean_box(0);
v_isShared_4434_ = v_isSharedCheck_4438_;
goto v_resetjp_4432_;
}
v_resetjp_4432_:
{
lean_object* v___x_4436_; 
if (v_isShared_4434_ == 0)
{
v___x_4436_ = v___x_4433_;
goto v_reusejp_4435_;
}
else
{
lean_object* v_reuseFailAlloc_4437_; 
v_reuseFailAlloc_4437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4437_, 0, v_a_4431_);
v___x_4436_ = v_reuseFailAlloc_4437_;
goto v_reusejp_4435_;
}
v_reusejp_4435_:
{
return v___x_4436_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0___boxed(lean_object* v_head_4439_, lean_object* v___x_4440_, lean_object* v___x_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_){
_start:
{
lean_object* v_res_4447_; 
v_res_4447_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0(v_head_4439_, v___x_4440_, v___x_4441_, v___y_4442_, v___y_4443_, v___y_4444_, v___y_4445_);
lean_dec(v___y_4445_);
lean_dec_ref(v___y_4444_);
lean_dec(v___y_4443_);
lean_dec_ref(v___y_4442_);
lean_dec(v___x_4440_);
return v_res_4447_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(uint8_t v___y_4448_, uint8_t v___x_4449_, lean_object* v_as_x27_4450_, lean_object* v_b_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_){
_start:
{
if (lean_obj_tag(v_as_x27_4450_) == 0)
{
lean_object* v___x_4457_; 
v___x_4457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4457_, 0, v_b_4451_);
return v___x_4457_;
}
else
{
lean_object* v_head_4458_; lean_object* v_tail_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v___f_4462_; uint8_t v___y_4464_; uint8_t v___x_4467_; 
v_head_4458_ = lean_ctor_get(v_as_x27_4450_, 0);
v_tail_4459_ = lean_ctor_get(v_as_x27_4450_, 1);
v___x_4460_ = lean_unsigned_to_nat(0u);
v___x_4461_ = lean_box(0);
lean_inc(v_head_4458_);
v___f_4462_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4462_, 0, v_head_4458_);
lean_closure_set(v___f_4462_, 1, v___x_4460_);
lean_closure_set(v___f_4462_, 2, v___x_4461_);
v___x_4467_ = l_Lean_isPrivateName(v_head_4458_);
if (v___x_4467_ == 0)
{
v___y_4464_ = v___y_4448_;
goto v___jp_4463_;
}
else
{
v___y_4464_ = v___x_4449_;
goto v___jp_4463_;
}
v___jp_4463_:
{
lean_object* v___x_4465_; 
v___x_4465_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(v___f_4462_, v___y_4464_, v___y_4452_, v___y_4453_, v___y_4454_, v___y_4455_);
if (lean_obj_tag(v___x_4465_) == 0)
{
lean_dec_ref_known(v___x_4465_, 1);
v_as_x27_4450_ = v_tail_4459_;
v_b_4451_ = v___x_4461_;
goto _start;
}
else
{
return v___x_4465_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___boxed(lean_object* v___y_4468_, lean_object* v___x_4469_, lean_object* v_as_x27_4470_, lean_object* v_b_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_){
_start:
{
uint8_t v___y_16772__boxed_4477_; uint8_t v___x_16773__boxed_4478_; lean_object* v_res_4479_; 
v___y_16772__boxed_4477_ = lean_unbox(v___y_4468_);
v___x_16773__boxed_4478_ = lean_unbox(v___x_4469_);
v_res_4479_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___y_16772__boxed_4477_, v___x_16773__boxed_4478_, v_as_x27_4470_, v_b_4471_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_);
lean_dec(v___y_4475_);
lean_dec_ref(v___y_4474_);
lean_dec(v___y_4473_);
lean_dec_ref(v___y_4472_);
lean_dec(v_as_x27_4470_);
return v_res_4479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__1(uint8_t v___y_4480_, uint8_t v_isUnsafe_4481_, lean_object* v_ctors_4482_, lean_object* v___x_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_){
_start:
{
lean_object* v___x_4489_; 
v___x_4489_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___y_4480_, v_isUnsafe_4481_, v_ctors_4482_, v___x_4483_, v___y_4484_, v___y_4485_, v___y_4486_, v___y_4487_);
if (lean_obj_tag(v___x_4489_) == 0)
{
lean_object* v___x_4491_; uint8_t v_isShared_4492_; uint8_t v_isSharedCheck_4496_; 
v_isSharedCheck_4496_ = !lean_is_exclusive(v___x_4489_);
if (v_isSharedCheck_4496_ == 0)
{
lean_object* v_unused_4497_; 
v_unused_4497_ = lean_ctor_get(v___x_4489_, 0);
lean_dec(v_unused_4497_);
v___x_4491_ = v___x_4489_;
v_isShared_4492_ = v_isSharedCheck_4496_;
goto v_resetjp_4490_;
}
else
{
lean_dec(v___x_4489_);
v___x_4491_ = lean_box(0);
v_isShared_4492_ = v_isSharedCheck_4496_;
goto v_resetjp_4490_;
}
v_resetjp_4490_:
{
lean_object* v___x_4494_; 
if (v_isShared_4492_ == 0)
{
lean_ctor_set(v___x_4491_, 0, v___x_4483_);
v___x_4494_ = v___x_4491_;
goto v_reusejp_4493_;
}
else
{
lean_object* v_reuseFailAlloc_4495_; 
v_reuseFailAlloc_4495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4495_, 0, v___x_4483_);
v___x_4494_ = v_reuseFailAlloc_4495_;
goto v_reusejp_4493_;
}
v_reusejp_4493_:
{
return v___x_4494_;
}
}
}
else
{
return v___x_4489_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed(lean_object* v___y_4498_, lean_object* v_isUnsafe_4499_, lean_object* v_ctors_4500_, lean_object* v___x_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_){
_start:
{
uint8_t v___y_16817__boxed_4507_; uint8_t v_isUnsafe_boxed_4508_; lean_object* v_res_4509_; 
v___y_16817__boxed_4507_ = lean_unbox(v___y_4498_);
v_isUnsafe_boxed_4508_ = lean_unbox(v_isUnsafe_4499_);
v_res_4509_ = l_Lean_Meta_mkInjectiveTheorems___lam__1(v___y_16817__boxed_4507_, v_isUnsafe_boxed_4508_, v_ctors_4500_, v___x_4501_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
lean_dec(v___y_4505_);
lean_dec_ref(v___y_4504_);
lean_dec(v___y_4503_);
lean_dec_ref(v___y_4502_);
lean_dec(v_ctors_4500_);
return v_res_4509_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4511_; lean_object* v___x_4512_; 
v___x_4511_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__0));
v___x_4512_ = l_Lean_stringToMessageData(v___x_4511_);
return v___x_4512_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(lean_object* v_constName_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_){
_start:
{
lean_object* v___x_4519_; lean_object* v_env_4520_; lean_object* v___x_4521_; 
v___x_4519_ = lean_st_ref_get(v___y_4517_);
v_env_4520_ = lean_ctor_get(v___x_4519_, 0);
lean_inc_ref(v_env_4520_);
lean_dec(v___x_4519_);
lean_inc(v_constName_4513_);
v___x_4521_ = l_Lean_isInductiveCore_x3f(v_env_4520_, v_constName_4513_);
if (lean_obj_tag(v___x_4521_) == 0)
{
lean_object* v___x_4522_; uint8_t v___x_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; lean_object* v___x_4528_; 
v___x_4522_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_4523_ = 0;
v___x_4524_ = l_Lean_MessageData_ofConstName(v_constName_4513_, v___x_4523_);
v___x_4525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4525_, 0, v___x_4522_);
lean_ctor_set(v___x_4525_, 1, v___x_4524_);
v___x_4526_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1);
v___x_4527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4527_, 0, v___x_4525_);
lean_ctor_set(v___x_4527_, 1, v___x_4526_);
v___x_4528_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_4527_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_);
return v___x_4528_;
}
else
{
lean_object* v_val_4529_; lean_object* v___x_4531_; uint8_t v_isShared_4532_; uint8_t v_isSharedCheck_4536_; 
lean_dec(v_constName_4513_);
v_val_4529_ = lean_ctor_get(v___x_4521_, 0);
v_isSharedCheck_4536_ = !lean_is_exclusive(v___x_4521_);
if (v_isSharedCheck_4536_ == 0)
{
v___x_4531_ = v___x_4521_;
v_isShared_4532_ = v_isSharedCheck_4536_;
goto v_resetjp_4530_;
}
else
{
lean_inc(v_val_4529_);
lean_dec(v___x_4521_);
v___x_4531_ = lean_box(0);
v_isShared_4532_ = v_isSharedCheck_4536_;
goto v_resetjp_4530_;
}
v_resetjp_4530_:
{
lean_object* v___x_4534_; 
if (v_isShared_4532_ == 0)
{
lean_ctor_set_tag(v___x_4531_, 0);
v___x_4534_ = v___x_4531_;
goto v_reusejp_4533_;
}
else
{
lean_object* v_reuseFailAlloc_4535_; 
v_reuseFailAlloc_4535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4535_, 0, v_val_4529_);
v___x_4534_ = v_reuseFailAlloc_4535_;
goto v_reusejp_4533_;
}
v_reusejp_4533_:
{
return v___x_4534_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___boxed(lean_object* v_constName_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_){
_start:
{
lean_object* v_res_4543_; 
v_res_4543_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_constName_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_);
lean_dec(v___y_4541_);
lean_dec_ref(v___y_4540_);
lean_dec(v___y_4539_);
lean_dec_ref(v___y_4538_);
return v_res_4543_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__0(void){
_start:
{
lean_object* v___x_4544_; 
v___x_4544_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4544_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__1(void){
_start:
{
lean_object* v___x_4545_; lean_object* v___x_4546_; 
v___x_4545_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__0, &l_Lean_Meta_mkInjectiveTheorems___closed__0_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__0);
v___x_4546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4546_, 0, v___x_4545_);
return v___x_4546_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__2(void){
_start:
{
lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; 
v___x_4547_ = lean_unsigned_to_nat(32u);
v___x_4548_ = lean_mk_empty_array_with_capacity(v___x_4547_);
v___x_4549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4549_, 0, v___x_4548_);
return v___x_4549_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__3(void){
_start:
{
size_t v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; 
v___x_4550_ = ((size_t)5ULL);
v___x_4551_ = lean_unsigned_to_nat(0u);
v___x_4552_ = lean_unsigned_to_nat(32u);
v___x_4553_ = lean_mk_empty_array_with_capacity(v___x_4552_);
v___x_4554_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__2, &l_Lean_Meta_mkInjectiveTheorems___closed__2_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__2);
v___x_4555_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4555_, 0, v___x_4554_);
lean_ctor_set(v___x_4555_, 1, v___x_4553_);
lean_ctor_set(v___x_4555_, 2, v___x_4551_);
lean_ctor_set(v___x_4555_, 3, v___x_4551_);
lean_ctor_set_usize(v___x_4555_, 4, v___x_4550_);
return v___x_4555_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__4(void){
_start:
{
lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; 
v___x_4556_ = lean_box(1);
v___x_4557_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_4558_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_4559_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4559_, 0, v___x_4558_);
lean_ctor_set(v___x_4559_, 1, v___x_4557_);
lean_ctor_set(v___x_4559_, 2, v___x_4556_);
return v___x_4559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems(lean_object* v_declName_4562_, lean_object* v_a_4563_, lean_object* v_a_4564_, lean_object* v_a_4565_, lean_object* v_a_4566_){
_start:
{
lean_object* v___x_4568_; lean_object* v___x_4569_; 
v___x_4568_ = lean_st_ref_get(v_a_4566_);
lean_inc(v_declName_4562_);
v___x_4569_ = l_Lean_Meta_isInductivePredicate(v_declName_4562_, v_a_4563_, v_a_4564_, v_a_4565_, v_a_4566_);
if (lean_obj_tag(v___x_4569_) == 0)
{
lean_object* v_a_4570_; lean_object* v___x_4572_; uint8_t v_isShared_4573_; uint8_t v_isSharedCheck_4768_; 
v_a_4570_ = lean_ctor_get(v___x_4569_, 0);
v_isSharedCheck_4768_ = !lean_is_exclusive(v___x_4569_);
if (v_isSharedCheck_4768_ == 0)
{
v___x_4572_ = v___x_4569_;
v_isShared_4573_ = v_isSharedCheck_4768_;
goto v_resetjp_4571_;
}
else
{
lean_inc(v_a_4570_);
lean_dec(v___x_4569_);
v___x_4572_ = lean_box(0);
v_isShared_4573_ = v_isSharedCheck_4768_;
goto v_resetjp_4571_;
}
v_resetjp_4571_:
{
lean_object* v_env_4579_; lean_object* v___f_4580_; lean_object* v___x_4581_; uint8_t v___x_4582_; lean_object* v___y_4584_; lean_object* v___y_4585_; lean_object* v___y_4586_; uint8_t v___y_4587_; lean_object* v___y_4588_; lean_object* v___y_4589_; lean_object* v_a_4590_; lean_object* v___y_4600_; lean_object* v___y_4601_; lean_object* v___y_4602_; lean_object* v___y_4603_; uint8_t v___y_4604_; lean_object* v___y_4605_; lean_object* v_a_4606_; lean_object* v___y_4609_; lean_object* v___y_4610_; lean_object* v___y_4611_; lean_object* v___y_4612_; uint8_t v___y_4613_; lean_object* v___y_4614_; lean_object* v_a_4615_; lean_object* v___y_4618_; lean_object* v___y_4619_; lean_object* v___y_4620_; lean_object* v___y_4621_; uint8_t v___y_4622_; lean_object* v___y_4623_; lean_object* v_a_4624_; lean_object* v___y_4637_; lean_object* v___y_4638_; lean_object* v___y_4639_; lean_object* v___y_4640_; lean_object* v___y_4641_; uint8_t v___y_4642_; lean_object* v_a_4643_; lean_object* v___y_4646_; lean_object* v___y_4647_; lean_object* v___y_4648_; lean_object* v___y_4649_; lean_object* v___y_4650_; uint8_t v___y_4651_; lean_object* v_a_4652_; uint8_t v___y_4655_; lean_object* v___y_4656_; lean_object* v___y_4657_; lean_object* v___y_4658_; uint8_t v___y_4659_; uint8_t v___y_4697_; uint8_t v___x_4763_; 
v_env_4579_ = lean_ctor_get(v___x_4568_, 0);
lean_inc_ref(v_env_4579_);
lean_dec(v___x_4568_);
lean_inc(v_declName_4562_);
v___f_4580_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4580_, 0, v_declName_4562_);
v___x_4581_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__2));
v___x_4582_ = 1;
v___x_4763_ = l_Lean_Environment_contains(v_env_4579_, v___x_4581_, v___x_4582_);
if (v___x_4763_ == 0)
{
v___y_4697_ = v___x_4763_;
goto v___jp_4696_;
}
else
{
lean_object* v_toCold_4764_; lean_object* v_options_4765_; lean_object* v___x_4766_; uint8_t v___x_4767_; 
v_toCold_4764_ = lean_ctor_get(v_a_4565_, 0);
v_options_4765_ = lean_ctor_get(v_toCold_4764_, 2);
v___x_4766_ = l_Lean_Meta_genInjectivity;
v___x_4767_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_4765_, v___x_4766_);
v___y_4697_ = v___x_4767_;
goto v___jp_4696_;
}
v___jp_4574_:
{
lean_object* v___x_4575_; lean_object* v___x_4577_; 
v___x_4575_ = lean_box(0);
if (v_isShared_4573_ == 0)
{
lean_ctor_set(v___x_4572_, 0, v___x_4575_);
v___x_4577_ = v___x_4572_;
goto v_reusejp_4576_;
}
else
{
lean_object* v_reuseFailAlloc_4578_; 
v_reuseFailAlloc_4578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4578_, 0, v___x_4575_);
v___x_4577_ = v_reuseFailAlloc_4578_;
goto v_reusejp_4576_;
}
v_reusejp_4576_:
{
return v___x_4577_;
}
}
v___jp_4583_:
{
lean_object* v___x_4591_; double v___x_4592_; double v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; 
v___x_4591_ = lean_io_get_num_heartbeats();
v___x_4592_ = lean_float_of_nat(v___y_4589_);
v___x_4593_ = lean_float_of_nat(v___x_4591_);
v___x_4594_ = lean_box_float(v___x_4592_);
v___x_4595_ = lean_box_float(v___x_4593_);
v___x_4596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4596_, 0, v___x_4594_);
lean_ctor_set(v___x_4596_, 1, v___x_4595_);
v___x_4597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4597_, 0, v_a_4590_);
lean_ctor_set(v___x_4597_, 1, v___x_4596_);
lean_inc_ref(v___y_4588_);
lean_inc(v___y_4586_);
v___x_4598_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v___y_4586_, v___x_4582_, v___y_4588_, v___y_4585_, v___y_4587_, v___y_4584_, v___f_4580_, v___x_4597_, v_a_4563_, v_a_4564_, v_a_4565_, v_a_4566_);
return v___x_4598_;
}
v___jp_4599_:
{
lean_object* v___x_4607_; 
v___x_4607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4607_, 0, v_a_4606_);
v___y_4584_ = v___y_4600_;
v___y_4585_ = v___y_4601_;
v___y_4586_ = v___y_4602_;
v___y_4587_ = v___y_4604_;
v___y_4588_ = v___y_4603_;
v___y_4589_ = v___y_4605_;
v_a_4590_ = v___x_4607_;
goto v___jp_4583_;
}
v___jp_4608_:
{
lean_object* v___x_4616_; 
v___x_4616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4616_, 0, v_a_4615_);
v___y_4584_ = v___y_4609_;
v___y_4585_ = v___y_4610_;
v___y_4586_ = v___y_4611_;
v___y_4587_ = v___y_4613_;
v___y_4588_ = v___y_4612_;
v___y_4589_ = v___y_4614_;
v_a_4590_ = v___x_4616_;
goto v___jp_4583_;
}
v___jp_4617_:
{
lean_object* v___x_4625_; double v___x_4626_; double v___x_4627_; double v___x_4628_; double v___x_4629_; double v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; 
v___x_4625_ = lean_io_mono_nanos_now();
v___x_4626_ = lean_float_of_nat(v___y_4619_);
v___x_4627_ = lean_float_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0);
v___x_4628_ = lean_float_div(v___x_4626_, v___x_4627_);
v___x_4629_ = lean_float_of_nat(v___x_4625_);
v___x_4630_ = lean_float_div(v___x_4629_, v___x_4627_);
v___x_4631_ = lean_box_float(v___x_4628_);
v___x_4632_ = lean_box_float(v___x_4630_);
v___x_4633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4633_, 0, v___x_4631_);
lean_ctor_set(v___x_4633_, 1, v___x_4632_);
v___x_4634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4634_, 0, v_a_4624_);
lean_ctor_set(v___x_4634_, 1, v___x_4633_);
lean_inc_ref(v___y_4623_);
lean_inc(v___y_4621_);
v___x_4635_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v___y_4621_, v___x_4582_, v___y_4623_, v___y_4620_, v___y_4622_, v___y_4618_, v___f_4580_, v___x_4634_, v_a_4563_, v_a_4564_, v_a_4565_, v_a_4566_);
return v___x_4635_;
}
v___jp_4636_:
{
lean_object* v___x_4644_; 
v___x_4644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4644_, 0, v_a_4643_);
v___y_4618_ = v___y_4637_;
v___y_4619_ = v___y_4638_;
v___y_4620_ = v___y_4639_;
v___y_4621_ = v___y_4640_;
v___y_4622_ = v___y_4642_;
v___y_4623_ = v___y_4641_;
v_a_4624_ = v___x_4644_;
goto v___jp_4617_;
}
v___jp_4645_:
{
lean_object* v___x_4653_; 
v___x_4653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4653_, 0, v_a_4652_);
v___y_4618_ = v___y_4646_;
v___y_4619_ = v___y_4647_;
v___y_4620_ = v___y_4648_;
v___y_4621_ = v___y_4649_;
v___y_4622_ = v___y_4651_;
v___y_4623_ = v___y_4650_;
v_a_4624_ = v___x_4653_;
goto v___jp_4617_;
}
v___jp_4654_:
{
lean_object* v___x_4660_; lean_object* v_a_4661_; lean_object* v___x_4662_; uint8_t v___x_4663_; 
v___x_4660_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v_a_4566_);
v_a_4661_ = lean_ctor_get(v___x_4660_, 0);
lean_inc(v_a_4661_);
lean_dec_ref(v___x_4660_);
v___x_4662_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4663_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v___y_4656_, v___x_4662_);
if (v___x_4663_ == 0)
{
lean_object* v___x_4664_; lean_object* v___x_4665_; 
v___x_4664_ = lean_io_mono_nanos_now();
v___x_4665_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4562_, v_a_4563_, v_a_4564_, v_a_4565_, v_a_4566_);
if (lean_obj_tag(v___x_4665_) == 0)
{
lean_object* v_a_4666_; uint8_t v_isUnsafe_4667_; 
v_a_4666_ = lean_ctor_get(v___x_4665_, 0);
lean_inc(v_a_4666_);
lean_dec_ref_known(v___x_4665_, 1);
v_isUnsafe_4667_ = lean_ctor_get_uint8(v_a_4666_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4667_ == 0)
{
lean_object* v_ctors_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; lean_object* v___f_4674_; lean_object* v___x_4675_; 
v_ctors_4668_ = lean_ctor_get(v_a_4666_, 4);
lean_inc(v_ctors_4668_);
lean_dec(v_a_4666_);
v___x_4669_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4670_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4671_ = lean_box(0);
v___x_4672_ = lean_box(v___y_4655_);
v___x_4673_ = lean_box(v_isUnsafe_4667_);
v___f_4674_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed), 9, 4);
lean_closure_set(v___f_4674_, 0, v___x_4672_);
lean_closure_set(v___f_4674_, 1, v___x_4673_);
lean_closure_set(v___f_4674_, 2, v_ctors_4668_);
lean_closure_set(v___f_4674_, 3, v___x_4671_);
v___x_4675_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4669_, v___x_4670_, v___f_4674_, v_a_4563_, v_a_4564_, v_a_4565_, v_a_4566_);
if (lean_obj_tag(v___x_4675_) == 0)
{
lean_object* v_a_4676_; 
v_a_4676_ = lean_ctor_get(v___x_4675_, 0);
lean_inc(v_a_4676_);
lean_dec_ref_known(v___x_4675_, 1);
v___y_4637_ = v_a_4661_;
v___y_4638_ = v___x_4664_;
v___y_4639_ = v___y_4656_;
v___y_4640_ = v___y_4657_;
v___y_4641_ = v___y_4658_;
v___y_4642_ = v___y_4659_;
v_a_4643_ = v_a_4676_;
goto v___jp_4636_;
}
else
{
lean_object* v_a_4677_; 
v_a_4677_ = lean_ctor_get(v___x_4675_, 0);
lean_inc(v_a_4677_);
lean_dec_ref_known(v___x_4675_, 1);
v___y_4646_ = v_a_4661_;
v___y_4647_ = v___x_4664_;
v___y_4648_ = v___y_4656_;
v___y_4649_ = v___y_4657_;
v___y_4650_ = v___y_4658_;
v___y_4651_ = v___y_4659_;
v_a_4652_ = v_a_4677_;
goto v___jp_4645_;
}
}
else
{
lean_object* v___x_4678_; 
lean_dec(v_a_4666_);
v___x_4678_ = lean_box(0);
v___y_4637_ = v_a_4661_;
v___y_4638_ = v___x_4664_;
v___y_4639_ = v___y_4656_;
v___y_4640_ = v___y_4657_;
v___y_4641_ = v___y_4658_;
v___y_4642_ = v___y_4659_;
v_a_4643_ = v___x_4678_;
goto v___jp_4636_;
}
}
else
{
lean_object* v_a_4679_; 
v_a_4679_ = lean_ctor_get(v___x_4665_, 0);
lean_inc(v_a_4679_);
lean_dec_ref_known(v___x_4665_, 1);
v___y_4646_ = v_a_4661_;
v___y_4647_ = v___x_4664_;
v___y_4648_ = v___y_4656_;
v___y_4649_ = v___y_4657_;
v___y_4650_ = v___y_4658_;
v___y_4651_ = v___y_4659_;
v_a_4652_ = v_a_4679_;
goto v___jp_4645_;
}
}
else
{
lean_object* v___x_4680_; lean_object* v___x_4681_; 
v___x_4680_ = lean_io_get_num_heartbeats();
v___x_4681_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4562_, v_a_4563_, v_a_4564_, v_a_4565_, v_a_4566_);
if (lean_obj_tag(v___x_4681_) == 0)
{
lean_object* v_a_4682_; uint8_t v_isUnsafe_4683_; 
v_a_4682_ = lean_ctor_get(v___x_4681_, 0);
lean_inc(v_a_4682_);
lean_dec_ref_known(v___x_4681_, 1);
v_isUnsafe_4683_ = lean_ctor_get_uint8(v_a_4682_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4683_ == 0)
{
lean_object* v_ctors_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___f_4690_; lean_object* v___x_4691_; 
v_ctors_4684_ = lean_ctor_get(v_a_4682_, 4);
lean_inc(v_ctors_4684_);
lean_dec(v_a_4682_);
v___x_4685_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4686_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4687_ = lean_box(0);
v___x_4688_ = lean_box(v___y_4655_);
v___x_4689_ = lean_box(v_isUnsafe_4683_);
v___f_4690_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed), 9, 4);
lean_closure_set(v___f_4690_, 0, v___x_4688_);
lean_closure_set(v___f_4690_, 1, v___x_4689_);
lean_closure_set(v___f_4690_, 2, v_ctors_4684_);
lean_closure_set(v___f_4690_, 3, v___x_4687_);
v___x_4691_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4685_, v___x_4686_, v___f_4690_, v_a_4563_, v_a_4564_, v_a_4565_, v_a_4566_);
if (lean_obj_tag(v___x_4691_) == 0)
{
lean_object* v_a_4692_; 
v_a_4692_ = lean_ctor_get(v___x_4691_, 0);
lean_inc(v_a_4692_);
lean_dec_ref_known(v___x_4691_, 1);
v___y_4600_ = v_a_4661_;
v___y_4601_ = v___y_4656_;
v___y_4602_ = v___y_4657_;
v___y_4603_ = v___y_4658_;
v___y_4604_ = v___y_4659_;
v___y_4605_ = v___x_4680_;
v_a_4606_ = v_a_4692_;
goto v___jp_4599_;
}
else
{
lean_object* v_a_4693_; 
v_a_4693_ = lean_ctor_get(v___x_4691_, 0);
lean_inc(v_a_4693_);
lean_dec_ref_known(v___x_4691_, 1);
v___y_4609_ = v_a_4661_;
v___y_4610_ = v___y_4656_;
v___y_4611_ = v___y_4657_;
v___y_4612_ = v___y_4658_;
v___y_4613_ = v___y_4659_;
v___y_4614_ = v___x_4680_;
v_a_4615_ = v_a_4693_;
goto v___jp_4608_;
}
}
else
{
lean_object* v___x_4694_; 
lean_dec(v_a_4682_);
v___x_4694_ = lean_box(0);
v___y_4600_ = v_a_4661_;
v___y_4601_ = v___y_4656_;
v___y_4602_ = v___y_4657_;
v___y_4603_ = v___y_4658_;
v___y_4604_ = v___y_4659_;
v___y_4605_ = v___x_4680_;
v_a_4606_ = v___x_4694_;
goto v___jp_4599_;
}
}
else
{
lean_object* v_a_4695_; 
v_a_4695_ = lean_ctor_get(v___x_4681_, 0);
lean_inc(v_a_4695_);
lean_dec_ref_known(v___x_4681_, 1);
v___y_4609_ = v_a_4661_;
v___y_4610_ = v___y_4656_;
v___y_4611_ = v___y_4657_;
v___y_4612_ = v___y_4658_;
v___y_4613_ = v___y_4659_;
v___y_4614_ = v___x_4680_;
v_a_4615_ = v_a_4695_;
goto v___jp_4608_;
}
}
}
v___jp_4696_:
{
if (v___y_4697_ == 0)
{
lean_dec_ref(v___f_4580_);
lean_dec(v_a_4570_);
lean_dec(v_declName_4562_);
goto v___jp_4574_;
}
else
{
uint8_t v___x_4698_; 
v___x_4698_ = lean_unbox(v_a_4570_);
lean_dec(v_a_4570_);
if (v___x_4698_ == 0)
{
lean_object* v_toCold_4699_; lean_object* v_options_4700_; uint8_t v_hasTrace_4701_; 
lean_del_object(v___x_4572_);
v_toCold_4699_ = lean_ctor_get(v_a_4565_, 0);
v_options_4700_ = lean_ctor_get(v_toCold_4699_, 2);
v_hasTrace_4701_ = lean_ctor_get_uint8(v_options_4700_, sizeof(void*)*1);
if (v_hasTrace_4701_ == 0)
{
lean_object* v___x_4702_; 
lean_dec_ref(v___f_4580_);
v___x_4702_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4562_, v_a_4563_, v_a_4564_, v_a_4565_, v_a_4566_);
if (lean_obj_tag(v___x_4702_) == 0)
{
lean_object* v_a_4703_; lean_object* v___x_4705_; uint8_t v_isShared_4706_; uint8_t v_isSharedCheck_4720_; 
v_a_4703_ = lean_ctor_get(v___x_4702_, 0);
v_isSharedCheck_4720_ = !lean_is_exclusive(v___x_4702_);
if (v_isSharedCheck_4720_ == 0)
{
v___x_4705_ = v___x_4702_;
v_isShared_4706_ = v_isSharedCheck_4720_;
goto v_resetjp_4704_;
}
else
{
lean_inc(v_a_4703_);
lean_dec(v___x_4702_);
v___x_4705_ = lean_box(0);
v_isShared_4706_ = v_isSharedCheck_4720_;
goto v_resetjp_4704_;
}
v_resetjp_4704_:
{
uint8_t v_isUnsafe_4707_; 
v_isUnsafe_4707_ = lean_ctor_get_uint8(v_a_4703_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4707_ == 0)
{
lean_object* v_ctors_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___f_4714_; lean_object* v___x_4715_; 
lean_del_object(v___x_4705_);
v_ctors_4708_ = lean_ctor_get(v_a_4703_, 4);
lean_inc(v_ctors_4708_);
lean_dec(v_a_4703_);
v___x_4709_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4710_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4711_ = lean_box(0);
v___x_4712_ = lean_box(v___y_4697_);
v___x_4713_ = lean_box(v_isUnsafe_4707_);
v___f_4714_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed), 9, 4);
lean_closure_set(v___f_4714_, 0, v___x_4712_);
lean_closure_set(v___f_4714_, 1, v___x_4713_);
lean_closure_set(v___f_4714_, 2, v_ctors_4708_);
lean_closure_set(v___f_4714_, 3, v___x_4711_);
v___x_4715_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4709_, v___x_4710_, v___f_4714_, v_a_4563_, v_a_4564_, v_a_4565_, v_a_4566_);
return v___x_4715_;
}
else
{
lean_object* v___x_4716_; lean_object* v___x_4718_; 
lean_dec(v_a_4703_);
v___x_4716_ = lean_box(0);
if (v_isShared_4706_ == 0)
{
lean_ctor_set(v___x_4705_, 0, v___x_4716_);
v___x_4718_ = v___x_4705_;
goto v_reusejp_4717_;
}
else
{
lean_object* v_reuseFailAlloc_4719_; 
v_reuseFailAlloc_4719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4719_, 0, v___x_4716_);
v___x_4718_ = v_reuseFailAlloc_4719_;
goto v_reusejp_4717_;
}
v_reusejp_4717_:
{
return v___x_4718_;
}
}
}
}
else
{
lean_object* v_a_4721_; lean_object* v___x_4723_; uint8_t v_isShared_4724_; uint8_t v_isSharedCheck_4728_; 
v_a_4721_ = lean_ctor_get(v___x_4702_, 0);
v_isSharedCheck_4728_ = !lean_is_exclusive(v___x_4702_);
if (v_isSharedCheck_4728_ == 0)
{
v___x_4723_ = v___x_4702_;
v_isShared_4724_ = v_isSharedCheck_4728_;
goto v_resetjp_4722_;
}
else
{
lean_inc(v_a_4721_);
lean_dec(v___x_4702_);
v___x_4723_ = lean_box(0);
v_isShared_4724_ = v_isSharedCheck_4728_;
goto v_resetjp_4722_;
}
v_resetjp_4722_:
{
lean_object* v___x_4726_; 
if (v_isShared_4724_ == 0)
{
v___x_4726_ = v___x_4723_;
goto v_reusejp_4725_;
}
else
{
lean_object* v_reuseFailAlloc_4727_; 
v_reuseFailAlloc_4727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4727_, 0, v_a_4721_);
v___x_4726_ = v_reuseFailAlloc_4727_;
goto v_reusejp_4725_;
}
v_reusejp_4725_:
{
return v___x_4726_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; uint8_t v___x_4733_; 
v_inheritedTraceOptions_4729_ = lean_ctor_get(v_toCold_4699_, 11);
v___x_4730_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_4731_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_4732_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_4733_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4729_, v_options_4700_, v___x_4732_);
if (v___x_4733_ == 0)
{
lean_object* v___x_4734_; uint8_t v___x_4735_; 
v___x_4734_ = l_Lean_trace_profiler;
v___x_4735_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_4700_, v___x_4734_);
if (v___x_4735_ == 0)
{
lean_object* v___x_4736_; 
lean_dec_ref(v___f_4580_);
v___x_4736_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4562_, v_a_4563_, v_a_4564_, v_a_4565_, v_a_4566_);
if (lean_obj_tag(v___x_4736_) == 0)
{
lean_object* v_a_4737_; lean_object* v___x_4739_; uint8_t v_isShared_4740_; uint8_t v_isSharedCheck_4754_; 
v_a_4737_ = lean_ctor_get(v___x_4736_, 0);
v_isSharedCheck_4754_ = !lean_is_exclusive(v___x_4736_);
if (v_isSharedCheck_4754_ == 0)
{
v___x_4739_ = v___x_4736_;
v_isShared_4740_ = v_isSharedCheck_4754_;
goto v_resetjp_4738_;
}
else
{
lean_inc(v_a_4737_);
lean_dec(v___x_4736_);
v___x_4739_ = lean_box(0);
v_isShared_4740_ = v_isSharedCheck_4754_;
goto v_resetjp_4738_;
}
v_resetjp_4738_:
{
uint8_t v_isUnsafe_4741_; 
v_isUnsafe_4741_ = lean_ctor_get_uint8(v_a_4737_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4741_ == 0)
{
lean_object* v_ctors_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; lean_object* v___x_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; lean_object* v___f_4748_; lean_object* v___x_4749_; 
lean_del_object(v___x_4739_);
v_ctors_4742_ = lean_ctor_get(v_a_4737_, 4);
lean_inc(v_ctors_4742_);
lean_dec(v_a_4737_);
v___x_4743_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4744_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4745_ = lean_box(0);
v___x_4746_ = lean_box(v___y_4697_);
v___x_4747_ = lean_box(v_isUnsafe_4741_);
v___f_4748_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed), 9, 4);
lean_closure_set(v___f_4748_, 0, v___x_4746_);
lean_closure_set(v___f_4748_, 1, v___x_4747_);
lean_closure_set(v___f_4748_, 2, v_ctors_4742_);
lean_closure_set(v___f_4748_, 3, v___x_4745_);
v___x_4749_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4743_, v___x_4744_, v___f_4748_, v_a_4563_, v_a_4564_, v_a_4565_, v_a_4566_);
return v___x_4749_;
}
else
{
lean_object* v___x_4750_; lean_object* v___x_4752_; 
lean_dec(v_a_4737_);
v___x_4750_ = lean_box(0);
if (v_isShared_4740_ == 0)
{
lean_ctor_set(v___x_4739_, 0, v___x_4750_);
v___x_4752_ = v___x_4739_;
goto v_reusejp_4751_;
}
else
{
lean_object* v_reuseFailAlloc_4753_; 
v_reuseFailAlloc_4753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4753_, 0, v___x_4750_);
v___x_4752_ = v_reuseFailAlloc_4753_;
goto v_reusejp_4751_;
}
v_reusejp_4751_:
{
return v___x_4752_;
}
}
}
}
else
{
lean_object* v_a_4755_; lean_object* v___x_4757_; uint8_t v_isShared_4758_; uint8_t v_isSharedCheck_4762_; 
v_a_4755_ = lean_ctor_get(v___x_4736_, 0);
v_isSharedCheck_4762_ = !lean_is_exclusive(v___x_4736_);
if (v_isSharedCheck_4762_ == 0)
{
v___x_4757_ = v___x_4736_;
v_isShared_4758_ = v_isSharedCheck_4762_;
goto v_resetjp_4756_;
}
else
{
lean_inc(v_a_4755_);
lean_dec(v___x_4736_);
v___x_4757_ = lean_box(0);
v_isShared_4758_ = v_isSharedCheck_4762_;
goto v_resetjp_4756_;
}
v_resetjp_4756_:
{
lean_object* v___x_4760_; 
if (v_isShared_4758_ == 0)
{
v___x_4760_ = v___x_4757_;
goto v_reusejp_4759_;
}
else
{
lean_object* v_reuseFailAlloc_4761_; 
v_reuseFailAlloc_4761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4761_, 0, v_a_4755_);
v___x_4760_ = v_reuseFailAlloc_4761_;
goto v_reusejp_4759_;
}
v_reusejp_4759_:
{
return v___x_4760_;
}
}
}
}
else
{
v___y_4655_ = v___y_4697_;
v___y_4656_ = v_options_4700_;
v___y_4657_ = v___x_4730_;
v___y_4658_ = v___x_4731_;
v___y_4659_ = v___x_4733_;
goto v___jp_4654_;
}
}
else
{
v___y_4655_ = v___y_4697_;
v___y_4656_ = v_options_4700_;
v___y_4657_ = v___x_4730_;
v___y_4658_ = v___x_4731_;
v___y_4659_ = v___x_4733_;
goto v___jp_4654_;
}
}
}
else
{
lean_dec_ref(v___f_4580_);
lean_dec(v_declName_4562_);
goto v___jp_4574_;
}
}
}
}
}
else
{
lean_object* v_a_4769_; lean_object* v___x_4771_; uint8_t v_isShared_4772_; uint8_t v_isSharedCheck_4776_; 
lean_dec(v___x_4568_);
lean_dec(v_declName_4562_);
v_a_4769_ = lean_ctor_get(v___x_4569_, 0);
v_isSharedCheck_4776_ = !lean_is_exclusive(v___x_4569_);
if (v_isSharedCheck_4776_ == 0)
{
v___x_4771_ = v___x_4569_;
v_isShared_4772_ = v_isSharedCheck_4776_;
goto v_resetjp_4770_;
}
else
{
lean_inc(v_a_4769_);
lean_dec(v___x_4569_);
v___x_4771_ = lean_box(0);
v_isShared_4772_ = v_isSharedCheck_4776_;
goto v_resetjp_4770_;
}
v_resetjp_4770_:
{
lean_object* v___x_4774_; 
if (v_isShared_4772_ == 0)
{
v___x_4774_ = v___x_4771_;
goto v_reusejp_4773_;
}
else
{
lean_object* v_reuseFailAlloc_4775_; 
v_reuseFailAlloc_4775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4775_, 0, v_a_4769_);
v___x_4774_ = v_reuseFailAlloc_4775_;
goto v_reusejp_4773_;
}
v_reusejp_4773_:
{
return v___x_4774_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___boxed(lean_object* v_declName_4777_, lean_object* v_a_4778_, lean_object* v_a_4779_, lean_object* v_a_4780_, lean_object* v_a_4781_, lean_object* v_a_4782_){
_start:
{
lean_object* v_res_4783_; 
v_res_4783_ = l_Lean_Meta_mkInjectiveTheorems(v_declName_4777_, v_a_4778_, v_a_4779_, v_a_4780_, v_a_4781_);
lean_dec(v_a_4781_);
lean_dec_ref(v_a_4780_);
lean_dec(v_a_4779_);
lean_dec_ref(v_a_4778_);
return v_res_4783_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3(uint8_t v___y_4784_, uint8_t v___x_4785_, lean_object* v_as_4786_, lean_object* v_as_x27_4787_, lean_object* v_b_4788_, lean_object* v_a_4789_, lean_object* v___y_4790_, lean_object* v___y_4791_, lean_object* v___y_4792_, lean_object* v___y_4793_){
_start:
{
lean_object* v___x_4795_; 
v___x_4795_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___y_4784_, v___x_4785_, v_as_x27_4787_, v_b_4788_, v___y_4790_, v___y_4791_, v___y_4792_, v___y_4793_);
return v___x_4795_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___boxed(lean_object* v___y_4796_, lean_object* v___x_4797_, lean_object* v_as_4798_, lean_object* v_as_x27_4799_, lean_object* v_b_4800_, lean_object* v_a_4801_, lean_object* v___y_4802_, lean_object* v___y_4803_, lean_object* v___y_4804_, lean_object* v___y_4805_, lean_object* v___y_4806_){
_start:
{
uint8_t v___y_17444__boxed_4807_; uint8_t v___x_17445__boxed_4808_; lean_object* v_res_4809_; 
v___y_17444__boxed_4807_ = lean_unbox(v___y_4796_);
v___x_17445__boxed_4808_ = lean_unbox(v___x_4797_);
v_res_4809_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3(v___y_17444__boxed_4807_, v___x_17445__boxed_4808_, v_as_4798_, v_as_x27_4799_, v_b_4800_, v_a_4801_, v___y_4802_, v___y_4803_, v___y_4804_, v___y_4805_);
lean_dec(v___y_4805_);
lean_dec_ref(v___y_4804_);
lean_dec(v___y_4803_);
lean_dec_ref(v___y_4802_);
lean_dec(v_as_x27_4799_);
lean_dec(v_as_4798_);
return v_res_4809_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4850_; lean_object* v___x_4851_; lean_object* v___x_4852_; 
v___x_4850_ = lean_unsigned_to_nat(4172903888u);
v___x_4851_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_));
v___x_4852_ = l_Lean_Name_num___override(v___x_4851_, v___x_4850_);
return v___x_4852_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; 
v___x_4854_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_));
v___x_4855_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4856_ = l_Lean_Name_str___override(v___x_4855_, v___x_4854_);
return v___x_4856_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4858_; lean_object* v___x_4859_; lean_object* v___x_4860_; 
v___x_4858_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_));
v___x_4859_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4860_ = l_Lean_Name_str___override(v___x_4859_, v___x_4858_);
return v___x_4860_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; 
v___x_4861_ = lean_unsigned_to_nat(2u);
v___x_4862_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4863_ = l_Lean_Name_num___override(v___x_4862_, v___x_4861_);
return v___x_4863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4865_; uint8_t v___x_4866_; lean_object* v___x_4867_; lean_object* v___x_4868_; 
v___x_4865_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_4866_ = 0;
v___x_4867_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4868_ = l_Lean_registerTraceClass(v___x_4865_, v___x_4866_, v___x_4867_);
return v___x_4868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2____boxed(lean_object* v_a_4869_){
_start:
{
lean_object* v_res_4870_; 
v_res_4870_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_();
return v_res_4870_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(lean_object* v_a_4871_, lean_object* v_b_4872_){
_start:
{
lean_object* v_array_4873_; lean_object* v_start_4874_; lean_object* v_stop_4875_; lean_object* v___x_4877_; uint8_t v_isShared_4878_; uint8_t v_isSharedCheck_4888_; 
v_array_4873_ = lean_ctor_get(v_a_4871_, 0);
v_start_4874_ = lean_ctor_get(v_a_4871_, 1);
v_stop_4875_ = lean_ctor_get(v_a_4871_, 2);
v_isSharedCheck_4888_ = !lean_is_exclusive(v_a_4871_);
if (v_isSharedCheck_4888_ == 0)
{
v___x_4877_ = v_a_4871_;
v_isShared_4878_ = v_isSharedCheck_4888_;
goto v_resetjp_4876_;
}
else
{
lean_inc(v_stop_4875_);
lean_inc(v_start_4874_);
lean_inc(v_array_4873_);
lean_dec(v_a_4871_);
v___x_4877_ = lean_box(0);
v_isShared_4878_ = v_isSharedCheck_4888_;
goto v_resetjp_4876_;
}
v_resetjp_4876_:
{
uint8_t v___x_4879_; 
v___x_4879_ = lean_nat_dec_lt(v_start_4874_, v_stop_4875_);
if (v___x_4879_ == 0)
{
lean_del_object(v___x_4877_);
lean_dec(v_stop_4875_);
lean_dec(v_start_4874_);
lean_dec_ref(v_array_4873_);
return v_b_4872_;
}
else
{
lean_object* v___x_4880_; lean_object* v___x_4881_; lean_object* v___x_4883_; 
v___x_4880_ = lean_unsigned_to_nat(1u);
v___x_4881_ = lean_nat_add(v_start_4874_, v___x_4880_);
lean_inc_ref(v_array_4873_);
if (v_isShared_4878_ == 0)
{
lean_ctor_set(v___x_4877_, 1, v___x_4881_);
v___x_4883_ = v___x_4877_;
goto v_reusejp_4882_;
}
else
{
lean_object* v_reuseFailAlloc_4887_; 
v_reuseFailAlloc_4887_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4887_, 0, v_array_4873_);
lean_ctor_set(v_reuseFailAlloc_4887_, 1, v___x_4881_);
lean_ctor_set(v_reuseFailAlloc_4887_, 2, v_stop_4875_);
v___x_4883_ = v_reuseFailAlloc_4887_;
goto v_reusejp_4882_;
}
v_reusejp_4882_:
{
lean_object* v___x_4884_; lean_object* v___x_4885_; 
v___x_4884_ = lean_array_fget(v_array_4873_, v_start_4874_);
lean_dec(v_start_4874_);
lean_dec_ref(v_array_4873_);
v___x_4885_ = lean_array_push(v_b_4872_, v___x_4884_);
v_a_4871_ = v___x_4883_;
v_b_4872_ = v___x_4885_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_4889_; 
v___x_4889_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4889_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_4890_; lean_object* v___x_4891_; 
v___x_4890_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_4891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4891_, 0, v___x_4890_);
return v___x_4891_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_4892_; lean_object* v___x_4893_; lean_object* v___x_4894_; 
v___x_4892_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
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
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_4895_; lean_object* v___x_4896_; lean_object* v___x_4897_; lean_object* v___x_4898_; 
v___x_4895_ = lean_box(1);
v___x_4896_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_4897_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_4898_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4898_, 0, v___x_4897_);
lean_ctor_set(v___x_4898_, 1, v___x_4896_);
lean_ctor_set(v___x_4898_, 2, v___x_4895_);
return v___x_4898_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_4900_; lean_object* v___x_4901_; 
v___x_4900_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4));
v___x_4901_ = l_Lean_stringToMessageData(v___x_4900_);
return v___x_4901_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_4903_; lean_object* v___x_4904_; 
v___x_4903_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_4904_ = l_Lean_stringToMessageData(v___x_4903_);
return v___x_4904_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_4906_; lean_object* v___x_4907_; 
v___x_4906_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_4907_ = l_Lean_stringToMessageData(v___x_4906_);
return v___x_4907_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_4909_; lean_object* v___x_4910_; 
v___x_4909_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_4910_ = l_Lean_stringToMessageData(v___x_4909_);
return v___x_4910_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_4912_; lean_object* v___x_4913_; 
v___x_4912_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_4913_ = l_Lean_stringToMessageData(v___x_4912_);
return v___x_4913_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15(void){
_start:
{
lean_object* v___x_4915_; lean_object* v___x_4916_; 
v___x_4915_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14));
v___x_4916_ = l_Lean_stringToMessageData(v___x_4915_);
return v___x_4916_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17(void){
_start:
{
lean_object* v___x_4918_; lean_object* v___x_4919_; 
v___x_4918_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16));
v___x_4919_ = l_Lean_stringToMessageData(v___x_4918_);
return v___x_4919_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_4920_, lean_object* v_declHint_4921_, lean_object* v___y_4922_){
_start:
{
lean_object* v___x_4924_; lean_object* v_env_4925_; uint8_t v___x_4926_; 
v___x_4924_ = lean_st_ref_get(v___y_4922_);
v_env_4925_ = lean_ctor_get(v___x_4924_, 0);
lean_inc_ref(v_env_4925_);
lean_dec(v___x_4924_);
v___x_4926_ = l_Lean_Name_isAnonymous(v_declHint_4921_);
if (v___x_4926_ == 0)
{
uint8_t v_isExporting_4927_; 
v_isExporting_4927_ = lean_ctor_get_uint8(v_env_4925_, sizeof(void*)*8);
if (v_isExporting_4927_ == 0)
{
lean_object* v___x_4928_; 
lean_dec_ref(v_env_4925_);
lean_dec(v_declHint_4921_);
v___x_4928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4928_, 0, v_msg_4920_);
return v___x_4928_;
}
else
{
lean_object* v___x_4929_; uint8_t v___x_4930_; 
lean_inc_ref(v_env_4925_);
v___x_4929_ = l_Lean_Environment_setExporting(v_env_4925_, v___x_4926_);
lean_inc(v_declHint_4921_);
lean_inc_ref(v___x_4929_);
v___x_4930_ = l_Lean_Environment_contains(v___x_4929_, v_declHint_4921_, v_isExporting_4927_);
if (v___x_4930_ == 0)
{
lean_object* v___x_4931_; 
lean_dec_ref(v___x_4929_);
lean_dec_ref(v_env_4925_);
lean_dec(v_declHint_4921_);
v___x_4931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4931_, 0, v_msg_4920_);
return v___x_4931_;
}
else
{
lean_object* v___x_4932_; lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; lean_object* v_c_4937_; lean_object* v___x_4938_; 
v___x_4932_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_4933_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_4934_ = l_Lean_Options_empty;
v___x_4935_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4935_, 0, v___x_4929_);
lean_ctor_set(v___x_4935_, 1, v___x_4932_);
lean_ctor_set(v___x_4935_, 2, v___x_4933_);
lean_ctor_set(v___x_4935_, 3, v___x_4934_);
lean_inc(v_declHint_4921_);
v___x_4936_ = l_Lean_MessageData_ofConstName(v_declHint_4921_, v___x_4926_);
v_c_4937_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_4937_, 0, v___x_4935_);
lean_ctor_set(v_c_4937_, 1, v___x_4936_);
v___x_4938_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4925_, v_declHint_4921_);
if (lean_obj_tag(v___x_4938_) == 0)
{
lean_object* v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; lean_object* v___x_4945_; 
lean_dec_ref(v_env_4925_);
lean_dec(v_declHint_4921_);
v___x_4939_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_4940_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4940_, 0, v___x_4939_);
lean_ctor_set(v___x_4940_, 1, v_c_4937_);
v___x_4941_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_4942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4942_, 0, v___x_4940_);
lean_ctor_set(v___x_4942_, 1, v___x_4941_);
v___x_4943_ = l_Lean_MessageData_note(v___x_4942_);
v___x_4944_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4944_, 0, v_msg_4920_);
lean_ctor_set(v___x_4944_, 1, v___x_4943_);
v___x_4945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4945_, 0, v___x_4944_);
return v___x_4945_;
}
else
{
lean_object* v_val_4946_; lean_object* v___x_4948_; uint8_t v_isShared_4949_; uint8_t v_isSharedCheck_4981_; 
v_val_4946_ = lean_ctor_get(v___x_4938_, 0);
v_isSharedCheck_4981_ = !lean_is_exclusive(v___x_4938_);
if (v_isSharedCheck_4981_ == 0)
{
v___x_4948_ = v___x_4938_;
v_isShared_4949_ = v_isSharedCheck_4981_;
goto v_resetjp_4947_;
}
else
{
lean_inc(v_val_4946_);
lean_dec(v___x_4938_);
v___x_4948_ = lean_box(0);
v_isShared_4949_ = v_isSharedCheck_4981_;
goto v_resetjp_4947_;
}
v_resetjp_4947_:
{
lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; lean_object* v_mod_4953_; uint8_t v___x_4954_; 
v___x_4950_ = lean_box(0);
v___x_4951_ = l_Lean_Environment_header(v_env_4925_);
lean_dec_ref(v_env_4925_);
v___x_4952_ = l_Lean_EnvironmentHeader_moduleNames(v___x_4951_);
v_mod_4953_ = lean_array_get(v___x_4950_, v___x_4952_, v_val_4946_);
lean_dec(v_val_4946_);
lean_dec_ref(v___x_4952_);
v___x_4954_ = l_Lean_isPrivateName(v_declHint_4921_);
lean_dec(v_declHint_4921_);
if (v___x_4954_ == 0)
{
lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; lean_object* v___x_4963_; lean_object* v___x_4964_; lean_object* v___x_4966_; 
v___x_4955_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_4956_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4956_, 0, v___x_4955_);
lean_ctor_set(v___x_4956_, 1, v_c_4937_);
v___x_4957_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_4958_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4958_, 0, v___x_4956_);
lean_ctor_set(v___x_4958_, 1, v___x_4957_);
v___x_4959_ = l_Lean_MessageData_ofName(v_mod_4953_);
v___x_4960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4960_, 0, v___x_4958_);
lean_ctor_set(v___x_4960_, 1, v___x_4959_);
v___x_4961_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_4962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4962_, 0, v___x_4960_);
lean_ctor_set(v___x_4962_, 1, v___x_4961_);
v___x_4963_ = l_Lean_MessageData_note(v___x_4962_);
v___x_4964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4964_, 0, v_msg_4920_);
lean_ctor_set(v___x_4964_, 1, v___x_4963_);
if (v_isShared_4949_ == 0)
{
lean_ctor_set_tag(v___x_4948_, 0);
lean_ctor_set(v___x_4948_, 0, v___x_4964_);
v___x_4966_ = v___x_4948_;
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
v___x_4968_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_4969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4969_, 0, v___x_4968_);
lean_ctor_set(v___x_4969_, 1, v_c_4937_);
v___x_4970_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_4971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4971_, 0, v___x_4969_);
lean_ctor_set(v___x_4971_, 1, v___x_4970_);
v___x_4972_ = l_Lean_MessageData_ofName(v_mod_4953_);
v___x_4973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4973_, 0, v___x_4971_);
lean_ctor_set(v___x_4973_, 1, v___x_4972_);
v___x_4974_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_4975_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4975_, 0, v___x_4973_);
lean_ctor_set(v___x_4975_, 1, v___x_4974_);
v___x_4976_ = l_Lean_MessageData_note(v___x_4975_);
v___x_4977_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4977_, 0, v_msg_4920_);
lean_ctor_set(v___x_4977_, 1, v___x_4976_);
if (v_isShared_4949_ == 0)
{
lean_ctor_set_tag(v___x_4948_, 0);
lean_ctor_set(v___x_4948_, 0, v___x_4977_);
v___x_4979_ = v___x_4948_;
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
lean_dec_ref(v_env_4925_);
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
lean_object* v_toCold_5021_; lean_object* v_currRecDepth_5022_; lean_object* v_ref_5023_; uint8_t v_diag_5024_; uint8_t v_suppressElabErrors_5025_; lean_object* v_ref_5026_; lean_object* v___x_5027_; lean_object* v___x_5028_; 
v_toCold_5021_ = lean_ctor_get(v___y_5018_, 0);
v_currRecDepth_5022_ = lean_ctor_get(v___y_5018_, 1);
v_ref_5023_ = lean_ctor_get(v___y_5018_, 2);
v_diag_5024_ = lean_ctor_get_uint8(v___y_5018_, sizeof(void*)*3);
v_suppressElabErrors_5025_ = lean_ctor_get_uint8(v___y_5018_, sizeof(void*)*3 + 1);
v_ref_5026_ = l_Lean_replaceRef(v_ref_5014_, v_ref_5023_);
lean_inc(v_currRecDepth_5022_);
lean_inc_ref(v_toCold_5021_);
v___x_5027_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5027_, 0, v_toCold_5021_);
lean_ctor_set(v___x_5027_, 1, v_currRecDepth_5022_);
lean_ctor_set(v___x_5027_, 2, v_ref_5026_);
lean_ctor_set_uint8(v___x_5027_, sizeof(void*)*3, v_diag_5024_);
lean_ctor_set_uint8(v___x_5027_, sizeof(void*)*3 + 1, v_suppressElabErrors_5025_);
v___x_5028_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v_msg_5015_, v___y_5016_, v___y_5017_, v___x_5027_, v___y_5019_);
lean_dec_ref_known(v___x_5027_, 3);
return v___x_5028_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_5029_, lean_object* v_msg_5030_, lean_object* v___y_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_, lean_object* v___y_5034_, lean_object* v___y_5035_){
_start:
{
lean_object* v_res_5036_; 
v_res_5036_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5029_, v_msg_5030_, v___y_5031_, v___y_5032_, v___y_5033_, v___y_5034_);
lean_dec(v___y_5034_);
lean_dec_ref(v___y_5033_);
lean_dec(v___y_5032_);
lean_dec_ref(v___y_5031_);
lean_dec(v_ref_5029_);
return v_res_5036_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_5037_, lean_object* v_msg_5038_, lean_object* v_declHint_5039_, lean_object* v___y_5040_, lean_object* v___y_5041_, lean_object* v___y_5042_, lean_object* v___y_5043_){
_start:
{
lean_object* v___x_5045_; lean_object* v_a_5046_; lean_object* v___x_5047_; 
v___x_5045_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_5038_, v_declHint_5039_, v___y_5040_, v___y_5041_, v___y_5042_, v___y_5043_);
v_a_5046_ = lean_ctor_get(v___x_5045_, 0);
lean_inc(v_a_5046_);
lean_dec_ref(v___x_5045_);
v___x_5047_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5037_, v_a_5046_, v___y_5040_, v___y_5041_, v___y_5042_, v___y_5043_);
return v___x_5047_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_5048_, lean_object* v_msg_5049_, lean_object* v_declHint_5050_, lean_object* v___y_5051_, lean_object* v___y_5052_, lean_object* v___y_5053_, lean_object* v___y_5054_, lean_object* v___y_5055_){
_start:
{
lean_object* v_res_5056_; 
v_res_5056_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5048_, v_msg_5049_, v_declHint_5050_, v___y_5051_, v___y_5052_, v___y_5053_, v___y_5054_);
lean_dec(v___y_5054_);
lean_dec_ref(v___y_5053_);
lean_dec(v___y_5052_);
lean_dec_ref(v___y_5051_);
lean_dec(v_ref_5048_);
return v_res_5056_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_5058_; lean_object* v___x_5059_; 
v___x_5058_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_5059_ = l_Lean_stringToMessageData(v___x_5058_);
return v___x_5059_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_5060_, lean_object* v_constName_5061_, lean_object* v___y_5062_, lean_object* v___y_5063_, lean_object* v___y_5064_, lean_object* v___y_5065_){
_start:
{
lean_object* v___x_5067_; uint8_t v___x_5068_; lean_object* v___x_5069_; lean_object* v___x_5070_; lean_object* v___x_5071_; lean_object* v___x_5072_; lean_object* v___x_5073_; 
v___x_5067_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_5068_ = 0;
lean_inc(v_constName_5061_);
v___x_5069_ = l_Lean_MessageData_ofConstName(v_constName_5061_, v___x_5068_);
v___x_5070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5070_, 0, v___x_5067_);
lean_ctor_set(v___x_5070_, 1, v___x_5069_);
v___x_5071_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_5072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5072_, 0, v___x_5070_);
lean_ctor_set(v___x_5072_, 1, v___x_5071_);
v___x_5073_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5060_, v___x_5072_, v_constName_5061_, v___y_5062_, v___y_5063_, v___y_5064_, v___y_5065_);
return v___x_5073_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_5074_, lean_object* v_constName_5075_, lean_object* v___y_5076_, lean_object* v___y_5077_, lean_object* v___y_5078_, lean_object* v___y_5079_, lean_object* v___y_5080_){
_start:
{
lean_object* v_res_5081_; 
v_res_5081_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(v_ref_5074_, v_constName_5075_, v___y_5076_, v___y_5077_, v___y_5078_, v___y_5079_);
lean_dec(v___y_5079_);
lean_dec_ref(v___y_5078_);
lean_dec(v___y_5077_);
lean_dec_ref(v___y_5076_);
lean_dec(v_ref_5074_);
return v_res_5081_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(lean_object* v_constName_5082_, lean_object* v___y_5083_, lean_object* v___y_5084_, lean_object* v___y_5085_, lean_object* v___y_5086_){
_start:
{
lean_object* v_ref_5088_; lean_object* v___x_5089_; 
v_ref_5088_ = lean_ctor_get(v___y_5085_, 2);
v___x_5089_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(v_ref_5088_, v_constName_5082_, v___y_5083_, v___y_5084_, v___y_5085_, v___y_5086_);
return v___x_5089_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_constName_5090_, lean_object* v___y_5091_, lean_object* v___y_5092_, lean_object* v___y_5093_, lean_object* v___y_5094_, lean_object* v___y_5095_){
_start:
{
lean_object* v_res_5096_; 
v_res_5096_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(v_constName_5090_, v___y_5091_, v___y_5092_, v___y_5093_, v___y_5094_);
lean_dec(v___y_5094_);
lean_dec_ref(v___y_5093_);
lean_dec(v___y_5092_);
lean_dec_ref(v___y_5091_);
return v_res_5096_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(lean_object* v_constName_5097_, lean_object* v___y_5098_, lean_object* v___y_5099_, lean_object* v___y_5100_, lean_object* v___y_5101_){
_start:
{
lean_object* v___x_5103_; lean_object* v_env_5104_; uint8_t v___x_5105_; lean_object* v___x_5106_; 
v___x_5103_ = lean_st_ref_get(v___y_5101_);
v_env_5104_ = lean_ctor_get(v___x_5103_, 0);
lean_inc_ref(v_env_5104_);
lean_dec(v___x_5103_);
v___x_5105_ = 0;
lean_inc(v_constName_5097_);
v___x_5106_ = l_Lean_Environment_find_x3f(v_env_5104_, v_constName_5097_, v___x_5105_);
if (lean_obj_tag(v___x_5106_) == 0)
{
lean_object* v___x_5107_; 
v___x_5107_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(v_constName_5097_, v___y_5098_, v___y_5099_, v___y_5100_, v___y_5101_);
return v___x_5107_;
}
else
{
lean_object* v_val_5108_; lean_object* v___x_5110_; uint8_t v_isShared_5111_; uint8_t v_isSharedCheck_5115_; 
lean_dec(v_constName_5097_);
v_val_5108_ = lean_ctor_get(v___x_5106_, 0);
v_isSharedCheck_5115_ = !lean_is_exclusive(v___x_5106_);
if (v_isSharedCheck_5115_ == 0)
{
v___x_5110_ = v___x_5106_;
v_isShared_5111_ = v_isSharedCheck_5115_;
goto v_resetjp_5109_;
}
else
{
lean_inc(v_val_5108_);
lean_dec(v___x_5106_);
v___x_5110_ = lean_box(0);
v_isShared_5111_ = v_isSharedCheck_5115_;
goto v_resetjp_5109_;
}
v_resetjp_5109_:
{
lean_object* v___x_5113_; 
if (v_isShared_5111_ == 0)
{
lean_ctor_set_tag(v___x_5110_, 0);
v___x_5113_ = v___x_5110_;
goto v_reusejp_5112_;
}
else
{
lean_object* v_reuseFailAlloc_5114_; 
v_reuseFailAlloc_5114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5114_, 0, v_val_5108_);
v___x_5113_ = v_reuseFailAlloc_5114_;
goto v_reusejp_5112_;
}
v_reusejp_5112_:
{
return v___x_5113_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0___boxed(lean_object* v_constName_5116_, lean_object* v___y_5117_, lean_object* v___y_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_){
_start:
{
lean_object* v_res_5122_; 
v_res_5122_ = l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(v_constName_5116_, v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_);
lean_dec(v___y_5120_);
lean_dec_ref(v___y_5119_);
lean_dec(v___y_5118_);
lean_dec_ref(v___y_5117_);
return v_res_5122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(lean_object* v_x_5125_, lean_object* v_x_5126_, lean_object* v_x_5127_, lean_object* v___y_5128_, lean_object* v___y_5129_, lean_object* v___y_5130_, lean_object* v___y_5131_){
_start:
{
if (lean_obj_tag(v_x_5125_) == 5)
{
lean_object* v_fn_5133_; lean_object* v_arg_5134_; lean_object* v___x_5135_; lean_object* v___x_5136_; lean_object* v___x_5137_; 
v_fn_5133_ = lean_ctor_get(v_x_5125_, 0);
lean_inc_ref(v_fn_5133_);
v_arg_5134_ = lean_ctor_get(v_x_5125_, 1);
lean_inc_ref(v_arg_5134_);
lean_dec_ref_known(v_x_5125_, 2);
v___x_5135_ = lean_array_set(v_x_5126_, v_x_5127_, v_arg_5134_);
v___x_5136_ = lean_unsigned_to_nat(1u);
v___x_5137_ = lean_nat_sub(v_x_5127_, v___x_5136_);
lean_dec(v_x_5127_);
v_x_5125_ = v_fn_5133_;
v_x_5126_ = v___x_5135_;
v_x_5127_ = v___x_5137_;
goto _start;
}
else
{
lean_dec(v_x_5127_);
if (lean_obj_tag(v_x_5125_) == 4)
{
lean_object* v_declName_5139_; lean_object* v___x_5140_; 
v_declName_5139_ = lean_ctor_get(v_x_5125_, 0);
lean_inc(v_declName_5139_);
lean_dec_ref_known(v_x_5125_, 2);
v___x_5140_ = l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(v_declName_5139_, v___y_5128_, v___y_5129_, v___y_5130_, v___y_5131_);
if (lean_obj_tag(v___x_5140_) == 0)
{
lean_object* v_a_5141_; lean_object* v___x_5143_; uint8_t v_isShared_5144_; uint8_t v_isSharedCheck_5172_; 
v_a_5141_ = lean_ctor_get(v___x_5140_, 0);
v_isSharedCheck_5172_ = !lean_is_exclusive(v___x_5140_);
if (v_isSharedCheck_5172_ == 0)
{
v___x_5143_ = v___x_5140_;
v_isShared_5144_ = v_isSharedCheck_5172_;
goto v_resetjp_5142_;
}
else
{
lean_inc(v_a_5141_);
lean_dec(v___x_5140_);
v___x_5143_ = lean_box(0);
v_isShared_5144_ = v_isSharedCheck_5172_;
goto v_resetjp_5142_;
}
v_resetjp_5142_:
{
lean_object* v_lower_5146_; lean_object* v_upper_5147_; 
if (lean_obj_tag(v_a_5141_) == 5)
{
lean_object* v_val_5155_; lean_object* v___x_5157_; uint8_t v_isShared_5158_; uint8_t v_isSharedCheck_5169_; 
v_val_5155_ = lean_ctor_get(v_a_5141_, 0);
v_isSharedCheck_5169_ = !lean_is_exclusive(v_a_5141_);
if (v_isSharedCheck_5169_ == 0)
{
v___x_5157_ = v_a_5141_;
v_isShared_5158_ = v_isSharedCheck_5169_;
goto v_resetjp_5156_;
}
else
{
lean_inc(v_val_5155_);
lean_dec(v_a_5141_);
v___x_5157_ = lean_box(0);
v_isShared_5158_ = v_isSharedCheck_5169_;
goto v_resetjp_5156_;
}
v_resetjp_5156_:
{
lean_object* v_numParams_5159_; lean_object* v_numIndices_5160_; lean_object* v___x_5161_; uint8_t v___x_5162_; 
v_numParams_5159_ = lean_ctor_get(v_val_5155_, 1);
lean_inc(v_numParams_5159_);
v_numIndices_5160_ = lean_ctor_get(v_val_5155_, 2);
lean_inc(v_numIndices_5160_);
lean_dec_ref(v_val_5155_);
v___x_5161_ = lean_unsigned_to_nat(0u);
v___x_5162_ = lean_nat_dec_eq(v_numIndices_5160_, v___x_5161_);
lean_dec(v_numIndices_5160_);
if (v___x_5162_ == 0)
{
lean_object* v___x_5163_; uint8_t v___x_5164_; 
lean_del_object(v___x_5157_);
v___x_5163_ = lean_array_get_size(v_x_5126_);
v___x_5164_ = lean_nat_dec_le(v_numParams_5159_, v___x_5161_);
if (v___x_5164_ == 0)
{
v_lower_5146_ = v_numParams_5159_;
v_upper_5147_ = v___x_5163_;
goto v___jp_5145_;
}
else
{
lean_dec(v_numParams_5159_);
v_lower_5146_ = v___x_5161_;
v_upper_5147_ = v___x_5163_;
goto v___jp_5145_;
}
}
else
{
lean_object* v___x_5165_; lean_object* v___x_5167_; 
lean_dec(v_numParams_5159_);
lean_del_object(v___x_5143_);
lean_dec_ref(v_x_5126_);
v___x_5165_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2___closed__0));
if (v_isShared_5158_ == 0)
{
lean_ctor_set_tag(v___x_5157_, 0);
lean_ctor_set(v___x_5157_, 0, v___x_5165_);
v___x_5167_ = v___x_5157_;
goto v_reusejp_5166_;
}
else
{
lean_object* v_reuseFailAlloc_5168_; 
v_reuseFailAlloc_5168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5168_, 0, v___x_5165_);
v___x_5167_ = v_reuseFailAlloc_5168_;
goto v_reusejp_5166_;
}
v_reusejp_5166_:
{
return v___x_5167_;
}
}
}
}
else
{
lean_object* v___x_5170_; lean_object* v___x_5171_; 
lean_del_object(v___x_5143_);
lean_dec(v_a_5141_);
lean_dec_ref(v_x_5126_);
v___x_5170_ = lean_box(0);
v___x_5171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5171_, 0, v___x_5170_);
return v___x_5171_;
}
v___jp_5145_:
{
lean_object* v___x_5148_; lean_object* v___x_5149_; lean_object* v___x_5150_; lean_object* v___x_5151_; lean_object* v___x_5153_; 
v___x_5148_ = l_Array_toSubarray___redArg(v_x_5126_, v_lower_5146_, v_upper_5147_);
v___x_5149_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_5150_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(v___x_5148_, v___x_5149_);
v___x_5151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5151_, 0, v___x_5150_);
if (v_isShared_5144_ == 0)
{
lean_ctor_set(v___x_5143_, 0, v___x_5151_);
v___x_5153_ = v___x_5143_;
goto v_reusejp_5152_;
}
else
{
lean_object* v_reuseFailAlloc_5154_; 
v_reuseFailAlloc_5154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5154_, 0, v___x_5151_);
v___x_5153_ = v_reuseFailAlloc_5154_;
goto v_reusejp_5152_;
}
v_reusejp_5152_:
{
return v___x_5153_;
}
}
}
}
else
{
lean_object* v_a_5173_; lean_object* v___x_5175_; uint8_t v_isShared_5176_; uint8_t v_isSharedCheck_5180_; 
lean_dec_ref(v_x_5126_);
v_a_5173_ = lean_ctor_get(v___x_5140_, 0);
v_isSharedCheck_5180_ = !lean_is_exclusive(v___x_5140_);
if (v_isSharedCheck_5180_ == 0)
{
v___x_5175_ = v___x_5140_;
v_isShared_5176_ = v_isSharedCheck_5180_;
goto v_resetjp_5174_;
}
else
{
lean_inc(v_a_5173_);
lean_dec(v___x_5140_);
v___x_5175_ = lean_box(0);
v_isShared_5176_ = v_isSharedCheck_5180_;
goto v_resetjp_5174_;
}
v_resetjp_5174_:
{
lean_object* v___x_5178_; 
if (v_isShared_5176_ == 0)
{
v___x_5178_ = v___x_5175_;
goto v_reusejp_5177_;
}
else
{
lean_object* v_reuseFailAlloc_5179_; 
v_reuseFailAlloc_5179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5179_, 0, v_a_5173_);
v___x_5178_ = v_reuseFailAlloc_5179_;
goto v_reusejp_5177_;
}
v_reusejp_5177_:
{
return v___x_5178_;
}
}
}
}
else
{
lean_object* v___x_5181_; lean_object* v___x_5182_; 
lean_dec_ref(v_x_5126_);
lean_dec_ref(v_x_5125_);
v___x_5181_ = lean_box(0);
v___x_5182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5182_, 0, v___x_5181_);
return v___x_5182_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2___boxed(lean_object* v_x_5183_, lean_object* v_x_5184_, lean_object* v_x_5185_, lean_object* v___y_5186_, lean_object* v___y_5187_, lean_object* v___y_5188_, lean_object* v___y_5189_, lean_object* v___y_5190_){
_start:
{
lean_object* v_res_5191_; 
v_res_5191_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(v_x_5183_, v_x_5184_, v_x_5185_, v___y_5186_, v___y_5187_, v___y_5188_, v___y_5189_);
lean_dec(v___y_5189_);
lean_dec_ref(v___y_5188_);
lean_dec(v___y_5187_);
lean_dec_ref(v___y_5186_);
return v_res_5191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorAppIndices_x3f(lean_object* v_ctorApp_5192_, lean_object* v_a_5193_, lean_object* v_a_5194_, lean_object* v_a_5195_, lean_object* v_a_5196_){
_start:
{
lean_object* v___x_5198_; 
lean_inc(v_a_5196_);
lean_inc_ref(v_a_5195_);
lean_inc(v_a_5194_);
lean_inc_ref(v_a_5193_);
v___x_5198_ = lean_infer_type(v_ctorApp_5192_, v_a_5193_, v_a_5194_, v_a_5195_, v_a_5196_);
if (lean_obj_tag(v___x_5198_) == 0)
{
lean_object* v_a_5199_; lean_object* v___x_5200_; 
v_a_5199_ = lean_ctor_get(v___x_5198_, 0);
lean_inc(v_a_5199_);
lean_dec_ref_known(v___x_5198_, 1);
v___x_5200_ = l_Lean_Meta_whnfD(v_a_5199_, v_a_5193_, v_a_5194_, v_a_5195_, v_a_5196_);
if (lean_obj_tag(v___x_5200_) == 0)
{
lean_object* v_a_5201_; lean_object* v_dummy_5202_; lean_object* v_nargs_5203_; lean_object* v___x_5204_; lean_object* v___x_5205_; lean_object* v___x_5206_; lean_object* v___x_5207_; 
v_a_5201_ = lean_ctor_get(v___x_5200_, 0);
lean_inc(v_a_5201_);
lean_dec_ref_known(v___x_5200_, 1);
v_dummy_5202_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0);
v_nargs_5203_ = l_Lean_Expr_getAppNumArgs(v_a_5201_);
lean_inc(v_nargs_5203_);
v___x_5204_ = lean_mk_array(v_nargs_5203_, v_dummy_5202_);
v___x_5205_ = lean_unsigned_to_nat(1u);
v___x_5206_ = lean_nat_sub(v_nargs_5203_, v___x_5205_);
lean_dec(v_nargs_5203_);
v___x_5207_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(v_a_5201_, v___x_5204_, v___x_5206_, v_a_5193_, v_a_5194_, v_a_5195_, v_a_5196_);
return v___x_5207_;
}
else
{
lean_object* v_a_5208_; lean_object* v___x_5210_; uint8_t v_isShared_5211_; uint8_t v_isSharedCheck_5215_; 
v_a_5208_ = lean_ctor_get(v___x_5200_, 0);
v_isSharedCheck_5215_ = !lean_is_exclusive(v___x_5200_);
if (v_isSharedCheck_5215_ == 0)
{
v___x_5210_ = v___x_5200_;
v_isShared_5211_ = v_isSharedCheck_5215_;
goto v_resetjp_5209_;
}
else
{
lean_inc(v_a_5208_);
lean_dec(v___x_5200_);
v___x_5210_ = lean_box(0);
v_isShared_5211_ = v_isSharedCheck_5215_;
goto v_resetjp_5209_;
}
v_resetjp_5209_:
{
lean_object* v___x_5213_; 
if (v_isShared_5211_ == 0)
{
v___x_5213_ = v___x_5210_;
goto v_reusejp_5212_;
}
else
{
lean_object* v_reuseFailAlloc_5214_; 
v_reuseFailAlloc_5214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5214_, 0, v_a_5208_);
v___x_5213_ = v_reuseFailAlloc_5214_;
goto v_reusejp_5212_;
}
v_reusejp_5212_:
{
return v___x_5213_;
}
}
}
}
else
{
lean_object* v_a_5216_; lean_object* v___x_5218_; uint8_t v_isShared_5219_; uint8_t v_isSharedCheck_5223_; 
v_a_5216_ = lean_ctor_get(v___x_5198_, 0);
v_isSharedCheck_5223_ = !lean_is_exclusive(v___x_5198_);
if (v_isSharedCheck_5223_ == 0)
{
v___x_5218_ = v___x_5198_;
v_isShared_5219_ = v_isSharedCheck_5223_;
goto v_resetjp_5217_;
}
else
{
lean_inc(v_a_5216_);
lean_dec(v___x_5198_);
v___x_5218_ = lean_box(0);
v_isShared_5219_ = v_isSharedCheck_5223_;
goto v_resetjp_5217_;
}
v_resetjp_5217_:
{
lean_object* v___x_5221_; 
if (v_isShared_5219_ == 0)
{
v___x_5221_ = v___x_5218_;
goto v_reusejp_5220_;
}
else
{
lean_object* v_reuseFailAlloc_5222_; 
v_reuseFailAlloc_5222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5222_, 0, v_a_5216_);
v___x_5221_ = v_reuseFailAlloc_5222_;
goto v_reusejp_5220_;
}
v_reusejp_5220_:
{
return v___x_5221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorAppIndices_x3f___boxed(lean_object* v_ctorApp_5224_, lean_object* v_a_5225_, lean_object* v_a_5226_, lean_object* v_a_5227_, lean_object* v_a_5228_, lean_object* v_a_5229_){
_start:
{
lean_object* v_res_5230_; 
v_res_5230_ = l_Lean_Meta_getCtorAppIndices_x3f(v_ctorApp_5224_, v_a_5225_, v_a_5226_, v_a_5227_, v_a_5228_);
lean_dec(v_a_5228_);
lean_dec_ref(v_a_5227_);
lean_dec(v_a_5226_);
lean_dec_ref(v_a_5225_);
return v_res_5230_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1(lean_object* v_inst_5231_, lean_object* v_R_5232_, lean_object* v_a_5233_, lean_object* v_b_5234_){
_start:
{
lean_object* v___x_5235_; 
v___x_5235_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(v_a_5233_, v_b_5234_);
return v___x_5235_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0(lean_object* v_00_u03b1_5236_, lean_object* v_constName_5237_, lean_object* v___y_5238_, lean_object* v___y_5239_, lean_object* v___y_5240_, lean_object* v___y_5241_){
_start:
{
lean_object* v___x_5243_; 
v___x_5243_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(v_constName_5237_, v___y_5238_, v___y_5239_, v___y_5240_, v___y_5241_);
return v___x_5243_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b1_5244_, lean_object* v_constName_5245_, lean_object* v___y_5246_, lean_object* v___y_5247_, lean_object* v___y_5248_, lean_object* v___y_5249_, lean_object* v___y_5250_){
_start:
{
lean_object* v_res_5251_; 
v_res_5251_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0(v_00_u03b1_5244_, v_constName_5245_, v___y_5246_, v___y_5247_, v___y_5248_, v___y_5249_);
lean_dec(v___y_5249_);
lean_dec_ref(v___y_5248_);
lean_dec(v___y_5247_);
lean_dec_ref(v___y_5246_);
return v_res_5251_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_5252_, lean_object* v_ref_5253_, lean_object* v_constName_5254_, lean_object* v___y_5255_, lean_object* v___y_5256_, lean_object* v___y_5257_, lean_object* v___y_5258_){
_start:
{
lean_object* v___x_5260_; 
v___x_5260_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(v_ref_5253_, v_constName_5254_, v___y_5255_, v___y_5256_, v___y_5257_, v___y_5258_);
return v___x_5260_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_5261_, lean_object* v_ref_5262_, lean_object* v_constName_5263_, lean_object* v___y_5264_, lean_object* v___y_5265_, lean_object* v___y_5266_, lean_object* v___y_5267_, lean_object* v___y_5268_){
_start:
{
lean_object* v_res_5269_; 
v_res_5269_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1(v_00_u03b1_5261_, v_ref_5262_, v_constName_5263_, v___y_5264_, v___y_5265_, v___y_5266_, v___y_5267_);
lean_dec(v___y_5267_);
lean_dec_ref(v___y_5266_);
lean_dec(v___y_5265_);
lean_dec_ref(v___y_5264_);
lean_dec(v_ref_5262_);
return v_res_5269_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_5270_, lean_object* v_ref_5271_, lean_object* v_msg_5272_, lean_object* v_declHint_5273_, lean_object* v___y_5274_, lean_object* v___y_5275_, lean_object* v___y_5276_, lean_object* v___y_5277_){
_start:
{
lean_object* v___x_5279_; 
v___x_5279_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5271_, v_msg_5272_, v_declHint_5273_, v___y_5274_, v___y_5275_, v___y_5276_, v___y_5277_);
return v___x_5279_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_5280_, lean_object* v_ref_5281_, lean_object* v_msg_5282_, lean_object* v_declHint_5283_, lean_object* v___y_5284_, lean_object* v___y_5285_, lean_object* v___y_5286_, lean_object* v___y_5287_, lean_object* v___y_5288_){
_start:
{
lean_object* v_res_5289_; 
v_res_5289_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_5280_, v_ref_5281_, v_msg_5282_, v_declHint_5283_, v___y_5284_, v___y_5285_, v___y_5286_, v___y_5287_);
lean_dec(v___y_5287_);
lean_dec_ref(v___y_5286_);
lean_dec(v___y_5285_);
lean_dec_ref(v___y_5284_);
lean_dec(v_ref_5281_);
return v_res_5289_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_msg_5290_, lean_object* v_declHint_5291_, lean_object* v___y_5292_, lean_object* v___y_5293_, lean_object* v___y_5294_, lean_object* v___y_5295_){
_start:
{
lean_object* v___x_5297_; 
v___x_5297_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_5290_, v_declHint_5291_, v___y_5295_);
return v___x_5297_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_5298_, lean_object* v_declHint_5299_, lean_object* v___y_5300_, lean_object* v___y_5301_, lean_object* v___y_5302_, lean_object* v___y_5303_, lean_object* v___y_5304_){
_start:
{
lean_object* v_res_5305_; 
v_res_5305_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_5298_, v_declHint_5299_, v___y_5300_, v___y_5301_, v___y_5302_, v___y_5303_);
lean_dec(v___y_5303_);
lean_dec_ref(v___y_5302_);
lean_dec(v___y_5301_);
lean_dec_ref(v___y_5300_);
return v_res_5305_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_5306_, lean_object* v_ref_5307_, lean_object* v_msg_5308_, lean_object* v___y_5309_, lean_object* v___y_5310_, lean_object* v___y_5311_, lean_object* v___y_5312_){
_start:
{
lean_object* v___x_5314_; 
v___x_5314_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5307_, v_msg_5308_, v___y_5309_, v___y_5310_, v___y_5311_, v___y_5312_);
return v___x_5314_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_5315_, lean_object* v_ref_5316_, lean_object* v_msg_5317_, lean_object* v___y_5318_, lean_object* v___y_5319_, lean_object* v___y_5320_, lean_object* v___y_5321_, lean_object* v___y_5322_){
_start:
{
lean_object* v_res_5323_; 
v_res_5323_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_5315_, v_ref_5316_, v_msg_5317_, v___y_5318_, v___y_5319_, v___y_5320_, v___y_5321_);
lean_dec(v___y_5321_);
lean_dec_ref(v___y_5320_);
lean_dec(v___y_5319_);
lean_dec_ref(v___y_5318_);
lean_dec(v_ref_5316_);
return v_res_5323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0___boxed(lean_object* v_i_5324_, lean_object* v_body_5325_, lean_object* v_args2_5326_, lean_object* v_ctorVal_5327_, lean_object* v_args1_5328_, lean_object* v_k_5329_, lean_object* v_arg2_5330_, lean_object* v___y_5331_, lean_object* v___y_5332_, lean_object* v___y_5333_, lean_object* v___y_5334_, lean_object* v___y_5335_){
_start:
{
lean_object* v_res_5336_; 
v_res_5336_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0(v_i_5324_, v_body_5325_, v_args2_5326_, v_ctorVal_5327_, v_args1_5328_, v_k_5329_, v_arg2_5330_, v___y_5331_, v___y_5332_, v___y_5333_, v___y_5334_);
lean_dec(v___y_5334_);
lean_dec_ref(v___y_5333_);
lean_dec(v___y_5332_);
lean_dec_ref(v___y_5331_);
lean_dec_ref(v_body_5325_);
lean_dec(v_i_5324_);
return v_res_5336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(lean_object* v_ctorVal_5337_, lean_object* v_args1_5338_, lean_object* v_k_5339_, lean_object* v_i_5340_, lean_object* v_type_5341_, lean_object* v_args2_5342_, lean_object* v_a_5343_, lean_object* v_a_5344_, lean_object* v_a_5345_, lean_object* v_a_5346_){
_start:
{
lean_object* v___x_5348_; uint8_t v___x_5349_; 
v___x_5348_ = lean_array_get_size(v_args1_5338_);
v___x_5349_ = lean_nat_dec_lt(v_i_5340_, v___x_5348_);
if (v___x_5349_ == 0)
{
lean_object* v___x_5350_; 
lean_dec_ref(v_type_5341_);
lean_dec(v_i_5340_);
lean_dec_ref(v_args1_5338_);
lean_dec_ref(v_ctorVal_5337_);
lean_inc(v_a_5346_);
lean_inc_ref(v_a_5345_);
lean_inc(v_a_5344_);
lean_inc_ref(v_a_5343_);
v___x_5350_ = lean_apply_6(v_k_5339_, v_args2_5342_, v_a_5343_, v_a_5344_, v_a_5345_, v_a_5346_, lean_box(0));
return v___x_5350_;
}
else
{
lean_object* v___x_5351_; 
lean_inc(v_a_5346_);
lean_inc_ref(v_a_5345_);
lean_inc(v_a_5344_);
lean_inc_ref(v_a_5343_);
v___x_5351_ = lean_whnf(v_type_5341_, v_a_5343_, v_a_5344_, v_a_5345_, v_a_5346_);
if (lean_obj_tag(v___x_5351_) == 0)
{
lean_object* v_a_5352_; 
v_a_5352_ = lean_ctor_get(v___x_5351_, 0);
lean_inc(v_a_5352_);
lean_dec_ref_known(v___x_5351_, 1);
if (lean_obj_tag(v_a_5352_) == 7)
{
lean_object* v_binderName_5353_; lean_object* v_binderType_5354_; lean_object* v_body_5355_; lean_object* v___f_5356_; uint8_t v___x_5357_; uint8_t v___x_5358_; lean_object* v___x_5359_; 
v_binderName_5353_ = lean_ctor_get(v_a_5352_, 0);
lean_inc(v_binderName_5353_);
v_binderType_5354_ = lean_ctor_get(v_a_5352_, 1);
lean_inc_ref(v_binderType_5354_);
v_body_5355_ = lean_ctor_get(v_a_5352_, 2);
lean_inc_ref(v_body_5355_);
lean_dec_ref_known(v_a_5352_, 3);
v___f_5356_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0___boxed), 12, 6);
lean_closure_set(v___f_5356_, 0, v_i_5340_);
lean_closure_set(v___f_5356_, 1, v_body_5355_);
lean_closure_set(v___f_5356_, 2, v_args2_5342_);
lean_closure_set(v___f_5356_, 3, v_ctorVal_5337_);
lean_closure_set(v___f_5356_, 4, v_args1_5338_);
lean_closure_set(v___f_5356_, 5, v_k_5339_);
v___x_5357_ = 1;
v___x_5358_ = 0;
v___x_5359_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_binderName_5353_, v___x_5357_, v_binderType_5354_, v___f_5356_, v___x_5358_, v_a_5343_, v_a_5344_, v_a_5345_, v_a_5346_);
return v___x_5359_;
}
else
{
lean_object* v_toConstantVal_5360_; lean_object* v_name_5361_; lean_object* v___x_5362_; lean_object* v___x_5363_; lean_object* v___x_5364_; lean_object* v___x_5365_; lean_object* v___x_5366_; lean_object* v___x_5367_; 
lean_dec(v_a_5352_);
lean_dec_ref(v_args2_5342_);
lean_dec(v_i_5340_);
lean_dec_ref(v_k_5339_);
lean_dec_ref(v_args1_5338_);
v_toConstantVal_5360_ = lean_ctor_get(v_ctorVal_5337_, 0);
lean_inc_ref(v_toConstantVal_5360_);
lean_dec_ref(v_ctorVal_5337_);
v_name_5361_ = lean_ctor_get(v_toConstantVal_5360_, 0);
lean_inc(v_name_5361_);
lean_dec_ref(v_toConstantVal_5360_);
v___x_5362_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1);
v___x_5363_ = l_Lean_MessageData_ofName(v_name_5361_);
v___x_5364_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5364_, 0, v___x_5362_);
lean_ctor_set(v___x_5364_, 1, v___x_5363_);
v___x_5365_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_5366_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5366_, 0, v___x_5364_);
lean_ctor_set(v___x_5366_, 1, v___x_5365_);
v___x_5367_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_5366_, v_a_5343_, v_a_5344_, v_a_5345_, v_a_5346_);
return v___x_5367_;
}
}
else
{
lean_object* v_a_5368_; lean_object* v___x_5370_; uint8_t v_isShared_5371_; uint8_t v_isSharedCheck_5375_; 
lean_dec_ref(v_args2_5342_);
lean_dec(v_i_5340_);
lean_dec_ref(v_k_5339_);
lean_dec_ref(v_args1_5338_);
lean_dec_ref(v_ctorVal_5337_);
v_a_5368_ = lean_ctor_get(v___x_5351_, 0);
v_isSharedCheck_5375_ = !lean_is_exclusive(v___x_5351_);
if (v_isSharedCheck_5375_ == 0)
{
v___x_5370_ = v___x_5351_;
v_isShared_5371_ = v_isSharedCheck_5375_;
goto v_resetjp_5369_;
}
else
{
lean_inc(v_a_5368_);
lean_dec(v___x_5351_);
v___x_5370_ = lean_box(0);
v_isShared_5371_ = v_isSharedCheck_5375_;
goto v_resetjp_5369_;
}
v_resetjp_5369_:
{
lean_object* v___x_5373_; 
if (v_isShared_5371_ == 0)
{
v___x_5373_ = v___x_5370_;
goto v_reusejp_5372_;
}
else
{
lean_object* v_reuseFailAlloc_5374_; 
v_reuseFailAlloc_5374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5374_, 0, v_a_5368_);
v___x_5373_ = v_reuseFailAlloc_5374_;
goto v_reusejp_5372_;
}
v_reusejp_5372_:
{
return v___x_5373_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0(lean_object* v_i_5376_, lean_object* v_body_5377_, lean_object* v_args2_5378_, lean_object* v_ctorVal_5379_, lean_object* v_args1_5380_, lean_object* v_k_5381_, lean_object* v_arg2_5382_, lean_object* v___y_5383_, lean_object* v___y_5384_, lean_object* v___y_5385_, lean_object* v___y_5386_){
_start:
{
lean_object* v___x_5388_; lean_object* v___x_5389_; lean_object* v___x_5390_; lean_object* v___x_5391_; lean_object* v___x_5392_; 
v___x_5388_ = lean_unsigned_to_nat(1u);
v___x_5389_ = lean_nat_add(v_i_5376_, v___x_5388_);
v___x_5390_ = lean_expr_instantiate1(v_body_5377_, v_arg2_5382_);
v___x_5391_ = lean_array_push(v_args2_5378_, v_arg2_5382_);
v___x_5392_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(v_ctorVal_5379_, v_args1_5380_, v_k_5381_, v___x_5389_, v___x_5390_, v___x_5391_, v___y_5383_, v___y_5384_, v___y_5385_, v___y_5386_);
return v___x_5392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___boxed(lean_object* v_ctorVal_5393_, lean_object* v_args1_5394_, lean_object* v_k_5395_, lean_object* v_i_5396_, lean_object* v_type_5397_, lean_object* v_args2_5398_, lean_object* v_a_5399_, lean_object* v_a_5400_, lean_object* v_a_5401_, lean_object* v_a_5402_, lean_object* v_a_5403_){
_start:
{
lean_object* v_res_5404_; 
v_res_5404_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(v_ctorVal_5393_, v_args1_5394_, v_k_5395_, v_i_5396_, v_type_5397_, v_args2_5398_, v_a_5399_, v_a_5400_, v_a_5401_, v_a_5402_);
lean_dec(v_a_5402_);
lean_dec_ref(v_a_5401_);
lean_dec(v_a_5400_);
lean_dec_ref(v_a_5399_);
return v_res_5404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0(lean_object* v_name_5405_, lean_object* v_us_5406_, lean_object* v_args1_5407_, lean_object* v___x_5408_, lean_object* v_numParams_5409_, lean_object* v___x_5410_, lean_object* v_args2_5411_, lean_object* v___y_5412_, lean_object* v___y_5413_, lean_object* v___y_5414_, lean_object* v___y_5415_){
_start:
{
lean_object* v___x_5417_; lean_object* v___x_5418_; lean_object* v___x_5419_; lean_object* v___x_5420_; 
lean_inc(v_us_5406_);
v___x_5417_ = l_Lean_mkConst(v_name_5405_, v_us_5406_);
lean_inc_ref(v___x_5417_);
v___x_5418_ = l_Lean_mkAppN(v___x_5417_, v_args1_5407_);
v___x_5419_ = l_Lean_mkAppN(v___x_5417_, v_args2_5411_);
lean_inc_ref(v___x_5419_);
lean_inc_ref(v___x_5418_);
v___x_5420_ = l_Lean_Meta_mkEqHEq(v___x_5418_, v___x_5419_, v___y_5412_, v___y_5413_, v___y_5414_, v___y_5415_);
if (lean_obj_tag(v___x_5420_) == 0)
{
lean_object* v_a_5421_; lean_object* v___x_5422_; uint8_t v___x_5423_; lean_object* v___x_5424_; 
v_a_5421_ = lean_ctor_get(v___x_5420_, 0);
lean_inc(v_a_5421_);
lean_dec_ref_known(v___x_5420_, 1);
lean_inc_ref_n(v_args2_5411_, 2);
v___x_5422_ = l_Array_toSubarray___redArg(v_args2_5411_, v___x_5408_, v_numParams_5409_);
v___x_5423_ = 1;
v___x_5424_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v_args1_5407_, v_args2_5411_, v___x_5423_, v___y_5412_, v___y_5413_, v___y_5414_, v___y_5415_);
if (lean_obj_tag(v___x_5424_) == 0)
{
lean_object* v_a_5425_; lean_object* v___x_5427_; uint8_t v_isShared_5428_; uint8_t v_isSharedCheck_5545_; 
v_a_5425_ = lean_ctor_get(v___x_5424_, 0);
v_isSharedCheck_5545_ = !lean_is_exclusive(v___x_5424_);
if (v_isSharedCheck_5545_ == 0)
{
v___x_5427_ = v___x_5424_;
v_isShared_5428_ = v_isSharedCheck_5545_;
goto v_resetjp_5426_;
}
else
{
lean_inc(v_a_5425_);
lean_dec(v___x_5424_);
v___x_5427_ = lean_box(0);
v_isShared_5428_ = v_isSharedCheck_5545_;
goto v_resetjp_5426_;
}
v_resetjp_5426_:
{
lean_object* v___x_5429_; 
v___x_5429_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f(v_a_5425_);
if (lean_obj_tag(v___x_5429_) == 1)
{
lean_object* v_val_5430_; lean_object* v___x_5431_; 
lean_del_object(v___x_5427_);
v_val_5430_ = lean_ctor_get(v___x_5429_, 0);
lean_inc(v_val_5430_);
lean_dec_ref_known(v___x_5429_, 1);
v___x_5431_ = l_Lean_mkArrow(v_a_5421_, v_val_5430_, v___y_5414_, v___y_5415_);
if (lean_obj_tag(v___x_5431_) == 0)
{
lean_object* v_a_5432_; lean_object* v___x_5433_; 
v_a_5432_ = lean_ctor_get(v___x_5431_, 0);
lean_inc(v_a_5432_);
lean_dec_ref_known(v___x_5431_, 1);
v___x_5433_ = l_Lean_Meta_getCtorAppIndices_x3f(v___x_5418_, v___y_5412_, v___y_5413_, v___y_5414_, v___y_5415_);
if (lean_obj_tag(v___x_5433_) == 0)
{
lean_object* v_a_5434_; lean_object* v___x_5436_; uint8_t v_isShared_5437_; uint8_t v_isSharedCheck_5524_; 
v_a_5434_ = lean_ctor_get(v___x_5433_, 0);
v_isSharedCheck_5524_ = !lean_is_exclusive(v___x_5433_);
if (v_isSharedCheck_5524_ == 0)
{
v___x_5436_ = v___x_5433_;
v_isShared_5437_ = v_isSharedCheck_5524_;
goto v_resetjp_5435_;
}
else
{
lean_inc(v_a_5434_);
lean_dec(v___x_5433_);
v___x_5436_ = lean_box(0);
v_isShared_5437_ = v_isSharedCheck_5524_;
goto v_resetjp_5435_;
}
v_resetjp_5435_:
{
if (lean_obj_tag(v_a_5434_) == 1)
{
lean_object* v_val_5438_; lean_object* v___x_5439_; 
lean_del_object(v___x_5436_);
v_val_5438_ = lean_ctor_get(v_a_5434_, 0);
lean_inc(v_val_5438_);
lean_dec_ref_known(v_a_5434_, 1);
v___x_5439_ = l_Lean_Meta_getCtorAppIndices_x3f(v___x_5419_, v___y_5412_, v___y_5413_, v___y_5414_, v___y_5415_);
if (lean_obj_tag(v___x_5439_) == 0)
{
lean_object* v_a_5440_; lean_object* v___x_5442_; uint8_t v_isShared_5443_; uint8_t v_isSharedCheck_5511_; 
v_a_5440_ = lean_ctor_get(v___x_5439_, 0);
v_isSharedCheck_5511_ = !lean_is_exclusive(v___x_5439_);
if (v_isSharedCheck_5511_ == 0)
{
v___x_5442_ = v___x_5439_;
v_isShared_5443_ = v_isSharedCheck_5511_;
goto v_resetjp_5441_;
}
else
{
lean_inc(v_a_5440_);
lean_dec(v___x_5439_);
v___x_5442_ = lean_box(0);
v_isShared_5443_ = v_isSharedCheck_5511_;
goto v_resetjp_5441_;
}
v_resetjp_5441_:
{
if (lean_obj_tag(v_a_5440_) == 1)
{
lean_object* v_val_5444_; lean_object* v___x_5446_; uint8_t v_isShared_5447_; uint8_t v_isSharedCheck_5506_; 
lean_del_object(v___x_5442_);
v_val_5444_ = lean_ctor_get(v_a_5440_, 0);
v_isSharedCheck_5506_ = !lean_is_exclusive(v_a_5440_);
if (v_isSharedCheck_5506_ == 0)
{
v___x_5446_ = v_a_5440_;
v_isShared_5447_ = v_isSharedCheck_5506_;
goto v_resetjp_5445_;
}
else
{
lean_inc(v_val_5444_);
lean_dec(v_a_5440_);
v___x_5446_ = lean_box(0);
v_isShared_5447_ = v_isSharedCheck_5506_;
goto v_resetjp_5445_;
}
v_resetjp_5445_:
{
lean_object* v___x_5448_; lean_object* v___x_5449_; lean_object* v___x_5450_; lean_object* v___x_5451_; uint8_t v___x_5452_; lean_object* v___x_5453_; 
v___x_5448_ = l_Subarray_copy___redArg(v___x_5410_);
v___x_5449_ = l_Array_append___redArg(v___x_5448_, v_val_5438_);
v___x_5450_ = l_Subarray_copy___redArg(v___x_5422_);
v___x_5451_ = l_Array_append___redArg(v___x_5450_, v_val_5444_);
lean_dec(v_val_5444_);
v___x_5452_ = 0;
v___x_5453_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v___x_5449_, v___x_5451_, v___x_5452_, v___y_5412_, v___y_5413_, v___y_5414_, v___y_5415_);
lean_dec_ref(v___x_5449_);
if (lean_obj_tag(v___x_5453_) == 0)
{
lean_object* v_a_5454_; lean_object* v___x_5455_; 
v_a_5454_ = lean_ctor_get(v___x_5453_, 0);
lean_inc(v_a_5454_);
lean_dec_ref_known(v___x_5453_, 1);
v___x_5455_ = l_Lean_mkArrowN(v_a_5454_, v_a_5432_, v___y_5414_, v___y_5415_);
lean_dec(v_a_5454_);
if (lean_obj_tag(v___x_5455_) == 0)
{
lean_object* v_a_5456_; uint8_t v___x_5457_; lean_object* v___x_5458_; 
v_a_5456_ = lean_ctor_get(v___x_5455_, 0);
lean_inc(v_a_5456_);
lean_dec_ref_known(v___x_5455_, 1);
v___x_5457_ = 1;
v___x_5458_ = l_Lean_Meta_mkForallFVars(v_args2_5411_, v_a_5456_, v___x_5452_, v___x_5423_, v___x_5423_, v___x_5457_, v___y_5412_, v___y_5413_, v___y_5414_, v___y_5415_);
lean_dec_ref(v_args2_5411_);
if (lean_obj_tag(v___x_5458_) == 0)
{
lean_object* v_a_5459_; lean_object* v___x_5460_; 
v_a_5459_ = lean_ctor_get(v___x_5458_, 0);
lean_inc(v_a_5459_);
lean_dec_ref_known(v___x_5458_, 1);
v___x_5460_ = l_Lean_Meta_mkForallFVars(v_args1_5407_, v_a_5459_, v___x_5452_, v___x_5423_, v___x_5423_, v___x_5457_, v___y_5412_, v___y_5413_, v___y_5414_, v___y_5415_);
if (lean_obj_tag(v___x_5460_) == 0)
{
lean_object* v_a_5461_; lean_object* v___x_5463_; uint8_t v_isShared_5464_; uint8_t v_isSharedCheck_5473_; 
v_a_5461_ = lean_ctor_get(v___x_5460_, 0);
v_isSharedCheck_5473_ = !lean_is_exclusive(v___x_5460_);
if (v_isSharedCheck_5473_ == 0)
{
v___x_5463_ = v___x_5460_;
v_isShared_5464_ = v_isSharedCheck_5473_;
goto v_resetjp_5462_;
}
else
{
lean_inc(v_a_5461_);
lean_dec(v___x_5460_);
v___x_5463_ = lean_box(0);
v_isShared_5464_ = v_isSharedCheck_5473_;
goto v_resetjp_5462_;
}
v_resetjp_5462_:
{
lean_object* v___x_5465_; lean_object* v___x_5466_; lean_object* v___x_5468_; 
v___x_5465_ = lean_array_get_size(v_val_5438_);
lean_dec(v_val_5438_);
v___x_5466_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5466_, 0, v_a_5461_);
lean_ctor_set(v___x_5466_, 1, v_us_5406_);
lean_ctor_set(v___x_5466_, 2, v___x_5465_);
if (v_isShared_5447_ == 0)
{
lean_ctor_set(v___x_5446_, 0, v___x_5466_);
v___x_5468_ = v___x_5446_;
goto v_reusejp_5467_;
}
else
{
lean_object* v_reuseFailAlloc_5472_; 
v_reuseFailAlloc_5472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5472_, 0, v___x_5466_);
v___x_5468_ = v_reuseFailAlloc_5472_;
goto v_reusejp_5467_;
}
v_reusejp_5467_:
{
lean_object* v___x_5470_; 
if (v_isShared_5464_ == 0)
{
lean_ctor_set(v___x_5463_, 0, v___x_5468_);
v___x_5470_ = v___x_5463_;
goto v_reusejp_5469_;
}
else
{
lean_object* v_reuseFailAlloc_5471_; 
v_reuseFailAlloc_5471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5471_, 0, v___x_5468_);
v___x_5470_ = v_reuseFailAlloc_5471_;
goto v_reusejp_5469_;
}
v_reusejp_5469_:
{
return v___x_5470_;
}
}
}
}
else
{
lean_object* v_a_5474_; lean_object* v___x_5476_; uint8_t v_isShared_5477_; uint8_t v_isSharedCheck_5481_; 
lean_del_object(v___x_5446_);
lean_dec(v_val_5438_);
lean_dec(v_us_5406_);
v_a_5474_ = lean_ctor_get(v___x_5460_, 0);
v_isSharedCheck_5481_ = !lean_is_exclusive(v___x_5460_);
if (v_isSharedCheck_5481_ == 0)
{
v___x_5476_ = v___x_5460_;
v_isShared_5477_ = v_isSharedCheck_5481_;
goto v_resetjp_5475_;
}
else
{
lean_inc(v_a_5474_);
lean_dec(v___x_5460_);
v___x_5476_ = lean_box(0);
v_isShared_5477_ = v_isSharedCheck_5481_;
goto v_resetjp_5475_;
}
v_resetjp_5475_:
{
lean_object* v___x_5479_; 
if (v_isShared_5477_ == 0)
{
v___x_5479_ = v___x_5476_;
goto v_reusejp_5478_;
}
else
{
lean_object* v_reuseFailAlloc_5480_; 
v_reuseFailAlloc_5480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5480_, 0, v_a_5474_);
v___x_5479_ = v_reuseFailAlloc_5480_;
goto v_reusejp_5478_;
}
v_reusejp_5478_:
{
return v___x_5479_;
}
}
}
}
else
{
lean_object* v_a_5482_; lean_object* v___x_5484_; uint8_t v_isShared_5485_; uint8_t v_isSharedCheck_5489_; 
lean_del_object(v___x_5446_);
lean_dec(v_val_5438_);
lean_dec(v_us_5406_);
v_a_5482_ = lean_ctor_get(v___x_5458_, 0);
v_isSharedCheck_5489_ = !lean_is_exclusive(v___x_5458_);
if (v_isSharedCheck_5489_ == 0)
{
v___x_5484_ = v___x_5458_;
v_isShared_5485_ = v_isSharedCheck_5489_;
goto v_resetjp_5483_;
}
else
{
lean_inc(v_a_5482_);
lean_dec(v___x_5458_);
v___x_5484_ = lean_box(0);
v_isShared_5485_ = v_isSharedCheck_5489_;
goto v_resetjp_5483_;
}
v_resetjp_5483_:
{
lean_object* v___x_5487_; 
if (v_isShared_5485_ == 0)
{
v___x_5487_ = v___x_5484_;
goto v_reusejp_5486_;
}
else
{
lean_object* v_reuseFailAlloc_5488_; 
v_reuseFailAlloc_5488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5488_, 0, v_a_5482_);
v___x_5487_ = v_reuseFailAlloc_5488_;
goto v_reusejp_5486_;
}
v_reusejp_5486_:
{
return v___x_5487_;
}
}
}
}
else
{
lean_object* v_a_5490_; lean_object* v___x_5492_; uint8_t v_isShared_5493_; uint8_t v_isSharedCheck_5497_; 
lean_del_object(v___x_5446_);
lean_dec(v_val_5438_);
lean_dec_ref(v_args2_5411_);
lean_dec(v_us_5406_);
v_a_5490_ = lean_ctor_get(v___x_5455_, 0);
v_isSharedCheck_5497_ = !lean_is_exclusive(v___x_5455_);
if (v_isSharedCheck_5497_ == 0)
{
v___x_5492_ = v___x_5455_;
v_isShared_5493_ = v_isSharedCheck_5497_;
goto v_resetjp_5491_;
}
else
{
lean_inc(v_a_5490_);
lean_dec(v___x_5455_);
v___x_5492_ = lean_box(0);
v_isShared_5493_ = v_isSharedCheck_5497_;
goto v_resetjp_5491_;
}
v_resetjp_5491_:
{
lean_object* v___x_5495_; 
if (v_isShared_5493_ == 0)
{
v___x_5495_ = v___x_5492_;
goto v_reusejp_5494_;
}
else
{
lean_object* v_reuseFailAlloc_5496_; 
v_reuseFailAlloc_5496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5496_, 0, v_a_5490_);
v___x_5495_ = v_reuseFailAlloc_5496_;
goto v_reusejp_5494_;
}
v_reusejp_5494_:
{
return v___x_5495_;
}
}
}
}
else
{
lean_object* v_a_5498_; lean_object* v___x_5500_; uint8_t v_isShared_5501_; uint8_t v_isSharedCheck_5505_; 
lean_del_object(v___x_5446_);
lean_dec(v_val_5438_);
lean_dec(v_a_5432_);
lean_dec_ref(v_args2_5411_);
lean_dec(v_us_5406_);
v_a_5498_ = lean_ctor_get(v___x_5453_, 0);
v_isSharedCheck_5505_ = !lean_is_exclusive(v___x_5453_);
if (v_isSharedCheck_5505_ == 0)
{
v___x_5500_ = v___x_5453_;
v_isShared_5501_ = v_isSharedCheck_5505_;
goto v_resetjp_5499_;
}
else
{
lean_inc(v_a_5498_);
lean_dec(v___x_5453_);
v___x_5500_ = lean_box(0);
v_isShared_5501_ = v_isSharedCheck_5505_;
goto v_resetjp_5499_;
}
v_resetjp_5499_:
{
lean_object* v___x_5503_; 
if (v_isShared_5501_ == 0)
{
v___x_5503_ = v___x_5500_;
goto v_reusejp_5502_;
}
else
{
lean_object* v_reuseFailAlloc_5504_; 
v_reuseFailAlloc_5504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5504_, 0, v_a_5498_);
v___x_5503_ = v_reuseFailAlloc_5504_;
goto v_reusejp_5502_;
}
v_reusejp_5502_:
{
return v___x_5503_;
}
}
}
}
}
else
{
lean_object* v___x_5507_; lean_object* v___x_5509_; 
lean_dec(v_a_5440_);
lean_dec(v_val_5438_);
lean_dec(v_a_5432_);
lean_dec_ref(v___x_5422_);
lean_dec_ref(v_args2_5411_);
lean_dec_ref(v___x_5410_);
lean_dec(v_us_5406_);
v___x_5507_ = lean_box(0);
if (v_isShared_5443_ == 0)
{
lean_ctor_set(v___x_5442_, 0, v___x_5507_);
v___x_5509_ = v___x_5442_;
goto v_reusejp_5508_;
}
else
{
lean_object* v_reuseFailAlloc_5510_; 
v_reuseFailAlloc_5510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5510_, 0, v___x_5507_);
v___x_5509_ = v_reuseFailAlloc_5510_;
goto v_reusejp_5508_;
}
v_reusejp_5508_:
{
return v___x_5509_;
}
}
}
}
else
{
lean_object* v_a_5512_; lean_object* v___x_5514_; uint8_t v_isShared_5515_; uint8_t v_isSharedCheck_5519_; 
lean_dec(v_val_5438_);
lean_dec(v_a_5432_);
lean_dec_ref(v___x_5422_);
lean_dec_ref(v_args2_5411_);
lean_dec_ref(v___x_5410_);
lean_dec(v_us_5406_);
v_a_5512_ = lean_ctor_get(v___x_5439_, 0);
v_isSharedCheck_5519_ = !lean_is_exclusive(v___x_5439_);
if (v_isSharedCheck_5519_ == 0)
{
v___x_5514_ = v___x_5439_;
v_isShared_5515_ = v_isSharedCheck_5519_;
goto v_resetjp_5513_;
}
else
{
lean_inc(v_a_5512_);
lean_dec(v___x_5439_);
v___x_5514_ = lean_box(0);
v_isShared_5515_ = v_isSharedCheck_5519_;
goto v_resetjp_5513_;
}
v_resetjp_5513_:
{
lean_object* v___x_5517_; 
if (v_isShared_5515_ == 0)
{
v___x_5517_ = v___x_5514_;
goto v_reusejp_5516_;
}
else
{
lean_object* v_reuseFailAlloc_5518_; 
v_reuseFailAlloc_5518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5518_, 0, v_a_5512_);
v___x_5517_ = v_reuseFailAlloc_5518_;
goto v_reusejp_5516_;
}
v_reusejp_5516_:
{
return v___x_5517_;
}
}
}
}
else
{
lean_object* v___x_5520_; lean_object* v___x_5522_; 
lean_dec(v_a_5434_);
lean_dec(v_a_5432_);
lean_dec_ref(v___x_5422_);
lean_dec_ref(v___x_5419_);
lean_dec_ref(v_args2_5411_);
lean_dec_ref(v___x_5410_);
lean_dec(v_us_5406_);
v___x_5520_ = lean_box(0);
if (v_isShared_5437_ == 0)
{
lean_ctor_set(v___x_5436_, 0, v___x_5520_);
v___x_5522_ = v___x_5436_;
goto v_reusejp_5521_;
}
else
{
lean_object* v_reuseFailAlloc_5523_; 
v_reuseFailAlloc_5523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5523_, 0, v___x_5520_);
v___x_5522_ = v_reuseFailAlloc_5523_;
goto v_reusejp_5521_;
}
v_reusejp_5521_:
{
return v___x_5522_;
}
}
}
}
else
{
lean_object* v_a_5525_; lean_object* v___x_5527_; uint8_t v_isShared_5528_; uint8_t v_isSharedCheck_5532_; 
lean_dec(v_a_5432_);
lean_dec_ref(v___x_5422_);
lean_dec_ref(v___x_5419_);
lean_dec_ref(v_args2_5411_);
lean_dec_ref(v___x_5410_);
lean_dec(v_us_5406_);
v_a_5525_ = lean_ctor_get(v___x_5433_, 0);
v_isSharedCheck_5532_ = !lean_is_exclusive(v___x_5433_);
if (v_isSharedCheck_5532_ == 0)
{
v___x_5527_ = v___x_5433_;
v_isShared_5528_ = v_isSharedCheck_5532_;
goto v_resetjp_5526_;
}
else
{
lean_inc(v_a_5525_);
lean_dec(v___x_5433_);
v___x_5527_ = lean_box(0);
v_isShared_5528_ = v_isSharedCheck_5532_;
goto v_resetjp_5526_;
}
v_resetjp_5526_:
{
lean_object* v___x_5530_; 
if (v_isShared_5528_ == 0)
{
v___x_5530_ = v___x_5527_;
goto v_reusejp_5529_;
}
else
{
lean_object* v_reuseFailAlloc_5531_; 
v_reuseFailAlloc_5531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5531_, 0, v_a_5525_);
v___x_5530_ = v_reuseFailAlloc_5531_;
goto v_reusejp_5529_;
}
v_reusejp_5529_:
{
return v___x_5530_;
}
}
}
}
else
{
lean_object* v_a_5533_; lean_object* v___x_5535_; uint8_t v_isShared_5536_; uint8_t v_isSharedCheck_5540_; 
lean_dec_ref(v___x_5422_);
lean_dec_ref(v___x_5419_);
lean_dec_ref(v___x_5418_);
lean_dec_ref(v_args2_5411_);
lean_dec_ref(v___x_5410_);
lean_dec(v_us_5406_);
v_a_5533_ = lean_ctor_get(v___x_5431_, 0);
v_isSharedCheck_5540_ = !lean_is_exclusive(v___x_5431_);
if (v_isSharedCheck_5540_ == 0)
{
v___x_5535_ = v___x_5431_;
v_isShared_5536_ = v_isSharedCheck_5540_;
goto v_resetjp_5534_;
}
else
{
lean_inc(v_a_5533_);
lean_dec(v___x_5431_);
v___x_5535_ = lean_box(0);
v_isShared_5536_ = v_isSharedCheck_5540_;
goto v_resetjp_5534_;
}
v_resetjp_5534_:
{
lean_object* v___x_5538_; 
if (v_isShared_5536_ == 0)
{
v___x_5538_ = v___x_5535_;
goto v_reusejp_5537_;
}
else
{
lean_object* v_reuseFailAlloc_5539_; 
v_reuseFailAlloc_5539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5539_, 0, v_a_5533_);
v___x_5538_ = v_reuseFailAlloc_5539_;
goto v_reusejp_5537_;
}
v_reusejp_5537_:
{
return v___x_5538_;
}
}
}
}
else
{
lean_object* v___x_5541_; lean_object* v___x_5543_; 
lean_dec(v___x_5429_);
lean_dec_ref(v___x_5422_);
lean_dec(v_a_5421_);
lean_dec_ref(v___x_5419_);
lean_dec_ref(v___x_5418_);
lean_dec_ref(v_args2_5411_);
lean_dec_ref(v___x_5410_);
lean_dec(v_us_5406_);
v___x_5541_ = lean_box(0);
if (v_isShared_5428_ == 0)
{
lean_ctor_set(v___x_5427_, 0, v___x_5541_);
v___x_5543_ = v___x_5427_;
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
lean_dec_ref(v___x_5422_);
lean_dec(v_a_5421_);
lean_dec_ref(v___x_5419_);
lean_dec_ref(v___x_5418_);
lean_dec_ref(v_args2_5411_);
lean_dec_ref(v___x_5410_);
lean_dec(v_us_5406_);
v_a_5546_ = lean_ctor_get(v___x_5424_, 0);
v_isSharedCheck_5553_ = !lean_is_exclusive(v___x_5424_);
if (v_isSharedCheck_5553_ == 0)
{
v___x_5548_ = v___x_5424_;
v_isShared_5549_ = v_isSharedCheck_5553_;
goto v_resetjp_5547_;
}
else
{
lean_inc(v_a_5546_);
lean_dec(v___x_5424_);
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
lean_object* v_a_5554_; lean_object* v___x_5556_; uint8_t v_isShared_5557_; uint8_t v_isSharedCheck_5561_; 
lean_dec_ref(v___x_5419_);
lean_dec_ref(v___x_5418_);
lean_dec_ref(v_args2_5411_);
lean_dec_ref(v___x_5410_);
lean_dec(v_numParams_5409_);
lean_dec(v___x_5408_);
lean_dec(v_us_5406_);
v_a_5554_ = lean_ctor_get(v___x_5420_, 0);
v_isSharedCheck_5561_ = !lean_is_exclusive(v___x_5420_);
if (v_isSharedCheck_5561_ == 0)
{
v___x_5556_ = v___x_5420_;
v_isShared_5557_ = v_isSharedCheck_5561_;
goto v_resetjp_5555_;
}
else
{
lean_inc(v_a_5554_);
lean_dec(v___x_5420_);
v___x_5556_ = lean_box(0);
v_isShared_5557_ = v_isSharedCheck_5561_;
goto v_resetjp_5555_;
}
v_resetjp_5555_:
{
lean_object* v___x_5559_; 
if (v_isShared_5557_ == 0)
{
v___x_5559_ = v___x_5556_;
goto v_reusejp_5558_;
}
else
{
lean_object* v_reuseFailAlloc_5560_; 
v_reuseFailAlloc_5560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5560_, 0, v_a_5554_);
v___x_5559_ = v_reuseFailAlloc_5560_;
goto v_reusejp_5558_;
}
v_reusejp_5558_:
{
return v___x_5559_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0___boxed(lean_object* v_name_5562_, lean_object* v_us_5563_, lean_object* v_args1_5564_, lean_object* v___x_5565_, lean_object* v_numParams_5566_, lean_object* v___x_5567_, lean_object* v_args2_5568_, lean_object* v___y_5569_, lean_object* v___y_5570_, lean_object* v___y_5571_, lean_object* v___y_5572_, lean_object* v___y_5573_){
_start:
{
lean_object* v_res_5574_; 
v_res_5574_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0(v_name_5562_, v_us_5563_, v_args1_5564_, v___x_5565_, v_numParams_5566_, v___x_5567_, v_args2_5568_, v___y_5569_, v___y_5570_, v___y_5571_, v___y_5572_);
lean_dec(v___y_5572_);
lean_dec_ref(v___y_5571_);
lean_dec(v___y_5570_);
lean_dec_ref(v___y_5569_);
lean_dec_ref(v_args1_5564_);
return v_res_5574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1(lean_object* v_numParams_5575_, lean_object* v_name_5576_, lean_object* v_us_5577_, lean_object* v_ctorVal_5578_, lean_object* v_a_5579_, lean_object* v_args1_5580_, lean_object* v_x_5581_, lean_object* v___y_5582_, lean_object* v___y_5583_, lean_object* v___y_5584_, lean_object* v___y_5585_){
_start:
{
lean_object* v___x_5587_; lean_object* v___x_5588_; lean_object* v___f_5589_; lean_object* v___x_5590_; lean_object* v___x_5591_; lean_object* v___x_5592_; 
v___x_5587_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_5575_);
lean_inc_ref_n(v_args1_5580_, 3);
v___x_5588_ = l_Array_toSubarray___redArg(v_args1_5580_, v___x_5587_, v_numParams_5575_);
v___f_5589_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0___boxed), 12, 6);
lean_closure_set(v___f_5589_, 0, v_name_5576_);
lean_closure_set(v___f_5589_, 1, v_us_5577_);
lean_closure_set(v___f_5589_, 2, v_args1_5580_);
lean_closure_set(v___f_5589_, 3, v___x_5587_);
lean_closure_set(v___f_5589_, 4, v_numParams_5575_);
lean_closure_set(v___f_5589_, 5, v___x_5588_);
v___x_5590_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_5591_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___boxed), 11, 6);
lean_closure_set(v___x_5591_, 0, v_ctorVal_5578_);
lean_closure_set(v___x_5591_, 1, v_args1_5580_);
lean_closure_set(v___x_5591_, 2, v___f_5589_);
lean_closure_set(v___x_5591_, 3, v___x_5587_);
lean_closure_set(v___x_5591_, 4, v_a_5579_);
lean_closure_set(v___x_5591_, 5, v___x_5590_);
v___x_5592_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v_args1_5580_, v___x_5591_, v___y_5582_, v___y_5583_, v___y_5584_, v___y_5585_);
return v___x_5592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1___boxed(lean_object* v_numParams_5593_, lean_object* v_name_5594_, lean_object* v_us_5595_, lean_object* v_ctorVal_5596_, lean_object* v_a_5597_, lean_object* v_args1_5598_, lean_object* v_x_5599_, lean_object* v___y_5600_, lean_object* v___y_5601_, lean_object* v___y_5602_, lean_object* v___y_5603_, lean_object* v___y_5604_){
_start:
{
lean_object* v_res_5605_; 
v_res_5605_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1(v_numParams_5593_, v_name_5594_, v_us_5595_, v_ctorVal_5596_, v_a_5597_, v_args1_5598_, v_x_5599_, v___y_5600_, v___y_5601_, v___y_5602_, v___y_5603_);
lean_dec(v___y_5603_);
lean_dec_ref(v___y_5602_);
lean_dec(v___y_5601_);
lean_dec_ref(v___y_5600_);
lean_dec_ref(v_x_5599_);
return v_res_5605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(lean_object* v_ctorVal_5606_, lean_object* v_a_5607_, lean_object* v_a_5608_, lean_object* v_a_5609_, lean_object* v_a_5610_){
_start:
{
lean_object* v_toConstantVal_5612_; lean_object* v_numParams_5613_; lean_object* v_name_5614_; lean_object* v_levelParams_5615_; lean_object* v_type_5616_; lean_object* v___x_5617_; 
v_toConstantVal_5612_ = lean_ctor_get(v_ctorVal_5606_, 0);
v_numParams_5613_ = lean_ctor_get(v_ctorVal_5606_, 3);
lean_inc(v_numParams_5613_);
v_name_5614_ = lean_ctor_get(v_toConstantVal_5612_, 0);
lean_inc(v_name_5614_);
v_levelParams_5615_ = lean_ctor_get(v_toConstantVal_5612_, 1);
v_type_5616_ = lean_ctor_get(v_toConstantVal_5612_, 2);
lean_inc_ref(v_type_5616_);
v___x_5617_ = l_Lean_Meta_elimOptParam(v_type_5616_, v_a_5609_, v_a_5610_);
if (lean_obj_tag(v___x_5617_) == 0)
{
lean_object* v_a_5618_; lean_object* v___x_5619_; lean_object* v_us_5620_; lean_object* v___f_5621_; uint8_t v___x_5622_; lean_object* v___x_5623_; 
v_a_5618_ = lean_ctor_get(v___x_5617_, 0);
lean_inc_n(v_a_5618_, 2);
lean_dec_ref_known(v___x_5617_, 1);
v___x_5619_ = lean_box(0);
lean_inc(v_levelParams_5615_);
v_us_5620_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(v_levelParams_5615_, v___x_5619_);
v___f_5621_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1___boxed), 12, 5);
lean_closure_set(v___f_5621_, 0, v_numParams_5613_);
lean_closure_set(v___f_5621_, 1, v_name_5614_);
lean_closure_set(v___f_5621_, 2, v_us_5620_);
lean_closure_set(v___f_5621_, 3, v_ctorVal_5606_);
lean_closure_set(v___f_5621_, 4, v_a_5618_);
v___x_5622_ = 0;
v___x_5623_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_a_5618_, v___f_5621_, v___x_5622_, v_a_5607_, v_a_5608_, v_a_5609_, v_a_5610_);
return v___x_5623_;
}
else
{
lean_object* v_a_5624_; lean_object* v___x_5626_; uint8_t v_isShared_5627_; uint8_t v_isSharedCheck_5631_; 
lean_dec(v_name_5614_);
lean_dec(v_numParams_5613_);
lean_dec_ref(v_ctorVal_5606_);
v_a_5624_ = lean_ctor_get(v___x_5617_, 0);
v_isSharedCheck_5631_ = !lean_is_exclusive(v___x_5617_);
if (v_isSharedCheck_5631_ == 0)
{
v___x_5626_ = v___x_5617_;
v_isShared_5627_ = v_isSharedCheck_5631_;
goto v_resetjp_5625_;
}
else
{
lean_inc(v_a_5624_);
lean_dec(v___x_5617_);
v___x_5626_ = lean_box(0);
v_isShared_5627_ = v_isSharedCheck_5631_;
goto v_resetjp_5625_;
}
v_resetjp_5625_:
{
lean_object* v___x_5629_; 
if (v_isShared_5627_ == 0)
{
v___x_5629_ = v___x_5626_;
goto v_reusejp_5628_;
}
else
{
lean_object* v_reuseFailAlloc_5630_; 
v_reuseFailAlloc_5630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5630_, 0, v_a_5624_);
v___x_5629_ = v_reuseFailAlloc_5630_;
goto v_reusejp_5628_;
}
v_reusejp_5628_:
{
return v___x_5629_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___boxed(lean_object* v_ctorVal_5632_, lean_object* v_a_5633_, lean_object* v_a_5634_, lean_object* v_a_5635_, lean_object* v_a_5636_, lean_object* v_a_5637_){
_start:
{
lean_object* v_res_5638_; 
v_res_5638_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(v_ctorVal_5632_, v_a_5633_, v_a_5634_, v_a_5635_, v_a_5636_);
lean_dec(v_a_5636_);
lean_dec_ref(v_a_5635_);
lean_dec(v_a_5634_);
lean_dec_ref(v_a_5633_);
return v_res_5638_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1(void){
_start:
{
lean_object* v___x_5640_; lean_object* v___x_5641_; 
v___x_5640_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__0));
v___x_5641_ = l_Lean_stringToMessageData(v___x_5640_);
return v___x_5641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(lean_object* v_ctorVal_5642_, lean_object* v_a_5643_, lean_object* v_a_5644_, lean_object* v_a_5645_, lean_object* v_a_5646_){
_start:
{
lean_object* v_toConstantVal_5648_; lean_object* v_name_5649_; lean_object* v___x_5650_; lean_object* v___x_5651_; lean_object* v___x_5652_; lean_object* v___x_5653_; lean_object* v___x_5654_; lean_object* v___x_5655_; 
v_toConstantVal_5648_ = lean_ctor_get(v_ctorVal_5642_, 0);
lean_inc_ref(v_toConstantVal_5648_);
lean_dec_ref(v_ctorVal_5642_);
v_name_5649_ = lean_ctor_get(v_toConstantVal_5648_, 0);
lean_inc(v_name_5649_);
lean_dec_ref(v_toConstantVal_5648_);
v___x_5650_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1);
v___x_5651_ = l_Lean_MessageData_ofName(v_name_5649_);
v___x_5652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5652_, 0, v___x_5650_);
lean_ctor_set(v___x_5652_, 1, v___x_5651_);
v___x_5653_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_5654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5654_, 0, v___x_5652_);
lean_ctor_set(v___x_5654_, 1, v___x_5653_);
v___x_5655_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_5654_, v_a_5643_, v_a_5644_, v_a_5645_, v_a_5646_);
return v___x_5655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___boxed(lean_object* v_ctorVal_5656_, lean_object* v_a_5657_, lean_object* v_a_5658_, lean_object* v_a_5659_, lean_object* v_a_5660_, lean_object* v_a_5661_){
_start:
{
lean_object* v_res_5662_; 
v_res_5662_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5656_, v_a_5657_, v_a_5658_, v_a_5659_, v_a_5660_);
lean_dec(v_a_5660_);
lean_dec_ref(v_a_5659_);
lean_dec(v_a_5658_);
lean_dec_ref(v_a_5657_);
return v_res_5662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj(lean_object* v_00_u03b1_5663_, lean_object* v_ctorVal_5664_, lean_object* v_a_5665_, lean_object* v_a_5666_, lean_object* v_a_5667_, lean_object* v_a_5668_){
_start:
{
lean_object* v___x_5670_; 
v___x_5670_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5664_, v_a_5665_, v_a_5666_, v_a_5667_, v_a_5668_);
return v___x_5670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___boxed(lean_object* v_00_u03b1_5671_, lean_object* v_ctorVal_5672_, lean_object* v_a_5673_, lean_object* v_a_5674_, lean_object* v_a_5675_, lean_object* v_a_5676_, lean_object* v_a_5677_){
_start:
{
lean_object* v_res_5678_; 
v_res_5678_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj(v_00_u03b1_5671_, v_ctorVal_5672_, v_a_5673_, v_a_5674_, v_a_5675_, v_a_5676_);
lean_dec(v_a_5676_);
lean_dec_ref(v_a_5675_);
lean_dec(v_a_5674_);
lean_dec_ref(v_a_5673_);
return v_res_5678_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(lean_object* v_ctorVal_5684_, size_t v_sz_5685_, size_t v_i_5686_, lean_object* v_bs_5687_, lean_object* v___y_5688_, lean_object* v___y_5689_, lean_object* v___y_5690_, lean_object* v___y_5691_){
_start:
{
uint8_t v___x_5693_; 
v___x_5693_ = lean_usize_dec_lt(v_i_5686_, v_sz_5685_);
if (v___x_5693_ == 0)
{
lean_object* v___x_5694_; 
lean_dec_ref(v_ctorVal_5684_);
v___x_5694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5694_, 0, v_bs_5687_);
return v___x_5694_;
}
else
{
lean_object* v_v_5695_; lean_object* v___x_5696_; 
v_v_5695_ = lean_array_uget_borrowed(v_bs_5687_, v_i_5686_);
lean_inc(v___y_5691_);
lean_inc_ref(v___y_5690_);
lean_inc(v___y_5689_);
lean_inc_ref(v___y_5688_);
lean_inc(v_v_5695_);
v___x_5696_ = lean_infer_type(v_v_5695_, v___y_5688_, v___y_5689_, v___y_5690_, v___y_5691_);
if (lean_obj_tag(v___x_5696_) == 0)
{
lean_object* v_a_5697_; lean_object* v___x_5698_; 
v_a_5697_ = lean_ctor_get(v___x_5696_, 0);
lean_inc(v_a_5697_);
lean_dec_ref_known(v___x_5696_, 1);
v___x_5698_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_5697_, v___y_5689_);
if (lean_obj_tag(v___x_5698_) == 0)
{
lean_object* v_a_5699_; lean_object* v___x_5700_; lean_object* v_bs_x27_5701_; lean_object* v_a_5703_; lean_object* v___y_5709_; lean_object* v_lhs_5720_; lean_object* v_rhs_5721_; lean_object* v___x_5723_; uint8_t v___x_5724_; 
v_a_5699_ = lean_ctor_get(v___x_5698_, 0);
lean_inc(v_a_5699_);
lean_dec_ref_known(v___x_5698_, 1);
v___x_5700_ = lean_unsigned_to_nat(0u);
v_bs_x27_5701_ = lean_array_uset(v_bs_5687_, v_i_5686_, v___x_5700_);
v___x_5723_ = l_Lean_Expr_cleanupAnnotations(v_a_5699_);
v___x_5724_ = l_Lean_Expr_isApp(v___x_5723_);
if (v___x_5724_ == 0)
{
lean_object* v___x_5725_; 
lean_dec_ref(v___x_5723_);
lean_inc_ref(v_ctorVal_5684_);
v___x_5725_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5684_, v___y_5688_, v___y_5689_, v___y_5690_, v___y_5691_);
v___y_5709_ = v___x_5725_;
goto v___jp_5708_;
}
else
{
lean_object* v_arg_5726_; lean_object* v___x_5727_; uint8_t v___x_5728_; 
v_arg_5726_ = lean_ctor_get(v___x_5723_, 1);
lean_inc_ref(v_arg_5726_);
v___x_5727_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5723_);
v___x_5728_ = l_Lean_Expr_isApp(v___x_5727_);
if (v___x_5728_ == 0)
{
lean_object* v___x_5729_; 
lean_dec_ref(v___x_5727_);
lean_dec_ref(v_arg_5726_);
lean_inc_ref(v_ctorVal_5684_);
v___x_5729_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5684_, v___y_5688_, v___y_5689_, v___y_5690_, v___y_5691_);
v___y_5709_ = v___x_5729_;
goto v___jp_5708_;
}
else
{
lean_object* v_arg_5730_; lean_object* v___x_5731_; uint8_t v___x_5732_; 
v_arg_5730_ = lean_ctor_get(v___x_5727_, 1);
lean_inc_ref(v_arg_5730_);
v___x_5731_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5727_);
v___x_5732_ = l_Lean_Expr_isApp(v___x_5731_);
if (v___x_5732_ == 0)
{
lean_object* v___x_5733_; 
lean_dec_ref(v___x_5731_);
lean_dec_ref(v_arg_5730_);
lean_dec_ref(v_arg_5726_);
lean_inc_ref(v_ctorVal_5684_);
v___x_5733_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5684_, v___y_5688_, v___y_5689_, v___y_5690_, v___y_5691_);
v___y_5709_ = v___x_5733_;
goto v___jp_5708_;
}
else
{
lean_object* v_arg_5734_; lean_object* v___x_5735_; lean_object* v___x_5736_; uint8_t v___x_5737_; 
v_arg_5734_ = lean_ctor_get(v___x_5731_, 1);
lean_inc_ref(v_arg_5734_);
v___x_5735_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5731_);
v___x_5736_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__0));
v___x_5737_ = l_Lean_Expr_isConstOf(v___x_5735_, v___x_5736_);
if (v___x_5737_ == 0)
{
uint8_t v___x_5738_; 
lean_dec_ref(v_arg_5730_);
v___x_5738_ = l_Lean_Expr_isApp(v___x_5735_);
if (v___x_5738_ == 0)
{
lean_object* v___x_5739_; 
lean_dec_ref(v___x_5735_);
lean_dec_ref(v_arg_5734_);
lean_dec_ref(v_arg_5726_);
lean_inc_ref(v_ctorVal_5684_);
v___x_5739_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5684_, v___y_5688_, v___y_5689_, v___y_5690_, v___y_5691_);
v___y_5709_ = v___x_5739_;
goto v___jp_5708_;
}
else
{
lean_object* v___x_5740_; lean_object* v___x_5741_; uint8_t v___x_5742_; 
v___x_5740_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5735_);
v___x_5741_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__2));
v___x_5742_ = l_Lean_Expr_isConstOf(v___x_5740_, v___x_5741_);
lean_dec_ref(v___x_5740_);
if (v___x_5742_ == 0)
{
lean_object* v___x_5743_; 
lean_dec_ref(v_arg_5734_);
lean_dec_ref(v_arg_5726_);
lean_inc_ref(v_ctorVal_5684_);
v___x_5743_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5684_, v___y_5688_, v___y_5689_, v___y_5690_, v___y_5691_);
v___y_5709_ = v___x_5743_;
goto v___jp_5708_;
}
else
{
v_lhs_5720_ = v_arg_5734_;
v_rhs_5721_ = v_arg_5726_;
goto v___jp_5719_;
}
}
}
else
{
lean_dec_ref(v___x_5735_);
lean_dec_ref(v_arg_5734_);
v_lhs_5720_ = v_arg_5730_;
v_rhs_5721_ = v_arg_5726_;
goto v___jp_5719_;
}
}
}
}
v___jp_5702_:
{
size_t v___x_5704_; size_t v___x_5705_; lean_object* v___x_5706_; 
v___x_5704_ = ((size_t)1ULL);
v___x_5705_ = lean_usize_add(v_i_5686_, v___x_5704_);
v___x_5706_ = lean_array_uset(v_bs_x27_5701_, v_i_5686_, v_a_5703_);
v_i_5686_ = v___x_5705_;
v_bs_5687_ = v___x_5706_;
goto _start;
}
v___jp_5708_:
{
if (lean_obj_tag(v___y_5709_) == 0)
{
lean_object* v_a_5710_; 
v_a_5710_ = lean_ctor_get(v___y_5709_, 0);
lean_inc(v_a_5710_);
lean_dec_ref_known(v___y_5709_, 1);
v_a_5703_ = v_a_5710_;
goto v___jp_5702_;
}
else
{
lean_object* v_a_5711_; lean_object* v___x_5713_; uint8_t v_isShared_5714_; uint8_t v_isSharedCheck_5718_; 
lean_dec_ref(v_bs_x27_5701_);
lean_dec_ref(v_ctorVal_5684_);
v_a_5711_ = lean_ctor_get(v___y_5709_, 0);
v_isSharedCheck_5718_ = !lean_is_exclusive(v___y_5709_);
if (v_isSharedCheck_5718_ == 0)
{
v___x_5713_ = v___y_5709_;
v_isShared_5714_ = v_isSharedCheck_5718_;
goto v_resetjp_5712_;
}
else
{
lean_inc(v_a_5711_);
lean_dec(v___y_5709_);
v___x_5713_ = lean_box(0);
v_isShared_5714_ = v_isSharedCheck_5718_;
goto v_resetjp_5712_;
}
v_resetjp_5712_:
{
lean_object* v___x_5716_; 
if (v_isShared_5714_ == 0)
{
v___x_5716_ = v___x_5713_;
goto v_reusejp_5715_;
}
else
{
lean_object* v_reuseFailAlloc_5717_; 
v_reuseFailAlloc_5717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5717_, 0, v_a_5711_);
v___x_5716_ = v_reuseFailAlloc_5717_;
goto v_reusejp_5715_;
}
v_reusejp_5715_:
{
return v___x_5716_;
}
}
}
}
v___jp_5719_:
{
lean_object* v___x_5722_; 
v___x_5722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5722_, 0, v_lhs_5720_);
lean_ctor_set(v___x_5722_, 1, v_rhs_5721_);
v_a_5703_ = v___x_5722_;
goto v___jp_5702_;
}
}
else
{
lean_object* v_a_5744_; lean_object* v___x_5746_; uint8_t v_isShared_5747_; uint8_t v_isSharedCheck_5751_; 
lean_dec_ref(v_bs_5687_);
lean_dec_ref(v_ctorVal_5684_);
v_a_5744_ = lean_ctor_get(v___x_5698_, 0);
v_isSharedCheck_5751_ = !lean_is_exclusive(v___x_5698_);
if (v_isSharedCheck_5751_ == 0)
{
v___x_5746_ = v___x_5698_;
v_isShared_5747_ = v_isSharedCheck_5751_;
goto v_resetjp_5745_;
}
else
{
lean_inc(v_a_5744_);
lean_dec(v___x_5698_);
v___x_5746_ = lean_box(0);
v_isShared_5747_ = v_isSharedCheck_5751_;
goto v_resetjp_5745_;
}
v_resetjp_5745_:
{
lean_object* v___x_5749_; 
if (v_isShared_5747_ == 0)
{
v___x_5749_ = v___x_5746_;
goto v_reusejp_5748_;
}
else
{
lean_object* v_reuseFailAlloc_5750_; 
v_reuseFailAlloc_5750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5750_, 0, v_a_5744_);
v___x_5749_ = v_reuseFailAlloc_5750_;
goto v_reusejp_5748_;
}
v_reusejp_5748_:
{
return v___x_5749_;
}
}
}
}
else
{
lean_object* v_a_5752_; lean_object* v___x_5754_; uint8_t v_isShared_5755_; uint8_t v_isSharedCheck_5759_; 
lean_dec_ref(v_bs_5687_);
lean_dec_ref(v_ctorVal_5684_);
v_a_5752_ = lean_ctor_get(v___x_5696_, 0);
v_isSharedCheck_5759_ = !lean_is_exclusive(v___x_5696_);
if (v_isSharedCheck_5759_ == 0)
{
v___x_5754_ = v___x_5696_;
v_isShared_5755_ = v_isSharedCheck_5759_;
goto v_resetjp_5753_;
}
else
{
lean_inc(v_a_5752_);
lean_dec(v___x_5696_);
v___x_5754_ = lean_box(0);
v_isShared_5755_ = v_isSharedCheck_5759_;
goto v_resetjp_5753_;
}
v_resetjp_5753_:
{
lean_object* v___x_5757_; 
if (v_isShared_5755_ == 0)
{
v___x_5757_ = v___x_5754_;
goto v_reusejp_5756_;
}
else
{
lean_object* v_reuseFailAlloc_5758_; 
v_reuseFailAlloc_5758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5758_, 0, v_a_5752_);
v___x_5757_ = v_reuseFailAlloc_5758_;
goto v_reusejp_5756_;
}
v_reusejp_5756_:
{
return v___x_5757_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___boxed(lean_object* v_ctorVal_5760_, lean_object* v_sz_5761_, lean_object* v_i_5762_, lean_object* v_bs_5763_, lean_object* v___y_5764_, lean_object* v___y_5765_, lean_object* v___y_5766_, lean_object* v___y_5767_, lean_object* v___y_5768_){
_start:
{
size_t v_sz_boxed_5769_; size_t v_i_boxed_5770_; lean_object* v_res_5771_; 
v_sz_boxed_5769_ = lean_unbox_usize(v_sz_5761_);
lean_dec(v_sz_5761_);
v_i_boxed_5770_ = lean_unbox_usize(v_i_5762_);
lean_dec(v_i_5762_);
v_res_5771_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(v_ctorVal_5760_, v_sz_boxed_5769_, v_i_boxed_5770_, v_bs_5763_, v___y_5764_, v___y_5765_, v___y_5766_, v___y_5767_);
lean_dec(v___y_5767_);
lean_dec_ref(v___y_5766_);
lean_dec(v___y_5765_);
lean_dec_ref(v___y_5764_);
return v_res_5771_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5773_; lean_object* v___x_5774_; 
v___x_5773_ = lean_unsigned_to_nat(0u);
v___x_5774_ = l_Lean_Level_ofNat(v___x_5773_);
return v___x_5774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0(lean_object* v_ctorVal_5775_, lean_object* v_us_5776_, lean_object* v_numIndices_5777_, lean_object* v_xs_5778_, lean_object* v_type_5779_, lean_object* v___y_5780_, lean_object* v___y_5781_, lean_object* v___y_5782_, lean_object* v___y_5783_){
_start:
{
lean_object* v_toConstantVal_5785_; lean_object* v_induct_5786_; lean_object* v_numParams_5787_; lean_object* v___x_5788_; lean_object* v_noConfusionName_5789_; lean_object* v___x_5790_; lean_object* v___x_5791_; lean_object* v___x_5792_; lean_object* v_noConfusion_5793_; lean_object* v_noConfusion_5794_; lean_object* v_lower_5796_; lean_object* v_upper_5797_; lean_object* v___x_5904_; lean_object* v___x_5905_; lean_object* v___x_5906_; lean_object* v___x_5907_; lean_object* v_n_5908_; uint8_t v___x_5909_; 
v_toConstantVal_5785_ = lean_ctor_get(v_ctorVal_5775_, 0);
v_induct_5786_ = lean_ctor_get(v_ctorVal_5775_, 1);
v_numParams_5787_ = lean_ctor_get(v_ctorVal_5775_, 3);
v___x_5788_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__0));
lean_inc(v_induct_5786_);
v_noConfusionName_5789_ = l_Lean_Name_str___override(v_induct_5786_, v___x_5788_);
v___x_5790_ = lean_unsigned_to_nat(0u);
v___x_5791_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1);
v___x_5792_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5792_, 0, v___x_5791_);
lean_ctor_set(v___x_5792_, 1, v_us_5776_);
v_noConfusion_5793_ = l_Lean_mkConst(v_noConfusionName_5789_, v___x_5792_);
v_noConfusion_5794_ = l_Lean_Expr_app___override(v_noConfusion_5793_, v_type_5779_);
v___x_5904_ = lean_array_get_size(v_xs_5778_);
v___x_5905_ = lean_nat_sub(v___x_5904_, v_numParams_5787_);
v___x_5906_ = lean_nat_sub(v___x_5905_, v_numIndices_5777_);
lean_dec(v___x_5905_);
v___x_5907_ = lean_unsigned_to_nat(1u);
v_n_5908_ = lean_nat_sub(v___x_5906_, v___x_5907_);
lean_dec(v___x_5906_);
v___x_5909_ = lean_nat_dec_le(v_n_5908_, v___x_5790_);
if (v___x_5909_ == 0)
{
v_lower_5796_ = v_n_5908_;
v_upper_5797_ = v___x_5904_;
goto v___jp_5795_;
}
else
{
lean_dec(v_n_5908_);
v_lower_5796_ = v___x_5790_;
v_upper_5797_ = v___x_5904_;
goto v___jp_5795_;
}
v___jp_5795_:
{
lean_object* v___x_5798_; lean_object* v___x_5799_; lean_object* v_eqs_5800_; size_t v_sz_5801_; size_t v___x_5802_; lean_object* v___x_5803_; 
lean_inc_ref(v_xs_5778_);
v___x_5798_ = l_Array_toSubarray___redArg(v_xs_5778_, v_lower_5796_, v_upper_5797_);
v___x_5799_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v_eqs_5800_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(v___x_5798_, v___x_5799_);
v_sz_5801_ = lean_array_size(v_eqs_5800_);
v___x_5802_ = ((size_t)0ULL);
lean_inc_ref(v_eqs_5800_);
lean_inc_ref(v_ctorVal_5775_);
v___x_5803_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(v_ctorVal_5775_, v_sz_5801_, v___x_5802_, v_eqs_5800_, v___y_5780_, v___y_5781_, v___y_5782_, v___y_5783_);
if (lean_obj_tag(v___x_5803_) == 0)
{
lean_object* v_a_5804_; lean_object* v___x_5805_; lean_object* v_fst_5806_; lean_object* v_snd_5807_; lean_object* v___x_5808_; lean_object* v___x_5809_; lean_object* v___x_5810_; lean_object* v___x_5811_; 
v_a_5804_ = lean_ctor_get(v___x_5803_, 0);
lean_inc(v_a_5804_);
lean_dec_ref_known(v___x_5803_, 1);
v___x_5805_ = l_Array_unzip___redArg(v_a_5804_);
lean_dec(v_a_5804_);
v_fst_5806_ = lean_ctor_get(v___x_5805_, 0);
lean_inc(v_fst_5806_);
v_snd_5807_ = lean_ctor_get(v___x_5805_, 1);
lean_inc(v_snd_5807_);
lean_dec_ref(v___x_5805_);
v___x_5808_ = l_Lean_mkAppN(v_noConfusion_5794_, v_fst_5806_);
lean_dec(v_fst_5806_);
v___x_5809_ = l_Lean_mkAppN(v___x_5808_, v_snd_5807_);
lean_dec(v_snd_5807_);
v___x_5810_ = l_Lean_mkAppN(v___x_5809_, v_eqs_5800_);
lean_dec_ref(v_eqs_5800_);
lean_inc(v___y_5783_);
lean_inc_ref(v___y_5782_);
lean_inc(v___y_5781_);
lean_inc_ref(v___y_5780_);
lean_inc_ref(v___x_5810_);
v___x_5811_ = lean_infer_type(v___x_5810_, v___y_5780_, v___y_5781_, v___y_5782_, v___y_5783_);
if (lean_obj_tag(v___x_5811_) == 0)
{
lean_object* v_a_5812_; lean_object* v___x_5813_; 
v_a_5812_ = lean_ctor_get(v___x_5811_, 0);
lean_inc(v_a_5812_);
lean_dec_ref_known(v___x_5811_, 1);
lean_inc(v___y_5783_);
lean_inc_ref(v___y_5782_);
lean_inc(v___y_5781_);
lean_inc_ref(v___y_5780_);
v___x_5813_ = lean_whnf(v_a_5812_, v___y_5780_, v___y_5781_, v___y_5782_, v___y_5783_);
if (lean_obj_tag(v___x_5813_) == 0)
{
lean_object* v_a_5814_; 
v_a_5814_ = lean_ctor_get(v___x_5813_, 0);
lean_inc(v_a_5814_);
lean_dec_ref_known(v___x_5813_, 1);
if (lean_obj_tag(v_a_5814_) == 7)
{
lean_object* v_binderType_5815_; lean_object* v___x_5816_; lean_object* v___x_5817_; 
lean_inc_ref(v_toConstantVal_5785_);
lean_dec_ref(v_ctorVal_5775_);
v_binderType_5815_ = lean_ctor_get(v_a_5814_, 1);
lean_inc_ref(v_binderType_5815_);
lean_dec_ref_known(v_a_5814_, 3);
v___x_5816_ = lean_box(0);
v___x_5817_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_binderType_5815_, v___x_5816_, v___y_5780_, v___y_5781_, v___y_5782_, v___y_5783_);
if (lean_obj_tag(v___x_5817_) == 0)
{
lean_object* v_a_5818_; lean_object* v___x_5819_; lean_object* v___x_5820_; 
v_a_5818_ = lean_ctor_get(v___x_5817_, 0);
lean_inc(v_a_5818_);
lean_dec_ref_known(v___x_5817_, 1);
v___x_5819_ = l_Lean_Expr_mvarId_x21(v_a_5818_);
v___x_5820_ = l_Lean_MVarId_intros(v___x_5819_, v___y_5780_, v___y_5781_, v___y_5782_, v___y_5783_);
if (lean_obj_tag(v___x_5820_) == 0)
{
lean_object* v_a_5821_; lean_object* v_snd_5822_; lean_object* v_name_5823_; lean_object* v___x_5824_; 
v_a_5821_ = lean_ctor_get(v___x_5820_, 0);
lean_inc(v_a_5821_);
lean_dec_ref_known(v___x_5820_, 1);
v_snd_5822_ = lean_ctor_get(v_a_5821_, 1);
lean_inc(v_snd_5822_);
lean_dec(v_a_5821_);
v_name_5823_ = lean_ctor_get(v_toConstantVal_5785_, 0);
lean_inc(v_name_5823_);
lean_dec_ref(v_toConstantVal_5785_);
v___x_5824_ = l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(v_snd_5822_, v_name_5823_, v___y_5780_, v___y_5781_, v___y_5782_, v___y_5783_);
if (lean_obj_tag(v___x_5824_) == 0)
{
lean_object* v___x_5825_; lean_object* v___x_5826_; lean_object* v_a_5827_; lean_object* v___x_5829_; uint8_t v_isShared_5830_; uint8_t v_isSharedCheck_5854_; 
lean_dec_ref_known(v___x_5824_, 1);
v___x_5825_ = l_Lean_Expr_app___override(v___x_5810_, v_a_5818_);
v___x_5826_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v___x_5825_, v___y_5781_);
v_a_5827_ = lean_ctor_get(v___x_5826_, 0);
v_isSharedCheck_5854_ = !lean_is_exclusive(v___x_5826_);
if (v_isSharedCheck_5854_ == 0)
{
v___x_5829_ = v___x_5826_;
v_isShared_5830_ = v_isSharedCheck_5854_;
goto v_resetjp_5828_;
}
else
{
lean_inc(v_a_5827_);
lean_dec(v___x_5826_);
v___x_5829_ = lean_box(0);
v_isShared_5830_ = v_isSharedCheck_5854_;
goto v_resetjp_5828_;
}
v_resetjp_5828_:
{
uint8_t v___x_5831_; uint8_t v___x_5832_; uint8_t v___x_5833_; lean_object* v___x_5834_; 
v___x_5831_ = 0;
v___x_5832_ = 1;
v___x_5833_ = 1;
v___x_5834_ = l_Lean_Meta_mkLambdaFVars(v_xs_5778_, v_a_5827_, v___x_5831_, v___x_5832_, v___x_5831_, v___x_5832_, v___x_5833_, v___y_5780_, v___y_5781_, v___y_5782_, v___y_5783_);
lean_dec_ref(v_xs_5778_);
if (lean_obj_tag(v___x_5834_) == 0)
{
lean_object* v_a_5835_; lean_object* v___x_5837_; uint8_t v_isShared_5838_; uint8_t v_isSharedCheck_5845_; 
v_a_5835_ = lean_ctor_get(v___x_5834_, 0);
v_isSharedCheck_5845_ = !lean_is_exclusive(v___x_5834_);
if (v_isSharedCheck_5845_ == 0)
{
v___x_5837_ = v___x_5834_;
v_isShared_5838_ = v_isSharedCheck_5845_;
goto v_resetjp_5836_;
}
else
{
lean_inc(v_a_5835_);
lean_dec(v___x_5834_);
v___x_5837_ = lean_box(0);
v_isShared_5838_ = v_isSharedCheck_5845_;
goto v_resetjp_5836_;
}
v_resetjp_5836_:
{
lean_object* v___x_5840_; 
if (v_isShared_5830_ == 0)
{
lean_ctor_set_tag(v___x_5829_, 1);
lean_ctor_set(v___x_5829_, 0, v_a_5835_);
v___x_5840_ = v___x_5829_;
goto v_reusejp_5839_;
}
else
{
lean_object* v_reuseFailAlloc_5844_; 
v_reuseFailAlloc_5844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5844_, 0, v_a_5835_);
v___x_5840_ = v_reuseFailAlloc_5844_;
goto v_reusejp_5839_;
}
v_reusejp_5839_:
{
lean_object* v___x_5842_; 
if (v_isShared_5838_ == 0)
{
lean_ctor_set(v___x_5837_, 0, v___x_5840_);
v___x_5842_ = v___x_5837_;
goto v_reusejp_5841_;
}
else
{
lean_object* v_reuseFailAlloc_5843_; 
v_reuseFailAlloc_5843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5843_, 0, v___x_5840_);
v___x_5842_ = v_reuseFailAlloc_5843_;
goto v_reusejp_5841_;
}
v_reusejp_5841_:
{
return v___x_5842_;
}
}
}
}
else
{
lean_object* v_a_5846_; lean_object* v___x_5848_; uint8_t v_isShared_5849_; uint8_t v_isSharedCheck_5853_; 
lean_del_object(v___x_5829_);
v_a_5846_ = lean_ctor_get(v___x_5834_, 0);
v_isSharedCheck_5853_ = !lean_is_exclusive(v___x_5834_);
if (v_isSharedCheck_5853_ == 0)
{
v___x_5848_ = v___x_5834_;
v_isShared_5849_ = v_isSharedCheck_5853_;
goto v_resetjp_5847_;
}
else
{
lean_inc(v_a_5846_);
lean_dec(v___x_5834_);
v___x_5848_ = lean_box(0);
v_isShared_5849_ = v_isSharedCheck_5853_;
goto v_resetjp_5847_;
}
v_resetjp_5847_:
{
lean_object* v___x_5851_; 
if (v_isShared_5849_ == 0)
{
v___x_5851_ = v___x_5848_;
goto v_reusejp_5850_;
}
else
{
lean_object* v_reuseFailAlloc_5852_; 
v_reuseFailAlloc_5852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5852_, 0, v_a_5846_);
v___x_5851_ = v_reuseFailAlloc_5852_;
goto v_reusejp_5850_;
}
v_reusejp_5850_:
{
return v___x_5851_;
}
}
}
}
}
else
{
lean_object* v_a_5855_; lean_object* v___x_5857_; uint8_t v_isShared_5858_; uint8_t v_isSharedCheck_5862_; 
lean_dec(v_a_5818_);
lean_dec_ref(v___x_5810_);
lean_dec_ref(v_xs_5778_);
v_a_5855_ = lean_ctor_get(v___x_5824_, 0);
v_isSharedCheck_5862_ = !lean_is_exclusive(v___x_5824_);
if (v_isSharedCheck_5862_ == 0)
{
v___x_5857_ = v___x_5824_;
v_isShared_5858_ = v_isSharedCheck_5862_;
goto v_resetjp_5856_;
}
else
{
lean_inc(v_a_5855_);
lean_dec(v___x_5824_);
v___x_5857_ = lean_box(0);
v_isShared_5858_ = v_isSharedCheck_5862_;
goto v_resetjp_5856_;
}
v_resetjp_5856_:
{
lean_object* v___x_5860_; 
if (v_isShared_5858_ == 0)
{
v___x_5860_ = v___x_5857_;
goto v_reusejp_5859_;
}
else
{
lean_object* v_reuseFailAlloc_5861_; 
v_reuseFailAlloc_5861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5861_, 0, v_a_5855_);
v___x_5860_ = v_reuseFailAlloc_5861_;
goto v_reusejp_5859_;
}
v_reusejp_5859_:
{
return v___x_5860_;
}
}
}
}
else
{
lean_object* v_a_5863_; lean_object* v___x_5865_; uint8_t v_isShared_5866_; uint8_t v_isSharedCheck_5870_; 
lean_dec(v_a_5818_);
lean_dec_ref(v___x_5810_);
lean_dec_ref(v_toConstantVal_5785_);
lean_dec_ref(v_xs_5778_);
v_a_5863_ = lean_ctor_get(v___x_5820_, 0);
v_isSharedCheck_5870_ = !lean_is_exclusive(v___x_5820_);
if (v_isSharedCheck_5870_ == 0)
{
v___x_5865_ = v___x_5820_;
v_isShared_5866_ = v_isSharedCheck_5870_;
goto v_resetjp_5864_;
}
else
{
lean_inc(v_a_5863_);
lean_dec(v___x_5820_);
v___x_5865_ = lean_box(0);
v_isShared_5866_ = v_isSharedCheck_5870_;
goto v_resetjp_5864_;
}
v_resetjp_5864_:
{
lean_object* v___x_5868_; 
if (v_isShared_5866_ == 0)
{
v___x_5868_ = v___x_5865_;
goto v_reusejp_5867_;
}
else
{
lean_object* v_reuseFailAlloc_5869_; 
v_reuseFailAlloc_5869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5869_, 0, v_a_5863_);
v___x_5868_ = v_reuseFailAlloc_5869_;
goto v_reusejp_5867_;
}
v_reusejp_5867_:
{
return v___x_5868_;
}
}
}
}
else
{
lean_object* v_a_5871_; lean_object* v___x_5873_; uint8_t v_isShared_5874_; uint8_t v_isSharedCheck_5878_; 
lean_dec_ref(v___x_5810_);
lean_dec_ref(v_toConstantVal_5785_);
lean_dec_ref(v_xs_5778_);
v_a_5871_ = lean_ctor_get(v___x_5817_, 0);
v_isSharedCheck_5878_ = !lean_is_exclusive(v___x_5817_);
if (v_isSharedCheck_5878_ == 0)
{
v___x_5873_ = v___x_5817_;
v_isShared_5874_ = v_isSharedCheck_5878_;
goto v_resetjp_5872_;
}
else
{
lean_inc(v_a_5871_);
lean_dec(v___x_5817_);
v___x_5873_ = lean_box(0);
v_isShared_5874_ = v_isSharedCheck_5878_;
goto v_resetjp_5872_;
}
v_resetjp_5872_:
{
lean_object* v___x_5876_; 
if (v_isShared_5874_ == 0)
{
v___x_5876_ = v___x_5873_;
goto v_reusejp_5875_;
}
else
{
lean_object* v_reuseFailAlloc_5877_; 
v_reuseFailAlloc_5877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5877_, 0, v_a_5871_);
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
lean_object* v___x_5879_; 
lean_dec(v_a_5814_);
lean_dec_ref(v___x_5810_);
lean_dec_ref(v_xs_5778_);
v___x_5879_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5775_, v___y_5780_, v___y_5781_, v___y_5782_, v___y_5783_);
return v___x_5879_;
}
}
else
{
lean_object* v_a_5880_; lean_object* v___x_5882_; uint8_t v_isShared_5883_; uint8_t v_isSharedCheck_5887_; 
lean_dec_ref(v___x_5810_);
lean_dec_ref(v_xs_5778_);
lean_dec_ref(v_ctorVal_5775_);
v_a_5880_ = lean_ctor_get(v___x_5813_, 0);
v_isSharedCheck_5887_ = !lean_is_exclusive(v___x_5813_);
if (v_isSharedCheck_5887_ == 0)
{
v___x_5882_ = v___x_5813_;
v_isShared_5883_ = v_isSharedCheck_5887_;
goto v_resetjp_5881_;
}
else
{
lean_inc(v_a_5880_);
lean_dec(v___x_5813_);
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
else
{
lean_object* v_a_5888_; lean_object* v___x_5890_; uint8_t v_isShared_5891_; uint8_t v_isSharedCheck_5895_; 
lean_dec_ref(v___x_5810_);
lean_dec_ref(v_xs_5778_);
lean_dec_ref(v_ctorVal_5775_);
v_a_5888_ = lean_ctor_get(v___x_5811_, 0);
v_isSharedCheck_5895_ = !lean_is_exclusive(v___x_5811_);
if (v_isSharedCheck_5895_ == 0)
{
v___x_5890_ = v___x_5811_;
v_isShared_5891_ = v_isSharedCheck_5895_;
goto v_resetjp_5889_;
}
else
{
lean_inc(v_a_5888_);
lean_dec(v___x_5811_);
v___x_5890_ = lean_box(0);
v_isShared_5891_ = v_isSharedCheck_5895_;
goto v_resetjp_5889_;
}
v_resetjp_5889_:
{
lean_object* v___x_5893_; 
if (v_isShared_5891_ == 0)
{
v___x_5893_ = v___x_5890_;
goto v_reusejp_5892_;
}
else
{
lean_object* v_reuseFailAlloc_5894_; 
v_reuseFailAlloc_5894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5894_, 0, v_a_5888_);
v___x_5893_ = v_reuseFailAlloc_5894_;
goto v_reusejp_5892_;
}
v_reusejp_5892_:
{
return v___x_5893_;
}
}
}
}
else
{
lean_object* v_a_5896_; lean_object* v___x_5898_; uint8_t v_isShared_5899_; uint8_t v_isSharedCheck_5903_; 
lean_dec_ref(v_eqs_5800_);
lean_dec_ref(v_noConfusion_5794_);
lean_dec_ref(v_xs_5778_);
lean_dec_ref(v_ctorVal_5775_);
v_a_5896_ = lean_ctor_get(v___x_5803_, 0);
v_isSharedCheck_5903_ = !lean_is_exclusive(v___x_5803_);
if (v_isSharedCheck_5903_ == 0)
{
v___x_5898_ = v___x_5803_;
v_isShared_5899_ = v_isSharedCheck_5903_;
goto v_resetjp_5897_;
}
else
{
lean_inc(v_a_5896_);
lean_dec(v___x_5803_);
v___x_5898_ = lean_box(0);
v_isShared_5899_ = v_isSharedCheck_5903_;
goto v_resetjp_5897_;
}
v_resetjp_5897_:
{
lean_object* v___x_5901_; 
if (v_isShared_5899_ == 0)
{
v___x_5901_ = v___x_5898_;
goto v_reusejp_5900_;
}
else
{
lean_object* v_reuseFailAlloc_5902_; 
v_reuseFailAlloc_5902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5902_, 0, v_a_5896_);
v___x_5901_ = v_reuseFailAlloc_5902_;
goto v_reusejp_5900_;
}
v_reusejp_5900_:
{
return v___x_5901_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___boxed(lean_object* v_ctorVal_5910_, lean_object* v_us_5911_, lean_object* v_numIndices_5912_, lean_object* v_xs_5913_, lean_object* v_type_5914_, lean_object* v___y_5915_, lean_object* v___y_5916_, lean_object* v___y_5917_, lean_object* v___y_5918_, lean_object* v___y_5919_){
_start:
{
lean_object* v_res_5920_; 
v_res_5920_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0(v_ctorVal_5910_, v_us_5911_, v_numIndices_5912_, v_xs_5913_, v_type_5914_, v___y_5915_, v___y_5916_, v___y_5917_, v___y_5918_);
lean_dec(v___y_5918_);
lean_dec_ref(v___y_5917_);
lean_dec(v___y_5916_);
lean_dec_ref(v___y_5915_);
lean_dec(v_numIndices_5912_);
return v_res_5920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(lean_object* v_ctorVal_5921_, lean_object* v_typeInfo_5922_, lean_object* v_a_5923_, lean_object* v_a_5924_, lean_object* v_a_5925_, lean_object* v_a_5926_){
_start:
{
lean_object* v_thmType_5928_; lean_object* v_us_5929_; lean_object* v_numIndices_5930_; lean_object* v___f_5931_; uint8_t v___x_5932_; lean_object* v___x_5933_; 
v_thmType_5928_ = lean_ctor_get(v_typeInfo_5922_, 0);
lean_inc_ref(v_thmType_5928_);
v_us_5929_ = lean_ctor_get(v_typeInfo_5922_, 1);
lean_inc(v_us_5929_);
v_numIndices_5930_ = lean_ctor_get(v_typeInfo_5922_, 2);
lean_inc(v_numIndices_5930_);
lean_dec_ref(v_typeInfo_5922_);
v___f_5931_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___boxed), 10, 3);
lean_closure_set(v___f_5931_, 0, v_ctorVal_5921_);
lean_closure_set(v___f_5931_, 1, v_us_5929_);
lean_closure_set(v___f_5931_, 2, v_numIndices_5930_);
v___x_5932_ = 0;
v___x_5933_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_thmType_5928_, v___f_5931_, v___x_5932_, v___x_5932_, v_a_5923_, v_a_5924_, v_a_5925_, v_a_5926_);
return v___x_5933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___boxed(lean_object* v_ctorVal_5934_, lean_object* v_typeInfo_5935_, lean_object* v_a_5936_, lean_object* v_a_5937_, lean_object* v_a_5938_, lean_object* v_a_5939_, lean_object* v_a_5940_){
_start:
{
lean_object* v_res_5941_; 
v_res_5941_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(v_ctorVal_5934_, v_typeInfo_5935_, v_a_5936_, v_a_5937_, v_a_5938_, v_a_5939_);
lean_dec(v_a_5939_);
lean_dec_ref(v_a_5938_);
lean_dec(v_a_5937_);
lean_dec_ref(v_a_5936_);
return v_res_5941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHInjectiveTheoremNameFor(lean_object* v_ctorName_5944_){
_start:
{
lean_object* v___x_5945_; lean_object* v___x_5946_; 
v___x_5945_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0));
v___x_5946_ = l_Lean_Name_str___override(v_ctorName_5944_, v___x_5945_);
return v___x_5946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(lean_object* v_thmName_5947_, lean_object* v_ctorVal_5948_, lean_object* v_a_5949_, lean_object* v_a_5950_, lean_object* v_a_5951_, lean_object* v_a_5952_){
_start:
{
lean_object* v___x_5954_; 
lean_inc_ref(v_ctorVal_5948_);
v___x_5954_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(v_ctorVal_5948_, v_a_5949_, v_a_5950_, v_a_5951_, v_a_5952_);
if (lean_obj_tag(v___x_5954_) == 0)
{
lean_object* v_a_5955_; lean_object* v___x_5957_; uint8_t v_isShared_5958_; uint8_t v_isSharedCheck_6016_; 
v_a_5955_ = lean_ctor_get(v___x_5954_, 0);
v_isSharedCheck_6016_ = !lean_is_exclusive(v___x_5954_);
if (v_isSharedCheck_6016_ == 0)
{
v___x_5957_ = v___x_5954_;
v_isShared_5958_ = v_isSharedCheck_6016_;
goto v_resetjp_5956_;
}
else
{
lean_inc(v_a_5955_);
lean_dec(v___x_5954_);
v___x_5957_ = lean_box(0);
v_isShared_5958_ = v_isSharedCheck_6016_;
goto v_resetjp_5956_;
}
v_resetjp_5956_:
{
if (lean_obj_tag(v_a_5955_) == 1)
{
lean_object* v_val_5959_; lean_object* v___x_5960_; 
lean_del_object(v___x_5957_);
v_val_5959_ = lean_ctor_get(v_a_5955_, 0);
lean_inc_n(v_val_5959_, 2);
lean_dec_ref_known(v_a_5955_, 1);
lean_inc_ref(v_ctorVal_5948_);
v___x_5960_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(v_ctorVal_5948_, v_val_5959_, v_a_5949_, v_a_5950_, v_a_5951_, v_a_5952_);
if (lean_obj_tag(v___x_5960_) == 0)
{
lean_object* v_a_5961_; lean_object* v___x_5963_; uint8_t v_isShared_5964_; uint8_t v_isSharedCheck_6003_; 
v_a_5961_ = lean_ctor_get(v___x_5960_, 0);
v_isSharedCheck_6003_ = !lean_is_exclusive(v___x_5960_);
if (v_isSharedCheck_6003_ == 0)
{
v___x_5963_ = v___x_5960_;
v_isShared_5964_ = v_isSharedCheck_6003_;
goto v_resetjp_5962_;
}
else
{
lean_inc(v_a_5961_);
lean_dec(v___x_5960_);
v___x_5963_ = lean_box(0);
v_isShared_5964_ = v_isSharedCheck_6003_;
goto v_resetjp_5962_;
}
v_resetjp_5962_:
{
if (lean_obj_tag(v_a_5961_) == 1)
{
lean_object* v_toConstantVal_5965_; lean_object* v_val_5966_; lean_object* v___x_5968_; uint8_t v_isShared_5969_; uint8_t v_isSharedCheck_5998_; 
v_toConstantVal_5965_ = lean_ctor_get(v_ctorVal_5948_, 0);
lean_inc_ref(v_toConstantVal_5965_);
lean_dec_ref(v_ctorVal_5948_);
v_val_5966_ = lean_ctor_get(v_a_5961_, 0);
v_isSharedCheck_5998_ = !lean_is_exclusive(v_a_5961_);
if (v_isSharedCheck_5998_ == 0)
{
v___x_5968_ = v_a_5961_;
v_isShared_5969_ = v_isSharedCheck_5998_;
goto v_resetjp_5967_;
}
else
{
lean_inc(v_val_5966_);
lean_dec(v_a_5961_);
v___x_5968_ = lean_box(0);
v_isShared_5969_ = v_isSharedCheck_5998_;
goto v_resetjp_5967_;
}
v_resetjp_5967_:
{
lean_object* v_levelParams_5970_; lean_object* v___x_5972_; uint8_t v_isShared_5973_; uint8_t v_isSharedCheck_5995_; 
v_levelParams_5970_ = lean_ctor_get(v_toConstantVal_5965_, 1);
v_isSharedCheck_5995_ = !lean_is_exclusive(v_toConstantVal_5965_);
if (v_isSharedCheck_5995_ == 0)
{
lean_object* v_unused_5996_; lean_object* v_unused_5997_; 
v_unused_5996_ = lean_ctor_get(v_toConstantVal_5965_, 2);
lean_dec(v_unused_5996_);
v_unused_5997_ = lean_ctor_get(v_toConstantVal_5965_, 0);
lean_dec(v_unused_5997_);
v___x_5972_ = v_toConstantVal_5965_;
v_isShared_5973_ = v_isSharedCheck_5995_;
goto v_resetjp_5971_;
}
else
{
lean_inc(v_levelParams_5970_);
lean_dec(v_toConstantVal_5965_);
v___x_5972_ = lean_box(0);
v_isShared_5973_ = v_isSharedCheck_5995_;
goto v_resetjp_5971_;
}
v_resetjp_5971_:
{
lean_object* v_thmType_5974_; lean_object* v___x_5976_; uint8_t v_isShared_5977_; uint8_t v_isSharedCheck_5992_; 
v_thmType_5974_ = lean_ctor_get(v_val_5959_, 0);
v_isSharedCheck_5992_ = !lean_is_exclusive(v_val_5959_);
if (v_isSharedCheck_5992_ == 0)
{
lean_object* v_unused_5993_; lean_object* v_unused_5994_; 
v_unused_5993_ = lean_ctor_get(v_val_5959_, 2);
lean_dec(v_unused_5993_);
v_unused_5994_ = lean_ctor_get(v_val_5959_, 1);
lean_dec(v_unused_5994_);
v___x_5976_ = v_val_5959_;
v_isShared_5977_ = v_isSharedCheck_5992_;
goto v_resetjp_5975_;
}
else
{
lean_inc(v_thmType_5974_);
lean_dec(v_val_5959_);
v___x_5976_ = lean_box(0);
v_isShared_5977_ = v_isSharedCheck_5992_;
goto v_resetjp_5975_;
}
v_resetjp_5975_:
{
lean_object* v___x_5979_; 
lean_inc(v_thmName_5947_);
if (v_isShared_5973_ == 0)
{
lean_ctor_set(v___x_5972_, 2, v_thmType_5974_);
lean_ctor_set(v___x_5972_, 0, v_thmName_5947_);
v___x_5979_ = v___x_5972_;
goto v_reusejp_5978_;
}
else
{
lean_object* v_reuseFailAlloc_5991_; 
v_reuseFailAlloc_5991_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5991_, 0, v_thmName_5947_);
lean_ctor_set(v_reuseFailAlloc_5991_, 1, v_levelParams_5970_);
lean_ctor_set(v_reuseFailAlloc_5991_, 2, v_thmType_5974_);
v___x_5979_ = v_reuseFailAlloc_5991_;
goto v_reusejp_5978_;
}
v_reusejp_5978_:
{
lean_object* v___x_5980_; lean_object* v___x_5981_; lean_object* v___x_5983_; 
v___x_5980_ = lean_box(0);
v___x_5981_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5981_, 0, v_thmName_5947_);
lean_ctor_set(v___x_5981_, 1, v___x_5980_);
if (v_isShared_5977_ == 0)
{
lean_ctor_set(v___x_5976_, 2, v___x_5981_);
lean_ctor_set(v___x_5976_, 1, v_val_5966_);
lean_ctor_set(v___x_5976_, 0, v___x_5979_);
v___x_5983_ = v___x_5976_;
goto v_reusejp_5982_;
}
else
{
lean_object* v_reuseFailAlloc_5990_; 
v_reuseFailAlloc_5990_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5990_, 0, v___x_5979_);
lean_ctor_set(v_reuseFailAlloc_5990_, 1, v_val_5966_);
lean_ctor_set(v_reuseFailAlloc_5990_, 2, v___x_5981_);
v___x_5983_ = v_reuseFailAlloc_5990_;
goto v_reusejp_5982_;
}
v_reusejp_5982_:
{
lean_object* v___x_5985_; 
if (v_isShared_5969_ == 0)
{
lean_ctor_set(v___x_5968_, 0, v___x_5983_);
v___x_5985_ = v___x_5968_;
goto v_reusejp_5984_;
}
else
{
lean_object* v_reuseFailAlloc_5989_; 
v_reuseFailAlloc_5989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5989_, 0, v___x_5983_);
v___x_5985_ = v_reuseFailAlloc_5989_;
goto v_reusejp_5984_;
}
v_reusejp_5984_:
{
lean_object* v___x_5987_; 
if (v_isShared_5964_ == 0)
{
lean_ctor_set(v___x_5963_, 0, v___x_5985_);
v___x_5987_ = v___x_5963_;
goto v_reusejp_5986_;
}
else
{
lean_object* v_reuseFailAlloc_5988_; 
v_reuseFailAlloc_5988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5988_, 0, v___x_5985_);
v___x_5987_ = v_reuseFailAlloc_5988_;
goto v_reusejp_5986_;
}
v_reusejp_5986_:
{
return v___x_5987_;
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
lean_object* v___x_5999_; lean_object* v___x_6001_; 
lean_dec(v_a_5961_);
lean_dec(v_val_5959_);
lean_dec_ref(v_ctorVal_5948_);
lean_dec(v_thmName_5947_);
v___x_5999_ = lean_box(0);
if (v_isShared_5964_ == 0)
{
lean_ctor_set(v___x_5963_, 0, v___x_5999_);
v___x_6001_ = v___x_5963_;
goto v_reusejp_6000_;
}
else
{
lean_object* v_reuseFailAlloc_6002_; 
v_reuseFailAlloc_6002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6002_, 0, v___x_5999_);
v___x_6001_ = v_reuseFailAlloc_6002_;
goto v_reusejp_6000_;
}
v_reusejp_6000_:
{
return v___x_6001_;
}
}
}
}
else
{
lean_object* v_a_6004_; lean_object* v___x_6006_; uint8_t v_isShared_6007_; uint8_t v_isSharedCheck_6011_; 
lean_dec(v_val_5959_);
lean_dec_ref(v_ctorVal_5948_);
lean_dec(v_thmName_5947_);
v_a_6004_ = lean_ctor_get(v___x_5960_, 0);
v_isSharedCheck_6011_ = !lean_is_exclusive(v___x_5960_);
if (v_isSharedCheck_6011_ == 0)
{
v___x_6006_ = v___x_5960_;
v_isShared_6007_ = v_isSharedCheck_6011_;
goto v_resetjp_6005_;
}
else
{
lean_inc(v_a_6004_);
lean_dec(v___x_5960_);
v___x_6006_ = lean_box(0);
v_isShared_6007_ = v_isSharedCheck_6011_;
goto v_resetjp_6005_;
}
v_resetjp_6005_:
{
lean_object* v___x_6009_; 
if (v_isShared_6007_ == 0)
{
v___x_6009_ = v___x_6006_;
goto v_reusejp_6008_;
}
else
{
lean_object* v_reuseFailAlloc_6010_; 
v_reuseFailAlloc_6010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6010_, 0, v_a_6004_);
v___x_6009_ = v_reuseFailAlloc_6010_;
goto v_reusejp_6008_;
}
v_reusejp_6008_:
{
return v___x_6009_;
}
}
}
}
else
{
lean_object* v___x_6012_; lean_object* v___x_6014_; 
lean_dec(v_a_5955_);
lean_dec_ref(v_ctorVal_5948_);
lean_dec(v_thmName_5947_);
v___x_6012_ = lean_box(0);
if (v_isShared_5958_ == 0)
{
lean_ctor_set(v___x_5957_, 0, v___x_6012_);
v___x_6014_ = v___x_5957_;
goto v_reusejp_6013_;
}
else
{
lean_object* v_reuseFailAlloc_6015_; 
v_reuseFailAlloc_6015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6015_, 0, v___x_6012_);
v___x_6014_ = v_reuseFailAlloc_6015_;
goto v_reusejp_6013_;
}
v_reusejp_6013_:
{
return v___x_6014_;
}
}
}
}
else
{
lean_object* v_a_6017_; lean_object* v___x_6019_; uint8_t v_isShared_6020_; uint8_t v_isSharedCheck_6024_; 
lean_dec_ref(v_ctorVal_5948_);
lean_dec(v_thmName_5947_);
v_a_6017_ = lean_ctor_get(v___x_5954_, 0);
v_isSharedCheck_6024_ = !lean_is_exclusive(v___x_5954_);
if (v_isSharedCheck_6024_ == 0)
{
v___x_6019_ = v___x_5954_;
v_isShared_6020_ = v_isSharedCheck_6024_;
goto v_resetjp_6018_;
}
else
{
lean_inc(v_a_6017_);
lean_dec(v___x_5954_);
v___x_6019_ = lean_box(0);
v_isShared_6020_ = v_isSharedCheck_6024_;
goto v_resetjp_6018_;
}
v_resetjp_6018_:
{
lean_object* v___x_6022_; 
if (v_isShared_6020_ == 0)
{
v___x_6022_ = v___x_6019_;
goto v_reusejp_6021_;
}
else
{
lean_object* v_reuseFailAlloc_6023_; 
v_reuseFailAlloc_6023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6023_, 0, v_a_6017_);
v___x_6022_ = v_reuseFailAlloc_6023_;
goto v_reusejp_6021_;
}
v_reusejp_6021_:
{
return v___x_6022_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f___boxed(lean_object* v_thmName_6025_, lean_object* v_ctorVal_6026_, lean_object* v_a_6027_, lean_object* v_a_6028_, lean_object* v_a_6029_, lean_object* v_a_6030_, lean_object* v_a_6031_){
_start:
{
lean_object* v_res_6032_; 
v_res_6032_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(v_thmName_6025_, v_ctorVal_6026_, v_a_6027_, v_a_6028_, v_a_6029_, v_a_6030_);
lean_dec(v_a_6030_);
lean_dec_ref(v_a_6029_);
lean_dec(v_a_6028_);
lean_dec_ref(v_a_6027_);
return v_res_6032_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(lean_object* v_env_6033_, lean_object* v_n_6034_){
_start:
{
if (lean_obj_tag(v_n_6034_) == 1)
{
lean_object* v_pre_6035_; lean_object* v_str_6036_; lean_object* v___x_6037_; uint8_t v___x_6038_; 
v_pre_6035_ = lean_ctor_get(v_n_6034_, 0);
lean_inc(v_pre_6035_);
v_str_6036_ = lean_ctor_get(v_n_6034_, 1);
lean_inc_ref(v_str_6036_);
lean_dec_ref_known(v_n_6034_, 2);
v___x_6037_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0));
v___x_6038_ = lean_string_dec_eq(v_str_6036_, v___x_6037_);
lean_dec_ref(v_str_6036_);
if (v___x_6038_ == 0)
{
lean_dec(v_pre_6035_);
lean_dec_ref(v_env_6033_);
return v___x_6038_;
}
else
{
uint8_t v___x_6039_; lean_object* v___x_6040_; 
v___x_6039_ = 0;
v___x_6040_ = l_Lean_Environment_find_x3f(v_env_6033_, v_pre_6035_, v___x_6039_);
if (lean_obj_tag(v___x_6040_) == 1)
{
lean_object* v_val_6041_; 
v_val_6041_ = lean_ctor_get(v___x_6040_, 0);
lean_inc(v_val_6041_);
lean_dec_ref_known(v___x_6040_, 1);
if (lean_obj_tag(v_val_6041_) == 6)
{
lean_dec_ref_known(v_val_6041_, 1);
return v___x_6038_;
}
else
{
lean_dec(v_val_6041_);
return v___x_6039_;
}
}
else
{
lean_dec(v___x_6040_);
return v___x_6039_;
}
}
}
else
{
uint8_t v___x_6042_; 
lean_dec(v_n_6034_);
lean_dec_ref(v_env_6033_);
v___x_6042_ = 0;
return v___x_6042_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2____boxed(lean_object* v_env_6043_, lean_object* v_n_6044_){
_start:
{
uint8_t v_res_6045_; lean_object* v_r_6046_; 
v_res_6045_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(v_env_6043_, v_n_6044_);
v_r_6046_ = lean_box(v_res_6045_);
return v_r_6046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_6049_; lean_object* v___x_6050_; 
v___f_6049_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_));
v___x_6050_ = l_Lean_registerReservedNamePredicate(v___f_6049_);
return v___x_6050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2____boxed(lean_object* v_a_6051_){
_start:
{
lean_object* v_res_6052_; 
v_res_6052_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_();
return v_res_6052_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(lean_object* v_thm_6053_, lean_object* v___y_6054_){
_start:
{
lean_object* v___x_6056_; lean_object* v_env_6057_; lean_object* v_toConstantVal_6058_; lean_object* v_value_6059_; lean_object* v_all_6060_; uint8_t v___y_6062_; lean_object* v_type_6070_; uint8_t v___x_6071_; 
v___x_6056_ = lean_st_ref_get(v___y_6054_);
v_env_6057_ = lean_ctor_get(v___x_6056_, 0);
lean_inc_ref_n(v_env_6057_, 2);
lean_dec(v___x_6056_);
v_toConstantVal_6058_ = lean_ctor_get(v_thm_6053_, 0);
v_value_6059_ = lean_ctor_get(v_thm_6053_, 1);
v_all_6060_ = lean_ctor_get(v_thm_6053_, 2);
v_type_6070_ = lean_ctor_get(v_toConstantVal_6058_, 2);
v___x_6071_ = l_Lean_Environment_hasUnsafe(v_env_6057_, v_type_6070_);
if (v___x_6071_ == 0)
{
uint8_t v___x_6072_; 
v___x_6072_ = l_Lean_Environment_hasUnsafe(v_env_6057_, v_value_6059_);
v___y_6062_ = v___x_6072_;
goto v___jp_6061_;
}
else
{
lean_dec_ref(v_env_6057_);
v___y_6062_ = v___x_6071_;
goto v___jp_6061_;
}
v___jp_6061_:
{
if (v___y_6062_ == 0)
{
lean_object* v___x_6063_; lean_object* v___x_6064_; 
v___x_6063_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_6063_, 0, v_thm_6053_);
v___x_6064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6064_, 0, v___x_6063_);
return v___x_6064_;
}
else
{
lean_object* v___x_6065_; uint8_t v___x_6066_; lean_object* v___x_6067_; lean_object* v___x_6068_; lean_object* v___x_6069_; 
lean_inc(v_all_6060_);
lean_inc_ref(v_value_6059_);
lean_inc_ref(v_toConstantVal_6058_);
lean_dec_ref(v_thm_6053_);
v___x_6065_ = lean_box(0);
v___x_6066_ = 0;
v___x_6067_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_6067_, 0, v_toConstantVal_6058_);
lean_ctor_set(v___x_6067_, 1, v_value_6059_);
lean_ctor_set(v___x_6067_, 2, v___x_6065_);
lean_ctor_set(v___x_6067_, 3, v_all_6060_);
lean_ctor_set_uint8(v___x_6067_, sizeof(void*)*4, v___x_6066_);
v___x_6068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6068_, 0, v___x_6067_);
v___x_6069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6069_, 0, v___x_6068_);
return v___x_6069_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_thm_6073_, lean_object* v___y_6074_, lean_object* v___y_6075_){
_start:
{
lean_object* v_res_6076_; 
v_res_6076_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(v_thm_6073_, v___y_6074_);
lean_dec(v___y_6074_);
return v_res_6076_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0(lean_object* v_thm_6077_, lean_object* v___y_6078_, lean_object* v___y_6079_, lean_object* v___y_6080_, lean_object* v___y_6081_){
_start:
{
lean_object* v___x_6083_; 
v___x_6083_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(v_thm_6077_, v___y_6081_);
return v___x_6083_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___boxed(lean_object* v_thm_6084_, lean_object* v___y_6085_, lean_object* v___y_6086_, lean_object* v___y_6087_, lean_object* v___y_6088_, lean_object* v___y_6089_){
_start:
{
lean_object* v_res_6090_; 
v_res_6090_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0(v_thm_6084_, v___y_6085_, v___y_6086_, v___y_6087_, v___y_6088_);
lean_dec(v___y_6088_);
lean_dec_ref(v___y_6087_);
lean_dec(v___y_6086_);
lean_dec_ref(v___y_6085_);
return v_res_6090_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(lean_object* v_val_6091_, uint8_t v___x_6092_, lean_object* v___y_6093_, lean_object* v___y_6094_, lean_object* v___y_6095_, lean_object* v___y_6096_){
_start:
{
lean_object* v___x_6098_; lean_object* v_a_6099_; lean_object* v___x_6100_; 
v___x_6098_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(v_val_6091_, v___y_6096_);
v_a_6099_ = lean_ctor_get(v___x_6098_, 0);
lean_inc(v_a_6099_);
lean_dec_ref(v___x_6098_);
v___x_6100_ = l_Lean_addDecl(v_a_6099_, v___x_6092_, v___y_6095_, v___y_6096_);
return v___x_6100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object* v_val_6101_, lean_object* v___x_6102_, lean_object* v___y_6103_, lean_object* v___y_6104_, lean_object* v___y_6105_, lean_object* v___y_6106_, lean_object* v___y_6107_){
_start:
{
uint8_t v___x_2127__boxed_6108_; lean_object* v_res_6109_; 
v___x_2127__boxed_6108_ = lean_unbox(v___x_6102_);
v_res_6109_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(v_val_6101_, v___x_2127__boxed_6108_, v___y_6103_, v___y_6104_, v___y_6105_, v___y_6106_);
lean_dec(v___y_6106_);
lean_dec_ref(v___y_6105_);
lean_dec(v___y_6104_);
lean_dec_ref(v___y_6103_);
return v_res_6109_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6112_; lean_object* v___x_6113_; lean_object* v___x_6114_; 
v___x_6112_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_6113_ = lean_unsigned_to_nat(0u);
v___x_6114_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_6114_, 0, v___x_6113_);
lean_ctor_set(v___x_6114_, 1, v___x_6113_);
lean_ctor_set(v___x_6114_, 2, v___x_6113_);
lean_ctor_set(v___x_6114_, 3, v___x_6113_);
lean_ctor_set(v___x_6114_, 4, v___x_6112_);
lean_ctor_set(v___x_6114_, 5, v___x_6112_);
lean_ctor_set(v___x_6114_, 6, v___x_6112_);
lean_ctor_set(v___x_6114_, 7, v___x_6112_);
lean_ctor_set(v___x_6114_, 8, v___x_6112_);
lean_ctor_set(v___x_6114_, 9, v___x_6112_);
lean_ctor_set(v___x_6114_, 10, v___x_6112_);
return v___x_6114_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6115_; lean_object* v___x_6116_; 
v___x_6115_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_6116_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6116_, 0, v___x_6115_);
lean_ctor_set(v___x_6116_, 1, v___x_6115_);
lean_ctor_set(v___x_6116_, 2, v___x_6115_);
lean_ctor_set(v___x_6116_, 3, v___x_6115_);
lean_ctor_set(v___x_6116_, 4, v___x_6115_);
lean_ctor_set(v___x_6116_, 5, v___x_6115_);
return v___x_6116_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6117_; lean_object* v___x_6118_; 
v___x_6117_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_6118_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6118_, 0, v___x_6117_);
lean_ctor_set(v___x_6118_, 1, v___x_6117_);
lean_ctor_set(v___x_6118_, 2, v___x_6117_);
lean_ctor_set(v___x_6118_, 3, v___x_6117_);
lean_ctor_set(v___x_6118_, 4, v___x_6117_);
return v___x_6118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(lean_object* v___x_6119_, lean_object* v_name_6120_, lean_object* v___y_6121_, lean_object* v___y_6122_){
_start:
{
if (lean_obj_tag(v_name_6120_) == 1)
{
lean_object* v_pre_6132_; lean_object* v_str_6133_; lean_object* v___x_6134_; uint8_t v___x_6135_; 
v_pre_6132_ = lean_ctor_get(v_name_6120_, 0);
lean_inc(v_pre_6132_);
v_str_6133_ = lean_ctor_get(v_name_6120_, 1);
v___x_6134_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0));
v___x_6135_ = lean_string_dec_eq(v_str_6133_, v___x_6134_);
if (v___x_6135_ == 0)
{
lean_dec_ref_known(v_name_6120_, 2);
lean_dec(v_pre_6132_);
lean_dec(v___x_6119_);
goto v___jp_6128_;
}
else
{
lean_object* v___x_6136_; lean_object* v_env_6137_; uint8_t v___x_6138_; lean_object* v___x_6139_; 
v___x_6136_ = lean_st_ref_get(v___y_6122_);
v_env_6137_ = lean_ctor_get(v___x_6136_, 0);
lean_inc_ref(v_env_6137_);
lean_dec(v___x_6136_);
v___x_6138_ = 0;
lean_inc(v_pre_6132_);
v___x_6139_ = l_Lean_Environment_find_x3f(v_env_6137_, v_pre_6132_, v___x_6138_);
if (lean_obj_tag(v___x_6139_) == 1)
{
lean_object* v_val_6140_; 
v_val_6140_ = lean_ctor_get(v___x_6139_, 0);
lean_inc(v_val_6140_);
lean_dec_ref_known(v___x_6139_, 1);
if (lean_obj_tag(v_val_6140_) == 6)
{
lean_object* v_val_6141_; lean_object* v___x_6143_; uint8_t v_isShared_6144_; uint8_t v_isSharedCheck_6191_; 
v_val_6141_ = lean_ctor_get(v_val_6140_, 0);
v_isSharedCheck_6191_ = !lean_is_exclusive(v_val_6140_);
if (v_isSharedCheck_6191_ == 0)
{
v___x_6143_ = v_val_6140_;
v_isShared_6144_ = v_isSharedCheck_6191_;
goto v_resetjp_6142_;
}
else
{
lean_inc(v_val_6141_);
lean_dec(v_val_6140_);
v___x_6143_ = lean_box(0);
v_isShared_6144_ = v_isSharedCheck_6191_;
goto v_resetjp_6142_;
}
v_resetjp_6142_:
{
uint8_t v___x_6145_; uint8_t v___x_6146_; uint8_t v___x_6147_; lean_object* v___x_6148_; uint64_t v___x_6149_; lean_object* v___x_6150_; lean_object* v___x_6151_; lean_object* v___x_6152_; lean_object* v___x_6153_; lean_object* v___x_6154_; lean_object* v___x_6155_; lean_object* v___x_6156_; lean_object* v___x_6157_; lean_object* v___x_6158_; lean_object* v___x_6159_; lean_object* v___x_6160_; lean_object* v___x_6161_; uint8_t v_a_6163_; lean_object* v___x_6169_; 
v___x_6145_ = 1;
v___x_6146_ = 0;
v___x_6147_ = 2;
v___x_6148_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_6148_, 0, v___x_6138_);
lean_ctor_set_uint8(v___x_6148_, 1, v___x_6138_);
lean_ctor_set_uint8(v___x_6148_, 2, v___x_6138_);
lean_ctor_set_uint8(v___x_6148_, 3, v___x_6138_);
lean_ctor_set_uint8(v___x_6148_, 4, v___x_6138_);
lean_ctor_set_uint8(v___x_6148_, 5, v___x_6135_);
lean_ctor_set_uint8(v___x_6148_, 6, v___x_6135_);
lean_ctor_set_uint8(v___x_6148_, 7, v___x_6138_);
lean_ctor_set_uint8(v___x_6148_, 8, v___x_6135_);
lean_ctor_set_uint8(v___x_6148_, 9, v___x_6145_);
lean_ctor_set_uint8(v___x_6148_, 10, v___x_6146_);
lean_ctor_set_uint8(v___x_6148_, 11, v___x_6135_);
lean_ctor_set_uint8(v___x_6148_, 12, v___x_6135_);
lean_ctor_set_uint8(v___x_6148_, 13, v___x_6135_);
lean_ctor_set_uint8(v___x_6148_, 14, v___x_6147_);
lean_ctor_set_uint8(v___x_6148_, 15, v___x_6135_);
lean_ctor_set_uint8(v___x_6148_, 16, v___x_6135_);
lean_ctor_set_uint8(v___x_6148_, 17, v___x_6135_);
lean_ctor_set_uint8(v___x_6148_, 18, v___x_6135_);
lean_ctor_set_uint8(v___x_6148_, 19, v___x_6138_);
v___x_6149_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_6148_);
v___x_6150_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_6150_, 0, v___x_6148_);
lean_ctor_set_uint64(v___x_6150_, sizeof(void*)*1, v___x_6149_);
v___x_6151_ = lean_unsigned_to_nat(0u);
v___x_6152_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_6153_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_6154_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_));
v___x_6155_ = lean_box(0);
lean_inc(v___x_6119_);
v___x_6156_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_6156_, 0, v___x_6150_);
lean_ctor_set(v___x_6156_, 1, v___x_6119_);
lean_ctor_set(v___x_6156_, 2, v___x_6153_);
lean_ctor_set(v___x_6156_, 3, v___x_6154_);
lean_ctor_set(v___x_6156_, 4, v___x_6155_);
lean_ctor_set(v___x_6156_, 5, v___x_6151_);
lean_ctor_set(v___x_6156_, 6, v___x_6155_);
lean_ctor_set_uint8(v___x_6156_, sizeof(void*)*7, v___x_6138_);
lean_ctor_set_uint8(v___x_6156_, sizeof(void*)*7 + 1, v___x_6138_);
lean_ctor_set_uint8(v___x_6156_, sizeof(void*)*7 + 2, v___x_6138_);
lean_ctor_set_uint8(v___x_6156_, sizeof(void*)*7 + 3, v___x_6135_);
v___x_6157_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6158_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6159_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6160_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6160_, 0, v___x_6157_);
lean_ctor_set(v___x_6160_, 1, v___x_6158_);
lean_ctor_set(v___x_6160_, 2, v___x_6119_);
lean_ctor_set(v___x_6160_, 3, v___x_6152_);
lean_ctor_set(v___x_6160_, 4, v___x_6159_);
v___x_6161_ = lean_st_mk_ref(v___x_6160_);
lean_inc_ref(v_name_6120_);
v___x_6169_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(v_name_6120_, v_val_6141_, v___x_6156_, v___x_6161_, v___y_6121_, v___y_6122_);
if (lean_obj_tag(v___x_6169_) == 0)
{
lean_object* v_a_6170_; 
v_a_6170_ = lean_ctor_get(v___x_6169_, 0);
lean_inc(v_a_6170_);
lean_dec_ref_known(v___x_6169_, 1);
if (lean_obj_tag(v_a_6170_) == 1)
{
lean_object* v_val_6171_; lean_object* v___x_6172_; lean_object* v___f_6173_; lean_object* v___x_6174_; 
v_val_6171_ = lean_ctor_get(v_a_6170_, 0);
lean_inc(v_val_6171_);
lean_dec_ref_known(v_a_6170_, 1);
v___x_6172_ = lean_box(v___x_6138_);
v___f_6173_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed), 7, 2);
lean_closure_set(v___f_6173_, 0, v_val_6171_);
lean_closure_set(v___f_6173_, 1, v___x_6172_);
v___x_6174_ = l_Lean_Meta_realizeConst(v_pre_6132_, v_name_6120_, v___f_6173_, v___x_6156_, v___x_6161_, v___y_6121_, v___y_6122_);
lean_dec_ref_known(v___x_6156_, 7);
if (lean_obj_tag(v___x_6174_) == 0)
{
lean_dec_ref_known(v___x_6174_, 1);
v_a_6163_ = v___x_6135_;
goto v___jp_6162_;
}
else
{
lean_object* v_a_6175_; lean_object* v___x_6177_; uint8_t v_isShared_6178_; uint8_t v_isSharedCheck_6182_; 
lean_dec(v___x_6161_);
lean_del_object(v___x_6143_);
v_a_6175_ = lean_ctor_get(v___x_6174_, 0);
v_isSharedCheck_6182_ = !lean_is_exclusive(v___x_6174_);
if (v_isSharedCheck_6182_ == 0)
{
v___x_6177_ = v___x_6174_;
v_isShared_6178_ = v_isSharedCheck_6182_;
goto v_resetjp_6176_;
}
else
{
lean_inc(v_a_6175_);
lean_dec(v___x_6174_);
v___x_6177_ = lean_box(0);
v_isShared_6178_ = v_isSharedCheck_6182_;
goto v_resetjp_6176_;
}
v_resetjp_6176_:
{
lean_object* v___x_6180_; 
if (v_isShared_6178_ == 0)
{
v___x_6180_ = v___x_6177_;
goto v_reusejp_6179_;
}
else
{
lean_object* v_reuseFailAlloc_6181_; 
v_reuseFailAlloc_6181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6181_, 0, v_a_6175_);
v___x_6180_ = v_reuseFailAlloc_6181_;
goto v_reusejp_6179_;
}
v_reusejp_6179_:
{
return v___x_6180_;
}
}
}
}
else
{
lean_dec(v_a_6170_);
lean_dec_ref_known(v___x_6156_, 7);
lean_dec(v_pre_6132_);
lean_dec_ref_known(v_name_6120_, 2);
v_a_6163_ = v___x_6138_;
goto v___jp_6162_;
}
}
else
{
lean_object* v_a_6183_; lean_object* v___x_6185_; uint8_t v_isShared_6186_; uint8_t v_isSharedCheck_6190_; 
lean_dec(v___x_6161_);
lean_dec_ref_known(v___x_6156_, 7);
lean_del_object(v___x_6143_);
lean_dec(v_pre_6132_);
lean_dec_ref_known(v_name_6120_, 2);
v_a_6183_ = lean_ctor_get(v___x_6169_, 0);
v_isSharedCheck_6190_ = !lean_is_exclusive(v___x_6169_);
if (v_isSharedCheck_6190_ == 0)
{
v___x_6185_ = v___x_6169_;
v_isShared_6186_ = v_isSharedCheck_6190_;
goto v_resetjp_6184_;
}
else
{
lean_inc(v_a_6183_);
lean_dec(v___x_6169_);
v___x_6185_ = lean_box(0);
v_isShared_6186_ = v_isSharedCheck_6190_;
goto v_resetjp_6184_;
}
v_resetjp_6184_:
{
lean_object* v___x_6188_; 
if (v_isShared_6186_ == 0)
{
v___x_6188_ = v___x_6185_;
goto v_reusejp_6187_;
}
else
{
lean_object* v_reuseFailAlloc_6189_; 
v_reuseFailAlloc_6189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6189_, 0, v_a_6183_);
v___x_6188_ = v_reuseFailAlloc_6189_;
goto v_reusejp_6187_;
}
v_reusejp_6187_:
{
return v___x_6188_;
}
}
}
v___jp_6162_:
{
lean_object* v___x_6164_; lean_object* v___x_6165_; lean_object* v___x_6167_; 
v___x_6164_ = lean_st_ref_get(v___x_6161_);
lean_dec(v___x_6161_);
lean_dec(v___x_6164_);
v___x_6165_ = lean_box(v_a_6163_);
if (v_isShared_6144_ == 0)
{
lean_ctor_set_tag(v___x_6143_, 0);
lean_ctor_set(v___x_6143_, 0, v___x_6165_);
v___x_6167_ = v___x_6143_;
goto v_reusejp_6166_;
}
else
{
lean_object* v_reuseFailAlloc_6168_; 
v_reuseFailAlloc_6168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6168_, 0, v___x_6165_);
v___x_6167_ = v_reuseFailAlloc_6168_;
goto v_reusejp_6166_;
}
v_reusejp_6166_:
{
return v___x_6167_;
}
}
}
}
else
{
lean_dec(v_val_6140_);
lean_dec_ref_known(v_name_6120_, 2);
lean_dec(v_pre_6132_);
lean_dec(v___x_6119_);
goto v___jp_6124_;
}
}
else
{
lean_dec(v___x_6139_);
lean_dec_ref_known(v_name_6120_, 2);
lean_dec(v_pre_6132_);
lean_dec(v___x_6119_);
goto v___jp_6124_;
}
}
}
else
{
lean_dec(v_name_6120_);
lean_dec(v___x_6119_);
goto v___jp_6128_;
}
v___jp_6124_:
{
uint8_t v___x_6125_; lean_object* v___x_6126_; lean_object* v___x_6127_; 
v___x_6125_ = 0;
v___x_6126_ = lean_box(v___x_6125_);
v___x_6127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6127_, 0, v___x_6126_);
return v___x_6127_;
}
v___jp_6128_:
{
uint8_t v___x_6129_; lean_object* v___x_6130_; lean_object* v___x_6131_; 
v___x_6129_ = 0;
v___x_6130_ = lean_box(v___x_6129_);
v___x_6131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6131_, 0, v___x_6130_);
return v___x_6131_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object* v___x_6192_, lean_object* v_name_6193_, lean_object* v___y_6194_, lean_object* v___y_6195_, lean_object* v___y_6196_){
_start:
{
lean_object* v_res_6197_; 
v_res_6197_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(v___x_6192_, v_name_6193_, v___y_6194_, v___y_6195_);
lean_dec(v___y_6195_);
lean_dec_ref(v___y_6194_);
return v_res_6197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_6201_; lean_object* v___x_6202_; 
v___f_6201_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_));
v___x_6202_ = l_Lean_registerReservedNameAction(v___f_6201_);
return v___x_6202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object* v_a_6203_){
_start:
{
lean_object* v_res_6204_; 
v_res_6204_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_();
return v_res_6204_;
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
