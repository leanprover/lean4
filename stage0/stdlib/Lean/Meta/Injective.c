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
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Meta_introSubstEq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_applyN(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* l_Lean_Meta_realizeConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInductivePredicate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__0 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__0_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "injEq_helper"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__1 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__1_value;
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__2_value_aux_0),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(167, 111, 180, 146, 132, 58, 155, 57)}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__2 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__2_value;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__3;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "unexpected number of goals after applying `Lean.and_imp`"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__4 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__4_value;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__5;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "genInjectivity"};
static const lean_object* l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(56, 68, 112, 222, 169, 79, 62, 37)}};
static const lean_object* l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 169, .m_capacity = 169, .m_length = 168, .m_data = "generate injectivity theorems for inductive datatype constructors. Temporarily (for bootstrapping reasons) also controls the generation of the\n    `ctorIdx` definition."};
static const lean_object* l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__4_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(53, 17, 232, 138, 187, 170, 36, 13)}};
static const lean_object* l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4____boxed(lean_object*);
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
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__4_value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Injective"};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(55, 101, 109, 194, 24, 99, 201, 78)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(74, 76, 255, 124, 31, 108, 47, 16)}};
static const lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 106, 16, 37, 3, 60, 11, 157)}};
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
static const lean_ctor_object l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 151, 10, 103, 183, 199, 62, 165)}};
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11___redArg(lean_object* v_a_82_, lean_object* v_b_83_, lean_object* v_x_84_){
_start:
{
if (lean_obj_tag(v_x_84_) == 0)
{
lean_dec(v_b_83_);
lean_dec_ref(v_a_82_);
return v_x_84_;
}
else
{
lean_object* v_key_85_; lean_object* v_value_86_; lean_object* v_tail_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_99_; 
v_key_85_ = lean_ctor_get(v_x_84_, 0);
v_value_86_ = lean_ctor_get(v_x_84_, 1);
v_tail_87_ = lean_ctor_get(v_x_84_, 2);
v_isSharedCheck_99_ = !lean_is_exclusive(v_x_84_);
if (v_isSharedCheck_99_ == 0)
{
v___x_89_ = v_x_84_;
v_isShared_90_ = v_isSharedCheck_99_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_tail_87_);
lean_inc(v_value_86_);
lean_inc(v_key_85_);
lean_dec(v_x_84_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_99_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
uint8_t v___x_91_; 
v___x_91_ = l_Lean_ExprStructEq_beq(v_key_85_, v_a_82_);
if (v___x_91_ == 0)
{
lean_object* v___x_92_; lean_object* v___x_94_; 
v___x_92_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11___redArg(v_a_82_, v_b_83_, v_tail_87_);
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 2, v___x_92_);
v___x_94_ = v___x_89_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_key_85_);
lean_ctor_set(v_reuseFailAlloc_95_, 1, v_value_86_);
lean_ctor_set(v_reuseFailAlloc_95_, 2, v___x_92_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
else
{
lean_object* v___x_97_; 
lean_dec(v_value_86_);
lean_dec(v_key_85_);
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 1, v_b_83_);
lean_ctor_set(v___x_89_, 0, v_a_82_);
v___x_97_ = v___x_89_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v_a_82_);
lean_ctor_set(v_reuseFailAlloc_98_, 1, v_b_83_);
lean_ctor_set(v_reuseFailAlloc_98_, 2, v_tail_87_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__9___redArg(lean_object* v_a_100_, lean_object* v_x_101_){
_start:
{
if (lean_obj_tag(v_x_101_) == 0)
{
uint8_t v___x_102_; 
v___x_102_ = 0;
return v___x_102_;
}
else
{
lean_object* v_key_103_; lean_object* v_tail_104_; uint8_t v___x_105_; 
v_key_103_ = lean_ctor_get(v_x_101_, 0);
v_tail_104_ = lean_ctor_get(v_x_101_, 2);
v___x_105_ = l_Lean_ExprStructEq_beq(v_key_103_, v_a_100_);
if (v___x_105_ == 0)
{
v_x_101_ = v_tail_104_;
goto _start;
}
else
{
return v___x_105_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__9___redArg___boxed(lean_object* v_a_107_, lean_object* v_x_108_){
_start:
{
uint8_t v_res_109_; lean_object* v_r_110_; 
v_res_109_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__9___redArg(v_a_107_, v_x_108_);
lean_dec(v_x_108_);
lean_dec_ref(v_a_107_);
v_r_110_ = lean_box(v_res_109_);
return v_r_110_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(lean_object* v_x_111_, lean_object* v_x_112_){
_start:
{
if (lean_obj_tag(v_x_112_) == 0)
{
return v_x_111_;
}
else
{
lean_object* v_key_113_; lean_object* v_value_114_; lean_object* v_tail_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_138_; 
v_key_113_ = lean_ctor_get(v_x_112_, 0);
v_value_114_ = lean_ctor_get(v_x_112_, 1);
v_tail_115_ = lean_ctor_get(v_x_112_, 2);
v_isSharedCheck_138_ = !lean_is_exclusive(v_x_112_);
if (v_isSharedCheck_138_ == 0)
{
v___x_117_ = v_x_112_;
v_isShared_118_ = v_isSharedCheck_138_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_tail_115_);
lean_inc(v_value_114_);
lean_inc(v_key_113_);
lean_dec(v_x_112_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_138_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_119_; uint64_t v___x_120_; uint64_t v___x_121_; uint64_t v___x_122_; uint64_t v_fold_123_; uint64_t v___x_124_; uint64_t v___x_125_; uint64_t v___x_126_; size_t v___x_127_; size_t v___x_128_; size_t v___x_129_; size_t v___x_130_; size_t v___x_131_; lean_object* v___x_132_; lean_object* v___x_134_; 
v___x_119_ = lean_array_get_size(v_x_111_);
v___x_120_ = l_Lean_ExprStructEq_hash(v_key_113_);
v___x_121_ = 32ULL;
v___x_122_ = lean_uint64_shift_right(v___x_120_, v___x_121_);
v_fold_123_ = lean_uint64_xor(v___x_120_, v___x_122_);
v___x_124_ = 16ULL;
v___x_125_ = lean_uint64_shift_right(v_fold_123_, v___x_124_);
v___x_126_ = lean_uint64_xor(v_fold_123_, v___x_125_);
v___x_127_ = lean_uint64_to_usize(v___x_126_);
v___x_128_ = lean_usize_of_nat(v___x_119_);
v___x_129_ = ((size_t)1ULL);
v___x_130_ = lean_usize_sub(v___x_128_, v___x_129_);
v___x_131_ = lean_usize_land(v___x_127_, v___x_130_);
v___x_132_ = lean_array_uget_borrowed(v_x_111_, v___x_131_);
lean_inc(v___x_132_);
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 2, v___x_132_);
v___x_134_ = v___x_117_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_key_113_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v_value_114_);
lean_ctor_set(v_reuseFailAlloc_137_, 2, v___x_132_);
v___x_134_ = v_reuseFailAlloc_137_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
lean_object* v___x_135_; 
v___x_135_ = lean_array_uset(v_x_111_, v___x_131_, v___x_134_);
v_x_111_ = v___x_135_;
v_x_112_ = v_tail_115_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(lean_object* v_i_139_, lean_object* v_source_140_, lean_object* v_target_141_){
_start:
{
lean_object* v___x_142_; uint8_t v___x_143_; 
v___x_142_ = lean_array_get_size(v_source_140_);
v___x_143_ = lean_nat_dec_lt(v_i_139_, v___x_142_);
if (v___x_143_ == 0)
{
lean_dec_ref(v_source_140_);
lean_dec(v_i_139_);
return v_target_141_;
}
else
{
lean_object* v_es_144_; lean_object* v___x_145_; lean_object* v_source_146_; lean_object* v_target_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v_es_144_ = lean_array_fget(v_source_140_, v_i_139_);
v___x_145_ = lean_box(0);
v_source_146_ = lean_array_fset(v_source_140_, v_i_139_, v___x_145_);
v_target_147_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(v_target_141_, v_es_144_);
v___x_148_ = lean_unsigned_to_nat(1u);
v___x_149_ = lean_nat_add(v_i_139_, v___x_148_);
lean_dec(v_i_139_);
v_i_139_ = v___x_149_;
v_source_140_ = v_source_146_;
v_target_141_ = v_target_147_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___redArg(lean_object* v_data_151_){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v_nbuckets_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_152_ = lean_array_get_size(v_data_151_);
v___x_153_ = lean_unsigned_to_nat(2u);
v_nbuckets_154_ = lean_nat_mul(v___x_152_, v___x_153_);
v___x_155_ = lean_unsigned_to_nat(0u);
v___x_156_ = lean_box(0);
v___x_157_ = lean_mk_array(v_nbuckets_154_, v___x_156_);
v___x_158_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(v___x_155_, v_data_151_, v___x_157_);
return v___x_158_;
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
v___x_181_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__9___redArg(v_a_160_, v_bkt_180_);
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
v_val_192_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___redArg(v_buckets_x27_185_);
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
v___x_201_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11___redArg(v_a_160_, v_b_161_, v_bkt_180_);
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
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = l_Lean_maxRecDepthErrorMessage;
v___x_226_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
return v___x_226_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__3);
v___x_228_ = l_Lean_MessageData_ofFormat(v___x_227_);
return v___x_228_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_229_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__4);
v___x_230_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__2));
v___x_231_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
lean_ctor_set(v___x_231_, 1, v___x_229_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_ref_232_){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_234_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_235_, 0, v_ref_232_);
lean_ctor_set(v___x_235_, 1, v___x_234_);
v___x_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_ref_237_, lean_object* v___y_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_237_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(lean_object* v_x_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_){
_start:
{
lean_object* v___y_246_; lean_object* v_fileName_255_; lean_object* v_fileMap_256_; lean_object* v_options_257_; lean_object* v_currRecDepth_258_; lean_object* v_maxRecDepth_259_; lean_object* v_ref_260_; lean_object* v_currNamespace_261_; lean_object* v_openDecls_262_; lean_object* v_initHeartbeats_263_; lean_object* v_maxHeartbeats_264_; lean_object* v_quotContext_265_; lean_object* v_currMacroScope_266_; uint8_t v_diag_267_; lean_object* v_cancelTk_x3f_268_; uint8_t v_suppressElabErrors_269_; lean_object* v_inheritedTraceOptions_270_; lean_object* v___x_276_; uint8_t v___x_277_; 
v_fileName_255_ = lean_ctor_get(v___y_242_, 0);
v_fileMap_256_ = lean_ctor_get(v___y_242_, 1);
v_options_257_ = lean_ctor_get(v___y_242_, 2);
v_currRecDepth_258_ = lean_ctor_get(v___y_242_, 3);
v_maxRecDepth_259_ = lean_ctor_get(v___y_242_, 4);
v_ref_260_ = lean_ctor_get(v___y_242_, 5);
v_currNamespace_261_ = lean_ctor_get(v___y_242_, 6);
v_openDecls_262_ = lean_ctor_get(v___y_242_, 7);
v_initHeartbeats_263_ = lean_ctor_get(v___y_242_, 8);
v_maxHeartbeats_264_ = lean_ctor_get(v___y_242_, 9);
v_quotContext_265_ = lean_ctor_get(v___y_242_, 10);
v_currMacroScope_266_ = lean_ctor_get(v___y_242_, 11);
v_diag_267_ = lean_ctor_get_uint8(v___y_242_, sizeof(void*)*14);
v_cancelTk_x3f_268_ = lean_ctor_get(v___y_242_, 12);
v_suppressElabErrors_269_ = lean_ctor_get_uint8(v___y_242_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_270_ = lean_ctor_get(v___y_242_, 13);
v___x_276_ = lean_unsigned_to_nat(0u);
v___x_277_ = lean_nat_dec_eq(v_maxRecDepth_259_, v___x_276_);
if (v___x_277_ == 0)
{
uint8_t v___x_278_; 
v___x_278_ = lean_nat_dec_eq(v_currRecDepth_258_, v_maxRecDepth_259_);
if (v___x_278_ == 0)
{
goto v___jp_271_;
}
else
{
lean_object* v___x_279_; 
lean_dec_ref(v_x_240_);
lean_inc(v_ref_260_);
v___x_279_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_260_);
v___y_246_ = v___x_279_;
goto v___jp_245_;
}
}
else
{
goto v___jp_271_;
}
v___jp_245_:
{
if (lean_obj_tag(v___y_246_) == 0)
{
return v___y_246_;
}
else
{
lean_object* v_a_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_254_; 
v_a_247_ = lean_ctor_get(v___y_246_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v___y_246_);
if (v_isSharedCheck_254_ == 0)
{
v___x_249_ = v___y_246_;
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_a_247_);
lean_dec(v___y_246_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_252_; 
if (v_isShared_250_ == 0)
{
v___x_252_ = v___x_249_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_a_247_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
}
}
v___jp_271_:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_272_ = lean_unsigned_to_nat(1u);
v___x_273_ = lean_nat_add(v_currRecDepth_258_, v___x_272_);
lean_inc_ref(v_inheritedTraceOptions_270_);
lean_inc(v_cancelTk_x3f_268_);
lean_inc(v_currMacroScope_266_);
lean_inc(v_quotContext_265_);
lean_inc(v_maxHeartbeats_264_);
lean_inc(v_initHeartbeats_263_);
lean_inc(v_openDecls_262_);
lean_inc(v_currNamespace_261_);
lean_inc(v_ref_260_);
lean_inc(v_maxRecDepth_259_);
lean_inc_ref(v_options_257_);
lean_inc_ref(v_fileMap_256_);
lean_inc_ref(v_fileName_255_);
v___x_274_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_274_, 0, v_fileName_255_);
lean_ctor_set(v___x_274_, 1, v_fileMap_256_);
lean_ctor_set(v___x_274_, 2, v_options_257_);
lean_ctor_set(v___x_274_, 3, v___x_273_);
lean_ctor_set(v___x_274_, 4, v_maxRecDepth_259_);
lean_ctor_set(v___x_274_, 5, v_ref_260_);
lean_ctor_set(v___x_274_, 6, v_currNamespace_261_);
lean_ctor_set(v___x_274_, 7, v_openDecls_262_);
lean_ctor_set(v___x_274_, 8, v_initHeartbeats_263_);
lean_ctor_set(v___x_274_, 9, v_maxHeartbeats_264_);
lean_ctor_set(v___x_274_, 10, v_quotContext_265_);
lean_ctor_set(v___x_274_, 11, v_currMacroScope_266_);
lean_ctor_set(v___x_274_, 12, v_cancelTk_x3f_268_);
lean_ctor_set(v___x_274_, 13, v_inheritedTraceOptions_270_);
lean_ctor_set_uint8(v___x_274_, sizeof(void*)*14, v_diag_267_);
lean_ctor_set_uint8(v___x_274_, sizeof(void*)*14 + 1, v_suppressElabErrors_269_);
lean_inc(v___y_243_);
lean_inc(v___y_241_);
v___x_275_ = lean_apply_4(v_x_240_, v___y_241_, v___x_274_, v___y_243_, lean_box(0));
v___y_246_ = v___x_275_;
goto v___jp_245_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(v_x_280_, v___y_281_, v___y_282_, v___y_283_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
lean_dec(v___y_281_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_286_, lean_object* v_x_287_, lean_object* v___y_288_, lean_object* v___y_289_){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = lean_apply_1(v_x_287_, lean_box(0));
v___x_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_293_, lean_object* v_x_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(v_00_u03b1_293_, v_x_294_, v___y_295_, v___y_296_);
lean_dec(v___y_296_);
lean_dec_ref(v___y_295_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_a_299_, lean_object* v_x_300_){
_start:
{
if (lean_obj_tag(v_x_300_) == 0)
{
lean_object* v___x_301_; 
v___x_301_ = lean_box(0);
return v___x_301_;
}
else
{
lean_object* v_key_302_; lean_object* v_value_303_; lean_object* v_tail_304_; uint8_t v___x_305_; 
v_key_302_ = lean_ctor_get(v_x_300_, 0);
v_value_303_ = lean_ctor_get(v_x_300_, 1);
v_tail_304_ = lean_ctor_get(v_x_300_, 2);
v___x_305_ = l_Lean_ExprStructEq_beq(v_key_302_, v_a_299_);
if (v___x_305_ == 0)
{
v_x_300_ = v_tail_304_;
goto _start;
}
else
{
lean_object* v___x_307_; 
lean_inc(v_value_303_);
v___x_307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_307_, 0, v_value_303_);
return v___x_307_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_a_308_, lean_object* v_x_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(v_a_308_, v_x_309_);
lean_dec(v_x_309_);
lean_dec_ref(v_a_308_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(lean_object* v_m_311_, lean_object* v_a_312_){
_start:
{
lean_object* v_buckets_313_; lean_object* v___x_314_; uint64_t v___x_315_; uint64_t v___x_316_; uint64_t v___x_317_; uint64_t v_fold_318_; uint64_t v___x_319_; uint64_t v___x_320_; uint64_t v___x_321_; size_t v___x_322_; size_t v___x_323_; size_t v___x_324_; size_t v___x_325_; size_t v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v_buckets_313_ = lean_ctor_get(v_m_311_, 1);
v___x_314_ = lean_array_get_size(v_buckets_313_);
v___x_315_ = l_Lean_ExprStructEq_hash(v_a_312_);
v___x_316_ = 32ULL;
v___x_317_ = lean_uint64_shift_right(v___x_315_, v___x_316_);
v_fold_318_ = lean_uint64_xor(v___x_315_, v___x_317_);
v___x_319_ = 16ULL;
v___x_320_ = lean_uint64_shift_right(v_fold_318_, v___x_319_);
v___x_321_ = lean_uint64_xor(v_fold_318_, v___x_320_);
v___x_322_ = lean_uint64_to_usize(v___x_321_);
v___x_323_ = lean_usize_of_nat(v___x_314_);
v___x_324_ = ((size_t)1ULL);
v___x_325_ = lean_usize_sub(v___x_323_, v___x_324_);
v___x_326_ = lean_usize_land(v___x_322_, v___x_325_);
v___x_327_ = lean_array_uget_borrowed(v_buckets_313_, v___x_326_);
v___x_328_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(v_a_312_, v___x_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_329_, lean_object* v_a_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(v_m_329_, v_a_330_);
lean_dec_ref(v_a_330_);
lean_dec_ref(v_m_329_);
return v_res_331_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0(void){
_start:
{
lean_object* v___x_333_; lean_object* v_dummy_334_; 
v___x_333_ = lean_box(0);
v_dummy_334_ = l_Lean_Expr_sort___override(v___x_333_);
return v_dummy_334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1(lean_object* v_pre_335_, lean_object* v_post_336_, size_t v_sz_337_, size_t v_i_338_, lean_object* v_bs_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_){
_start:
{
uint8_t v___x_344_; 
v___x_344_ = lean_usize_dec_lt(v_i_338_, v_sz_337_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; 
lean_dec_ref(v_post_336_);
lean_dec_ref(v_pre_335_);
v___x_345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_345_, 0, v_bs_339_);
return v___x_345_;
}
else
{
lean_object* v_v_346_; lean_object* v___x_347_; 
v_v_346_ = lean_array_uget_borrowed(v_bs_339_, v_i_338_);
lean_inc(v_v_346_);
lean_inc_ref(v_post_336_);
lean_inc_ref(v_pre_335_);
v___x_347_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_335_, v_post_336_, v_v_346_, v___y_340_, v___y_341_, v___y_342_);
if (lean_obj_tag(v___x_347_) == 0)
{
lean_object* v_a_348_; lean_object* v___x_349_; lean_object* v_bs_x27_350_; size_t v___x_351_; size_t v___x_352_; lean_object* v___x_353_; 
v_a_348_ = lean_ctor_get(v___x_347_, 0);
lean_inc(v_a_348_);
lean_dec_ref(v___x_347_);
v___x_349_ = lean_unsigned_to_nat(0u);
v_bs_x27_350_ = lean_array_uset(v_bs_339_, v_i_338_, v___x_349_);
v___x_351_ = ((size_t)1ULL);
v___x_352_ = lean_usize_add(v_i_338_, v___x_351_);
v___x_353_ = lean_array_uset(v_bs_x27_350_, v_i_338_, v_a_348_);
v_i_338_ = v___x_352_;
v_bs_339_ = v___x_353_;
goto _start;
}
else
{
lean_object* v_a_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_362_; 
lean_dec_ref(v_bs_339_);
lean_dec_ref(v_post_336_);
lean_dec_ref(v_pre_335_);
v_a_355_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_362_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_362_ == 0)
{
v___x_357_ = v___x_347_;
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_a_355_);
lean_dec(v___x_347_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_360_; 
if (v_isShared_358_ == 0)
{
v___x_360_ = v___x_357_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_a_355_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4(lean_object* v_pre_363_, lean_object* v_post_364_, lean_object* v_x_365_, lean_object* v_x_366_, lean_object* v_x_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
if (lean_obj_tag(v_x_365_) == 5)
{
lean_object* v_fn_372_; lean_object* v_arg_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v_fn_372_ = lean_ctor_get(v_x_365_, 0);
lean_inc_ref(v_fn_372_);
v_arg_373_ = lean_ctor_get(v_x_365_, 1);
lean_inc_ref(v_arg_373_);
lean_dec_ref(v_x_365_);
v___x_374_ = lean_array_set(v_x_366_, v_x_367_, v_arg_373_);
v___x_375_ = lean_unsigned_to_nat(1u);
v___x_376_ = lean_nat_sub(v_x_367_, v___x_375_);
lean_dec(v_x_367_);
v_x_365_ = v_fn_372_;
v_x_366_ = v___x_374_;
v_x_367_ = v___x_376_;
goto _start;
}
else
{
lean_object* v___x_378_; 
lean_dec(v_x_367_);
lean_inc_ref(v_post_364_);
lean_inc_ref(v_pre_363_);
v___x_378_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_363_, v_post_364_, v_x_365_, v___y_368_, v___y_369_, v___y_370_);
if (lean_obj_tag(v___x_378_) == 0)
{
lean_object* v_a_379_; size_t v_sz_380_; size_t v___x_381_; lean_object* v___x_382_; 
v_a_379_ = lean_ctor_get(v___x_378_, 0);
lean_inc(v_a_379_);
lean_dec_ref(v___x_378_);
v_sz_380_ = lean_array_size(v_x_366_);
v___x_381_ = ((size_t)0ULL);
lean_inc_ref(v_post_364_);
lean_inc_ref(v_pre_363_);
v___x_382_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1(v_pre_363_, v_post_364_, v_sz_380_, v___x_381_, v_x_366_, v___y_368_, v___y_369_, v___y_370_);
if (lean_obj_tag(v___x_382_) == 0)
{
lean_object* v_a_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v_a_383_ = lean_ctor_get(v___x_382_, 0);
lean_inc(v_a_383_);
lean_dec_ref(v___x_382_);
v___x_384_ = l_Lean_mkAppN(v_a_379_, v_a_383_);
lean_dec(v_a_383_);
v___x_385_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_363_, v_post_364_, v___x_384_, v___y_368_, v___y_369_, v___y_370_);
return v___x_385_;
}
else
{
lean_object* v_a_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_393_; 
lean_dec(v_a_379_);
lean_dec_ref(v_post_364_);
lean_dec_ref(v_pre_363_);
v_a_386_ = lean_ctor_get(v___x_382_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_382_);
if (v_isSharedCheck_393_ == 0)
{
v___x_388_ = v___x_382_;
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_a_386_);
lean_dec(v___x_382_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_391_; 
if (v_isShared_389_ == 0)
{
v___x_391_ = v___x_388_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_a_386_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
}
}
else
{
lean_dec_ref(v_x_366_);
lean_dec_ref(v_post_364_);
lean_dec_ref(v_pre_363_);
return v___x_378_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1(lean_object* v___x_394_, lean_object* v_pre_395_, lean_object* v_e_396_, lean_object* v_post_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v___y_403_; lean_object* v___y_404_; lean_object* v___y_405_; lean_object* v___y_406_; uint8_t v___y_407_; lean_object* v___y_408_; lean_object* v___y_409_; uint8_t v___y_410_; lean_object* v___y_420_; lean_object* v___y_421_; uint8_t v___y_422_; lean_object* v___y_423_; lean_object* v___y_424_; uint8_t v___y_425_; lean_object* v___y_433_; lean_object* v___y_434_; lean_object* v___y_435_; uint8_t v___y_436_; lean_object* v___y_437_; uint8_t v___y_438_; lean_object* v___x_445_; 
v___x_445_ = l_Lean_Core_checkSystem(v___x_394_, v___y_399_, v___y_400_);
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v___x_446_; 
lean_dec_ref(v___x_445_);
lean_inc_ref(v_pre_395_);
lean_inc(v___y_400_);
lean_inc_ref(v___y_399_);
lean_inc_ref(v_e_396_);
v___x_446_ = lean_apply_4(v_pre_395_, v_e_396_, v___y_399_, v___y_400_, lean_box(0));
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_536_; 
v_a_447_ = lean_ctor_get(v___x_446_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_536_ == 0)
{
v___x_449_ = v___x_446_;
v_isShared_450_ = v_isSharedCheck_536_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v___x_446_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_536_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___y_452_; 
switch(lean_obj_tag(v_a_447_))
{
case 0:
{
lean_object* v_e_526_; lean_object* v___x_528_; 
lean_dec_ref(v_post_397_);
lean_dec_ref(v_e_396_);
lean_dec_ref(v_pre_395_);
v_e_526_ = lean_ctor_get(v_a_447_, 0);
lean_inc_ref(v_e_526_);
lean_dec_ref(v_a_447_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 0, v_e_526_);
v___x_528_ = v___x_449_;
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
lean_del_object(v___x_449_);
lean_dec_ref(v_e_396_);
v_e_530_ = lean_ctor_get(v_a_447_, 0);
lean_inc_ref(v_e_530_);
lean_dec_ref(v_a_447_);
lean_inc_ref(v_post_397_);
lean_inc_ref(v_pre_395_);
v___x_531_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_395_, v_post_397_, v_e_530_, v___y_398_, v___y_399_, v___y_400_);
if (lean_obj_tag(v___x_531_) == 0)
{
lean_object* v_a_532_; lean_object* v___x_533_; 
v_a_532_ = lean_ctor_get(v___x_531_, 0);
lean_inc(v_a_532_);
lean_dec_ref(v___x_531_);
v___x_533_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_395_, v_post_397_, v_a_532_, v___y_398_, v___y_399_, v___y_400_);
return v___x_533_;
}
else
{
lean_dec_ref(v_post_397_);
lean_dec_ref(v_pre_395_);
return v___x_531_;
}
}
default: 
{
lean_object* v_e_x3f_534_; 
lean_del_object(v___x_449_);
v_e_x3f_534_ = lean_ctor_get(v_a_447_, 0);
lean_inc(v_e_x3f_534_);
lean_dec_ref(v_a_447_);
if (lean_obj_tag(v_e_x3f_534_) == 0)
{
v___y_452_ = v_e_396_;
goto v___jp_451_;
}
else
{
lean_object* v_val_535_; 
lean_dec_ref(v_e_396_);
v_val_535_ = lean_ctor_get(v_e_x3f_534_, 0);
lean_inc(v_val_535_);
lean_dec_ref(v_e_x3f_534_);
v___y_452_ = v_val_535_;
goto v___jp_451_;
}
}
}
v___jp_451_:
{
switch(lean_obj_tag(v___y_452_))
{
case 7:
{
lean_object* v_binderName_453_; lean_object* v_binderType_454_; lean_object* v_body_455_; uint8_t v_binderInfo_456_; lean_object* v___x_457_; 
v_binderName_453_ = lean_ctor_get(v___y_452_, 0);
lean_inc(v_binderName_453_);
v_binderType_454_ = lean_ctor_get(v___y_452_, 1);
v_body_455_ = lean_ctor_get(v___y_452_, 2);
v_binderInfo_456_ = lean_ctor_get_uint8(v___y_452_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_454_);
lean_inc_ref(v_post_397_);
lean_inc_ref(v_pre_395_);
v___x_457_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_395_, v_post_397_, v_binderType_454_, v___y_398_, v___y_399_, v___y_400_);
if (lean_obj_tag(v___x_457_) == 0)
{
lean_object* v_a_458_; lean_object* v___x_459_; 
v_a_458_ = lean_ctor_get(v___x_457_, 0);
lean_inc(v_a_458_);
lean_dec_ref(v___x_457_);
lean_inc_ref(v_body_455_);
lean_inc_ref(v_post_397_);
lean_inc_ref(v_pre_395_);
v___x_459_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_395_, v_post_397_, v_body_455_, v___y_398_, v___y_399_, v___y_400_);
if (lean_obj_tag(v___x_459_) == 0)
{
lean_object* v_a_460_; size_t v___x_461_; size_t v___x_462_; uint8_t v___x_463_; 
v_a_460_ = lean_ctor_get(v___x_459_, 0);
lean_inc(v_a_460_);
lean_dec_ref(v___x_459_);
v___x_461_ = lean_ptr_addr(v_binderType_454_);
v___x_462_ = lean_ptr_addr(v_a_458_);
v___x_463_ = lean_usize_dec_eq(v___x_461_, v___x_462_);
if (v___x_463_ == 0)
{
v___y_433_ = v_a_460_;
v___y_434_ = v_a_458_;
v___y_435_ = v_binderName_453_;
v___y_436_ = v_binderInfo_456_;
v___y_437_ = v___y_452_;
v___y_438_ = v___x_463_;
goto v___jp_432_;
}
else
{
size_t v___x_464_; size_t v___x_465_; uint8_t v___x_466_; 
v___x_464_ = lean_ptr_addr(v_body_455_);
v___x_465_ = lean_ptr_addr(v_a_460_);
v___x_466_ = lean_usize_dec_eq(v___x_464_, v___x_465_);
v___y_433_ = v_a_460_;
v___y_434_ = v_a_458_;
v___y_435_ = v_binderName_453_;
v___y_436_ = v_binderInfo_456_;
v___y_437_ = v___y_452_;
v___y_438_ = v___x_466_;
goto v___jp_432_;
}
}
else
{
lean_dec(v_a_458_);
lean_dec_ref(v___y_452_);
lean_dec(v_binderName_453_);
lean_dec_ref(v_post_397_);
lean_dec_ref(v_pre_395_);
return v___x_459_;
}
}
else
{
lean_dec(v_binderName_453_);
lean_dec_ref(v___y_452_);
lean_dec_ref(v_post_397_);
lean_dec_ref(v_pre_395_);
return v___x_457_;
}
}
case 6:
{
lean_object* v_binderName_467_; lean_object* v_binderType_468_; lean_object* v_body_469_; uint8_t v_binderInfo_470_; lean_object* v___x_471_; 
v_binderName_467_ = lean_ctor_get(v___y_452_, 0);
lean_inc(v_binderName_467_);
v_binderType_468_ = lean_ctor_get(v___y_452_, 1);
v_body_469_ = lean_ctor_get(v___y_452_, 2);
v_binderInfo_470_ = lean_ctor_get_uint8(v___y_452_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_468_);
lean_inc_ref(v_post_397_);
lean_inc_ref(v_pre_395_);
v___x_471_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_395_, v_post_397_, v_binderType_468_, v___y_398_, v___y_399_, v___y_400_);
if (lean_obj_tag(v___x_471_) == 0)
{
lean_object* v_a_472_; lean_object* v___x_473_; 
v_a_472_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_a_472_);
lean_dec_ref(v___x_471_);
lean_inc_ref(v_body_469_);
lean_inc_ref(v_post_397_);
lean_inc_ref(v_pre_395_);
v___x_473_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_395_, v_post_397_, v_body_469_, v___y_398_, v___y_399_, v___y_400_);
if (lean_obj_tag(v___x_473_) == 0)
{
lean_object* v_a_474_; size_t v___x_475_; size_t v___x_476_; uint8_t v___x_477_; 
v_a_474_ = lean_ctor_get(v___x_473_, 0);
lean_inc(v_a_474_);
lean_dec_ref(v___x_473_);
v___x_475_ = lean_ptr_addr(v_binderType_468_);
v___x_476_ = lean_ptr_addr(v_a_472_);
v___x_477_ = lean_usize_dec_eq(v___x_475_, v___x_476_);
if (v___x_477_ == 0)
{
v___y_420_ = v_a_472_;
v___y_421_ = v_a_474_;
v___y_422_ = v_binderInfo_470_;
v___y_423_ = v_binderName_467_;
v___y_424_ = v___y_452_;
v___y_425_ = v___x_477_;
goto v___jp_419_;
}
else
{
size_t v___x_478_; size_t v___x_479_; uint8_t v___x_480_; 
v___x_478_ = lean_ptr_addr(v_body_469_);
v___x_479_ = lean_ptr_addr(v_a_474_);
v___x_480_ = lean_usize_dec_eq(v___x_478_, v___x_479_);
v___y_420_ = v_a_472_;
v___y_421_ = v_a_474_;
v___y_422_ = v_binderInfo_470_;
v___y_423_ = v_binderName_467_;
v___y_424_ = v___y_452_;
v___y_425_ = v___x_480_;
goto v___jp_419_;
}
}
else
{
lean_dec(v_a_472_);
lean_dec_ref(v___y_452_);
lean_dec(v_binderName_467_);
lean_dec_ref(v_post_397_);
lean_dec_ref(v_pre_395_);
return v___x_473_;
}
}
else
{
lean_dec(v_binderName_467_);
lean_dec_ref(v___y_452_);
lean_dec_ref(v_post_397_);
lean_dec_ref(v_pre_395_);
return v___x_471_;
}
}
case 8:
{
lean_object* v_declName_481_; lean_object* v_type_482_; lean_object* v_value_483_; lean_object* v_body_484_; uint8_t v_nondep_485_; lean_object* v___x_486_; 
v_declName_481_ = lean_ctor_get(v___y_452_, 0);
lean_inc(v_declName_481_);
v_type_482_ = lean_ctor_get(v___y_452_, 1);
v_value_483_ = lean_ctor_get(v___y_452_, 2);
v_body_484_ = lean_ctor_get(v___y_452_, 3);
lean_inc_ref(v_body_484_);
v_nondep_485_ = lean_ctor_get_uint8(v___y_452_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_482_);
lean_inc_ref(v_post_397_);
lean_inc_ref(v_pre_395_);
v___x_486_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_395_, v_post_397_, v_type_482_, v___y_398_, v___y_399_, v___y_400_);
if (lean_obj_tag(v___x_486_) == 0)
{
lean_object* v_a_487_; lean_object* v___x_488_; 
v_a_487_ = lean_ctor_get(v___x_486_, 0);
lean_inc(v_a_487_);
lean_dec_ref(v___x_486_);
lean_inc_ref(v_value_483_);
lean_inc_ref(v_post_397_);
lean_inc_ref(v_pre_395_);
v___x_488_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_395_, v_post_397_, v_value_483_, v___y_398_, v___y_399_, v___y_400_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v_a_489_; lean_object* v___x_490_; 
v_a_489_ = lean_ctor_get(v___x_488_, 0);
lean_inc(v_a_489_);
lean_dec_ref(v___x_488_);
lean_inc_ref(v_body_484_);
lean_inc_ref(v_post_397_);
lean_inc_ref(v_pre_395_);
v___x_490_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_395_, v_post_397_, v_body_484_, v___y_398_, v___y_399_, v___y_400_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v_a_491_; size_t v___x_492_; size_t v___x_493_; uint8_t v___x_494_; 
v_a_491_ = lean_ctor_get(v___x_490_, 0);
lean_inc(v_a_491_);
lean_dec_ref(v___x_490_);
v___x_492_ = lean_ptr_addr(v_type_482_);
v___x_493_ = lean_ptr_addr(v_a_487_);
v___x_494_ = lean_usize_dec_eq(v___x_492_, v___x_493_);
if (v___x_494_ == 0)
{
v___y_403_ = v_declName_481_;
v___y_404_ = v_a_487_;
v___y_405_ = v_a_489_;
v___y_406_ = v_body_484_;
v___y_407_ = v_nondep_485_;
v___y_408_ = v_a_491_;
v___y_409_ = v___y_452_;
v___y_410_ = v___x_494_;
goto v___jp_402_;
}
else
{
size_t v___x_495_; size_t v___x_496_; uint8_t v___x_497_; 
v___x_495_ = lean_ptr_addr(v_value_483_);
v___x_496_ = lean_ptr_addr(v_a_489_);
v___x_497_ = lean_usize_dec_eq(v___x_495_, v___x_496_);
v___y_403_ = v_declName_481_;
v___y_404_ = v_a_487_;
v___y_405_ = v_a_489_;
v___y_406_ = v_body_484_;
v___y_407_ = v_nondep_485_;
v___y_408_ = v_a_491_;
v___y_409_ = v___y_452_;
v___y_410_ = v___x_497_;
goto v___jp_402_;
}
}
else
{
lean_dec(v_a_489_);
lean_dec(v_a_487_);
lean_dec_ref(v_body_484_);
lean_dec(v_declName_481_);
lean_dec_ref(v___y_452_);
lean_dec_ref(v_post_397_);
lean_dec_ref(v_pre_395_);
return v___x_490_;
}
}
else
{
lean_dec(v_a_487_);
lean_dec_ref(v_body_484_);
lean_dec_ref(v___y_452_);
lean_dec(v_declName_481_);
lean_dec_ref(v_post_397_);
lean_dec_ref(v_pre_395_);
return v___x_488_;
}
}
else
{
lean_dec_ref(v_body_484_);
lean_dec(v_declName_481_);
lean_dec_ref(v___y_452_);
lean_dec_ref(v_post_397_);
lean_dec_ref(v_pre_395_);
return v___x_486_;
}
}
case 5:
{
lean_object* v_dummy_498_; lean_object* v_nargs_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v_dummy_498_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0);
v_nargs_499_ = l_Lean_Expr_getAppNumArgs(v___y_452_);
lean_inc(v_nargs_499_);
v___x_500_ = lean_mk_array(v_nargs_499_, v_dummy_498_);
v___x_501_ = lean_unsigned_to_nat(1u);
v___x_502_ = lean_nat_sub(v_nargs_499_, v___x_501_);
lean_dec(v_nargs_499_);
v___x_503_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4(v_pre_395_, v_post_397_, v___y_452_, v___x_500_, v___x_502_, v___y_398_, v___y_399_, v___y_400_);
return v___x_503_;
}
case 10:
{
lean_object* v_data_504_; lean_object* v_expr_505_; lean_object* v___x_506_; 
v_data_504_ = lean_ctor_get(v___y_452_, 0);
v_expr_505_ = lean_ctor_get(v___y_452_, 1);
lean_inc_ref(v_expr_505_);
lean_inc_ref(v_post_397_);
lean_inc_ref(v_pre_395_);
v___x_506_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_395_, v_post_397_, v_expr_505_, v___y_398_, v___y_399_, v___y_400_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v_a_507_; size_t v___x_508_; size_t v___x_509_; uint8_t v___x_510_; 
v_a_507_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_a_507_);
lean_dec_ref(v___x_506_);
v___x_508_ = lean_ptr_addr(v_expr_505_);
v___x_509_ = lean_ptr_addr(v_a_507_);
v___x_510_ = lean_usize_dec_eq(v___x_508_, v___x_509_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; lean_object* v___x_512_; 
lean_inc(v_data_504_);
lean_dec_ref(v___y_452_);
v___x_511_ = l_Lean_Expr_mdata___override(v_data_504_, v_a_507_);
v___x_512_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_395_, v_post_397_, v___x_511_, v___y_398_, v___y_399_, v___y_400_);
return v___x_512_;
}
else
{
lean_object* v___x_513_; 
lean_dec(v_a_507_);
v___x_513_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_395_, v_post_397_, v___y_452_, v___y_398_, v___y_399_, v___y_400_);
return v___x_513_;
}
}
else
{
lean_dec_ref(v___y_452_);
lean_dec_ref(v_post_397_);
lean_dec_ref(v_pre_395_);
return v___x_506_;
}
}
case 11:
{
lean_object* v_typeName_514_; lean_object* v_idx_515_; lean_object* v_struct_516_; lean_object* v___x_517_; 
v_typeName_514_ = lean_ctor_get(v___y_452_, 0);
v_idx_515_ = lean_ctor_get(v___y_452_, 1);
v_struct_516_ = lean_ctor_get(v___y_452_, 2);
lean_inc_ref(v_struct_516_);
lean_inc_ref(v_post_397_);
lean_inc_ref(v_pre_395_);
v___x_517_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_395_, v_post_397_, v_struct_516_, v___y_398_, v___y_399_, v___y_400_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v_a_518_; size_t v___x_519_; size_t v___x_520_; uint8_t v___x_521_; 
v_a_518_ = lean_ctor_get(v___x_517_, 0);
lean_inc(v_a_518_);
lean_dec_ref(v___x_517_);
v___x_519_ = lean_ptr_addr(v_struct_516_);
v___x_520_ = lean_ptr_addr(v_a_518_);
v___x_521_ = lean_usize_dec_eq(v___x_519_, v___x_520_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; lean_object* v___x_523_; 
lean_inc(v_idx_515_);
lean_inc(v_typeName_514_);
lean_dec_ref(v___y_452_);
v___x_522_ = l_Lean_Expr_proj___override(v_typeName_514_, v_idx_515_, v_a_518_);
v___x_523_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_395_, v_post_397_, v___x_522_, v___y_398_, v___y_399_, v___y_400_);
return v___x_523_;
}
else
{
lean_object* v___x_524_; 
lean_dec(v_a_518_);
v___x_524_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_395_, v_post_397_, v___y_452_, v___y_398_, v___y_399_, v___y_400_);
return v___x_524_;
}
}
else
{
lean_dec_ref(v___y_452_);
lean_dec_ref(v_post_397_);
lean_dec_ref(v_pre_395_);
return v___x_517_;
}
}
default: 
{
lean_object* v___x_525_; 
v___x_525_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_395_, v_post_397_, v___y_452_, v___y_398_, v___y_399_, v___y_400_);
return v___x_525_;
}
}
}
}
}
else
{
lean_object* v_a_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_544_; 
lean_dec_ref(v_post_397_);
lean_dec_ref(v_e_396_);
lean_dec_ref(v_pre_395_);
v_a_537_ = lean_ctor_get(v___x_446_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_544_ == 0)
{
v___x_539_ = v___x_446_;
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_a_537_);
lean_dec(v___x_446_);
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
lean_dec_ref(v_post_397_);
lean_dec_ref(v_e_396_);
lean_dec_ref(v_pre_395_);
v_a_545_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_552_ == 0)
{
v___x_547_ = v___x_445_;
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___x_445_);
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
v___jp_402_:
{
if (v___y_410_ == 0)
{
lean_object* v___x_411_; lean_object* v___x_412_; 
lean_dec_ref(v___y_409_);
lean_dec_ref(v___y_406_);
v___x_411_ = l_Lean_Expr_letE___override(v___y_403_, v___y_404_, v___y_405_, v___y_408_, v___y_407_);
v___x_412_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_395_, v_post_397_, v___x_411_, v___y_398_, v___y_399_, v___y_400_);
return v___x_412_;
}
else
{
size_t v___x_413_; size_t v___x_414_; uint8_t v___x_415_; 
v___x_413_ = lean_ptr_addr(v___y_406_);
lean_dec_ref(v___y_406_);
v___x_414_ = lean_ptr_addr(v___y_408_);
v___x_415_ = lean_usize_dec_eq(v___x_413_, v___x_414_);
if (v___x_415_ == 0)
{
lean_object* v___x_416_; lean_object* v___x_417_; 
lean_dec_ref(v___y_409_);
v___x_416_ = l_Lean_Expr_letE___override(v___y_403_, v___y_404_, v___y_405_, v___y_408_, v___y_407_);
v___x_417_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_395_, v_post_397_, v___x_416_, v___y_398_, v___y_399_, v___y_400_);
return v___x_417_;
}
else
{
lean_object* v___x_418_; 
lean_dec_ref(v___y_408_);
lean_dec_ref(v___y_405_);
lean_dec_ref(v___y_404_);
lean_dec(v___y_403_);
v___x_418_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_395_, v_post_397_, v___y_409_, v___y_398_, v___y_399_, v___y_400_);
return v___x_418_;
}
}
}
v___jp_419_:
{
if (v___y_425_ == 0)
{
lean_object* v___x_426_; lean_object* v___x_427_; 
lean_dec_ref(v___y_424_);
v___x_426_ = l_Lean_Expr_lam___override(v___y_423_, v___y_420_, v___y_421_, v___y_422_);
v___x_427_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_395_, v_post_397_, v___x_426_, v___y_398_, v___y_399_, v___y_400_);
return v___x_427_;
}
else
{
uint8_t v___x_428_; 
v___x_428_ = l_Lean_instBEqBinderInfo_beq(v___y_422_, v___y_422_);
if (v___x_428_ == 0)
{
lean_object* v___x_429_; lean_object* v___x_430_; 
lean_dec_ref(v___y_424_);
v___x_429_ = l_Lean_Expr_lam___override(v___y_423_, v___y_420_, v___y_421_, v___y_422_);
v___x_430_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_395_, v_post_397_, v___x_429_, v___y_398_, v___y_399_, v___y_400_);
return v___x_430_;
}
else
{
lean_object* v___x_431_; 
lean_dec(v___y_423_);
lean_dec_ref(v___y_421_);
lean_dec_ref(v___y_420_);
v___x_431_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_395_, v_post_397_, v___y_424_, v___y_398_, v___y_399_, v___y_400_);
return v___x_431_;
}
}
}
v___jp_432_:
{
if (v___y_438_ == 0)
{
lean_object* v___x_439_; lean_object* v___x_440_; 
lean_dec_ref(v___y_437_);
v___x_439_ = l_Lean_Expr_forallE___override(v___y_435_, v___y_434_, v___y_433_, v___y_436_);
v___x_440_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_395_, v_post_397_, v___x_439_, v___y_398_, v___y_399_, v___y_400_);
return v___x_440_;
}
else
{
uint8_t v___x_441_; 
v___x_441_ = l_Lean_instBEqBinderInfo_beq(v___y_436_, v___y_436_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; lean_object* v___x_443_; 
lean_dec_ref(v___y_437_);
v___x_442_ = l_Lean_Expr_forallE___override(v___y_435_, v___y_434_, v___y_433_, v___y_436_);
v___x_443_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_395_, v_post_397_, v___x_442_, v___y_398_, v___y_399_, v___y_400_);
return v___x_443_;
}
else
{
lean_object* v___x_444_; 
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
lean_dec_ref(v___y_433_);
v___x_444_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_395_, v_post_397_, v___y_437_, v___y_398_, v___y_399_, v___y_400_);
return v___x_444_;
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
lean_dec_ref(v___x_578_);
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
lean_dec_ref(v___x_575_);
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
lean_dec_ref(v_a_619_);
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
lean_dec_ref(v_a_619_);
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
lean_dec_ref(v_a_619_);
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
lean_dec_ref(v_e_x3f_629_);
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
lean_dec_ref(v___x_714_);
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
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_767_, lean_object* v_x_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(v_x_768_, v___y_769_, v___y_770_, v___y_771_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_774_, lean_object* v_x_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5(v_00_u03b1_774_, v_x_775_, v___y_776_, v___y_777_, v___y_778_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec(v___y_776_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_781_, lean_object* v_m_782_, lean_object* v_a_783_, lean_object* v_b_784_){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6___redArg(v_m_782_, v_a_783_, v_b_784_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_786_, lean_object* v_a_787_, lean_object* v_x_788_){
_start:
{
lean_object* v___x_789_; 
v___x_789_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(v_a_787_, v_x_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_790_, lean_object* v_a_791_, lean_object* v_x_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_790_, v_a_791_, v_x_792_);
lean_dec(v_x_792_);
lean_dec_ref(v_a_791_);
return v_res_793_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__9(lean_object* v_00_u03b2_794_, lean_object* v_a_795_, lean_object* v_x_796_){
_start:
{
uint8_t v___x_797_; 
v___x_797_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__9___redArg(v_a_795_, v_x_796_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__9___boxed(lean_object* v_00_u03b2_798_, lean_object* v_a_799_, lean_object* v_x_800_){
_start:
{
uint8_t v_res_801_; lean_object* v_r_802_; 
v_res_801_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__9(v_00_u03b2_798_, v_a_799_, v_x_800_);
lean_dec(v_x_800_);
lean_dec_ref(v_a_799_);
v_r_802_ = lean_box(v_res_801_);
return v_r_802_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_803_, lean_object* v_data_804_){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___redArg(v_data_804_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_806_, lean_object* v_a_807_, lean_object* v_b_808_, lean_object* v_x_809_){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11___redArg(v_a_807_, v_b_808_, v_x_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10_spec__11(lean_object* v_00_u03b2_811_, lean_object* v_i_812_, lean_object* v_source_813_, lean_object* v_target_814_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(v_i_812_, v_source_813_, v_target_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12(lean_object* v_00_u03b2_816_, lean_object* v_x_817_, lean_object* v_x_818_){
_start:
{
lean_object* v___x_819_; 
v___x_819_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(v_x_817_, v_x_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0(uint8_t v_skipIfPropOrEq_820_, lean_object* v_as_821_, size_t v_sz_822_, size_t v_i_823_, lean_object* v_b_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
lean_object* v_a_831_; uint8_t v___x_835_; 
v___x_835_ = lean_usize_dec_lt(v_i_823_, v_sz_822_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; 
v___x_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_836_, 0, v_b_824_);
return v___x_836_;
}
else
{
lean_object* v_snd_837_; lean_object* v_fst_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_916_; 
v_snd_837_ = lean_ctor_get(v_b_824_, 1);
v_fst_838_ = lean_ctor_get(v_b_824_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v_b_824_);
if (v_isSharedCheck_916_ == 0)
{
v___x_840_ = v_b_824_;
v_isShared_841_ = v_isSharedCheck_916_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_snd_837_);
lean_inc(v_fst_838_);
lean_dec(v_b_824_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_916_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v_array_842_; lean_object* v_start_843_; lean_object* v_stop_844_; uint8_t v___x_845_; 
v_array_842_ = lean_ctor_get(v_snd_837_, 0);
v_start_843_ = lean_ctor_get(v_snd_837_, 1);
v_stop_844_ = lean_ctor_get(v_snd_837_, 2);
v___x_845_ = lean_nat_dec_lt(v_start_843_, v_stop_844_);
if (v___x_845_ == 0)
{
lean_object* v___x_847_; 
if (v_isShared_841_ == 0)
{
v___x_847_ = v___x_840_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_fst_838_);
lean_ctor_set(v_reuseFailAlloc_849_, 1, v_snd_837_);
v___x_847_ = v_reuseFailAlloc_849_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
lean_object* v___x_848_; 
v___x_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
return v___x_848_;
}
}
else
{
lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_912_; 
lean_inc(v_stop_844_);
lean_inc(v_start_843_);
lean_inc_ref(v_array_842_);
v_isSharedCheck_912_ = !lean_is_exclusive(v_snd_837_);
if (v_isSharedCheck_912_ == 0)
{
lean_object* v_unused_913_; lean_object* v_unused_914_; lean_object* v_unused_915_; 
v_unused_913_ = lean_ctor_get(v_snd_837_, 2);
lean_dec(v_unused_913_);
v_unused_914_ = lean_ctor_get(v_snd_837_, 1);
lean_dec(v_unused_914_);
v_unused_915_ = lean_ctor_get(v_snd_837_, 0);
lean_dec(v_unused_915_);
v___x_851_ = v_snd_837_;
v_isShared_852_ = v_isSharedCheck_912_;
goto v_resetjp_850_;
}
else
{
lean_dec(v_snd_837_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_912_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v_a_853_; lean_object* v___x_854_; 
v_a_853_ = lean_array_uget_borrowed(v_as_821_, v_i_823_);
lean_inc(v___y_828_);
lean_inc_ref(v___y_827_);
lean_inc(v___y_826_);
lean_inc_ref(v___y_825_);
lean_inc(v_a_853_);
v___x_854_ = lean_infer_type(v_a_853_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_860_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_a_855_);
lean_dec_ref(v___x_854_);
v___x_856_ = lean_array_fget(v_array_842_, v_start_843_);
v___x_857_ = lean_unsigned_to_nat(1u);
v___x_858_ = lean_nat_add(v_start_843_, v___x_857_);
lean_dec(v_start_843_);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 1, v___x_858_);
v___x_860_ = v___x_851_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_array_842_);
lean_ctor_set(v_reuseFailAlloc_903_, 1, v___x_858_);
lean_ctor_set(v_reuseFailAlloc_903_, 2, v_stop_844_);
v___x_860_ = v_reuseFailAlloc_903_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
if (v_skipIfPropOrEq_820_ == 0)
{
lean_object* v___x_861_; 
lean_dec(v_a_855_);
lean_inc(v_a_853_);
v___x_861_ = l_Lean_Meta_mkEqHEq(v_a_853_, v___x_856_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v_a_862_; lean_object* v___x_863_; lean_object* v___x_865_; 
v_a_862_ = lean_ctor_get(v___x_861_, 0);
lean_inc(v_a_862_);
lean_dec_ref(v___x_861_);
v___x_863_ = lean_array_push(v_fst_838_, v_a_862_);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 1, v___x_860_);
lean_ctor_set(v___x_840_, 0, v___x_863_);
v___x_865_ = v___x_840_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_863_);
lean_ctor_set(v_reuseFailAlloc_866_, 1, v___x_860_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
v_a_831_ = v___x_865_;
goto v___jp_830_;
}
}
else
{
lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_874_; 
lean_dec_ref(v___x_860_);
lean_del_object(v___x_840_);
lean_dec(v_fst_838_);
v_a_867_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_874_ == 0)
{
v___x_869_ = v___x_861_;
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v___x_861_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_872_; 
if (v_isShared_870_ == 0)
{
v___x_872_ = v___x_869_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_a_867_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
}
else
{
lean_object* v___x_875_; 
v___x_875_ = l_Lean_Meta_isProp(v_a_855_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
if (lean_obj_tag(v___x_875_) == 0)
{
lean_object* v_a_876_; uint8_t v___x_881_; 
v_a_876_ = lean_ctor_get(v___x_875_, 0);
lean_inc(v_a_876_);
lean_dec_ref(v___x_875_);
v___x_881_ = lean_unbox(v_a_876_);
lean_dec(v_a_876_);
if (v___x_881_ == 0)
{
uint8_t v___x_882_; 
v___x_882_ = lean_expr_eqv(v_a_853_, v___x_856_);
if (v___x_882_ == 0)
{
lean_object* v___x_883_; 
lean_del_object(v___x_840_);
lean_inc(v_a_853_);
v___x_883_ = l_Lean_Meta_mkEqHEq(v_a_853_, v___x_856_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_a_884_);
lean_dec_ref(v___x_883_);
v___x_885_ = lean_array_push(v_fst_838_, v_a_884_);
v___x_886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_886_, 0, v___x_885_);
lean_ctor_set(v___x_886_, 1, v___x_860_);
v_a_831_ = v___x_886_;
goto v___jp_830_;
}
else
{
lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_894_; 
lean_dec_ref(v___x_860_);
lean_dec(v_fst_838_);
v_a_887_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_894_ == 0)
{
v___x_889_ = v___x_883_;
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v___x_883_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_892_; 
if (v_isShared_890_ == 0)
{
v___x_892_ = v___x_889_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_a_887_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
}
else
{
lean_dec(v___x_856_);
goto v___jp_877_;
}
}
else
{
lean_dec(v___x_856_);
goto v___jp_877_;
}
v___jp_877_:
{
lean_object* v___x_879_; 
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 1, v___x_860_);
v___x_879_ = v___x_840_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_fst_838_);
lean_ctor_set(v_reuseFailAlloc_880_, 1, v___x_860_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
v_a_831_ = v___x_879_;
goto v___jp_830_;
}
}
}
else
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
lean_dec_ref(v___x_860_);
lean_dec(v___x_856_);
lean_del_object(v___x_840_);
lean_dec(v_fst_838_);
v_a_895_ = lean_ctor_get(v___x_875_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_902_ == 0)
{
v___x_897_ = v___x_875_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_875_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_898_ == 0)
{
v___x_900_ = v___x_897_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_895_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
}
}
else
{
lean_object* v_a_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_911_; 
lean_del_object(v___x_851_);
lean_dec(v_stop_844_);
lean_dec(v_start_843_);
lean_dec_ref(v_array_842_);
lean_del_object(v___x_840_);
lean_dec(v_fst_838_);
v_a_904_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_911_ == 0)
{
v___x_906_ = v___x_854_;
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_a_904_);
lean_dec(v___x_854_);
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
}
v___jp_830_:
{
size_t v___x_832_; size_t v___x_833_; 
v___x_832_ = ((size_t)1ULL);
v___x_833_ = lean_usize_add(v_i_823_, v___x_832_);
v_i_823_ = v___x_833_;
v_b_824_ = v_a_831_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0___boxed(lean_object* v_skipIfPropOrEq_917_, lean_object* v_as_918_, lean_object* v_sz_919_, lean_object* v_i_920_, lean_object* v_b_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
uint8_t v_skipIfPropOrEq_boxed_927_; size_t v_sz_boxed_928_; size_t v_i_boxed_929_; lean_object* v_res_930_; 
v_skipIfPropOrEq_boxed_927_ = lean_unbox(v_skipIfPropOrEq_917_);
v_sz_boxed_928_ = lean_unbox_usize(v_sz_919_);
lean_dec(v_sz_919_);
v_i_boxed_929_ = lean_unbox_usize(v_i_920_);
lean_dec(v_i_920_);
v_res_930_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0(v_skipIfPropOrEq_boxed_927_, v_as_918_, v_sz_boxed_928_, v_i_boxed_929_, v_b_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
lean_dec_ref(v_as_918_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(lean_object* v_args1_933_, lean_object* v_args2_934_, uint8_t v_skipIfPropOrEq_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_){
_start:
{
lean_object* v___x_941_; lean_object* v_eqs_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; size_t v_sz_946_; size_t v___x_947_; lean_object* v___x_948_; 
v___x_941_ = lean_unsigned_to_nat(0u);
v_eqs_942_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_943_ = lean_array_get_size(v_args2_934_);
v___x_944_ = l_Array_toSubarray___redArg(v_args2_934_, v___x_941_, v___x_943_);
v___x_945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_945_, 0, v_eqs_942_);
lean_ctor_set(v___x_945_, 1, v___x_944_);
v_sz_946_ = lean_array_size(v_args1_933_);
v___x_947_ = ((size_t)0ULL);
v___x_948_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0(v_skipIfPropOrEq_935_, v_args1_933_, v_sz_946_, v___x_947_, v___x_945_, v_a_936_, v_a_937_, v_a_938_, v_a_939_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_957_; 
v_a_949_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_957_ == 0)
{
v___x_951_ = v___x_948_;
v_isShared_952_ = v_isSharedCheck_957_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_948_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_957_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v_fst_953_; lean_object* v___x_955_; 
v_fst_953_ = lean_ctor_get(v_a_949_, 0);
lean_inc(v_fst_953_);
lean_dec(v_a_949_);
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 0, v_fst_953_);
v___x_955_ = v___x_951_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_fst_953_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
else
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_965_; 
v_a_958_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_965_ == 0)
{
v___x_960_ = v___x_948_;
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_948_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___boxed(lean_object* v_args1_966_, lean_object* v_args2_967_, lean_object* v_skipIfPropOrEq_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_){
_start:
{
uint8_t v_skipIfPropOrEq_boxed_974_; lean_object* v_res_975_; 
v_skipIfPropOrEq_boxed_974_ = lean_unbox(v_skipIfPropOrEq_968_);
v_res_975_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v_args1_966_, v_args2_967_, v_skipIfPropOrEq_boxed_974_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
lean_dec(v_a_972_);
lean_dec_ref(v_a_971_);
lean_dec(v_a_970_);
lean_dec_ref(v_a_969_);
lean_dec_ref(v_args1_966_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0(lean_object* v_k_976_, lean_object* v_b_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
lean_object* v___x_983_; 
lean_inc(v___y_981_);
lean_inc_ref(v___y_980_);
lean_inc(v___y_979_);
lean_inc_ref(v___y_978_);
v___x_983_ = lean_apply_6(v_k_976_, v_b_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, lean_box(0));
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0___boxed(lean_object* v_k_984_, lean_object* v_b_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0(v_k_984_, v_b_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(lean_object* v_name_992_, uint8_t v_bi_993_, lean_object* v_type_994_, lean_object* v_k_995_, uint8_t v_kind_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_){
_start:
{
lean_object* v___f_1002_; lean_object* v___x_1003_; 
v___f_1002_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1002_, 0, v_k_995_);
v___x_1003_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_992_, v_bi_993_, v_type_994_, v___f_1002_, v_kind_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1011_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1006_ = v___x_1003_;
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_1003_);
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
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1019_; 
v_a_1012_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1014_ = v___x_1003_;
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_1003_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___boxed(lean_object* v_name_1020_, lean_object* v_bi_1021_, lean_object* v_type_1022_, lean_object* v_k_1023_, lean_object* v_kind_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_){
_start:
{
uint8_t v_bi_boxed_1030_; uint8_t v_kind_boxed_1031_; lean_object* v_res_1032_; 
v_bi_boxed_1030_ = lean_unbox(v_bi_1021_);
v_kind_boxed_1031_ = lean_unbox(v_kind_1024_);
v_res_1032_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_name_1020_, v_bi_boxed_1030_, v_type_1022_, v_k_1023_, v_kind_boxed_1031_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0(lean_object* v_00_u03b1_1033_, lean_object* v_name_1034_, uint8_t v_bi_1035_, lean_object* v_type_1036_, lean_object* v_k_1037_, uint8_t v_kind_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_name_1034_, v_bi_1035_, v_type_1036_, v_k_1037_, v_kind_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___boxed(lean_object* v_00_u03b1_1045_, lean_object* v_name_1046_, lean_object* v_bi_1047_, lean_object* v_type_1048_, lean_object* v_k_1049_, lean_object* v_kind_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
uint8_t v_bi_boxed_1056_; uint8_t v_kind_boxed_1057_; lean_object* v_res_1058_; 
v_bi_boxed_1056_ = lean_unbox(v_bi_1047_);
v_kind_boxed_1057_ = lean_unbox(v_kind_1050_);
v_res_1058_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0(v_00_u03b1_1045_, v_name_1046_, v_bi_boxed_1056_, v_type_1048_, v_k_1049_, v_kind_boxed_1057_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(lean_object* v_msgData_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
lean_object* v___x_1065_; lean_object* v_env_1066_; lean_object* v___x_1067_; lean_object* v_mctx_1068_; lean_object* v_lctx_1069_; lean_object* v_options_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1065_ = lean_st_ref_get(v___y_1063_);
v_env_1066_ = lean_ctor_get(v___x_1065_, 0);
lean_inc_ref(v_env_1066_);
lean_dec(v___x_1065_);
v___x_1067_ = lean_st_ref_get(v___y_1061_);
v_mctx_1068_ = lean_ctor_get(v___x_1067_, 0);
lean_inc_ref(v_mctx_1068_);
lean_dec(v___x_1067_);
v_lctx_1069_ = lean_ctor_get(v___y_1060_, 2);
v_options_1070_ = lean_ctor_get(v___y_1062_, 2);
lean_inc_ref(v_options_1070_);
lean_inc_ref(v_lctx_1069_);
v___x_1071_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1071_, 0, v_env_1066_);
lean_ctor_set(v___x_1071_, 1, v_mctx_1068_);
lean_ctor_set(v___x_1071_, 2, v_lctx_1069_);
lean_ctor_set(v___x_1071_, 3, v_options_1070_);
v___x_1072_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1071_);
lean_ctor_set(v___x_1072_, 1, v_msgData_1059_);
v___x_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1___boxed(lean_object* v_msgData_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msgData_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(lean_object* v_msg_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
lean_object* v_ref_1087_; lean_object* v___x_1088_; lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1097_; 
v_ref_1087_ = lean_ctor_get(v___y_1084_, 5);
v___x_1088_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msg_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
v_a_1089_ = lean_ctor_get(v___x_1088_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1091_ = v___x_1088_;
v_isShared_1092_ = v_isSharedCheck_1097_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1089_);
lean_dec(v___x_1088_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1097_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1093_; lean_object* v___x_1095_; 
lean_inc(v_ref_1087_);
v___x_1093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1093_, 0, v_ref_1087_);
lean_ctor_set(v___x_1093_, 1, v_a_1089_);
if (v_isShared_1092_ == 0)
{
lean_ctor_set_tag(v___x_1091_, 1);
lean_ctor_set(v___x_1091_, 0, v___x_1093_);
v___x_1095_ = v___x_1091_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg___boxed(lean_object* v_msg_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v_msg_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0___boxed(lean_object* v_i_1105_, lean_object* v_body_1106_, lean_object* v_args2_1107_, lean_object* v_args2New_1108_, lean_object* v_ctorVal_1109_, lean_object* v_useEq_1110_, lean_object* v_args1_1111_, lean_object* v_resultType_1112_, lean_object* v_k_1113_, lean_object* v_arg2_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
uint8_t v_useEq_boxed_1120_; lean_object* v_res_1121_; 
v_useEq_boxed_1120_ = lean_unbox(v_useEq_1110_);
v_res_1121_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0(v_i_1105_, v_body_1106_, v_args2_1107_, v_args2New_1108_, v_ctorVal_1109_, v_useEq_boxed_1120_, v_args1_1111_, v_resultType_1112_, v_k_1113_, v_arg2_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
lean_dec(v___y_1118_);
lean_dec_ref(v___y_1117_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
lean_dec_ref(v_body_1106_);
lean_dec(v_i_1105_);
return v_res_1121_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1(void){
_start:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1123_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__0));
v___x_1124_ = l_Lean_stringToMessageData(v___x_1123_);
return v___x_1124_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3(void){
_start:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1126_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__2));
v___x_1127_ = l_Lean_stringToMessageData(v___x_1126_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(lean_object* v_ctorVal_1128_, uint8_t v_useEq_1129_, lean_object* v_args1_1130_, lean_object* v_resultType_1131_, lean_object* v_k_1132_, lean_object* v_i_1133_, lean_object* v_type_1134_, lean_object* v_args2_1135_, lean_object* v_args2New_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_){
_start:
{
lean_object* v___x_1142_; uint8_t v___x_1143_; 
v___x_1142_ = lean_array_get_size(v_args1_1130_);
v___x_1143_ = lean_nat_dec_lt(v_i_1133_, v___x_1142_);
if (v___x_1143_ == 0)
{
lean_object* v___x_1144_; 
lean_dec_ref(v_type_1134_);
lean_dec(v_i_1133_);
lean_dec_ref(v_resultType_1131_);
lean_dec_ref(v_args1_1130_);
lean_dec_ref(v_ctorVal_1128_);
lean_inc(v_a_1140_);
lean_inc_ref(v_a_1139_);
lean_inc(v_a_1138_);
lean_inc_ref(v_a_1137_);
v___x_1144_ = lean_apply_7(v_k_1132_, v_args2_1135_, v_args2New_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_, lean_box(0));
return v___x_1144_;
}
else
{
lean_object* v___x_1145_; 
lean_inc(v_a_1140_);
lean_inc_ref(v_a_1139_);
lean_inc(v_a_1138_);
lean_inc_ref(v_a_1137_);
v___x_1145_ = lean_whnf(v_type_1134_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v_a_1146_; 
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
lean_inc(v_a_1146_);
lean_dec_ref(v___x_1145_);
if (lean_obj_tag(v_a_1146_) == 7)
{
lean_object* v_binderName_1147_; lean_object* v_binderType_1148_; lean_object* v_body_1149_; lean_object* v_lctx_1150_; lean_object* v___x_1151_; uint8_t v___x_1152_; 
v_binderName_1147_ = lean_ctor_get(v_a_1146_, 0);
lean_inc(v_binderName_1147_);
v_binderType_1148_ = lean_ctor_get(v_a_1146_, 1);
lean_inc_ref(v_binderType_1148_);
v_body_1149_ = lean_ctor_get(v_a_1146_, 2);
lean_inc_ref(v_body_1149_);
lean_dec_ref(v_a_1146_);
v_lctx_1150_ = lean_ctor_get(v_a_1137_, 2);
v___x_1151_ = lean_array_fget_borrowed(v_args1_1130_, v_i_1133_);
lean_inc(v___x_1151_);
lean_inc_ref(v_lctx_1150_);
v___x_1152_ = l_Lean_Meta_occursOrInType(v_lctx_1150_, v___x_1151_, v_resultType_1131_);
if (v___x_1152_ == 0)
{
lean_object* v___x_1153_; lean_object* v___f_1154_; uint8_t v___y_1156_; 
v___x_1153_ = lean_box(v_useEq_1129_);
v___f_1154_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0___boxed), 15, 9);
lean_closure_set(v___f_1154_, 0, v_i_1133_);
lean_closure_set(v___f_1154_, 1, v_body_1149_);
lean_closure_set(v___f_1154_, 2, v_args2_1135_);
lean_closure_set(v___f_1154_, 3, v_args2New_1136_);
lean_closure_set(v___f_1154_, 4, v_ctorVal_1128_);
lean_closure_set(v___f_1154_, 5, v___x_1153_);
lean_closure_set(v___f_1154_, 6, v_args1_1130_);
lean_closure_set(v___f_1154_, 7, v_resultType_1131_);
lean_closure_set(v___f_1154_, 8, v_k_1132_);
if (v_useEq_1129_ == 0)
{
uint8_t v___x_1159_; 
v___x_1159_ = 1;
v___y_1156_ = v___x_1159_;
goto v___jp_1155_;
}
else
{
uint8_t v___x_1160_; 
v___x_1160_ = 0;
v___y_1156_ = v___x_1160_;
goto v___jp_1155_;
}
v___jp_1155_:
{
uint8_t v___x_1157_; lean_object* v___x_1158_; 
v___x_1157_ = 0;
v___x_1158_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_binderName_1147_, v___y_1156_, v_binderType_1148_, v___f_1154_, v___x_1157_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_);
return v___x_1158_;
}
}
else
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
lean_dec_ref(v_binderType_1148_);
lean_dec(v_binderName_1147_);
v___x_1161_ = lean_unsigned_to_nat(1u);
v___x_1162_ = lean_nat_add(v_i_1133_, v___x_1161_);
lean_dec(v_i_1133_);
v___x_1163_ = lean_expr_instantiate1(v_body_1149_, v___x_1151_);
lean_dec_ref(v_body_1149_);
lean_inc(v___x_1151_);
v___x_1164_ = lean_array_push(v_args2_1135_, v___x_1151_);
v_i_1133_ = v___x_1162_;
v_type_1134_ = v___x_1163_;
v_args2_1135_ = v___x_1164_;
goto _start;
}
}
else
{
lean_object* v_toConstantVal_1166_; lean_object* v_name_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; 
lean_dec(v_a_1146_);
lean_dec_ref(v_args2New_1136_);
lean_dec_ref(v_args2_1135_);
lean_dec(v_i_1133_);
lean_dec_ref(v_k_1132_);
lean_dec_ref(v_resultType_1131_);
lean_dec_ref(v_args1_1130_);
v_toConstantVal_1166_ = lean_ctor_get(v_ctorVal_1128_, 0);
lean_inc_ref(v_toConstantVal_1166_);
lean_dec_ref(v_ctorVal_1128_);
v_name_1167_ = lean_ctor_get(v_toConstantVal_1166_, 0);
lean_inc(v_name_1167_);
lean_dec_ref(v_toConstantVal_1166_);
v___x_1168_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1);
v___x_1169_ = l_Lean_MessageData_ofName(v_name_1167_);
v___x_1170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1168_);
lean_ctor_set(v___x_1170_, 1, v___x_1169_);
v___x_1171_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_1172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1170_);
lean_ctor_set(v___x_1172_, 1, v___x_1171_);
v___x_1173_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_1172_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_);
return v___x_1173_;
}
}
else
{
lean_object* v_a_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1181_; 
lean_dec_ref(v_args2New_1136_);
lean_dec_ref(v_args2_1135_);
lean_dec(v_i_1133_);
lean_dec_ref(v_k_1132_);
lean_dec_ref(v_resultType_1131_);
lean_dec_ref(v_args1_1130_);
lean_dec_ref(v_ctorVal_1128_);
v_a_1174_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1176_ = v___x_1145_;
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_a_1174_);
lean_dec(v___x_1145_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1179_; 
if (v_isShared_1177_ == 0)
{
v___x_1179_ = v___x_1176_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_a_1174_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0(lean_object* v_i_1182_, lean_object* v_body_1183_, lean_object* v_args2_1184_, lean_object* v_args2New_1185_, lean_object* v_ctorVal_1186_, uint8_t v_useEq_1187_, lean_object* v_args1_1188_, lean_object* v_resultType_1189_, lean_object* v_k_1190_, lean_object* v_arg2_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1197_ = lean_unsigned_to_nat(1u);
v___x_1198_ = lean_nat_add(v_i_1182_, v___x_1197_);
v___x_1199_ = lean_expr_instantiate1(v_body_1183_, v_arg2_1191_);
lean_inc_ref(v_arg2_1191_);
v___x_1200_ = lean_array_push(v_args2_1184_, v_arg2_1191_);
v___x_1201_ = lean_array_push(v_args2New_1185_, v_arg2_1191_);
v___x_1202_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(v_ctorVal_1186_, v_useEq_1187_, v_args1_1188_, v_resultType_1189_, v_k_1190_, v___x_1198_, v___x_1199_, v___x_1200_, v___x_1201_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___boxed(lean_object* v_ctorVal_1203_, lean_object* v_useEq_1204_, lean_object* v_args1_1205_, lean_object* v_resultType_1206_, lean_object* v_k_1207_, lean_object* v_i_1208_, lean_object* v_type_1209_, lean_object* v_args2_1210_, lean_object* v_args2New_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_){
_start:
{
uint8_t v_useEq_boxed_1217_; lean_object* v_res_1218_; 
v_useEq_boxed_1217_ = lean_unbox(v_useEq_1204_);
v_res_1218_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(v_ctorVal_1203_, v_useEq_boxed_1217_, v_args1_1205_, v_resultType_1206_, v_k_1207_, v_i_1208_, v_type_1209_, v_args2_1210_, v_args2New_1211_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_);
lean_dec(v_a_1215_);
lean_dec_ref(v_a_1214_);
lean_dec(v_a_1213_);
lean_dec_ref(v_a_1212_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1(lean_object* v_00_u03b1_1219_, lean_object* v_msg_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v___x_1226_; 
v___x_1226_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v_msg_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___boxed(lean_object* v_00_u03b1_1227_, lean_object* v_msg_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1(v_00_u03b1_1227_, v_msg_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_match__1_splitter___redArg(lean_object* v_____x_1235_, lean_object* v_h__1_1236_, lean_object* v_h__2_1237_){
_start:
{
if (lean_obj_tag(v_____x_1235_) == 7)
{
lean_object* v_binderName_1238_; lean_object* v_binderType_1239_; lean_object* v_body_1240_; uint8_t v_binderInfo_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
lean_dec(v_h__2_1237_);
v_binderName_1238_ = lean_ctor_get(v_____x_1235_, 0);
lean_inc(v_binderName_1238_);
v_binderType_1239_ = lean_ctor_get(v_____x_1235_, 1);
lean_inc_ref(v_binderType_1239_);
v_body_1240_ = lean_ctor_get(v_____x_1235_, 2);
lean_inc_ref(v_body_1240_);
v_binderInfo_1241_ = lean_ctor_get_uint8(v_____x_1235_, sizeof(void*)*3 + 8);
lean_dec_ref(v_____x_1235_);
v___x_1242_ = lean_box(v_binderInfo_1241_);
v___x_1243_ = lean_apply_4(v_h__1_1236_, v_binderName_1238_, v_binderType_1239_, v_body_1240_, v___x_1242_);
return v___x_1243_;
}
else
{
lean_object* v___x_1244_; 
lean_dec(v_h__1_1236_);
v___x_1244_ = lean_apply_2(v_h__2_1237_, v_____x_1235_, lean_box(0));
return v___x_1244_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_match__1_splitter(lean_object* v_motive_1245_, lean_object* v_____x_1246_, lean_object* v_h__1_1247_, lean_object* v_h__2_1248_){
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
lean_dec_ref(v_____x_1246_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0(lean_object* v_k_1256_, lean_object* v_b_1257_, lean_object* v_c_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
lean_object* v___x_1264_; 
lean_inc(v___y_1262_);
lean_inc_ref(v___y_1261_);
lean_inc(v___y_1260_);
lean_inc_ref(v___y_1259_);
v___x_1264_ = lean_apply_7(v_k_1256_, v_b_1257_, v_c_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, lean_box(0));
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed(lean_object* v_k_1265_, lean_object* v_b_1266_, lean_object* v_c_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0(v_k_1265_, v_b_1266_, v_c_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(lean_object* v_type_1274_, lean_object* v_k_1275_, uint8_t v_cleanupAnnotations_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v___f_1282_; uint8_t v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___f_1282_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1282_, 0, v_k_1275_);
v___x_1283_ = 0;
v___x_1284_ = lean_box(0);
v___x_1285_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_1283_, v___x_1284_, v_type_1274_, v___f_1282_, v_cleanupAnnotations_1276_, v___x_1283_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
v_a_1286_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1288_ = v___x_1285_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1285_);
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
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1301_; 
v_a_1294_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1296_ = v___x_1285_;
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1285_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1299_; 
if (v_isShared_1297_ == 0)
{
v___x_1299_ = v___x_1296_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1294_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___boxed(lean_object* v_type_1302_, lean_object* v_k_1303_, lean_object* v_cleanupAnnotations_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1310_; lean_object* v_res_1311_; 
v_cleanupAnnotations_boxed_1310_ = lean_unbox(v_cleanupAnnotations_1304_);
v_res_1311_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_type_1302_, v_k_1303_, v_cleanupAnnotations_boxed_1310_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2(lean_object* v_00_u03b1_1312_, lean_object* v_type_1313_, lean_object* v_k_1314_, uint8_t v_cleanupAnnotations_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_){
_start:
{
lean_object* v___x_1321_; 
v___x_1321_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_type_1313_, v_k_1314_, v_cleanupAnnotations_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___boxed(lean_object* v_00_u03b1_1322_, lean_object* v_type_1323_, lean_object* v_k_1324_, lean_object* v_cleanupAnnotations_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1331_; lean_object* v_res_1332_; 
v_cleanupAnnotations_boxed_1331_ = lean_unbox(v_cleanupAnnotations_1325_);
v_res_1332_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2(v_00_u03b1_1322_, v_type_1323_, v_k_1324_, v_cleanupAnnotations_boxed_1331_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(lean_object* v_type_1333_, lean_object* v_maxFVars_x3f_1334_, lean_object* v_k_1335_, uint8_t v_cleanupAnnotations_1336_, uint8_t v_whnfType_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
lean_object* v___f_1343_; lean_object* v___x_1344_; 
v___f_1343_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1343_, 0, v_k_1335_);
v___x_1344_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_1333_, v_maxFVars_x3f_1334_, v___f_1343_, v_cleanupAnnotations_1336_, v_whnfType_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1352_; 
v_a_1345_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1347_ = v___x_1344_;
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_dec(v___x_1344_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1350_; 
if (v_isShared_1348_ == 0)
{
v___x_1350_ = v___x_1347_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_a_1345_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
}
else
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1360_; 
v_a_1353_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1355_ = v___x_1344_;
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___x_1344_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1358_; 
if (v_isShared_1356_ == 0)
{
v___x_1358_ = v___x_1355_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_a_1353_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg___boxed(lean_object* v_type_1361_, lean_object* v_maxFVars_x3f_1362_, lean_object* v_k_1363_, lean_object* v_cleanupAnnotations_1364_, lean_object* v_whnfType_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1371_; uint8_t v_whnfType_boxed_1372_; lean_object* v_res_1373_; 
v_cleanupAnnotations_boxed_1371_ = lean_unbox(v_cleanupAnnotations_1364_);
v_whnfType_boxed_1372_ = lean_unbox(v_whnfType_1365_);
v_res_1373_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(v_type_1361_, v_maxFVars_x3f_1362_, v_k_1363_, v_cleanupAnnotations_boxed_1371_, v_whnfType_boxed_1372_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
lean_dec(v___y_1367_);
lean_dec_ref(v___y_1366_);
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3(lean_object* v_00_u03b1_1374_, lean_object* v_type_1375_, lean_object* v_maxFVars_x3f_1376_, lean_object* v_k_1377_, uint8_t v_cleanupAnnotations_1378_, uint8_t v_whnfType_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
lean_object* v___x_1385_; 
v___x_1385_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(v_type_1375_, v_maxFVars_x3f_1376_, v_k_1377_, v_cleanupAnnotations_1378_, v_whnfType_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_);
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___boxed(lean_object* v_00_u03b1_1386_, lean_object* v_type_1387_, lean_object* v_maxFVars_x3f_1388_, lean_object* v_k_1389_, lean_object* v_cleanupAnnotations_1390_, lean_object* v_whnfType_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1397_; uint8_t v_whnfType_boxed_1398_; lean_object* v_res_1399_; 
v_cleanupAnnotations_boxed_1397_ = lean_unbox(v_cleanupAnnotations_1390_);
v_whnfType_boxed_1398_ = lean_unbox(v_whnfType_1391_);
v_res_1399_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3(v_00_u03b1_1386_, v_type_1387_, v_maxFVars_x3f_1388_, v_k_1389_, v_cleanupAnnotations_boxed_1397_, v_whnfType_boxed_1398_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0(lean_object* v_name_1400_, lean_object* v_us_1401_, lean_object* v_params_1402_, lean_object* v_args1_1403_, uint8_t v_useEq_1404_, lean_object* v_args2_1405_, lean_object* v_args2New_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_){
_start:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1412_ = l_Lean_mkConst(v_name_1400_, v_us_1401_);
v___x_1413_ = l_Lean_mkAppN(v___x_1412_, v_params_1402_);
lean_inc_ref(v___x_1413_);
v___x_1414_ = l_Lean_mkAppN(v___x_1413_, v_args1_1403_);
v___x_1415_ = l_Lean_mkAppN(v___x_1413_, v_args2_1405_);
v___x_1416_ = l_Lean_Meta_mkEq(v___x_1414_, v___x_1415_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_object* v_a_1417_; uint8_t v___x_1418_; lean_object* v_result_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v___x_1465_; 
v_a_1417_ = lean_ctor_get(v___x_1416_, 0);
lean_inc(v_a_1417_);
lean_dec_ref(v___x_1416_);
v___x_1418_ = 1;
v___x_1465_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v_args1_1403_, v_args2_1405_, v___x_1418_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1497_; 
v_a_1466_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1468_ = v___x_1465_;
v_isShared_1469_ = v_isSharedCheck_1497_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v___x_1465_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1497_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1470_; 
v___x_1470_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f(v_a_1466_);
if (lean_obj_tag(v___x_1470_) == 1)
{
lean_del_object(v___x_1468_);
if (v_useEq_1404_ == 0)
{
lean_object* v_val_1471_; lean_object* v___x_1472_; 
v_val_1471_ = lean_ctor_get(v___x_1470_, 0);
lean_inc(v_val_1471_);
lean_dec_ref(v___x_1470_);
v___x_1472_ = l_Lean_mkArrow(v_a_1417_, v_val_1471_, v___y_1409_, v___y_1410_);
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_object* v_a_1473_; 
v_a_1473_ = lean_ctor_get(v___x_1472_, 0);
lean_inc(v_a_1473_);
lean_dec_ref(v___x_1472_);
v_result_1420_ = v_a_1473_;
v___y_1421_ = v___y_1407_;
v___y_1422_ = v___y_1408_;
v___y_1423_ = v___y_1409_;
v___y_1424_ = v___y_1410_;
goto v___jp_1419_;
}
else
{
lean_object* v_a_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1481_; 
v_a_1474_ = lean_ctor_get(v___x_1472_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1472_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1476_ = v___x_1472_;
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_a_1474_);
lean_dec(v___x_1472_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1479_; 
if (v_isShared_1477_ == 0)
{
v___x_1479_ = v___x_1476_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_a_1474_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
}
}
else
{
lean_object* v_val_1482_; lean_object* v___x_1483_; 
v_val_1482_ = lean_ctor_get(v___x_1470_, 0);
lean_inc(v_val_1482_);
lean_dec_ref(v___x_1470_);
v___x_1483_ = l_Lean_Meta_mkEq(v_a_1417_, v_val_1482_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_object* v_a_1484_; 
v_a_1484_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_a_1484_);
lean_dec_ref(v___x_1483_);
v_result_1420_ = v_a_1484_;
v___y_1421_ = v___y_1407_;
v___y_1422_ = v___y_1408_;
v___y_1423_ = v___y_1409_;
v___y_1424_ = v___y_1410_;
goto v___jp_1419_;
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
}
else
{
lean_object* v___x_1493_; lean_object* v___x_1495_; 
lean_dec(v___x_1470_);
lean_dec(v_a_1417_);
v___x_1493_ = lean_box(0);
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 0, v___x_1493_);
v___x_1495_ = v___x_1468_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v___x_1493_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
}
else
{
lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1505_; 
lean_dec(v_a_1417_);
v_a_1498_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1500_ = v___x_1465_;
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_a_1498_);
lean_dec(v___x_1465_);
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
v___jp_1419_:
{
uint8_t v___x_1425_; uint8_t v___x_1426_; lean_object* v___x_1427_; 
v___x_1425_ = 0;
v___x_1426_ = 1;
v___x_1427_ = l_Lean_Meta_mkForallFVars(v_args2New_1406_, v_result_1420_, v___x_1425_, v___x_1418_, v___x_1418_, v___x_1426_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v_a_1428_; lean_object* v___x_1429_; 
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
lean_inc(v_a_1428_);
lean_dec_ref(v___x_1427_);
v___x_1429_ = l_Lean_Meta_mkForallFVars(v_args1_1403_, v_a_1428_, v___x_1425_, v___x_1418_, v___x_1418_, v___x_1426_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v_a_1430_; lean_object* v___x_1431_; 
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
lean_inc(v_a_1430_);
lean_dec_ref(v___x_1429_);
v___x_1431_ = l_Lean_Meta_mkForallFVars(v_params_1402_, v_a_1430_, v___x_1425_, v___x_1418_, v___x_1418_, v___x_1426_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v_a_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1440_; 
v_a_1432_ = lean_ctor_get(v___x_1431_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1434_ = v___x_1431_;
v_isShared_1435_ = v_isSharedCheck_1440_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_a_1432_);
lean_dec(v___x_1431_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1440_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1436_; lean_object* v___x_1438_; 
v___x_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1436_, 0, v_a_1432_);
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 0, v___x_1436_);
v___x_1438_ = v___x_1434_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v___x_1436_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
else
{
lean_object* v_a_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1448_; 
v_a_1441_ = lean_ctor_get(v___x_1431_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1443_ = v___x_1431_;
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_a_1441_);
lean_dec(v___x_1431_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1446_; 
if (v_isShared_1444_ == 0)
{
v___x_1446_ = v___x_1443_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_a_1441_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
}
else
{
lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1456_; 
v_a_1449_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1451_ = v___x_1429_;
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1429_);
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
v_a_1457_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1459_ = v___x_1427_;
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v___x_1427_);
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
else
{
lean_object* v_a_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1513_; 
lean_dec_ref(v_args2_1405_);
v_a_1506_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1508_ = v___x_1416_;
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_a_1506_);
lean_dec(v___x_1416_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1511_; 
if (v_isShared_1509_ == 0)
{
v___x_1511_ = v___x_1508_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_a_1506_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0___boxed(lean_object* v_name_1514_, lean_object* v_us_1515_, lean_object* v_params_1516_, lean_object* v_args1_1517_, lean_object* v_useEq_1518_, lean_object* v_args2_1519_, lean_object* v_args2New_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_){
_start:
{
uint8_t v_useEq_boxed_1526_; lean_object* v_res_1527_; 
v_useEq_boxed_1526_ = lean_unbox(v_useEq_1518_);
v_res_1527_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0(v_name_1514_, v_us_1515_, v_params_1516_, v_args1_1517_, v_useEq_boxed_1526_, v_args2_1519_, v_args2New_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec_ref(v_args2New_1520_);
lean_dec_ref(v_args1_1517_);
lean_dec_ref(v_params_1516_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1(size_t v_sz_1528_, size_t v_i_1529_, lean_object* v_bs_1530_){
_start:
{
uint8_t v___x_1531_; 
v___x_1531_ = lean_usize_dec_lt(v_i_1529_, v_sz_1528_);
if (v___x_1531_ == 0)
{
return v_bs_1530_;
}
else
{
lean_object* v_v_1532_; lean_object* v___x_1533_; lean_object* v_bs_x27_1534_; lean_object* v___x_1535_; uint8_t v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; size_t v___x_1539_; size_t v___x_1540_; lean_object* v___x_1541_; 
v_v_1532_ = lean_array_uget(v_bs_1530_, v_i_1529_);
v___x_1533_ = lean_unsigned_to_nat(0u);
v_bs_x27_1534_ = lean_array_uset(v_bs_1530_, v_i_1529_, v___x_1533_);
v___x_1535_ = l_Lean_Expr_fvarId_x21(v_v_1532_);
lean_dec(v_v_1532_);
v___x_1536_ = 1;
v___x_1537_ = lean_box(v___x_1536_);
v___x_1538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1535_);
lean_ctor_set(v___x_1538_, 1, v___x_1537_);
v___x_1539_ = ((size_t)1ULL);
v___x_1540_ = lean_usize_add(v_i_1529_, v___x_1539_);
v___x_1541_ = lean_array_uset(v_bs_x27_1534_, v_i_1529_, v___x_1538_);
v_i_1529_ = v___x_1540_;
v_bs_1530_ = v___x_1541_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1___boxed(lean_object* v_sz_1543_, lean_object* v_i_1544_, lean_object* v_bs_1545_){
_start:
{
size_t v_sz_boxed_1546_; size_t v_i_boxed_1547_; lean_object* v_res_1548_; 
v_sz_boxed_1546_ = lean_unbox_usize(v_sz_1543_);
lean_dec(v_sz_1543_);
v_i_boxed_1547_ = lean_unbox_usize(v_i_1544_);
lean_dec(v_i_1544_);
v_res_1548_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1(v_sz_boxed_1546_, v_i_boxed_1547_, v_bs_1545_);
return v_res_1548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(lean_object* v_bs_1549_, lean_object* v_k_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
lean_object* v___x_1556_; 
v___x_1556_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_box(0), v_bs_1549_, v_k_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1564_; 
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1559_ = v___x_1556_;
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1556_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1562_; 
if (v_isShared_1560_ == 0)
{
v___x_1562_ = v___x_1559_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_a_1557_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
else
{
lean_object* v_a_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1572_; 
v_a_1565_ = lean_ctor_get(v___x_1556_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1567_ = v___x_1556_;
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_a_1565_);
lean_dec(v___x_1556_);
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
v_reuseFailAlloc_1571_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_bs_1573_, lean_object* v_k_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(v_bs_1573_, v_k_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
lean_dec(v___y_1576_);
lean_dec_ref(v___y_1575_);
lean_dec_ref(v_bs_1573_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(lean_object* v_bs_1581_, lean_object* v_k_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_){
_start:
{
size_t v_sz_1588_; size_t v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; 
v_sz_1588_ = lean_array_size(v_bs_1581_);
v___x_1589_ = ((size_t)0ULL);
v___x_1590_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1(v_sz_1588_, v___x_1589_, v_bs_1581_);
v___x_1591_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(v___x_1590_, v_k_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_);
lean_dec_ref(v___x_1590_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg___boxed(lean_object* v_bs_1592_, lean_object* v_k_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
lean_object* v_res_1599_; 
v_res_1599_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v_bs_1592_, v_k_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
lean_dec(v___y_1597_);
lean_dec_ref(v___y_1596_);
lean_dec(v___y_1595_);
lean_dec_ref(v___y_1594_);
return v_res_1599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1(lean_object* v_name_1600_, lean_object* v_us_1601_, lean_object* v_params_1602_, uint8_t v_useEq_1603_, lean_object* v_ctorVal_1604_, lean_object* v_type_1605_, lean_object* v_args1_1606_, lean_object* v_resultType_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_){
_start:
{
lean_object* v___x_1613_; lean_object* v___f_1614_; 
v___x_1613_ = lean_box(v_useEq_1603_);
lean_inc_ref(v_args1_1606_);
lean_inc_ref(v_params_1602_);
v___f_1614_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1614_, 0, v_name_1600_);
lean_closure_set(v___f_1614_, 1, v_us_1601_);
lean_closure_set(v___f_1614_, 2, v_params_1602_);
lean_closure_set(v___f_1614_, 3, v_args1_1606_);
lean_closure_set(v___f_1614_, 4, v___x_1613_);
if (v_useEq_1603_ == 0)
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1615_ = l_Array_append___redArg(v_params_1602_, v_args1_1606_);
v___x_1616_ = lean_unsigned_to_nat(0u);
v___x_1617_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_1618_ = lean_box(v_useEq_1603_);
v___x_1619_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___boxed), 14, 9);
lean_closure_set(v___x_1619_, 0, v_ctorVal_1604_);
lean_closure_set(v___x_1619_, 1, v___x_1618_);
lean_closure_set(v___x_1619_, 2, v_args1_1606_);
lean_closure_set(v___x_1619_, 3, v_resultType_1607_);
lean_closure_set(v___x_1619_, 4, v___f_1614_);
lean_closure_set(v___x_1619_, 5, v___x_1616_);
lean_closure_set(v___x_1619_, 6, v_type_1605_);
lean_closure_set(v___x_1619_, 7, v___x_1617_);
lean_closure_set(v___x_1619_, 8, v___x_1617_);
v___x_1620_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v___x_1615_, v___x_1619_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
return v___x_1620_;
}
else
{
lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; 
lean_dec_ref(v_params_1602_);
v___x_1621_ = lean_unsigned_to_nat(0u);
v___x_1622_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_1623_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(v_ctorVal_1604_, v_useEq_1603_, v_args1_1606_, v_resultType_1607_, v___f_1614_, v___x_1621_, v_type_1605_, v___x_1622_, v___x_1622_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
return v___x_1623_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1___boxed(lean_object* v_name_1624_, lean_object* v_us_1625_, lean_object* v_params_1626_, lean_object* v_useEq_1627_, lean_object* v_ctorVal_1628_, lean_object* v_type_1629_, lean_object* v_args1_1630_, lean_object* v_resultType_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
uint8_t v_useEq_boxed_1637_; lean_object* v_res_1638_; 
v_useEq_boxed_1637_ = lean_unbox(v_useEq_1627_);
v_res_1638_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1(v_name_1624_, v_us_1625_, v_params_1626_, v_useEq_boxed_1637_, v_ctorVal_1628_, v_type_1629_, v_args1_1630_, v_resultType_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2(lean_object* v_name_1639_, lean_object* v_us_1640_, uint8_t v_useEq_1641_, lean_object* v_ctorVal_1642_, lean_object* v_params_1643_, lean_object* v_type_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
lean_object* v___x_1650_; lean_object* v___f_1651_; uint8_t v___x_1652_; lean_object* v___x_1653_; 
v___x_1650_ = lean_box(v_useEq_1641_);
lean_inc_ref(v_type_1644_);
v___f_1651_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1___boxed), 13, 6);
lean_closure_set(v___f_1651_, 0, v_name_1639_);
lean_closure_set(v___f_1651_, 1, v_us_1640_);
lean_closure_set(v___f_1651_, 2, v_params_1643_);
lean_closure_set(v___f_1651_, 3, v___x_1650_);
lean_closure_set(v___f_1651_, 4, v_ctorVal_1642_);
lean_closure_set(v___f_1651_, 5, v_type_1644_);
v___x_1652_ = 0;
v___x_1653_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_type_1644_, v___f_1651_, v___x_1652_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2___boxed(lean_object* v_name_1654_, lean_object* v_us_1655_, lean_object* v_useEq_1656_, lean_object* v_ctorVal_1657_, lean_object* v_params_1658_, lean_object* v_type_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_){
_start:
{
uint8_t v_useEq_boxed_1665_; lean_object* v_res_1666_; 
v_useEq_boxed_1665_ = lean_unbox(v_useEq_1656_);
v_res_1666_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2(v_name_1654_, v_us_1655_, v_useEq_boxed_1665_, v_ctorVal_1657_, v_params_1658_, v_type_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_);
lean_dec(v___y_1663_);
lean_dec_ref(v___y_1662_);
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1660_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(lean_object* v_a_1667_, lean_object* v_a_1668_){
_start:
{
if (lean_obj_tag(v_a_1667_) == 0)
{
lean_object* v___x_1669_; 
v___x_1669_ = l_List_reverse___redArg(v_a_1668_);
return v___x_1669_;
}
else
{
lean_object* v_head_1670_; lean_object* v_tail_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1680_; 
v_head_1670_ = lean_ctor_get(v_a_1667_, 0);
v_tail_1671_ = lean_ctor_get(v_a_1667_, 1);
v_isSharedCheck_1680_ = !lean_is_exclusive(v_a_1667_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1673_ = v_a_1667_;
v_isShared_1674_ = v_isSharedCheck_1680_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_tail_1671_);
lean_inc(v_head_1670_);
lean_dec(v_a_1667_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1680_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1675_; lean_object* v___x_1677_; 
v___x_1675_ = l_Lean_mkLevelParam(v_head_1670_);
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 1, v_a_1668_);
lean_ctor_set(v___x_1673_, 0, v___x_1675_);
v___x_1677_ = v___x_1673_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v___x_1675_);
lean_ctor_set(v_reuseFailAlloc_1679_, 1, v_a_1668_);
v___x_1677_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
v_a_1667_ = v_tail_1671_;
v_a_1668_ = v___x_1677_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(lean_object* v_ctorVal_1681_, uint8_t v_useEq_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_){
_start:
{
lean_object* v_toConstantVal_1688_; lean_object* v_numParams_1689_; lean_object* v_name_1690_; lean_object* v_levelParams_1691_; lean_object* v_type_1692_; lean_object* v___x_1693_; 
v_toConstantVal_1688_ = lean_ctor_get(v_ctorVal_1681_, 0);
v_numParams_1689_ = lean_ctor_get(v_ctorVal_1681_, 3);
lean_inc(v_numParams_1689_);
v_name_1690_ = lean_ctor_get(v_toConstantVal_1688_, 0);
lean_inc(v_name_1690_);
v_levelParams_1691_ = lean_ctor_get(v_toConstantVal_1688_, 1);
v_type_1692_ = lean_ctor_get(v_toConstantVal_1688_, 2);
lean_inc_ref(v_type_1692_);
v___x_1693_ = l_Lean_Meta_elimOptParam(v_type_1692_, v_a_1685_, v_a_1686_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v_a_1694_; lean_object* v___x_1695_; lean_object* v_us_1696_; lean_object* v___x_1697_; lean_object* v___f_1698_; lean_object* v___x_1699_; uint8_t v___x_1700_; lean_object* v___x_1701_; 
v_a_1694_ = lean_ctor_get(v___x_1693_, 0);
lean_inc(v_a_1694_);
lean_dec_ref(v___x_1693_);
v___x_1695_ = lean_box(0);
lean_inc(v_levelParams_1691_);
v_us_1696_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(v_levelParams_1691_, v___x_1695_);
v___x_1697_ = lean_box(v_useEq_1682_);
v___f_1698_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2___boxed), 11, 4);
lean_closure_set(v___f_1698_, 0, v_name_1690_);
lean_closure_set(v___f_1698_, 1, v_us_1696_);
lean_closure_set(v___f_1698_, 2, v___x_1697_);
lean_closure_set(v___f_1698_, 3, v_ctorVal_1681_);
v___x_1699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1699_, 0, v_numParams_1689_);
v___x_1700_ = 0;
v___x_1701_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(v_a_1694_, v___x_1699_, v___f_1698_, v___x_1700_, v___x_1700_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_);
return v___x_1701_;
}
else
{
lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1709_; 
lean_dec(v_name_1690_);
lean_dec(v_numParams_1689_);
lean_dec_ref(v_ctorVal_1681_);
v_a_1702_ = lean_ctor_get(v___x_1693_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1704_ = v___x_1693_;
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v___x_1693_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1707_; 
if (v_isShared_1705_ == 0)
{
v___x_1707_ = v___x_1704_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_a_1702_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___boxed(lean_object* v_ctorVal_1710_, lean_object* v_useEq_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_){
_start:
{
uint8_t v_useEq_boxed_1717_; lean_object* v_res_1718_; 
v_useEq_boxed_1717_ = lean_unbox(v_useEq_1711_);
v_res_1718_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(v_ctorVal_1710_, v_useEq_boxed_1717_, v_a_1712_, v_a_1713_, v_a_1714_, v_a_1715_);
lean_dec(v_a_1715_);
lean_dec_ref(v_a_1714_);
lean_dec(v_a_1713_);
lean_dec_ref(v_a_1712_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2(lean_object* v_00_u03b1_1719_, lean_object* v_bs_1720_, lean_object* v_k_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
lean_object* v___x_1727_; 
v___x_1727_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(v_bs_1720_, v_k_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1728_, lean_object* v_bs_1729_, lean_object* v_k_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_){
_start:
{
lean_object* v_res_1736_; 
v_res_1736_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2(v_00_u03b1_1728_, v_bs_1729_, v_k_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
lean_dec_ref(v_bs_1729_);
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1(lean_object* v_00_u03b1_1737_, lean_object* v_bs_1738_, lean_object* v_k_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
lean_object* v___x_1745_; 
v___x_1745_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v_bs_1738_, v_k_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___boxed(lean_object* v_00_u03b1_1746_, lean_object* v_bs_1747_, lean_object* v_k_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_){
_start:
{
lean_object* v_res_1754_; 
v_res_1754_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1(v_00_u03b1_1746_, v_bs_1747_, v_k_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
lean_dec(v___y_1752_);
lean_dec_ref(v___y_1751_);
lean_dec(v___y_1750_);
lean_dec_ref(v___y_1749_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(lean_object* v_ctorVal_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_){
_start:
{
uint8_t v___x_1761_; lean_object* v___x_1762_; 
v___x_1761_ = 0;
v___x_1762_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(v_ctorVal_1755_, v___x_1761_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f___boxed(lean_object* v_ctorVal_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_){
_start:
{
lean_object* v_res_1769_; 
v_res_1769_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_1763_, v_a_1764_, v_a_1765_, v_a_1766_, v_a_1767_);
lean_dec(v_a_1767_);
lean_dec_ref(v_a_1766_);
lean_dec(v_a_1765_);
lean_dec_ref(v_a_1764_);
return v_res_1769_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1(void){
_start:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1771_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__0));
v___x_1772_ = l_Lean_stringToMessageData(v___x_1771_);
return v___x_1772_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3(void){
_start:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1774_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__2));
v___x_1775_ = l_Lean_stringToMessageData(v___x_1774_);
return v___x_1775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(lean_object* v_ctorName_1776_){
_start:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1777_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1);
v___x_1778_ = l_Lean_MessageData_ofName(v_ctorName_1776_);
v___x_1779_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1777_);
lean_ctor_set(v___x_1779_, 1, v___x_1778_);
v___x_1780_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3);
v___x_1781_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1779_);
lean_ctor_set(v___x_1781_, 1, v___x_1780_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(lean_object* v_ctorName_1782_, lean_object* v_mvarId_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_){
_start:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1789_ = l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(v_ctorName_1782_);
v___x_1790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1790_, 0, v_mvarId_1783_);
v___x_1791_ = l_Lean_indentD(v___x_1790_);
v___x_1792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1792_, 0, v___x_1789_);
lean_ctor_set(v___x_1792_, 1, v___x_1791_);
v___x_1793_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_1792_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg___boxed(lean_object* v_ctorName_1794_, lean_object* v_mvarId_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_){
_start:
{
lean_object* v_res_1801_; 
v_res_1801_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(v_ctorName_1794_, v_mvarId_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_);
lean_dec(v_a_1799_);
lean_dec_ref(v_a_1798_);
lean_dec(v_a_1797_);
lean_dec_ref(v_a_1796_);
return v_res_1801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure(lean_object* v_00_u03b1_1802_, lean_object* v_ctorName_1803_, lean_object* v_mvarId_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_){
_start:
{
lean_object* v___x_1810_; 
v___x_1810_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(v_ctorName_1803_, v_mvarId_1804_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___boxed(lean_object* v_00_u03b1_1811_, lean_object* v_ctorName_1812_, lean_object* v_mvarId_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure(v_00_u03b1_1811_, v_ctorName_1812_, v_mvarId_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_);
lean_dec(v_a_1817_);
lean_dec_ref(v_a_1816_);
lean_dec(v_a_1815_);
lean_dec_ref(v_a_1814_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0(lean_object* v_ctorName_1820_, lean_object* v_as_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_){
_start:
{
if (lean_obj_tag(v_as_1821_) == 0)
{
lean_object* v___x_1827_; lean_object* v___x_1828_; 
lean_dec(v_ctorName_1820_);
v___x_1827_ = lean_box(0);
v___x_1828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1827_);
return v___x_1828_;
}
else
{
lean_object* v_head_1829_; lean_object* v_tail_1830_; lean_object* v___x_1831_; 
v_head_1829_ = lean_ctor_get(v_as_1821_, 0);
lean_inc_n(v_head_1829_, 2);
v_tail_1830_ = lean_ctor_get(v_as_1821_, 1);
lean_inc(v_tail_1830_);
lean_dec_ref(v_as_1821_);
v___x_1831_ = l_Lean_MVarId_assumptionCore(v_head_1829_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_object* v_a_1832_; uint8_t v___x_1833_; 
v_a_1832_ = lean_ctor_get(v___x_1831_, 0);
lean_inc(v_a_1832_);
lean_dec_ref(v___x_1831_);
v___x_1833_ = lean_unbox(v_a_1832_);
lean_dec(v_a_1832_);
if (v___x_1833_ == 0)
{
lean_object* v___x_1834_; 
lean_dec(v_tail_1830_);
v___x_1834_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(v_ctorName_1820_, v_head_1829_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_);
return v___x_1834_;
}
else
{
lean_dec(v_head_1829_);
v_as_1821_ = v_tail_1830_;
goto _start;
}
}
else
{
lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1843_; 
lean_dec(v_tail_1830_);
lean_dec(v_head_1829_);
lean_dec(v_ctorName_1820_);
v_a_1836_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1838_ = v___x_1831_;
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v___x_1831_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1841_; 
if (v_isShared_1839_ == 0)
{
v___x_1841_ = v___x_1838_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_a_1836_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0___boxed(lean_object* v_ctorName_1844_, lean_object* v_as_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_){
_start:
{
lean_object* v_res_1851_; 
v_res_1851_ = l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0(v_ctorName_1844_, v_as_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
return v_res_1851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(lean_object* v_mvarId_1852_, lean_object* v_ctorName_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_){
_start:
{
lean_object* v___x_1859_; 
v___x_1859_ = l_Lean_MVarId_splitAndCore(v_mvarId_1852_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_);
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_object* v_a_1860_; lean_object* v___x_1861_; 
v_a_1860_ = lean_ctor_get(v___x_1859_, 0);
lean_inc(v_a_1860_);
lean_dec_ref(v___x_1859_);
v___x_1861_ = l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0(v_ctorName_1853_, v_a_1860_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_);
return v___x_1861_;
}
else
{
lean_object* v_a_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1869_; 
lean_dec(v_ctorName_1853_);
v_a_1862_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1864_ = v___x_1859_;
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_a_1862_);
lean_dec(v___x_1859_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1867_; 
if (v_isShared_1865_ == 0)
{
v___x_1867_ = v___x_1864_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_a_1862_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption___boxed(lean_object* v_mvarId_1870_, lean_object* v_ctorName_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(v_mvarId_1870_, v_ctorName_1871_, v_a_1872_, v_a_1873_, v_a_1874_, v_a_1875_);
lean_dec(v_a_1875_);
lean_dec_ref(v_a_1874_);
lean_dec(v_a_1873_);
lean_dec_ref(v_a_1872_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0(lean_object* v_msg_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_){
_start:
{
lean_object* v___f_1885_; lean_object* v___x_1014__overap_1886_; lean_object* v___x_1887_; 
v___f_1885_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0___closed__0));
v___x_1014__overap_1886_ = lean_panic_fn_borrowed(v___f_1885_, v_msg_1879_);
lean_inc(v___y_1883_);
lean_inc_ref(v___y_1882_);
lean_inc(v___y_1881_);
lean_inc_ref(v___y_1880_);
v___x_1887_ = lean_apply_5(v___x_1014__overap_1886_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, lean_box(0));
return v___x_1887_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0___boxed(lean_object* v_msg_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
lean_object* v_res_1894_; 
v_res_1894_ = l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0(v_msg_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec(v___y_1890_);
lean_dec_ref(v___y_1889_);
return v_res_1894_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1895_; double v___x_1896_; 
v___x_1895_ = lean_unsigned_to_nat(0u);
v___x_1896_ = lean_float_of_nat(v___x_1895_);
return v___x_1896_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(lean_object* v_cls_1900_, lean_object* v_msg_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_){
_start:
{
lean_object* v_ref_1907_; lean_object* v___x_1908_; lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1953_; 
v_ref_1907_ = lean_ctor_get(v___y_1904_, 5);
v___x_1908_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msg_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
v_a_1909_ = lean_ctor_get(v___x_1908_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1911_ = v___x_1908_;
v_isShared_1912_ = v_isSharedCheck_1953_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1908_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1953_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1913_; lean_object* v_traceState_1914_; lean_object* v_env_1915_; lean_object* v_nextMacroScope_1916_; lean_object* v_ngen_1917_; lean_object* v_auxDeclNGen_1918_; lean_object* v_cache_1919_; lean_object* v_messages_1920_; lean_object* v_infoState_1921_; lean_object* v_snapshotTasks_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1952_; 
v___x_1913_ = lean_st_ref_take(v___y_1905_);
v_traceState_1914_ = lean_ctor_get(v___x_1913_, 4);
v_env_1915_ = lean_ctor_get(v___x_1913_, 0);
v_nextMacroScope_1916_ = lean_ctor_get(v___x_1913_, 1);
v_ngen_1917_ = lean_ctor_get(v___x_1913_, 2);
v_auxDeclNGen_1918_ = lean_ctor_get(v___x_1913_, 3);
v_cache_1919_ = lean_ctor_get(v___x_1913_, 5);
v_messages_1920_ = lean_ctor_get(v___x_1913_, 6);
v_infoState_1921_ = lean_ctor_get(v___x_1913_, 7);
v_snapshotTasks_1922_ = lean_ctor_get(v___x_1913_, 8);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1924_ = v___x_1913_;
v_isShared_1925_ = v_isSharedCheck_1952_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_snapshotTasks_1922_);
lean_inc(v_infoState_1921_);
lean_inc(v_messages_1920_);
lean_inc(v_cache_1919_);
lean_inc(v_traceState_1914_);
lean_inc(v_auxDeclNGen_1918_);
lean_inc(v_ngen_1917_);
lean_inc(v_nextMacroScope_1916_);
lean_inc(v_env_1915_);
lean_dec(v___x_1913_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1952_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
uint64_t v_tid_1926_; lean_object* v_traces_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1951_; 
v_tid_1926_ = lean_ctor_get_uint64(v_traceState_1914_, sizeof(void*)*1);
v_traces_1927_ = lean_ctor_get(v_traceState_1914_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v_traceState_1914_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1929_ = v_traceState_1914_;
v_isShared_1930_ = v_isSharedCheck_1951_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_traces_1927_);
lean_dec(v_traceState_1914_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1951_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1931_; double v___x_1932_; uint8_t v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1941_; 
v___x_1931_ = lean_box(0);
v___x_1932_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0);
v___x_1933_ = 0;
v___x_1934_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_1935_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1935_, 0, v_cls_1900_);
lean_ctor_set(v___x_1935_, 1, v___x_1931_);
lean_ctor_set(v___x_1935_, 2, v___x_1934_);
lean_ctor_set_float(v___x_1935_, sizeof(void*)*3, v___x_1932_);
lean_ctor_set_float(v___x_1935_, sizeof(void*)*3 + 8, v___x_1932_);
lean_ctor_set_uint8(v___x_1935_, sizeof(void*)*3 + 16, v___x_1933_);
v___x_1936_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__2));
v___x_1937_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1935_);
lean_ctor_set(v___x_1937_, 1, v_a_1909_);
lean_ctor_set(v___x_1937_, 2, v___x_1936_);
lean_inc(v_ref_1907_);
v___x_1938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1938_, 0, v_ref_1907_);
lean_ctor_set(v___x_1938_, 1, v___x_1937_);
v___x_1939_ = l_Lean_PersistentArray_push___redArg(v_traces_1927_, v___x_1938_);
if (v_isShared_1930_ == 0)
{
lean_ctor_set(v___x_1929_, 0, v___x_1939_);
v___x_1941_ = v___x_1929_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v___x_1939_);
lean_ctor_set_uint64(v_reuseFailAlloc_1950_, sizeof(void*)*1, v_tid_1926_);
v___x_1941_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
lean_object* v___x_1943_; 
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 4, v___x_1941_);
v___x_1943_ = v___x_1924_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_env_1915_);
lean_ctor_set(v_reuseFailAlloc_1949_, 1, v_nextMacroScope_1916_);
lean_ctor_set(v_reuseFailAlloc_1949_, 2, v_ngen_1917_);
lean_ctor_set(v_reuseFailAlloc_1949_, 3, v_auxDeclNGen_1918_);
lean_ctor_set(v_reuseFailAlloc_1949_, 4, v___x_1941_);
lean_ctor_set(v_reuseFailAlloc_1949_, 5, v_cache_1919_);
lean_ctor_set(v_reuseFailAlloc_1949_, 6, v_messages_1920_);
lean_ctor_set(v_reuseFailAlloc_1949_, 7, v_infoState_1921_);
lean_ctor_set(v_reuseFailAlloc_1949_, 8, v_snapshotTasks_1922_);
v___x_1943_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1947_; 
v___x_1944_ = lean_st_ref_set(v___y_1905_, v___x_1943_);
v___x_1945_ = lean_box(0);
if (v_isShared_1912_ == 0)
{
lean_ctor_set(v___x_1911_, 0, v___x_1945_);
v___x_1947_ = v___x_1911_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v___x_1945_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___boxed(lean_object* v_cls_1954_, lean_object* v_msg_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_1954_, v_msg_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
return v_res_1961_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3(void){
_start:
{
lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; 
v___x_1965_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__2));
v___x_1966_ = lean_unsigned_to_nat(30u);
v___x_1967_ = lean_unsigned_to_nat(96u);
v___x_1968_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__1));
v___x_1969_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__0));
v___x_1970_ = l_mkPanicMessageWithDecl(v___x_1969_, v___x_1968_, v___x_1967_, v___x_1966_, v___x_1965_);
return v___x_1970_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9(void){
_start:
{
lean_object* v_cls_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; 
v_cls_1979_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_1980_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__8));
v___x_1981_ = l_Lean_Name_append(v___x_1980_, v_cls_1979_);
return v___x_1981_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11(void){
_start:
{
lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___x_1983_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__10));
v___x_1984_ = l_Lean_stringToMessageData(v___x_1983_);
return v___x_1984_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13(void){
_start:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1986_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__12));
v___x_1987_ = l_Lean_stringToMessageData(v___x_1986_);
return v___x_1987_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15(void){
_start:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1989_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__14));
v___x_1990_ = l_Lean_stringToMessageData(v___x_1989_);
return v___x_1990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(lean_object* v_ctorName_1991_, lean_object* v_mvarId_1992_, lean_object* v_h_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_){
_start:
{
lean_object* v___y_2000_; lean_object* v___y_2001_; lean_object* v___y_2002_; lean_object* v___y_2003_; lean_object* v_options_2019_; uint8_t v_hasTrace_2020_; 
v_options_2019_ = lean_ctor_get(v_a_1996_, 2);
v_hasTrace_2020_ = lean_ctor_get_uint8(v_options_2019_, sizeof(void*)*1);
if (v_hasTrace_2020_ == 0)
{
v___y_2000_ = v_a_1994_;
v___y_2001_ = v_a_1995_;
v___y_2002_ = v_a_1996_;
v___y_2003_ = v_a_1997_;
goto v___jp_1999_;
}
else
{
lean_object* v_inheritedTraceOptions_2021_; lean_object* v_cls_2022_; lean_object* v___x_2023_; uint8_t v___x_2024_; 
v_inheritedTraceOptions_2021_ = lean_ctor_get(v_a_1996_, 13);
v_cls_2022_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_2023_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_2024_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2021_, v_options_2019_, v___x_2023_);
if (v___x_2024_ == 0)
{
v___y_2000_ = v_a_1994_;
v___y_2001_ = v_a_1995_;
v___y_2002_ = v_a_1996_;
v___y_2003_ = v_a_1997_;
goto v___jp_1999_;
}
else
{
lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2025_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11);
lean_inc(v_ctorName_1991_);
v___x_2026_ = l_Lean_MessageData_ofName(v_ctorName_1991_);
v___x_2027_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2027_, 0, v___x_2025_);
lean_ctor_set(v___x_2027_, 1, v___x_2026_);
v___x_2028_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13);
v___x_2029_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2029_, 0, v___x_2027_);
lean_ctor_set(v___x_2029_, 1, v___x_2028_);
lean_inc(v_h_1993_);
v___x_2030_ = l_Lean_mkFVar(v_h_1993_);
v___x_2031_ = l_Lean_MessageData_ofExpr(v___x_2030_);
v___x_2032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2032_, 0, v___x_2029_);
lean_ctor_set(v___x_2032_, 1, v___x_2031_);
v___x_2033_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15);
v___x_2034_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2032_);
lean_ctor_set(v___x_2034_, 1, v___x_2033_);
lean_inc(v_mvarId_1992_);
v___x_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2035_, 0, v_mvarId_1992_);
v___x_2036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2036_, 0, v___x_2034_);
lean_ctor_set(v___x_2036_, 1, v___x_2035_);
v___x_2037_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2022_, v___x_2036_, v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_);
if (lean_obj_tag(v___x_2037_) == 0)
{
lean_dec_ref(v___x_2037_);
v___y_2000_ = v_a_1994_;
v___y_2001_ = v_a_1995_;
v___y_2002_ = v_a_1996_;
v___y_2003_ = v_a_1997_;
goto v___jp_1999_;
}
else
{
lean_dec(v_h_1993_);
lean_dec(v_mvarId_1992_);
lean_dec(v_ctorName_1991_);
return v___x_2037_;
}
}
}
v___jp_1999_:
{
lean_object* v___x_2004_; lean_object* v___x_2005_; 
v___x_2004_ = lean_box(0);
v___x_2005_ = l_Lean_Meta_injection(v_mvarId_1992_, v_h_1993_, v___x_2004_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_);
if (lean_obj_tag(v___x_2005_) == 0)
{
lean_object* v_a_2006_; 
v_a_2006_ = lean_ctor_get(v___x_2005_, 0);
lean_inc(v_a_2006_);
lean_dec_ref(v___x_2005_);
if (lean_obj_tag(v_a_2006_) == 0)
{
lean_object* v___x_2007_; lean_object* v___x_2008_; 
lean_dec(v_ctorName_1991_);
v___x_2007_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3);
v___x_2008_ = l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0(v___x_2007_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_);
return v___x_2008_;
}
else
{
lean_object* v_mvarId_2009_; lean_object* v___x_2010_; 
v_mvarId_2009_ = lean_ctor_get(v_a_2006_, 0);
lean_inc(v_mvarId_2009_);
lean_dec_ref(v_a_2006_);
v___x_2010_ = l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(v_mvarId_2009_, v_ctorName_1991_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_);
return v___x_2010_;
}
}
else
{
lean_object* v_a_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2018_; 
lean_dec(v_ctorName_1991_);
v_a_2011_ = lean_ctor_get(v___x_2005_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_2005_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2013_ = v___x_2005_;
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_a_2011_);
lean_dec(v___x_2005_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2016_; 
if (v_isShared_2014_ == 0)
{
v___x_2016_ = v___x_2013_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_a_2011_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___boxed(lean_object* v_ctorName_2038_, lean_object* v_mvarId_2039_, lean_object* v_h_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_){
_start:
{
lean_object* v_res_2046_; 
v_res_2046_ = l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(v_ctorName_2038_, v_mvarId_2039_, v_h_2040_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_);
lean_dec(v_a_2044_);
lean_dec_ref(v_a_2043_);
lean_dec(v_a_2042_);
lean_dec_ref(v_a_2041_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(lean_object* v_type_2047_, lean_object* v_k_2048_, uint8_t v_cleanupAnnotations_2049_, uint8_t v_whnfType_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
lean_object* v___f_2056_; lean_object* v___x_2057_; 
v___f_2056_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2056_, 0, v_k_2048_);
v___x_2057_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_2047_, v___f_2056_, v_cleanupAnnotations_2049_, v_whnfType_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2065_; 
v_a_2058_ = lean_ctor_get(v___x_2057_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2060_ = v___x_2057_;
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_2057_);
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
v_reuseFailAlloc_2064_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
v_a_2066_ = lean_ctor_get(v___x_2057_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_2057_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_2057_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2069_ == 0)
{
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2066_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg___boxed(lean_object* v_type_2074_, lean_object* v_k_2075_, lean_object* v_cleanupAnnotations_2076_, lean_object* v_whnfType_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2083_; uint8_t v_whnfType_boxed_2084_; lean_object* v_res_2085_; 
v_cleanupAnnotations_boxed_2083_ = lean_unbox(v_cleanupAnnotations_2076_);
v_whnfType_boxed_2084_ = lean_unbox(v_whnfType_2077_);
v_res_2085_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_type_2074_, v_k_2075_, v_cleanupAnnotations_boxed_2083_, v_whnfType_boxed_2084_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_);
lean_dec(v___y_2081_);
lean_dec_ref(v___y_2080_);
lean_dec(v___y_2079_);
lean_dec_ref(v___y_2078_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0(lean_object* v_00_u03b1_2086_, lean_object* v_type_2087_, lean_object* v_k_2088_, uint8_t v_cleanupAnnotations_2089_, uint8_t v_whnfType_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_){
_start:
{
lean_object* v___x_2096_; 
v___x_2096_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_type_2087_, v_k_2088_, v_cleanupAnnotations_2089_, v_whnfType_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
return v___x_2096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___boxed(lean_object* v_00_u03b1_2097_, lean_object* v_type_2098_, lean_object* v_k_2099_, lean_object* v_cleanupAnnotations_2100_, lean_object* v_whnfType_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2107_; uint8_t v_whnfType_boxed_2108_; lean_object* v_res_2109_; 
v_cleanupAnnotations_boxed_2107_ = lean_unbox(v_cleanupAnnotations_2100_);
v_whnfType_boxed_2108_ = lean_unbox(v_whnfType_2101_);
v_res_2109_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0(v_00_u03b1_2097_, v_type_2098_, v_k_2099_, v_cleanupAnnotations_boxed_2107_, v_whnfType_boxed_2108_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_);
lean_dec(v___y_2105_);
lean_dec_ref(v___y_2104_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0(lean_object* v___x_2110_, lean_object* v_ctorName_2111_, lean_object* v_xs_2112_, lean_object* v_type_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_){
_start:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2119_ = lean_box(0);
v___x_2120_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_2113_, v___x_2119_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v_a_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
lean_inc(v_a_2121_);
lean_dec_ref(v___x_2120_);
v___x_2122_ = l_Lean_Expr_mvarId_x21(v_a_2121_);
v___x_2123_ = lean_array_get_size(v_xs_2112_);
v___x_2124_ = lean_unsigned_to_nat(1u);
v___x_2125_ = lean_nat_sub(v___x_2123_, v___x_2124_);
v___x_2126_ = lean_array_get_borrowed(v___x_2110_, v_xs_2112_, v___x_2125_);
lean_dec(v___x_2125_);
v___x_2127_ = l_Lean_Expr_fvarId_x21(v___x_2126_);
v___x_2128_ = l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(v_ctorName_2111_, v___x_2122_, v___x_2127_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_);
if (lean_obj_tag(v___x_2128_) == 0)
{
uint8_t v___x_2129_; uint8_t v___x_2130_; uint8_t v___x_2131_; lean_object* v___x_2132_; 
lean_dec_ref(v___x_2128_);
v___x_2129_ = 0;
v___x_2130_ = 1;
v___x_2131_ = 1;
v___x_2132_ = l_Lean_Meta_mkLambdaFVars(v_xs_2112_, v_a_2121_, v___x_2129_, v___x_2130_, v___x_2129_, v___x_2130_, v___x_2131_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_);
return v___x_2132_;
}
else
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2140_; 
lean_dec(v_a_2121_);
v_a_2133_ = lean_ctor_get(v___x_2128_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2135_ = v___x_2128_;
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2128_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2138_; 
if (v_isShared_2136_ == 0)
{
v___x_2138_ = v___x_2135_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_a_2133_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
}
else
{
lean_dec(v_ctorName_2111_);
return v___x_2120_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0___boxed(lean_object* v___x_2141_, lean_object* v_ctorName_2142_, lean_object* v_xs_2143_, lean_object* v_type_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_){
_start:
{
lean_object* v_res_2150_; 
v_res_2150_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0(v___x_2141_, v_ctorName_2142_, v_xs_2143_, v_type_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
lean_dec(v___y_2146_);
lean_dec_ref(v___y_2145_);
lean_dec_ref(v_xs_2143_);
lean_dec_ref(v___x_2141_);
return v_res_2150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(lean_object* v_ctorName_2151_, lean_object* v_targetType_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_){
_start:
{
lean_object* v___x_2158_; lean_object* v___f_2159_; uint8_t v___x_2160_; lean_object* v___x_2161_; 
v___x_2158_ = l_Lean_instInhabitedExpr;
v___f_2159_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2159_, 0, v___x_2158_);
lean_closure_set(v___f_2159_, 1, v_ctorName_2151_);
v___x_2160_ = 0;
v___x_2161_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_targetType_2152_, v___f_2159_, v___x_2160_, v___x_2160_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_);
return v___x_2161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___boxed(lean_object* v_ctorName_2162_, lean_object* v_targetType_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_){
_start:
{
lean_object* v_res_2169_; 
v_res_2169_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_ctorName_2162_, v_targetType_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_);
lean_dec(v_a_2167_);
lean_dec_ref(v_a_2166_);
lean_dec(v_a_2165_);
lean_dec_ref(v_a_2164_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheoremNameFor(lean_object* v_ctorName_2173_){
_start:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2174_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheoremNameFor___closed__1));
v___x_2175_ = l_Lean_Name_append(v_ctorName_2173_, v___x_2174_);
return v___x_2175_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(lean_object* v_e_2176_, lean_object* v___y_2177_){
_start:
{
uint8_t v___x_2179_; 
v___x_2179_ = l_Lean_Expr_hasMVar(v_e_2176_);
if (v___x_2179_ == 0)
{
lean_object* v___x_2180_; 
v___x_2180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2180_, 0, v_e_2176_);
return v___x_2180_;
}
else
{
lean_object* v___x_2181_; lean_object* v_mctx_2182_; lean_object* v___x_2183_; lean_object* v_fst_2184_; lean_object* v_snd_2185_; lean_object* v___x_2186_; lean_object* v_cache_2187_; lean_object* v_zetaDeltaFVarIds_2188_; lean_object* v_postponed_2189_; lean_object* v_diag_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2199_; 
v___x_2181_ = lean_st_ref_get(v___y_2177_);
v_mctx_2182_ = lean_ctor_get(v___x_2181_, 0);
lean_inc_ref(v_mctx_2182_);
lean_dec(v___x_2181_);
v___x_2183_ = l_Lean_instantiateMVarsCore(v_mctx_2182_, v_e_2176_);
v_fst_2184_ = lean_ctor_get(v___x_2183_, 0);
lean_inc(v_fst_2184_);
v_snd_2185_ = lean_ctor_get(v___x_2183_, 1);
lean_inc(v_snd_2185_);
lean_dec_ref(v___x_2183_);
v___x_2186_ = lean_st_ref_take(v___y_2177_);
v_cache_2187_ = lean_ctor_get(v___x_2186_, 1);
v_zetaDeltaFVarIds_2188_ = lean_ctor_get(v___x_2186_, 2);
v_postponed_2189_ = lean_ctor_get(v___x_2186_, 3);
v_diag_2190_ = lean_ctor_get(v___x_2186_, 4);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2199_ == 0)
{
lean_object* v_unused_2200_; 
v_unused_2200_ = lean_ctor_get(v___x_2186_, 0);
lean_dec(v_unused_2200_);
v___x_2192_ = v___x_2186_;
v_isShared_2193_ = v_isSharedCheck_2199_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_diag_2190_);
lean_inc(v_postponed_2189_);
lean_inc(v_zetaDeltaFVarIds_2188_);
lean_inc(v_cache_2187_);
lean_dec(v___x_2186_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2199_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2195_; 
if (v_isShared_2193_ == 0)
{
lean_ctor_set(v___x_2192_, 0, v_snd_2185_);
v___x_2195_ = v___x_2192_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_snd_2185_);
lean_ctor_set(v_reuseFailAlloc_2198_, 1, v_cache_2187_);
lean_ctor_set(v_reuseFailAlloc_2198_, 2, v_zetaDeltaFVarIds_2188_);
lean_ctor_set(v_reuseFailAlloc_2198_, 3, v_postponed_2189_);
lean_ctor_set(v_reuseFailAlloc_2198_, 4, v_diag_2190_);
v___x_2195_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2196_ = lean_st_ref_set(v___y_2177_, v___x_2195_);
v___x_2197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2197_, 0, v_fst_2184_);
return v___x_2197_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg___boxed(lean_object* v_e_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
lean_object* v_res_2204_; 
v_res_2204_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_e_2201_, v___y_2202_);
lean_dec(v___y_2202_);
return v_res_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0(lean_object* v_e_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_){
_start:
{
lean_object* v___x_2211_; 
v___x_2211_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_e_2205_, v___y_2207_);
return v___x_2211_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___boxed(lean_object* v_e_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
lean_object* v_res_2218_; 
v_res_2218_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0(v_e_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_);
lean_dec(v___y_2216_);
lean_dec_ref(v___y_2215_);
lean_dec(v___y_2214_);
lean_dec_ref(v___y_2213_);
return v_res_2218_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2219_ = lean_unsigned_to_nat(32u);
v___x_2220_ = lean_mk_empty_array_with_capacity(v___x_2219_);
v___x_2221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2220_);
return v___x_2221_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2222_ = ((size_t)5ULL);
v___x_2223_ = lean_unsigned_to_nat(0u);
v___x_2224_ = lean_unsigned_to_nat(32u);
v___x_2225_ = lean_mk_empty_array_with_capacity(v___x_2224_);
v___x_2226_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0);
v___x_2227_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2227_, 0, v___x_2226_);
lean_ctor_set(v___x_2227_, 1, v___x_2225_);
lean_ctor_set(v___x_2227_, 2, v___x_2223_);
lean_ctor_set(v___x_2227_, 3, v___x_2223_);
lean_ctor_set_usize(v___x_2227_, 4, v___x_2222_);
return v___x_2227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(lean_object* v___y_2228_){
_start:
{
lean_object* v___x_2230_; lean_object* v_traceState_2231_; lean_object* v_traces_2232_; lean_object* v___x_2233_; lean_object* v_traceState_2234_; lean_object* v_env_2235_; lean_object* v_nextMacroScope_2236_; lean_object* v_ngen_2237_; lean_object* v_auxDeclNGen_2238_; lean_object* v_cache_2239_; lean_object* v_messages_2240_; lean_object* v_infoState_2241_; lean_object* v_snapshotTasks_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2261_; 
v___x_2230_ = lean_st_ref_get(v___y_2228_);
v_traceState_2231_ = lean_ctor_get(v___x_2230_, 4);
lean_inc_ref(v_traceState_2231_);
lean_dec(v___x_2230_);
v_traces_2232_ = lean_ctor_get(v_traceState_2231_, 0);
lean_inc_ref(v_traces_2232_);
lean_dec_ref(v_traceState_2231_);
v___x_2233_ = lean_st_ref_take(v___y_2228_);
v_traceState_2234_ = lean_ctor_get(v___x_2233_, 4);
v_env_2235_ = lean_ctor_get(v___x_2233_, 0);
v_nextMacroScope_2236_ = lean_ctor_get(v___x_2233_, 1);
v_ngen_2237_ = lean_ctor_get(v___x_2233_, 2);
v_auxDeclNGen_2238_ = lean_ctor_get(v___x_2233_, 3);
v_cache_2239_ = lean_ctor_get(v___x_2233_, 5);
v_messages_2240_ = lean_ctor_get(v___x_2233_, 6);
v_infoState_2241_ = lean_ctor_get(v___x_2233_, 7);
v_snapshotTasks_2242_ = lean_ctor_get(v___x_2233_, 8);
v_isSharedCheck_2261_ = !lean_is_exclusive(v___x_2233_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2244_ = v___x_2233_;
v_isShared_2245_ = v_isSharedCheck_2261_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_snapshotTasks_2242_);
lean_inc(v_infoState_2241_);
lean_inc(v_messages_2240_);
lean_inc(v_cache_2239_);
lean_inc(v_traceState_2234_);
lean_inc(v_auxDeclNGen_2238_);
lean_inc(v_ngen_2237_);
lean_inc(v_nextMacroScope_2236_);
lean_inc(v_env_2235_);
lean_dec(v___x_2233_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2261_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
uint64_t v_tid_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2259_; 
v_tid_2246_ = lean_ctor_get_uint64(v_traceState_2234_, sizeof(void*)*1);
v_isSharedCheck_2259_ = !lean_is_exclusive(v_traceState_2234_);
if (v_isSharedCheck_2259_ == 0)
{
lean_object* v_unused_2260_; 
v_unused_2260_ = lean_ctor_get(v_traceState_2234_, 0);
lean_dec(v_unused_2260_);
v___x_2248_ = v_traceState_2234_;
v_isShared_2249_ = v_isSharedCheck_2259_;
goto v_resetjp_2247_;
}
else
{
lean_dec(v_traceState_2234_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2259_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2250_; lean_object* v___x_2252_; 
v___x_2250_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1);
if (v_isShared_2249_ == 0)
{
lean_ctor_set(v___x_2248_, 0, v___x_2250_);
v___x_2252_ = v___x_2248_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v___x_2250_);
lean_ctor_set_uint64(v_reuseFailAlloc_2258_, sizeof(void*)*1, v_tid_2246_);
v___x_2252_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
lean_object* v___x_2254_; 
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 4, v___x_2252_);
v___x_2254_ = v___x_2244_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_env_2235_);
lean_ctor_set(v_reuseFailAlloc_2257_, 1, v_nextMacroScope_2236_);
lean_ctor_set(v_reuseFailAlloc_2257_, 2, v_ngen_2237_);
lean_ctor_set(v_reuseFailAlloc_2257_, 3, v_auxDeclNGen_2238_);
lean_ctor_set(v_reuseFailAlloc_2257_, 4, v___x_2252_);
lean_ctor_set(v_reuseFailAlloc_2257_, 5, v_cache_2239_);
lean_ctor_set(v_reuseFailAlloc_2257_, 6, v_messages_2240_);
lean_ctor_set(v_reuseFailAlloc_2257_, 7, v_infoState_2241_);
lean_ctor_set(v_reuseFailAlloc_2257_, 8, v_snapshotTasks_2242_);
v___x_2254_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2255_ = lean_st_ref_set(v___y_2228_, v___x_2254_);
v___x_2256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2256_, 0, v_traces_2232_);
return v___x_2256_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___boxed(lean_object* v___y_2262_, lean_object* v___y_2263_){
_start:
{
lean_object* v_res_2264_; 
v_res_2264_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v___y_2262_);
lean_dec(v___y_2262_);
return v_res_2264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1(lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
lean_object* v___x_2270_; 
v___x_2270_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v___y_2268_);
return v___x_2270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___boxed(lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_){
_start:
{
lean_object* v_res_2276_; 
v_res_2276_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1(v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
return v_res_2276_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(lean_object* v_opts_2277_, lean_object* v_opt_2278_){
_start:
{
lean_object* v_name_2279_; lean_object* v_defValue_2280_; lean_object* v_map_2281_; lean_object* v___x_2282_; 
v_name_2279_ = lean_ctor_get(v_opt_2278_, 0);
v_defValue_2280_ = lean_ctor_get(v_opt_2278_, 1);
v_map_2281_ = lean_ctor_get(v_opts_2277_, 0);
v___x_2282_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2281_, v_name_2279_);
if (lean_obj_tag(v___x_2282_) == 0)
{
uint8_t v___x_2283_; 
v___x_2283_ = lean_unbox(v_defValue_2280_);
return v___x_2283_;
}
else
{
lean_object* v_val_2284_; 
v_val_2284_ = lean_ctor_get(v___x_2282_, 0);
lean_inc(v_val_2284_);
lean_dec_ref(v___x_2282_);
if (lean_obj_tag(v_val_2284_) == 1)
{
uint8_t v_v_2285_; 
v_v_2285_ = lean_ctor_get_uint8(v_val_2284_, 0);
lean_dec_ref(v_val_2284_);
return v_v_2285_;
}
else
{
uint8_t v___x_2286_; 
lean_dec(v_val_2284_);
v___x_2286_ = lean_unbox(v_defValue_2280_);
return v___x_2286_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2___boxed(lean_object* v_opts_2287_, lean_object* v_opt_2288_){
_start:
{
uint8_t v_res_2289_; lean_object* v_r_2290_; 
v_res_2289_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_opts_2287_, v_opt_2288_);
lean_dec_ref(v_opt_2288_);
lean_dec_ref(v_opts_2287_);
v_r_2290_ = lean_box(v_res_2289_);
return v_r_2290_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___x_2292_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__0));
v___x_2293_ = l_Lean_stringToMessageData(v___x_2292_);
return v___x_2293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0(lean_object* v_name_2294_, lean_object* v_x_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_){
_start:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___x_2301_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1);
v___x_2302_ = l_Lean_MessageData_ofName(v_name_2294_);
v___x_2303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2301_);
lean_ctor_set(v___x_2303_, 1, v___x_2302_);
v___x_2304_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_2305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2305_, 0, v___x_2303_);
lean_ctor_set(v___x_2305_, 1, v___x_2304_);
v___x_2306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2305_);
return v___x_2306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed(lean_object* v_name_2307_, lean_object* v_x_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_){
_start:
{
lean_object* v_res_2314_; 
v_res_2314_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0(v_name_2307_, v_x_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
lean_dec_ref(v_x_2308_);
return v_res_2314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(lean_object* v_name_2315_, lean_object* v_val_2316_, lean_object* v_name_2317_, lean_object* v_levelParams_2318_, uint8_t v___x_2319_, lean_object* v_____r_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_){
_start:
{
lean_object* v___x_2326_; 
lean_inc_ref(v_val_2316_);
v___x_2326_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2315_, v_val_2316_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_);
if (lean_obj_tag(v___x_2326_) == 0)
{
lean_object* v_a_2327_; lean_object* v___x_2328_; lean_object* v_a_2329_; lean_object* v___x_2330_; lean_object* v_a_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2343_; 
v_a_2327_ = lean_ctor_get(v___x_2326_, 0);
lean_inc(v_a_2327_);
lean_dec_ref(v___x_2326_);
v___x_2328_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2316_, v___y_2322_);
v_a_2329_ = lean_ctor_get(v___x_2328_, 0);
lean_inc(v_a_2329_);
lean_dec_ref(v___x_2328_);
v___x_2330_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2327_, v___y_2322_);
v_a_2331_ = lean_ctor_get(v___x_2330_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2333_ = v___x_2330_;
v_isShared_2334_ = v_isSharedCheck_2343_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_a_2331_);
lean_dec(v___x_2330_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2343_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2340_; 
lean_inc(v_name_2317_);
v___x_2335_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2335_, 0, v_name_2317_);
lean_ctor_set(v___x_2335_, 1, v_levelParams_2318_);
lean_ctor_set(v___x_2335_, 2, v_a_2329_);
v___x_2336_ = lean_box(0);
v___x_2337_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2337_, 0, v_name_2317_);
lean_ctor_set(v___x_2337_, 1, v___x_2336_);
v___x_2338_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2338_, 0, v___x_2335_);
lean_ctor_set(v___x_2338_, 1, v_a_2331_);
lean_ctor_set(v___x_2338_, 2, v___x_2337_);
if (v_isShared_2334_ == 0)
{
lean_ctor_set_tag(v___x_2333_, 2);
lean_ctor_set(v___x_2333_, 0, v___x_2338_);
v___x_2340_ = v___x_2333_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v___x_2338_);
v___x_2340_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
lean_object* v___x_2341_; 
v___x_2341_ = l_Lean_addDecl(v___x_2340_, v___x_2319_, v___y_2323_, v___y_2324_);
return v___x_2341_;
}
}
}
else
{
lean_object* v_a_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2351_; 
lean_dec(v_levelParams_2318_);
lean_dec(v_name_2317_);
lean_dec_ref(v_val_2316_);
v_a_2344_ = lean_ctor_get(v___x_2326_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2326_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2346_ = v___x_2326_;
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_a_2344_);
lean_dec(v___x_2326_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___x_2349_; 
if (v_isShared_2347_ == 0)
{
v___x_2349_ = v___x_2346_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_a_2344_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1___boxed(lean_object* v_name_2352_, lean_object* v_val_2353_, lean_object* v_name_2354_, lean_object* v_levelParams_2355_, lean_object* v___x_2356_, lean_object* v_____r_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_){
_start:
{
uint8_t v___x_12938__boxed_2363_; lean_object* v_res_2364_; 
v___x_12938__boxed_2363_ = lean_unbox(v___x_2356_);
v_res_2364_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(v_name_2352_, v_val_2353_, v_name_2354_, v_levelParams_2355_, v___x_12938__boxed_2363_, v_____r_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_);
lean_dec(v___y_2361_);
lean_dec_ref(v___y_2360_);
lean_dec(v___y_2359_);
lean_dec_ref(v___y_2358_);
return v_res_2364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(lean_object* v_name_2365_, lean_object* v_val_2366_, lean_object* v_name_2367_, lean_object* v_levelParams_2368_, lean_object* v_____r_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_){
_start:
{
lean_object* v___x_2375_; 
lean_inc_ref(v_val_2366_);
v___x_2375_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2365_, v_val_2366_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_);
if (lean_obj_tag(v___x_2375_) == 0)
{
lean_object* v_a_2376_; lean_object* v___x_2377_; lean_object* v_a_2378_; lean_object* v___x_2379_; lean_object* v_a_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2393_; 
v_a_2376_ = lean_ctor_get(v___x_2375_, 0);
lean_inc(v_a_2376_);
lean_dec_ref(v___x_2375_);
v___x_2377_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2366_, v___y_2371_);
v_a_2378_ = lean_ctor_get(v___x_2377_, 0);
lean_inc(v_a_2378_);
lean_dec_ref(v___x_2377_);
v___x_2379_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2376_, v___y_2371_);
v_a_2380_ = lean_ctor_get(v___x_2379_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2382_ = v___x_2379_;
v_isShared_2383_ = v_isSharedCheck_2393_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_a_2380_);
lean_dec(v___x_2379_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2393_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2389_; 
lean_inc(v_name_2367_);
v___x_2384_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2384_, 0, v_name_2367_);
lean_ctor_set(v___x_2384_, 1, v_levelParams_2368_);
lean_ctor_set(v___x_2384_, 2, v_a_2378_);
v___x_2385_ = lean_box(0);
v___x_2386_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2386_, 0, v_name_2367_);
lean_ctor_set(v___x_2386_, 1, v___x_2385_);
v___x_2387_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2384_);
lean_ctor_set(v___x_2387_, 1, v_a_2380_);
lean_ctor_set(v___x_2387_, 2, v___x_2386_);
if (v_isShared_2383_ == 0)
{
lean_ctor_set_tag(v___x_2382_, 2);
lean_ctor_set(v___x_2382_, 0, v___x_2387_);
v___x_2389_ = v___x_2382_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v___x_2387_);
v___x_2389_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
uint8_t v___x_2390_; lean_object* v___x_2391_; 
v___x_2390_ = 0;
v___x_2391_ = l_Lean_addDecl(v___x_2389_, v___x_2390_, v___y_2372_, v___y_2373_);
return v___x_2391_;
}
}
}
else
{
lean_object* v_a_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2401_; 
lean_dec(v_levelParams_2368_);
lean_dec(v_name_2367_);
lean_dec_ref(v_val_2366_);
v_a_2394_ = lean_ctor_get(v___x_2375_, 0);
v_isSharedCheck_2401_ = !lean_is_exclusive(v___x_2375_);
if (v_isSharedCheck_2401_ == 0)
{
v___x_2396_ = v___x_2375_;
v_isShared_2397_ = v_isSharedCheck_2401_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_a_2394_);
lean_dec(v___x_2375_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2401_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v___x_2399_; 
if (v_isShared_2397_ == 0)
{
v___x_2399_ = v___x_2396_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_a_2394_);
v___x_2399_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
return v___x_2399_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2___boxed(lean_object* v_name_2402_, lean_object* v_val_2403_, lean_object* v_name_2404_, lean_object* v_levelParams_2405_, lean_object* v_____r_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_){
_start:
{
lean_object* v_res_2412_; 
v_res_2412_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(v_name_2402_, v_val_2403_, v_name_2404_, v_levelParams_2405_, v_____r_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
return v_res_2412_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(lean_object* v_e_2413_){
_start:
{
if (lean_obj_tag(v_e_2413_) == 0)
{
uint8_t v___x_2414_; 
v___x_2414_ = 2;
return v___x_2414_;
}
else
{
uint8_t v___x_2415_; 
v___x_2415_ = 0;
return v___x_2415_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3___boxed(lean_object* v_e_2416_){
_start:
{
uint8_t v_res_2417_; lean_object* v_r_2418_; 
v_res_2417_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(v_e_2416_);
lean_dec_ref(v_e_2416_);
v_r_2418_ = lean_box(v_res_2417_);
return v_r_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(lean_object* v_opts_2419_, lean_object* v_opt_2420_){
_start:
{
lean_object* v_name_2421_; lean_object* v_defValue_2422_; lean_object* v_map_2423_; lean_object* v___x_2424_; 
v_name_2421_ = lean_ctor_get(v_opt_2420_, 0);
v_defValue_2422_ = lean_ctor_get(v_opt_2420_, 1);
v_map_2423_ = lean_ctor_get(v_opts_2419_, 0);
v___x_2424_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2423_, v_name_2421_);
if (lean_obj_tag(v___x_2424_) == 0)
{
lean_inc(v_defValue_2422_);
return v_defValue_2422_;
}
else
{
lean_object* v_val_2425_; 
v_val_2425_ = lean_ctor_get(v___x_2424_, 0);
lean_inc(v_val_2425_);
lean_dec_ref(v___x_2424_);
if (lean_obj_tag(v_val_2425_) == 3)
{
lean_object* v_v_2426_; 
v_v_2426_ = lean_ctor_get(v_val_2425_, 0);
lean_inc(v_v_2426_);
lean_dec_ref(v_val_2425_);
return v_v_2426_;
}
else
{
lean_dec(v_val_2425_);
lean_inc(v_defValue_2422_);
return v_defValue_2422_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6___boxed(lean_object* v_opts_2427_, lean_object* v_opt_2428_){
_start:
{
lean_object* v_res_2429_; 
v_res_2429_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(v_opts_2427_, v_opt_2428_);
lean_dec_ref(v_opt_2428_);
lean_dec_ref(v_opts_2427_);
return v_res_2429_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___redArg(lean_object* v_x_2430_){
_start:
{
if (lean_obj_tag(v_x_2430_) == 0)
{
lean_object* v_a_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2439_; 
v_a_2432_ = lean_ctor_get(v_x_2430_, 0);
v_isSharedCheck_2439_ = !lean_is_exclusive(v_x_2430_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2434_ = v_x_2430_;
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_a_2432_);
lean_dec(v_x_2430_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v___x_2437_; 
if (v_isShared_2435_ == 0)
{
lean_ctor_set_tag(v___x_2434_, 1);
v___x_2437_ = v___x_2434_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v_a_2432_);
v___x_2437_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
return v___x_2437_;
}
}
}
else
{
lean_object* v_a_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2447_; 
v_a_2440_ = lean_ctor_get(v_x_2430_, 0);
v_isSharedCheck_2447_ = !lean_is_exclusive(v_x_2430_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2442_ = v_x_2430_;
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_a_2440_);
lean_dec(v_x_2430_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2445_; 
if (v_isShared_2443_ == 0)
{
lean_ctor_set_tag(v___x_2442_, 0);
v___x_2445_ = v___x_2442_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v_a_2440_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
return v___x_2445_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___redArg___boxed(lean_object* v_x_2448_, lean_object* v___y_2449_){
_start:
{
lean_object* v_res_2450_; 
v_res_2450_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___redArg(v_x_2448_);
return v_res_2450_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4_spec__5(size_t v_sz_2451_, size_t v_i_2452_, lean_object* v_bs_2453_){
_start:
{
uint8_t v___x_2454_; 
v___x_2454_ = lean_usize_dec_lt(v_i_2452_, v_sz_2451_);
if (v___x_2454_ == 0)
{
return v_bs_2453_;
}
else
{
lean_object* v_v_2455_; lean_object* v_msg_2456_; lean_object* v___x_2457_; lean_object* v_bs_x27_2458_; size_t v___x_2459_; size_t v___x_2460_; lean_object* v___x_2461_; 
v_v_2455_ = lean_array_uget_borrowed(v_bs_2453_, v_i_2452_);
v_msg_2456_ = lean_ctor_get(v_v_2455_, 1);
lean_inc_ref(v_msg_2456_);
v___x_2457_ = lean_unsigned_to_nat(0u);
v_bs_x27_2458_ = lean_array_uset(v_bs_2453_, v_i_2452_, v___x_2457_);
v___x_2459_ = ((size_t)1ULL);
v___x_2460_ = lean_usize_add(v_i_2452_, v___x_2459_);
v___x_2461_ = lean_array_uset(v_bs_x27_2458_, v_i_2452_, v_msg_2456_);
v_i_2452_ = v___x_2460_;
v_bs_2453_ = v___x_2461_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4_spec__5___boxed(lean_object* v_sz_2463_, lean_object* v_i_2464_, lean_object* v_bs_2465_){
_start:
{
size_t v_sz_boxed_2466_; size_t v_i_boxed_2467_; lean_object* v_res_2468_; 
v_sz_boxed_2466_ = lean_unbox_usize(v_sz_2463_);
lean_dec(v_sz_2463_);
v_i_boxed_2467_ = lean_unbox_usize(v_i_2464_);
lean_dec(v_i_2464_);
v_res_2468_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4_spec__5(v_sz_boxed_2466_, v_i_boxed_2467_, v_bs_2465_);
return v_res_2468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4(lean_object* v_oldTraces_2469_, lean_object* v_data_2470_, lean_object* v_ref_2471_, lean_object* v_msg_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_){
_start:
{
lean_object* v_fileName_2478_; lean_object* v_fileMap_2479_; lean_object* v_options_2480_; lean_object* v_currRecDepth_2481_; lean_object* v_maxRecDepth_2482_; lean_object* v_ref_2483_; lean_object* v_currNamespace_2484_; lean_object* v_openDecls_2485_; lean_object* v_initHeartbeats_2486_; lean_object* v_maxHeartbeats_2487_; lean_object* v_quotContext_2488_; lean_object* v_currMacroScope_2489_; uint8_t v_diag_2490_; lean_object* v_cancelTk_x3f_2491_; uint8_t v_suppressElabErrors_2492_; lean_object* v_inheritedTraceOptions_2493_; lean_object* v___x_2494_; lean_object* v_traceState_2495_; lean_object* v_traces_2496_; lean_object* v_ref_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; size_t v_sz_2500_; size_t v___x_2501_; lean_object* v___x_2502_; lean_object* v_msg_2503_; lean_object* v___x_2504_; lean_object* v_a_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2542_; 
v_fileName_2478_ = lean_ctor_get(v___y_2475_, 0);
v_fileMap_2479_ = lean_ctor_get(v___y_2475_, 1);
v_options_2480_ = lean_ctor_get(v___y_2475_, 2);
v_currRecDepth_2481_ = lean_ctor_get(v___y_2475_, 3);
v_maxRecDepth_2482_ = lean_ctor_get(v___y_2475_, 4);
v_ref_2483_ = lean_ctor_get(v___y_2475_, 5);
v_currNamespace_2484_ = lean_ctor_get(v___y_2475_, 6);
v_openDecls_2485_ = lean_ctor_get(v___y_2475_, 7);
v_initHeartbeats_2486_ = lean_ctor_get(v___y_2475_, 8);
v_maxHeartbeats_2487_ = lean_ctor_get(v___y_2475_, 9);
v_quotContext_2488_ = lean_ctor_get(v___y_2475_, 10);
v_currMacroScope_2489_ = lean_ctor_get(v___y_2475_, 11);
v_diag_2490_ = lean_ctor_get_uint8(v___y_2475_, sizeof(void*)*14);
v_cancelTk_x3f_2491_ = lean_ctor_get(v___y_2475_, 12);
v_suppressElabErrors_2492_ = lean_ctor_get_uint8(v___y_2475_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2493_ = lean_ctor_get(v___y_2475_, 13);
v___x_2494_ = lean_st_ref_get(v___y_2476_);
v_traceState_2495_ = lean_ctor_get(v___x_2494_, 4);
lean_inc_ref(v_traceState_2495_);
lean_dec(v___x_2494_);
v_traces_2496_ = lean_ctor_get(v_traceState_2495_, 0);
lean_inc_ref(v_traces_2496_);
lean_dec_ref(v_traceState_2495_);
v_ref_2497_ = l_Lean_replaceRef(v_ref_2471_, v_ref_2483_);
lean_inc_ref(v_inheritedTraceOptions_2493_);
lean_inc(v_cancelTk_x3f_2491_);
lean_inc(v_currMacroScope_2489_);
lean_inc(v_quotContext_2488_);
lean_inc(v_maxHeartbeats_2487_);
lean_inc(v_initHeartbeats_2486_);
lean_inc(v_openDecls_2485_);
lean_inc(v_currNamespace_2484_);
lean_inc(v_maxRecDepth_2482_);
lean_inc(v_currRecDepth_2481_);
lean_inc_ref(v_options_2480_);
lean_inc_ref(v_fileMap_2479_);
lean_inc_ref(v_fileName_2478_);
v___x_2498_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2498_, 0, v_fileName_2478_);
lean_ctor_set(v___x_2498_, 1, v_fileMap_2479_);
lean_ctor_set(v___x_2498_, 2, v_options_2480_);
lean_ctor_set(v___x_2498_, 3, v_currRecDepth_2481_);
lean_ctor_set(v___x_2498_, 4, v_maxRecDepth_2482_);
lean_ctor_set(v___x_2498_, 5, v_ref_2497_);
lean_ctor_set(v___x_2498_, 6, v_currNamespace_2484_);
lean_ctor_set(v___x_2498_, 7, v_openDecls_2485_);
lean_ctor_set(v___x_2498_, 8, v_initHeartbeats_2486_);
lean_ctor_set(v___x_2498_, 9, v_maxHeartbeats_2487_);
lean_ctor_set(v___x_2498_, 10, v_quotContext_2488_);
lean_ctor_set(v___x_2498_, 11, v_currMacroScope_2489_);
lean_ctor_set(v___x_2498_, 12, v_cancelTk_x3f_2491_);
lean_ctor_set(v___x_2498_, 13, v_inheritedTraceOptions_2493_);
lean_ctor_set_uint8(v___x_2498_, sizeof(void*)*14, v_diag_2490_);
lean_ctor_set_uint8(v___x_2498_, sizeof(void*)*14 + 1, v_suppressElabErrors_2492_);
v___x_2499_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2496_);
lean_dec_ref(v_traces_2496_);
v_sz_2500_ = lean_array_size(v___x_2499_);
v___x_2501_ = ((size_t)0ULL);
v___x_2502_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4_spec__5(v_sz_2500_, v___x_2501_, v___x_2499_);
v_msg_2503_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2503_, 0, v_data_2470_);
lean_ctor_set(v_msg_2503_, 1, v_msg_2472_);
lean_ctor_set(v_msg_2503_, 2, v___x_2502_);
v___x_2504_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msg_2503_, v___y_2473_, v___y_2474_, v___x_2498_, v___y_2476_);
lean_dec_ref(v___x_2498_);
v_a_2505_ = lean_ctor_get(v___x_2504_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2504_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2507_ = v___x_2504_;
v_isShared_2508_ = v_isSharedCheck_2542_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_a_2505_);
lean_dec(v___x_2504_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2542_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v___x_2509_; lean_object* v_traceState_2510_; lean_object* v_env_2511_; lean_object* v_nextMacroScope_2512_; lean_object* v_ngen_2513_; lean_object* v_auxDeclNGen_2514_; lean_object* v_cache_2515_; lean_object* v_messages_2516_; lean_object* v_infoState_2517_; lean_object* v_snapshotTasks_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2541_; 
v___x_2509_ = lean_st_ref_take(v___y_2476_);
v_traceState_2510_ = lean_ctor_get(v___x_2509_, 4);
v_env_2511_ = lean_ctor_get(v___x_2509_, 0);
v_nextMacroScope_2512_ = lean_ctor_get(v___x_2509_, 1);
v_ngen_2513_ = lean_ctor_get(v___x_2509_, 2);
v_auxDeclNGen_2514_ = lean_ctor_get(v___x_2509_, 3);
v_cache_2515_ = lean_ctor_get(v___x_2509_, 5);
v_messages_2516_ = lean_ctor_get(v___x_2509_, 6);
v_infoState_2517_ = lean_ctor_get(v___x_2509_, 7);
v_snapshotTasks_2518_ = lean_ctor_get(v___x_2509_, 8);
v_isSharedCheck_2541_ = !lean_is_exclusive(v___x_2509_);
if (v_isSharedCheck_2541_ == 0)
{
v___x_2520_ = v___x_2509_;
v_isShared_2521_ = v_isSharedCheck_2541_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_snapshotTasks_2518_);
lean_inc(v_infoState_2517_);
lean_inc(v_messages_2516_);
lean_inc(v_cache_2515_);
lean_inc(v_traceState_2510_);
lean_inc(v_auxDeclNGen_2514_);
lean_inc(v_ngen_2513_);
lean_inc(v_nextMacroScope_2512_);
lean_inc(v_env_2511_);
lean_dec(v___x_2509_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2541_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
uint64_t v_tid_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2539_; 
v_tid_2522_ = lean_ctor_get_uint64(v_traceState_2510_, sizeof(void*)*1);
v_isSharedCheck_2539_ = !lean_is_exclusive(v_traceState_2510_);
if (v_isSharedCheck_2539_ == 0)
{
lean_object* v_unused_2540_; 
v_unused_2540_ = lean_ctor_get(v_traceState_2510_, 0);
lean_dec(v_unused_2540_);
v___x_2524_ = v_traceState_2510_;
v_isShared_2525_ = v_isSharedCheck_2539_;
goto v_resetjp_2523_;
}
else
{
lean_dec(v_traceState_2510_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2539_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2529_; 
v___x_2526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2526_, 0, v_ref_2471_);
lean_ctor_set(v___x_2526_, 1, v_a_2505_);
v___x_2527_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2469_, v___x_2526_);
if (v_isShared_2525_ == 0)
{
lean_ctor_set(v___x_2524_, 0, v___x_2527_);
v___x_2529_ = v___x_2524_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v___x_2527_);
lean_ctor_set_uint64(v_reuseFailAlloc_2538_, sizeof(void*)*1, v_tid_2522_);
v___x_2529_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
lean_object* v___x_2531_; 
if (v_isShared_2521_ == 0)
{
lean_ctor_set(v___x_2520_, 4, v___x_2529_);
v___x_2531_ = v___x_2520_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_env_2511_);
lean_ctor_set(v_reuseFailAlloc_2537_, 1, v_nextMacroScope_2512_);
lean_ctor_set(v_reuseFailAlloc_2537_, 2, v_ngen_2513_);
lean_ctor_set(v_reuseFailAlloc_2537_, 3, v_auxDeclNGen_2514_);
lean_ctor_set(v_reuseFailAlloc_2537_, 4, v___x_2529_);
lean_ctor_set(v_reuseFailAlloc_2537_, 5, v_cache_2515_);
lean_ctor_set(v_reuseFailAlloc_2537_, 6, v_messages_2516_);
lean_ctor_set(v_reuseFailAlloc_2537_, 7, v_infoState_2517_);
lean_ctor_set(v_reuseFailAlloc_2537_, 8, v_snapshotTasks_2518_);
v___x_2531_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2535_; 
v___x_2532_ = lean_st_ref_set(v___y_2476_, v___x_2531_);
v___x_2533_ = lean_box(0);
if (v_isShared_2508_ == 0)
{
lean_ctor_set(v___x_2507_, 0, v___x_2533_);
v___x_2535_ = v___x_2507_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v___x_2533_);
v___x_2535_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
return v___x_2535_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___boxed(lean_object* v_oldTraces_2543_, lean_object* v_data_2544_, lean_object* v_ref_2545_, lean_object* v_msg_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4(v_oldTraces_2543_, v_data_2544_, v_ref_2545_, v_msg_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
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
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__3(void){
_start:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; 
v___x_2557_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2));
v___x_2558_ = l_Lean_stringToMessageData(v___x_2557_);
return v___x_2558_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__4(void){
_start:
{
lean_object* v___x_2559_; double v___x_2560_; 
v___x_2559_ = lean_unsigned_to_nat(1000u);
v___x_2560_ = lean_float_of_nat(v___x_2559_);
return v___x_2560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(lean_object* v_cls_2561_, uint8_t v_collapsed_2562_, lean_object* v_tag_2563_, lean_object* v_opts_2564_, uint8_t v_clsEnabled_2565_, lean_object* v_oldTraces_2566_, lean_object* v_msg_2567_, lean_object* v_resStartStop_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_){
_start:
{
lean_object* v_fst_2574_; lean_object* v_snd_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2665_; 
v_fst_2574_ = lean_ctor_get(v_resStartStop_2568_, 0);
v_snd_2575_ = lean_ctor_get(v_resStartStop_2568_, 1);
v_isSharedCheck_2665_ = !lean_is_exclusive(v_resStartStop_2568_);
if (v_isSharedCheck_2665_ == 0)
{
v___x_2577_ = v_resStartStop_2568_;
v_isShared_2578_ = v_isSharedCheck_2665_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_snd_2575_);
lean_inc(v_fst_2574_);
lean_dec(v_resStartStop_2568_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2665_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v___y_2580_; lean_object* v___y_2581_; lean_object* v_data_2582_; lean_object* v_fst_2585_; lean_object* v_snd_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2664_; 
v_fst_2585_ = lean_ctor_get(v_snd_2575_, 0);
v_snd_2586_ = lean_ctor_get(v_snd_2575_, 1);
v_isSharedCheck_2664_ = !lean_is_exclusive(v_snd_2575_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2588_ = v_snd_2575_;
v_isShared_2589_ = v_isSharedCheck_2664_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_snd_2586_);
lean_inc(v_fst_2585_);
lean_dec(v_snd_2575_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2664_;
goto v_resetjp_2587_;
}
v___jp_2579_:
{
lean_object* v___x_2583_; 
lean_inc(v___y_2581_);
v___x_2583_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4(v_oldTraces_2566_, v_data_2582_, v___y_2581_, v___y_2580_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_);
if (lean_obj_tag(v___x_2583_) == 0)
{
lean_object* v___x_2584_; 
lean_dec_ref(v___x_2583_);
v___x_2584_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___redArg(v_fst_2574_);
return v___x_2584_;
}
else
{
lean_dec(v_fst_2574_);
return v___x_2583_;
}
}
v_resetjp_2587_:
{
lean_object* v___x_2590_; uint8_t v___x_2591_; lean_object* v___y_2593_; lean_object* v_a_2594_; uint8_t v___y_2618_; double v___y_2649_; 
v___x_2590_ = l_Lean_trace_profiler;
v___x_2591_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_opts_2564_, v___x_2590_);
if (v___x_2591_ == 0)
{
v___y_2618_ = v___x_2591_;
goto v___jp_2617_;
}
else
{
lean_object* v___x_2654_; uint8_t v___x_2655_; 
v___x_2654_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2655_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_opts_2564_, v___x_2654_);
if (v___x_2655_ == 0)
{
lean_object* v___x_2656_; lean_object* v___x_2657_; double v___x_2658_; double v___x_2659_; double v___x_2660_; 
v___x_2656_ = l_Lean_trace_profiler_threshold;
v___x_2657_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(v_opts_2564_, v___x_2656_);
v___x_2658_ = lean_float_of_nat(v___x_2657_);
v___x_2659_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__4);
v___x_2660_ = lean_float_div(v___x_2658_, v___x_2659_);
v___y_2649_ = v___x_2660_;
goto v___jp_2648_;
}
else
{
lean_object* v___x_2661_; lean_object* v___x_2662_; double v___x_2663_; 
v___x_2661_ = l_Lean_trace_profiler_threshold;
v___x_2662_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(v_opts_2564_, v___x_2661_);
v___x_2663_ = lean_float_of_nat(v___x_2662_);
v___y_2649_ = v___x_2663_;
goto v___jp_2648_;
}
}
v___jp_2592_:
{
uint8_t v_result_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2600_; 
v_result_2595_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(v_fst_2574_);
v___x_2596_ = l_Lean_TraceResult_toEmoji(v_result_2595_);
v___x_2597_ = l_Lean_stringToMessageData(v___x_2596_);
v___x_2598_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1);
if (v_isShared_2589_ == 0)
{
lean_ctor_set_tag(v___x_2588_, 7);
lean_ctor_set(v___x_2588_, 1, v___x_2598_);
lean_ctor_set(v___x_2588_, 0, v___x_2597_);
v___x_2600_ = v___x_2588_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v___x_2597_);
lean_ctor_set(v_reuseFailAlloc_2611_, 1, v___x_2598_);
v___x_2600_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
lean_object* v_m_2602_; 
if (v_isShared_2578_ == 0)
{
lean_ctor_set_tag(v___x_2577_, 7);
lean_ctor_set(v___x_2577_, 1, v_a_2594_);
lean_ctor_set(v___x_2577_, 0, v___x_2600_);
v_m_2602_ = v___x_2577_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v___x_2600_);
lean_ctor_set(v_reuseFailAlloc_2610_, 1, v_a_2594_);
v_m_2602_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
lean_object* v___x_2603_; lean_object* v___x_2604_; double v___x_2605_; lean_object* v_data_2606_; 
v___x_2603_ = lean_box(v_result_2595_);
v___x_2604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2604_, 0, v___x_2603_);
v___x_2605_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0);
lean_inc_ref(v_tag_2563_);
lean_inc_ref(v___x_2604_);
lean_inc(v_cls_2561_);
v_data_2606_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2606_, 0, v_cls_2561_);
lean_ctor_set(v_data_2606_, 1, v___x_2604_);
lean_ctor_set(v_data_2606_, 2, v_tag_2563_);
lean_ctor_set_float(v_data_2606_, sizeof(void*)*3, v___x_2605_);
lean_ctor_set_float(v_data_2606_, sizeof(void*)*3 + 8, v___x_2605_);
lean_ctor_set_uint8(v_data_2606_, sizeof(void*)*3 + 16, v_collapsed_2562_);
if (v___x_2591_ == 0)
{
lean_dec_ref(v___x_2604_);
lean_dec(v_snd_2586_);
lean_dec(v_fst_2585_);
lean_dec_ref(v_tag_2563_);
lean_dec(v_cls_2561_);
v___y_2580_ = v_m_2602_;
v___y_2581_ = v___y_2593_;
v_data_2582_ = v_data_2606_;
goto v___jp_2579_;
}
else
{
lean_object* v_data_2607_; double v___x_2608_; double v___x_2609_; 
lean_dec_ref(v_data_2606_);
v_data_2607_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2607_, 0, v_cls_2561_);
lean_ctor_set(v_data_2607_, 1, v___x_2604_);
lean_ctor_set(v_data_2607_, 2, v_tag_2563_);
v___x_2608_ = lean_unbox_float(v_fst_2585_);
lean_dec(v_fst_2585_);
lean_ctor_set_float(v_data_2607_, sizeof(void*)*3, v___x_2608_);
v___x_2609_ = lean_unbox_float(v_snd_2586_);
lean_dec(v_snd_2586_);
lean_ctor_set_float(v_data_2607_, sizeof(void*)*3 + 8, v___x_2609_);
lean_ctor_set_uint8(v_data_2607_, sizeof(void*)*3 + 16, v_collapsed_2562_);
v___y_2580_ = v_m_2602_;
v___y_2581_ = v___y_2593_;
v_data_2582_ = v_data_2607_;
goto v___jp_2579_;
}
}
}
}
v___jp_2612_:
{
lean_object* v_ref_2613_; lean_object* v___x_2614_; 
v_ref_2613_ = lean_ctor_get(v___y_2571_, 5);
lean_inc(v___y_2572_);
lean_inc_ref(v___y_2571_);
lean_inc(v___y_2570_);
lean_inc_ref(v___y_2569_);
lean_inc(v_fst_2574_);
v___x_2614_ = lean_apply_6(v_msg_2567_, v_fst_2574_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, lean_box(0));
if (lean_obj_tag(v___x_2614_) == 0)
{
lean_object* v_a_2615_; 
v_a_2615_ = lean_ctor_get(v___x_2614_, 0);
lean_inc(v_a_2615_);
lean_dec_ref(v___x_2614_);
v___y_2593_ = v_ref_2613_;
v_a_2594_ = v_a_2615_;
goto v___jp_2592_;
}
else
{
lean_object* v___x_2616_; 
lean_dec_ref(v___x_2614_);
v___x_2616_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__3);
v___y_2593_ = v_ref_2613_;
v_a_2594_ = v___x_2616_;
goto v___jp_2592_;
}
}
v___jp_2617_:
{
if (v_clsEnabled_2565_ == 0)
{
if (v___y_2618_ == 0)
{
lean_object* v___x_2619_; lean_object* v_traceState_2620_; lean_object* v_env_2621_; lean_object* v_nextMacroScope_2622_; lean_object* v_ngen_2623_; lean_object* v_auxDeclNGen_2624_; lean_object* v_cache_2625_; lean_object* v_messages_2626_; lean_object* v_infoState_2627_; lean_object* v_snapshotTasks_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2647_; 
lean_del_object(v___x_2588_);
lean_dec(v_snd_2586_);
lean_dec(v_fst_2585_);
lean_del_object(v___x_2577_);
lean_dec_ref(v_msg_2567_);
lean_dec_ref(v_tag_2563_);
lean_dec(v_cls_2561_);
v___x_2619_ = lean_st_ref_take(v___y_2572_);
v_traceState_2620_ = lean_ctor_get(v___x_2619_, 4);
v_env_2621_ = lean_ctor_get(v___x_2619_, 0);
v_nextMacroScope_2622_ = lean_ctor_get(v___x_2619_, 1);
v_ngen_2623_ = lean_ctor_get(v___x_2619_, 2);
v_auxDeclNGen_2624_ = lean_ctor_get(v___x_2619_, 3);
v_cache_2625_ = lean_ctor_get(v___x_2619_, 5);
v_messages_2626_ = lean_ctor_get(v___x_2619_, 6);
v_infoState_2627_ = lean_ctor_get(v___x_2619_, 7);
v_snapshotTasks_2628_ = lean_ctor_get(v___x_2619_, 8);
v_isSharedCheck_2647_ = !lean_is_exclusive(v___x_2619_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2630_ = v___x_2619_;
v_isShared_2631_ = v_isSharedCheck_2647_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_snapshotTasks_2628_);
lean_inc(v_infoState_2627_);
lean_inc(v_messages_2626_);
lean_inc(v_cache_2625_);
lean_inc(v_traceState_2620_);
lean_inc(v_auxDeclNGen_2624_);
lean_inc(v_ngen_2623_);
lean_inc(v_nextMacroScope_2622_);
lean_inc(v_env_2621_);
lean_dec(v___x_2619_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2647_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
uint64_t v_tid_2632_; lean_object* v_traces_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2646_; 
v_tid_2632_ = lean_ctor_get_uint64(v_traceState_2620_, sizeof(void*)*1);
v_traces_2633_ = lean_ctor_get(v_traceState_2620_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v_traceState_2620_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2635_ = v_traceState_2620_;
v_isShared_2636_ = v_isSharedCheck_2646_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_traces_2633_);
lean_dec(v_traceState_2620_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2646_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2637_; lean_object* v___x_2639_; 
v___x_2637_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2566_, v_traces_2633_);
lean_dec_ref(v_traces_2633_);
if (v_isShared_2636_ == 0)
{
lean_ctor_set(v___x_2635_, 0, v___x_2637_);
v___x_2639_ = v___x_2635_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v___x_2637_);
lean_ctor_set_uint64(v_reuseFailAlloc_2645_, sizeof(void*)*1, v_tid_2632_);
v___x_2639_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
lean_object* v___x_2641_; 
if (v_isShared_2631_ == 0)
{
lean_ctor_set(v___x_2630_, 4, v___x_2639_);
v___x_2641_ = v___x_2630_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v_env_2621_);
lean_ctor_set(v_reuseFailAlloc_2644_, 1, v_nextMacroScope_2622_);
lean_ctor_set(v_reuseFailAlloc_2644_, 2, v_ngen_2623_);
lean_ctor_set(v_reuseFailAlloc_2644_, 3, v_auxDeclNGen_2624_);
lean_ctor_set(v_reuseFailAlloc_2644_, 4, v___x_2639_);
lean_ctor_set(v_reuseFailAlloc_2644_, 5, v_cache_2625_);
lean_ctor_set(v_reuseFailAlloc_2644_, 6, v_messages_2626_);
lean_ctor_set(v_reuseFailAlloc_2644_, 7, v_infoState_2627_);
lean_ctor_set(v_reuseFailAlloc_2644_, 8, v_snapshotTasks_2628_);
v___x_2641_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2642_ = lean_st_ref_set(v___y_2572_, v___x_2641_);
v___x_2643_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___redArg(v_fst_2574_);
return v___x_2643_;
}
}
}
}
}
else
{
goto v___jp_2612_;
}
}
else
{
goto v___jp_2612_;
}
}
v___jp_2648_:
{
double v___x_2650_; double v___x_2651_; double v___x_2652_; uint8_t v___x_2653_; 
v___x_2650_ = lean_unbox_float(v_snd_2586_);
v___x_2651_ = lean_unbox_float(v_fst_2585_);
v___x_2652_ = lean_float_sub(v___x_2650_, v___x_2651_);
v___x_2653_ = lean_float_decLt(v___y_2649_, v___x_2652_);
v___y_2618_ = v___x_2653_;
goto v___jp_2617_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___boxed(lean_object* v_cls_2666_, lean_object* v_collapsed_2667_, lean_object* v_tag_2668_, lean_object* v_opts_2669_, lean_object* v_clsEnabled_2670_, lean_object* v_oldTraces_2671_, lean_object* v_msg_2672_, lean_object* v_resStartStop_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_){
_start:
{
uint8_t v_collapsed_boxed_2679_; uint8_t v_clsEnabled_boxed_2680_; lean_object* v_res_2681_; 
v_collapsed_boxed_2679_ = lean_unbox(v_collapsed_2667_);
v_clsEnabled_boxed_2680_ = lean_unbox(v_clsEnabled_2670_);
v_res_2681_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_2666_, v_collapsed_boxed_2679_, v_tag_2668_, v_opts_2669_, v_clsEnabled_boxed_2680_, v_oldTraces_2671_, v_msg_2672_, v_resStartStop_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_);
lean_dec(v___y_2677_);
lean_dec_ref(v___y_2676_);
lean_dec(v___y_2675_);
lean_dec_ref(v___y_2674_);
lean_dec_ref(v_opts_2669_);
return v_res_2681_;
}
}
static double _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0(void){
_start:
{
lean_object* v___x_2682_; double v___x_2683_; 
v___x_2682_ = lean_unsigned_to_nat(1000000000u);
v___x_2683_ = lean_float_of_nat(v___x_2682_);
return v___x_2683_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2(void){
_start:
{
lean_object* v___x_2685_; lean_object* v___x_2686_; 
v___x_2685_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1));
v___x_2686_ = l_Lean_stringToMessageData(v___x_2685_);
return v___x_2686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(lean_object* v_ctorVal_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_){
_start:
{
lean_object* v_toConstantVal_2693_; lean_object* v_options_2694_; lean_object* v_name_2695_; lean_object* v_levelParams_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2907_; 
v_toConstantVal_2693_ = lean_ctor_get(v_ctorVal_2687_, 0);
lean_inc_ref(v_toConstantVal_2693_);
v_options_2694_ = lean_ctor_get(v_a_2690_, 2);
v_name_2695_ = lean_ctor_get(v_toConstantVal_2693_, 0);
v_levelParams_2696_ = lean_ctor_get(v_toConstantVal_2693_, 1);
v_isSharedCheck_2907_ = !lean_is_exclusive(v_toConstantVal_2693_);
if (v_isSharedCheck_2907_ == 0)
{
lean_object* v_unused_2908_; 
v_unused_2908_ = lean_ctor_get(v_toConstantVal_2693_, 2);
lean_dec(v_unused_2908_);
v___x_2698_ = v_toConstantVal_2693_;
v_isShared_2699_ = v_isSharedCheck_2907_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_levelParams_2696_);
lean_inc(v_name_2695_);
lean_dec(v_toConstantVal_2693_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2907_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v_inheritedTraceOptions_2700_; uint8_t v_hasTrace_2701_; lean_object* v_name_2702_; 
v_inheritedTraceOptions_2700_ = lean_ctor_get(v_a_2690_, 13);
v_hasTrace_2701_ = lean_ctor_get_uint8(v_options_2694_, sizeof(void*)*1);
lean_inc(v_name_2695_);
v_name_2702_ = l_Lean_Meta_mkInjectiveTheoremNameFor(v_name_2695_);
if (v_hasTrace_2701_ == 0)
{
lean_object* v___x_2703_; 
v___x_2703_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_);
if (lean_obj_tag(v___x_2703_) == 0)
{
lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2741_; 
v_a_2704_ = lean_ctor_get(v___x_2703_, 0);
v_isSharedCheck_2741_ = !lean_is_exclusive(v___x_2703_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2706_ = v___x_2703_;
v_isShared_2707_ = v_isSharedCheck_2741_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v___x_2703_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2741_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
if (lean_obj_tag(v_a_2704_) == 1)
{
lean_object* v_val_2708_; lean_object* v___x_2709_; 
lean_del_object(v___x_2706_);
v_val_2708_ = lean_ctor_get(v_a_2704_, 0);
lean_inc_n(v_val_2708_, 2);
lean_dec_ref(v_a_2704_);
v___x_2709_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2695_, v_val_2708_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_);
if (lean_obj_tag(v___x_2709_) == 0)
{
lean_object* v_a_2710_; lean_object* v___x_2711_; lean_object* v_a_2712_; lean_object* v___x_2713_; lean_object* v_a_2714_; lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2728_; 
v_a_2710_ = lean_ctor_get(v___x_2709_, 0);
lean_inc(v_a_2710_);
lean_dec_ref(v___x_2709_);
v___x_2711_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2708_, v_a_2689_);
v_a_2712_ = lean_ctor_get(v___x_2711_, 0);
lean_inc(v_a_2712_);
lean_dec_ref(v___x_2711_);
v___x_2713_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2710_, v_a_2689_);
v_a_2714_ = lean_ctor_get(v___x_2713_, 0);
v_isSharedCheck_2728_ = !lean_is_exclusive(v___x_2713_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2716_ = v___x_2713_;
v_isShared_2717_ = v_isSharedCheck_2728_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_a_2714_);
lean_dec(v___x_2713_);
v___x_2716_ = lean_box(0);
v_isShared_2717_ = v_isSharedCheck_2728_;
goto v_resetjp_2715_;
}
v_resetjp_2715_:
{
lean_object* v___x_2719_; 
lean_inc(v_name_2702_);
if (v_isShared_2699_ == 0)
{
lean_ctor_set(v___x_2698_, 2, v_a_2712_);
lean_ctor_set(v___x_2698_, 0, v_name_2702_);
v___x_2719_ = v___x_2698_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v_name_2702_);
lean_ctor_set(v_reuseFailAlloc_2727_, 1, v_levelParams_2696_);
lean_ctor_set(v_reuseFailAlloc_2727_, 2, v_a_2712_);
v___x_2719_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2724_; 
v___x_2720_ = lean_box(0);
v___x_2721_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2721_, 0, v_name_2702_);
lean_ctor_set(v___x_2721_, 1, v___x_2720_);
v___x_2722_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2722_, 0, v___x_2719_);
lean_ctor_set(v___x_2722_, 1, v_a_2714_);
lean_ctor_set(v___x_2722_, 2, v___x_2721_);
if (v_isShared_2717_ == 0)
{
lean_ctor_set_tag(v___x_2716_, 2);
lean_ctor_set(v___x_2716_, 0, v___x_2722_);
v___x_2724_ = v___x_2716_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v___x_2722_);
v___x_2724_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
lean_object* v___x_2725_; 
v___x_2725_ = l_Lean_addDecl(v___x_2724_, v_hasTrace_2701_, v_a_2690_, v_a_2691_);
return v___x_2725_;
}
}
}
}
else
{
lean_object* v_a_2729_; lean_object* v___x_2731_; uint8_t v_isShared_2732_; uint8_t v_isSharedCheck_2736_; 
lean_dec(v_val_2708_);
lean_dec(v_name_2702_);
lean_del_object(v___x_2698_);
lean_dec(v_levelParams_2696_);
v_a_2729_ = lean_ctor_get(v___x_2709_, 0);
v_isSharedCheck_2736_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2736_ == 0)
{
v___x_2731_ = v___x_2709_;
v_isShared_2732_ = v_isSharedCheck_2736_;
goto v_resetjp_2730_;
}
else
{
lean_inc(v_a_2729_);
lean_dec(v___x_2709_);
v___x_2731_ = lean_box(0);
v_isShared_2732_ = v_isSharedCheck_2736_;
goto v_resetjp_2730_;
}
v_resetjp_2730_:
{
lean_object* v___x_2734_; 
if (v_isShared_2732_ == 0)
{
v___x_2734_ = v___x_2731_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v_a_2729_);
v___x_2734_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
return v___x_2734_;
}
}
}
}
else
{
lean_object* v___x_2737_; lean_object* v___x_2739_; 
lean_dec(v_a_2704_);
lean_dec(v_name_2702_);
lean_del_object(v___x_2698_);
lean_dec(v_levelParams_2696_);
lean_dec(v_name_2695_);
v___x_2737_ = lean_box(0);
if (v_isShared_2707_ == 0)
{
lean_ctor_set(v___x_2706_, 0, v___x_2737_);
v___x_2739_ = v___x_2706_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v___x_2737_);
v___x_2739_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
return v___x_2739_;
}
}
}
}
else
{
lean_object* v_a_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2749_; 
lean_dec(v_name_2702_);
lean_del_object(v___x_2698_);
lean_dec(v_levelParams_2696_);
lean_dec(v_name_2695_);
v_a_2742_ = lean_ctor_get(v___x_2703_, 0);
v_isSharedCheck_2749_ = !lean_is_exclusive(v___x_2703_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2744_ = v___x_2703_;
v_isShared_2745_ = v_isSharedCheck_2749_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_a_2742_);
lean_dec(v___x_2703_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2749_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
lean_object* v___x_2747_; 
if (v_isShared_2745_ == 0)
{
v___x_2747_ = v___x_2744_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v_a_2742_);
v___x_2747_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
return v___x_2747_;
}
}
}
}
else
{
lean_object* v___f_2750_; lean_object* v_cls_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; uint8_t v___x_2754_; lean_object* v___y_2756_; lean_object* v___y_2757_; lean_object* v_a_2758_; lean_object* v___y_2768_; lean_object* v___y_2769_; lean_object* v_a_2770_; lean_object* v___y_2773_; lean_object* v___y_2774_; lean_object* v_a_2775_; lean_object* v___y_2778_; lean_object* v___y_2779_; lean_object* v___y_2780_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v_a_2786_; lean_object* v___y_2799_; lean_object* v___y_2800_; lean_object* v_a_2801_; lean_object* v___y_2804_; lean_object* v___y_2805_; lean_object* v_a_2806_; lean_object* v___y_2809_; lean_object* v___y_2810_; lean_object* v___y_2811_; 
lean_inc(v_name_2702_);
v___f_2750_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2750_, 0, v_name_2702_);
v_cls_2751_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_2752_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_2753_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_2754_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2700_, v_options_2694_, v___x_2753_);
if (v___x_2754_ == 0)
{
lean_object* v___x_2849_; uint8_t v___x_2850_; 
v___x_2849_ = l_Lean_trace_profiler;
v___x_2850_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_2694_, v___x_2849_);
if (v___x_2850_ == 0)
{
lean_object* v___x_2851_; 
lean_dec_ref(v___f_2750_);
v___x_2851_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_);
if (lean_obj_tag(v___x_2851_) == 0)
{
lean_object* v_a_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2898_; 
v_a_2852_ = lean_ctor_get(v___x_2851_, 0);
v_isSharedCheck_2898_ = !lean_is_exclusive(v___x_2851_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2854_ = v___x_2851_;
v_isShared_2855_ = v_isSharedCheck_2898_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_a_2852_);
lean_dec(v___x_2851_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2898_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
if (lean_obj_tag(v_a_2852_) == 1)
{
lean_object* v_val_2856_; lean_object* v___y_2858_; lean_object* v___y_2859_; lean_object* v___y_2860_; lean_object* v___y_2861_; 
lean_del_object(v___x_2854_);
v_val_2856_ = lean_ctor_get(v_a_2852_, 0);
lean_inc(v_val_2856_);
lean_dec_ref(v_a_2852_);
if (v___x_2754_ == 0)
{
v___y_2858_ = v_a_2688_;
v___y_2859_ = v_a_2689_;
v___y_2860_ = v_a_2690_;
v___y_2861_ = v_a_2691_;
goto v___jp_2857_;
}
else
{
lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___x_2890_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
lean_inc(v_val_2856_);
v___x_2891_ = l_Lean_MessageData_ofExpr(v_val_2856_);
v___x_2892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2892_, 0, v___x_2890_);
lean_ctor_set(v___x_2892_, 1, v___x_2891_);
v___x_2893_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2751_, v___x_2892_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_);
if (lean_obj_tag(v___x_2893_) == 0)
{
lean_dec_ref(v___x_2893_);
v___y_2858_ = v_a_2688_;
v___y_2859_ = v_a_2689_;
v___y_2860_ = v_a_2690_;
v___y_2861_ = v_a_2691_;
goto v___jp_2857_;
}
else
{
lean_dec(v_val_2856_);
lean_dec(v_name_2702_);
lean_del_object(v___x_2698_);
lean_dec(v_levelParams_2696_);
lean_dec(v_name_2695_);
return v___x_2893_;
}
}
v___jp_2857_:
{
lean_object* v___x_2862_; 
lean_inc(v_val_2856_);
v___x_2862_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2695_, v_val_2856_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_);
if (lean_obj_tag(v___x_2862_) == 0)
{
lean_object* v_a_2863_; lean_object* v___x_2864_; lean_object* v_a_2865_; lean_object* v___x_2866_; lean_object* v_a_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2881_; 
v_a_2863_ = lean_ctor_get(v___x_2862_, 0);
lean_inc(v_a_2863_);
lean_dec_ref(v___x_2862_);
v___x_2864_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2856_, v___y_2859_);
v_a_2865_ = lean_ctor_get(v___x_2864_, 0);
lean_inc(v_a_2865_);
lean_dec_ref(v___x_2864_);
v___x_2866_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2863_, v___y_2859_);
v_a_2867_ = lean_ctor_get(v___x_2866_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2869_ = v___x_2866_;
v_isShared_2870_ = v_isSharedCheck_2881_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_a_2867_);
lean_dec(v___x_2866_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2881_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
lean_object* v___x_2872_; 
lean_inc(v_name_2702_);
if (v_isShared_2699_ == 0)
{
lean_ctor_set(v___x_2698_, 2, v_a_2865_);
lean_ctor_set(v___x_2698_, 0, v_name_2702_);
v___x_2872_ = v___x_2698_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_name_2702_);
lean_ctor_set(v_reuseFailAlloc_2880_, 1, v_levelParams_2696_);
lean_ctor_set(v_reuseFailAlloc_2880_, 2, v_a_2865_);
v___x_2872_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2877_; 
v___x_2873_ = lean_box(0);
v___x_2874_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2874_, 0, v_name_2702_);
lean_ctor_set(v___x_2874_, 1, v___x_2873_);
v___x_2875_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2875_, 0, v___x_2872_);
lean_ctor_set(v___x_2875_, 1, v_a_2867_);
lean_ctor_set(v___x_2875_, 2, v___x_2874_);
if (v_isShared_2870_ == 0)
{
lean_ctor_set_tag(v___x_2869_, 2);
lean_ctor_set(v___x_2869_, 0, v___x_2875_);
v___x_2877_ = v___x_2869_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v___x_2875_);
v___x_2877_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
lean_object* v___x_2878_; 
v___x_2878_ = l_Lean_addDecl(v___x_2877_, v___x_2850_, v___y_2860_, v___y_2861_);
return v___x_2878_;
}
}
}
}
else
{
lean_object* v_a_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2889_; 
lean_dec(v_val_2856_);
lean_dec(v_name_2702_);
lean_del_object(v___x_2698_);
lean_dec(v_levelParams_2696_);
v_a_2882_ = lean_ctor_get(v___x_2862_, 0);
v_isSharedCheck_2889_ = !lean_is_exclusive(v___x_2862_);
if (v_isSharedCheck_2889_ == 0)
{
v___x_2884_ = v___x_2862_;
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_a_2882_);
lean_dec(v___x_2862_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
lean_object* v___x_2887_; 
if (v_isShared_2885_ == 0)
{
v___x_2887_ = v___x_2884_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v_a_2882_);
v___x_2887_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
return v___x_2887_;
}
}
}
}
}
else
{
lean_object* v___x_2894_; lean_object* v___x_2896_; 
lean_dec(v_a_2852_);
lean_dec(v_name_2702_);
lean_del_object(v___x_2698_);
lean_dec(v_levelParams_2696_);
lean_dec(v_name_2695_);
v___x_2894_ = lean_box(0);
if (v_isShared_2855_ == 0)
{
lean_ctor_set(v___x_2854_, 0, v___x_2894_);
v___x_2896_ = v___x_2854_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v___x_2894_);
v___x_2896_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
return v___x_2896_;
}
}
}
}
else
{
lean_object* v_a_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2906_; 
lean_dec(v_name_2702_);
lean_del_object(v___x_2698_);
lean_dec(v_levelParams_2696_);
lean_dec(v_name_2695_);
v_a_2899_ = lean_ctor_get(v___x_2851_, 0);
v_isSharedCheck_2906_ = !lean_is_exclusive(v___x_2851_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2901_ = v___x_2851_;
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_a_2899_);
lean_dec(v___x_2851_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v___x_2904_; 
if (v_isShared_2902_ == 0)
{
v___x_2904_ = v___x_2901_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v_a_2899_);
v___x_2904_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
return v___x_2904_;
}
}
}
}
else
{
lean_del_object(v___x_2698_);
goto v___jp_2814_;
}
}
else
{
lean_del_object(v___x_2698_);
goto v___jp_2814_;
}
v___jp_2755_:
{
lean_object* v___x_2759_; double v___x_2760_; double v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; 
v___x_2759_ = lean_io_get_num_heartbeats();
v___x_2760_ = lean_float_of_nat(v___y_2757_);
v___x_2761_ = lean_float_of_nat(v___x_2759_);
v___x_2762_ = lean_box_float(v___x_2760_);
v___x_2763_ = lean_box_float(v___x_2761_);
v___x_2764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2764_, 0, v___x_2762_);
lean_ctor_set(v___x_2764_, 1, v___x_2763_);
v___x_2765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2765_, 0, v_a_2758_);
lean_ctor_set(v___x_2765_, 1, v___x_2764_);
v___x_2766_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_2751_, v_hasTrace_2701_, v___x_2752_, v_options_2694_, v___x_2754_, v___y_2756_, v___f_2750_, v___x_2765_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_);
return v___x_2766_;
}
v___jp_2767_:
{
lean_object* v___x_2771_; 
v___x_2771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2771_, 0, v_a_2770_);
v___y_2756_ = v___y_2768_;
v___y_2757_ = v___y_2769_;
v_a_2758_ = v___x_2771_;
goto v___jp_2755_;
}
v___jp_2772_:
{
lean_object* v___x_2776_; 
v___x_2776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2776_, 0, v_a_2775_);
v___y_2756_ = v___y_2773_;
v___y_2757_ = v___y_2774_;
v_a_2758_ = v___x_2776_;
goto v___jp_2755_;
}
v___jp_2777_:
{
if (lean_obj_tag(v___y_2780_) == 0)
{
lean_object* v_a_2781_; 
v_a_2781_ = lean_ctor_get(v___y_2780_, 0);
lean_inc(v_a_2781_);
lean_dec_ref(v___y_2780_);
v___y_2773_ = v___y_2778_;
v___y_2774_ = v___y_2779_;
v_a_2775_ = v_a_2781_;
goto v___jp_2772_;
}
else
{
lean_object* v_a_2782_; 
v_a_2782_ = lean_ctor_get(v___y_2780_, 0);
lean_inc(v_a_2782_);
lean_dec_ref(v___y_2780_);
v___y_2768_ = v___y_2778_;
v___y_2769_ = v___y_2779_;
v_a_2770_ = v_a_2782_;
goto v___jp_2767_;
}
}
v___jp_2783_:
{
lean_object* v___x_2787_; double v___x_2788_; double v___x_2789_; double v___x_2790_; double v___x_2791_; double v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; 
v___x_2787_ = lean_io_mono_nanos_now();
v___x_2788_ = lean_float_of_nat(v___y_2785_);
v___x_2789_ = lean_float_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0);
v___x_2790_ = lean_float_div(v___x_2788_, v___x_2789_);
v___x_2791_ = lean_float_of_nat(v___x_2787_);
v___x_2792_ = lean_float_div(v___x_2791_, v___x_2789_);
v___x_2793_ = lean_box_float(v___x_2790_);
v___x_2794_ = lean_box_float(v___x_2792_);
v___x_2795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2795_, 0, v___x_2793_);
lean_ctor_set(v___x_2795_, 1, v___x_2794_);
v___x_2796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2796_, 0, v_a_2786_);
lean_ctor_set(v___x_2796_, 1, v___x_2795_);
v___x_2797_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_2751_, v_hasTrace_2701_, v___x_2752_, v_options_2694_, v___x_2754_, v___y_2784_, v___f_2750_, v___x_2796_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_);
return v___x_2797_;
}
v___jp_2798_:
{
lean_object* v___x_2802_; 
v___x_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2802_, 0, v_a_2801_);
v___y_2784_ = v___y_2799_;
v___y_2785_ = v___y_2800_;
v_a_2786_ = v___x_2802_;
goto v___jp_2783_;
}
v___jp_2803_:
{
lean_object* v___x_2807_; 
v___x_2807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2807_, 0, v_a_2806_);
v___y_2784_ = v___y_2804_;
v___y_2785_ = v___y_2805_;
v_a_2786_ = v___x_2807_;
goto v___jp_2783_;
}
v___jp_2808_:
{
if (lean_obj_tag(v___y_2811_) == 0)
{
lean_object* v_a_2812_; 
v_a_2812_ = lean_ctor_get(v___y_2811_, 0);
lean_inc(v_a_2812_);
lean_dec_ref(v___y_2811_);
v___y_2799_ = v___y_2809_;
v___y_2800_ = v___y_2810_;
v_a_2801_ = v_a_2812_;
goto v___jp_2798_;
}
else
{
lean_object* v_a_2813_; 
v_a_2813_ = lean_ctor_get(v___y_2811_, 0);
lean_inc(v_a_2813_);
lean_dec_ref(v___y_2811_);
v___y_2804_ = v___y_2809_;
v___y_2805_ = v___y_2810_;
v_a_2806_ = v_a_2813_;
goto v___jp_2803_;
}
}
v___jp_2814_:
{
lean_object* v___x_2815_; lean_object* v_a_2816_; lean_object* v___x_2817_; uint8_t v___x_2818_; 
v___x_2815_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v_a_2691_);
v_a_2816_ = lean_ctor_get(v___x_2815_, 0);
lean_inc(v_a_2816_);
lean_dec_ref(v___x_2815_);
v___x_2817_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2818_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_2694_, v___x_2817_);
if (v___x_2818_ == 0)
{
lean_object* v___x_2819_; lean_object* v___x_2820_; 
v___x_2819_ = lean_io_mono_nanos_now();
v___x_2820_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_);
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_object* v_a_2821_; 
v_a_2821_ = lean_ctor_get(v___x_2820_, 0);
lean_inc(v_a_2821_);
lean_dec_ref(v___x_2820_);
if (lean_obj_tag(v_a_2821_) == 1)
{
if (v___x_2754_ == 0)
{
lean_object* v_val_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; 
v_val_2822_ = lean_ctor_get(v_a_2821_, 0);
lean_inc(v_val_2822_);
lean_dec_ref(v_a_2821_);
v___x_2823_ = lean_box(0);
v___x_2824_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(v_name_2695_, v_val_2822_, v_name_2702_, v_levelParams_2696_, v___x_2818_, v___x_2823_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_);
v___y_2809_ = v_a_2816_;
v___y_2810_ = v___x_2819_;
v___y_2811_ = v___x_2824_;
goto v___jp_2808_;
}
else
{
lean_object* v_val_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
v_val_2825_ = lean_ctor_get(v_a_2821_, 0);
lean_inc_n(v_val_2825_, 2);
lean_dec_ref(v_a_2821_);
v___x_2826_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_2827_ = l_Lean_MessageData_ofExpr(v_val_2825_);
v___x_2828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2828_, 0, v___x_2826_);
lean_ctor_set(v___x_2828_, 1, v___x_2827_);
v___x_2829_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2751_, v___x_2828_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_);
if (lean_obj_tag(v___x_2829_) == 0)
{
lean_object* v_a_2830_; lean_object* v___x_2831_; 
v_a_2830_ = lean_ctor_get(v___x_2829_, 0);
lean_inc(v_a_2830_);
lean_dec_ref(v___x_2829_);
v___x_2831_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(v_name_2695_, v_val_2825_, v_name_2702_, v_levelParams_2696_, v___x_2818_, v_a_2830_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_);
v___y_2809_ = v_a_2816_;
v___y_2810_ = v___x_2819_;
v___y_2811_ = v___x_2831_;
goto v___jp_2808_;
}
else
{
lean_dec(v_val_2825_);
lean_dec(v_name_2702_);
lean_dec(v_levelParams_2696_);
lean_dec(v_name_2695_);
v___y_2809_ = v_a_2816_;
v___y_2810_ = v___x_2819_;
v___y_2811_ = v___x_2829_;
goto v___jp_2808_;
}
}
}
else
{
lean_object* v___x_2832_; 
lean_dec(v_a_2821_);
lean_dec(v_name_2702_);
lean_dec(v_levelParams_2696_);
lean_dec(v_name_2695_);
v___x_2832_ = lean_box(0);
v___y_2799_ = v_a_2816_;
v___y_2800_ = v___x_2819_;
v_a_2801_ = v___x_2832_;
goto v___jp_2798_;
}
}
else
{
lean_object* v_a_2833_; 
lean_dec(v_name_2702_);
lean_dec(v_levelParams_2696_);
lean_dec(v_name_2695_);
v_a_2833_ = lean_ctor_get(v___x_2820_, 0);
lean_inc(v_a_2833_);
lean_dec_ref(v___x_2820_);
v___y_2804_ = v_a_2816_;
v___y_2805_ = v___x_2819_;
v_a_2806_ = v_a_2833_;
goto v___jp_2803_;
}
}
else
{
lean_object* v___x_2834_; lean_object* v___x_2835_; 
v___x_2834_ = lean_io_get_num_heartbeats();
v___x_2835_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_);
if (lean_obj_tag(v___x_2835_) == 0)
{
lean_object* v_a_2836_; 
v_a_2836_ = lean_ctor_get(v___x_2835_, 0);
lean_inc(v_a_2836_);
lean_dec_ref(v___x_2835_);
if (lean_obj_tag(v_a_2836_) == 1)
{
if (v___x_2754_ == 0)
{
lean_object* v_val_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; 
v_val_2837_ = lean_ctor_get(v_a_2836_, 0);
lean_inc(v_val_2837_);
lean_dec_ref(v_a_2836_);
v___x_2838_ = lean_box(0);
v___x_2839_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(v_name_2695_, v_val_2837_, v_name_2702_, v_levelParams_2696_, v___x_2838_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_);
v___y_2778_ = v_a_2816_;
v___y_2779_ = v___x_2834_;
v___y_2780_ = v___x_2839_;
goto v___jp_2777_;
}
else
{
lean_object* v_val_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; 
v_val_2840_ = lean_ctor_get(v_a_2836_, 0);
lean_inc_n(v_val_2840_, 2);
lean_dec_ref(v_a_2836_);
v___x_2841_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_2842_ = l_Lean_MessageData_ofExpr(v_val_2840_);
v___x_2843_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2843_, 0, v___x_2841_);
lean_ctor_set(v___x_2843_, 1, v___x_2842_);
v___x_2844_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2751_, v___x_2843_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_);
if (lean_obj_tag(v___x_2844_) == 0)
{
lean_object* v_a_2845_; lean_object* v___x_2846_; 
v_a_2845_ = lean_ctor_get(v___x_2844_, 0);
lean_inc(v_a_2845_);
lean_dec_ref(v___x_2844_);
v___x_2846_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(v_name_2695_, v_val_2840_, v_name_2702_, v_levelParams_2696_, v_a_2845_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_);
v___y_2778_ = v_a_2816_;
v___y_2779_ = v___x_2834_;
v___y_2780_ = v___x_2846_;
goto v___jp_2777_;
}
else
{
lean_dec(v_val_2840_);
lean_dec(v_name_2702_);
lean_dec(v_levelParams_2696_);
lean_dec(v_name_2695_);
v___y_2778_ = v_a_2816_;
v___y_2779_ = v___x_2834_;
v___y_2780_ = v___x_2844_;
goto v___jp_2777_;
}
}
}
else
{
lean_object* v___x_2847_; 
lean_dec(v_a_2836_);
lean_dec(v_name_2702_);
lean_dec(v_levelParams_2696_);
lean_dec(v_name_2695_);
v___x_2847_ = lean_box(0);
v___y_2773_ = v_a_2816_;
v___y_2774_ = v___x_2834_;
v_a_2775_ = v___x_2847_;
goto v___jp_2772_;
}
}
else
{
lean_object* v_a_2848_; 
lean_dec(v_name_2702_);
lean_dec(v_levelParams_2696_);
lean_dec(v_name_2695_);
v_a_2848_ = lean_ctor_get(v___x_2835_, 0);
lean_inc(v_a_2848_);
lean_dec_ref(v___x_2835_);
v___y_2768_ = v_a_2816_;
v___y_2769_ = v___x_2834_;
v_a_2770_ = v_a_2848_;
goto v___jp_2767_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___boxed(lean_object* v_ctorVal_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_){
_start:
{
lean_object* v_res_2915_; 
v_res_2915_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(v_ctorVal_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_);
lean_dec(v_a_2913_);
lean_dec_ref(v_a_2912_);
lean_dec(v_a_2911_);
lean_dec_ref(v_a_2910_);
return v_res_2915_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5(lean_object* v_00_u03b1_2916_, lean_object* v_x_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_){
_start:
{
lean_object* v___x_2923_; 
v___x_2923_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___redArg(v_x_2917_);
return v___x_2923_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2924_, lean_object* v_x_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_){
_start:
{
lean_object* v_res_2931_; 
v_res_2931_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5(v_00_u03b1_2924_, v_x_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v___y_2927_);
lean_dec_ref(v___y_2926_);
return v_res_2931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveEqTheoremNameFor(lean_object* v_ctorName_2935_){
_start:
{
lean_object* v___x_2936_; lean_object* v___x_2937_; 
v___x_2936_ = ((lean_object*)(l_Lean_Meta_mkInjectiveEqTheoremNameFor___closed__1));
v___x_2937_ = l_Lean_Name_append(v_ctorName_2935_, v___x_2936_);
return v___x_2937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(lean_object* v_ctorVal_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_){
_start:
{
uint8_t v___x_2944_; lean_object* v___x_2945_; 
v___x_2944_ = 1;
v___x_2945_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(v_ctorVal_2938_, v___x_2944_, v_a_2939_, v_a_2940_, v_a_2941_, v_a_2942_);
return v___x_2945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f___boxed(lean_object* v_ctorVal_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_){
_start:
{
lean_object* v_res_2952_; 
v_res_2952_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_2946_, v_a_2947_, v_a_2948_, v_a_2949_, v_a_2950_);
lean_dec(v_a_2950_);
lean_dec_ref(v_a_2949_);
lean_dec(v_a_2948_);
lean_dec_ref(v_a_2947_);
return v_res_2952_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(lean_object* v_e_2953_, lean_object* v_t_2954_, lean_object* v_acc_2955_, lean_object* v_a_2956_){
_start:
{
lean_object* v___x_2958_; 
v___x_2958_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_t_2954_, v_a_2956_);
if (lean_obj_tag(v___x_2958_) == 0)
{
lean_object* v_a_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2982_; 
v_a_2959_ = lean_ctor_get(v___x_2958_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2961_ = v___x_2958_;
v_isShared_2962_ = v_isSharedCheck_2982_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_a_2959_);
lean_dec(v___x_2958_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2982_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
lean_object* v___x_2968_; uint8_t v___x_2969_; 
v___x_2968_ = l_Lean_Expr_cleanupAnnotations(v_a_2959_);
v___x_2969_ = l_Lean_Expr_isApp(v___x_2968_);
if (v___x_2969_ == 0)
{
lean_dec_ref(v___x_2968_);
goto v___jp_2963_;
}
else
{
lean_object* v_arg_2970_; lean_object* v___x_2971_; uint8_t v___x_2972_; 
v_arg_2970_ = lean_ctor_get(v___x_2968_, 1);
lean_inc_ref(v_arg_2970_);
v___x_2971_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2968_);
v___x_2972_ = l_Lean_Expr_isApp(v___x_2971_);
if (v___x_2972_ == 0)
{
lean_dec_ref(v___x_2971_);
lean_dec_ref(v_arg_2970_);
goto v___jp_2963_;
}
else
{
lean_object* v_arg_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; uint8_t v___x_2976_; 
v_arg_2973_ = lean_ctor_get(v___x_2971_, 1);
lean_inc_ref(v_arg_2973_);
v___x_2974_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2971_);
v___x_2975_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__1));
v___x_2976_ = l_Lean_Expr_isConstOf(v___x_2974_, v___x_2975_);
lean_dec_ref(v___x_2974_);
if (v___x_2976_ == 0)
{
lean_dec_ref(v_arg_2973_);
lean_dec_ref(v_arg_2970_);
goto v___jp_2963_;
}
else
{
lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; 
lean_del_object(v___x_2961_);
v___x_2977_ = lean_unsigned_to_nat(0u);
v___x_2978_ = l_Lean_mkProj(v___x_2975_, v___x_2977_, v_e_2953_);
lean_inc_ref(v___x_2978_);
v___x_2979_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v___x_2978_, v_arg_2973_, v_acc_2955_, v_a_2956_);
if (lean_obj_tag(v___x_2979_) == 0)
{
lean_object* v_a_2980_; 
v_a_2980_ = lean_ctor_get(v___x_2979_, 0);
lean_inc(v_a_2980_);
lean_dec_ref(v___x_2979_);
v_e_2953_ = v___x_2978_;
v_t_2954_ = v_arg_2970_;
v_acc_2955_ = v_a_2980_;
goto _start;
}
else
{
lean_dec_ref(v___x_2978_);
lean_dec_ref(v_arg_2970_);
return v___x_2979_;
}
}
}
}
v___jp_2963_:
{
lean_object* v___x_2964_; lean_object* v___x_2966_; 
v___x_2964_ = lean_array_push(v_acc_2955_, v_e_2953_);
if (v_isShared_2962_ == 0)
{
lean_ctor_set(v___x_2961_, 0, v___x_2964_);
v___x_2966_ = v___x_2961_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v___x_2964_);
v___x_2966_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
return v___x_2966_;
}
}
}
}
else
{
lean_object* v_a_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_2990_; 
lean_dec_ref(v_acc_2955_);
lean_dec_ref(v_e_2953_);
v_a_2983_ = lean_ctor_get(v___x_2958_, 0);
v_isSharedCheck_2990_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_2990_ == 0)
{
v___x_2985_ = v___x_2958_;
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_a_2983_);
lean_dec(v___x_2958_);
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
lean_dec_ref(v___x_3021_);
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
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__3(void){
_start:
{
lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3045_ = lean_box(0);
v___x_3046_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__2));
v___x_3047_ = l_Lean_mkConst(v___x_3046_, v___x_3045_);
return v___x_3047_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__5(void){
_start:
{
lean_object* v___x_3049_; lean_object* v___x_3050_; 
v___x_3049_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__4));
v___x_3050_ = l_Lean_stringToMessageData(v___x_3049_);
return v___x_3050_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1(lean_object* v_b_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_){
_start:
{
lean_object* v___x_3057_; 
lean_inc(v_b_3051_);
v___x_3057_ = l_Lean_MVarId_getType(v_b_3051_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_);
if (lean_obj_tag(v___x_3057_) == 0)
{
lean_object* v_a_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3138_; 
v_a_3058_ = lean_ctor_get(v___x_3057_, 0);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3057_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3060_ = v___x_3057_;
v_isShared_3061_ = v_isSharedCheck_3138_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_a_3058_);
lean_dec(v___x_3057_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3138_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
if (lean_obj_tag(v_a_3058_) == 7)
{
lean_object* v_binderType_3062_; lean_object* v_body_3063_; uint8_t v___x_3064_; lean_object* v_mvarId_u2082_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3070_; 
v_binderType_3062_ = lean_ctor_get(v_a_3058_, 1);
lean_inc_ref(v_binderType_3062_);
v_body_3063_ = lean_ctor_get(v_a_3058_, 2);
lean_inc_ref(v_body_3063_);
lean_dec_ref(v_a_3058_);
v___x_3064_ = l_Lean_Expr_hasLooseBVars(v_body_3063_);
if (v___x_3064_ == 0)
{
lean_object* v___x_3083_; 
lean_del_object(v___x_3060_);
v___x_3083_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_3062_, v___y_3053_);
if (lean_obj_tag(v___x_3083_) == 0)
{
lean_object* v_a_3084_; lean_object* v___x_3085_; uint8_t v___x_3086_; 
v_a_3084_ = lean_ctor_get(v___x_3083_, 0);
lean_inc(v_a_3084_);
lean_dec_ref(v___x_3083_);
v___x_3085_ = l_Lean_Expr_cleanupAnnotations(v_a_3084_);
v___x_3086_ = l_Lean_Expr_isApp(v___x_3085_);
if (v___x_3086_ == 0)
{
lean_dec_ref(v___x_3085_);
lean_dec_ref(v_body_3063_);
v_mvarId_u2082_3066_ = v_b_3051_;
v___y_3067_ = v___y_3052_;
v___y_3068_ = v___y_3053_;
v___y_3069_ = v___y_3054_;
v___y_3070_ = v___y_3055_;
goto v___jp_3065_;
}
else
{
lean_object* v_arg_3087_; lean_object* v___x_3088_; uint8_t v___x_3089_; 
v_arg_3087_ = lean_ctor_get(v___x_3085_, 1);
lean_inc_ref(v_arg_3087_);
v___x_3088_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3085_);
v___x_3089_ = l_Lean_Expr_isApp(v___x_3088_);
if (v___x_3089_ == 0)
{
lean_dec_ref(v___x_3088_);
lean_dec_ref(v_arg_3087_);
lean_dec_ref(v_body_3063_);
v_mvarId_u2082_3066_ = v_b_3051_;
v___y_3067_ = v___y_3052_;
v___y_3068_ = v___y_3053_;
v___y_3069_ = v___y_3054_;
v___y_3070_ = v___y_3055_;
goto v___jp_3065_;
}
else
{
lean_object* v_arg_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; uint8_t v___x_3093_; 
v_arg_3090_ = lean_ctor_get(v___x_3088_, 1);
lean_inc_ref(v_arg_3090_);
v___x_3091_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3088_);
v___x_3092_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__1));
v___x_3093_ = l_Lean_Expr_isConstOf(v___x_3091_, v___x_3092_);
lean_dec_ref(v___x_3091_);
if (v___x_3093_ == 0)
{
lean_dec_ref(v_arg_3090_);
lean_dec_ref(v_arg_3087_);
lean_dec_ref(v_body_3063_);
v_mvarId_u2082_3066_ = v_b_3051_;
v___y_3067_ = v___y_3052_;
v___y_3068_ = v___y_3053_;
v___y_3069_ = v___y_3054_;
v___y_3070_ = v___y_3055_;
goto v___jp_3065_;
}
else
{
lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; 
v___x_3094_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__3, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__3_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__3);
v___x_3095_ = l_Lean_mkApp3(v___x_3094_, v_arg_3090_, v_arg_3087_, v_body_3063_);
v___x_3096_ = lean_unsigned_to_nat(1u);
lean_inc(v_b_3051_);
v___x_3097_ = l_Lean_MVarId_applyN(v_b_3051_, v___x_3095_, v___x_3096_, v___x_3093_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_);
if (lean_obj_tag(v___x_3097_) == 0)
{
lean_object* v_a_3098_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v___y_3103_; 
v_a_3098_ = lean_ctor_get(v___x_3097_, 0);
lean_inc(v_a_3098_);
lean_dec_ref(v___x_3097_);
if (lean_obj_tag(v_a_3098_) == 1)
{
lean_object* v_tail_3114_; 
v_tail_3114_ = lean_ctor_get(v_a_3098_, 1);
if (lean_obj_tag(v_tail_3114_) == 0)
{
lean_object* v_head_3115_; 
lean_dec(v_b_3051_);
v_head_3115_ = lean_ctor_get(v_a_3098_, 0);
lean_inc(v_head_3115_);
lean_dec_ref(v_a_3098_);
v_mvarId_u2082_3066_ = v_head_3115_;
v___y_3067_ = v___y_3052_;
v___y_3068_ = v___y_3053_;
v___y_3069_ = v___y_3054_;
v___y_3070_ = v___y_3055_;
goto v___jp_3065_;
}
else
{
lean_dec_ref(v_a_3098_);
v___y_3100_ = v___y_3052_;
v___y_3101_ = v___y_3053_;
v___y_3102_ = v___y_3054_;
v___y_3103_ = v___y_3055_;
goto v___jp_3099_;
}
}
else
{
lean_dec(v_a_3098_);
v___y_3100_ = v___y_3052_;
v___y_3101_ = v___y_3053_;
v___y_3102_ = v___y_3054_;
v___y_3103_ = v___y_3055_;
goto v___jp_3099_;
}
v___jp_3099_:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___x_3104_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__5, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__5_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__5);
v___x_3105_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_3104_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_);
if (lean_obj_tag(v___x_3105_) == 0)
{
lean_dec_ref(v___x_3105_);
v_mvarId_u2082_3066_ = v_b_3051_;
v___y_3067_ = v___y_3100_;
v___y_3068_ = v___y_3101_;
v___y_3069_ = v___y_3102_;
v___y_3070_ = v___y_3103_;
goto v___jp_3065_;
}
else
{
lean_object* v_a_3106_; lean_object* v___x_3108_; uint8_t v_isShared_3109_; uint8_t v_isSharedCheck_3113_; 
lean_dec(v_b_3051_);
v_a_3106_ = lean_ctor_get(v___x_3105_, 0);
v_isSharedCheck_3113_ = !lean_is_exclusive(v___x_3105_);
if (v_isSharedCheck_3113_ == 0)
{
v___x_3108_ = v___x_3105_;
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
else
{
lean_inc(v_a_3106_);
lean_dec(v___x_3105_);
v___x_3108_ = lean_box(0);
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
v_resetjp_3107_:
{
lean_object* v___x_3111_; 
if (v_isShared_3109_ == 0)
{
v___x_3111_ = v___x_3108_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v_a_3106_);
v___x_3111_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
return v___x_3111_;
}
}
}
}
}
else
{
lean_object* v_a_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3123_; 
lean_dec(v_b_3051_);
v_a_3116_ = lean_ctor_get(v___x_3097_, 0);
v_isSharedCheck_3123_ = !lean_is_exclusive(v___x_3097_);
if (v_isSharedCheck_3123_ == 0)
{
v___x_3118_ = v___x_3097_;
v_isShared_3119_ = v_isSharedCheck_3123_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_a_3116_);
lean_dec(v___x_3097_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3123_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
lean_object* v___x_3121_; 
if (v_isShared_3119_ == 0)
{
v___x_3121_ = v___x_3118_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v_a_3116_);
v___x_3121_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
return v___x_3121_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3124_; lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3131_; 
lean_dec_ref(v_body_3063_);
lean_dec(v_b_3051_);
v_a_3124_ = lean_ctor_get(v___x_3083_, 0);
v_isSharedCheck_3131_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3126_ = v___x_3083_;
v_isShared_3127_ = v_isSharedCheck_3131_;
goto v_resetjp_3125_;
}
else
{
lean_inc(v_a_3124_);
lean_dec(v___x_3083_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3131_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
lean_object* v___x_3129_; 
if (v_isShared_3127_ == 0)
{
v___x_3129_ = v___x_3126_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v_a_3124_);
v___x_3129_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
return v___x_3129_;
}
}
}
}
else
{
lean_object* v___x_3133_; 
lean_dec_ref(v_body_3063_);
lean_dec_ref(v_binderType_3062_);
if (v_isShared_3061_ == 0)
{
lean_ctor_set(v___x_3060_, 0, v_b_3051_);
v___x_3133_ = v___x_3060_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v_b_3051_);
v___x_3133_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
return v___x_3133_;
}
}
v___jp_3065_:
{
lean_object* v___x_3071_; 
v___x_3071_ = l_Lean_Meta_introSubstEq(v_mvarId_u2082_3066_, v___x_3064_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_);
if (lean_obj_tag(v___x_3071_) == 0)
{
lean_object* v_a_3072_; lean_object* v_snd_3073_; 
v_a_3072_ = lean_ctor_get(v___x_3071_, 0);
lean_inc(v_a_3072_);
lean_dec_ref(v___x_3071_);
v_snd_3073_ = lean_ctor_get(v_a_3072_, 1);
lean_inc(v_snd_3073_);
lean_dec(v_a_3072_);
v_b_3051_ = v_snd_3073_;
goto _start;
}
else
{
lean_object* v_a_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3082_; 
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
else
{
lean_object* v___x_3136_; 
lean_dec(v_a_3058_);
if (v_isShared_3061_ == 0)
{
lean_ctor_set(v___x_3060_, 0, v_b_3051_);
v___x_3136_ = v___x_3060_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_b_3051_);
v___x_3136_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
return v___x_3136_;
}
}
}
}
else
{
lean_object* v_a_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3146_; 
lean_dec(v_b_3051_);
v_a_3139_ = lean_ctor_get(v___x_3057_, 0);
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_3057_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3141_ = v___x_3057_;
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_a_3139_);
lean_dec(v___x_3057_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
lean_object* v___x_3144_; 
if (v_isShared_3142_ == 0)
{
v___x_3144_ = v___x_3141_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v_a_3139_);
v___x_3144_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
return v___x_3144_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___boxed(lean_object* v_b_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_){
_start:
{
lean_object* v_res_3153_; 
v_res_3153_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1(v_b_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_);
lean_dec(v___y_3151_);
lean_dec_ref(v___y_3150_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
return v_res_3153_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_x_3154_, lean_object* v_x_3155_, lean_object* v_x_3156_, lean_object* v_x_3157_){
_start:
{
lean_object* v_ks_3158_; lean_object* v_vs_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3183_; 
v_ks_3158_ = lean_ctor_get(v_x_3154_, 0);
v_vs_3159_ = lean_ctor_get(v_x_3154_, 1);
v_isSharedCheck_3183_ = !lean_is_exclusive(v_x_3154_);
if (v_isSharedCheck_3183_ == 0)
{
v___x_3161_ = v_x_3154_;
v_isShared_3162_ = v_isSharedCheck_3183_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_vs_3159_);
lean_inc(v_ks_3158_);
lean_dec(v_x_3154_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3183_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
lean_object* v___x_3163_; uint8_t v___x_3164_; 
v___x_3163_ = lean_array_get_size(v_ks_3158_);
v___x_3164_ = lean_nat_dec_lt(v_x_3155_, v___x_3163_);
if (v___x_3164_ == 0)
{
lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3168_; 
lean_dec(v_x_3155_);
v___x_3165_ = lean_array_push(v_ks_3158_, v_x_3156_);
v___x_3166_ = lean_array_push(v_vs_3159_, v_x_3157_);
if (v_isShared_3162_ == 0)
{
lean_ctor_set(v___x_3161_, 1, v___x_3166_);
lean_ctor_set(v___x_3161_, 0, v___x_3165_);
v___x_3168_ = v___x_3161_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v___x_3165_);
lean_ctor_set(v_reuseFailAlloc_3169_, 1, v___x_3166_);
v___x_3168_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
return v___x_3168_;
}
}
else
{
lean_object* v_k_x27_3170_; uint8_t v___x_3171_; 
v_k_x27_3170_ = lean_array_fget_borrowed(v_ks_3158_, v_x_3155_);
v___x_3171_ = l_Lean_instBEqMVarId_beq(v_x_3156_, v_k_x27_3170_);
if (v___x_3171_ == 0)
{
lean_object* v___x_3173_; 
if (v_isShared_3162_ == 0)
{
v___x_3173_ = v___x_3161_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v_ks_3158_);
lean_ctor_set(v_reuseFailAlloc_3177_, 1, v_vs_3159_);
v___x_3173_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
lean_object* v___x_3174_; lean_object* v___x_3175_; 
v___x_3174_ = lean_unsigned_to_nat(1u);
v___x_3175_ = lean_nat_add(v_x_3155_, v___x_3174_);
lean_dec(v_x_3155_);
v_x_3154_ = v___x_3173_;
v_x_3155_ = v___x_3175_;
goto _start;
}
}
else
{
lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3181_; 
v___x_3178_ = lean_array_fset(v_ks_3158_, v_x_3155_, v_x_3156_);
v___x_3179_ = lean_array_fset(v_vs_3159_, v_x_3155_, v_x_3157_);
lean_dec(v_x_3155_);
if (v_isShared_3162_ == 0)
{
lean_ctor_set(v___x_3161_, 1, v___x_3179_);
lean_ctor_set(v___x_3161_, 0, v___x_3178_);
v___x_3181_ = v___x_3161_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v___x_3178_);
lean_ctor_set(v_reuseFailAlloc_3182_, 1, v___x_3179_);
v___x_3181_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
return v___x_3181_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_n_3184_, lean_object* v_k_3185_, lean_object* v_v_3186_){
_start:
{
lean_object* v___x_3187_; lean_object* v___x_3188_; 
v___x_3187_ = lean_unsigned_to_nat(0u);
v___x_3188_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_n_3184_, v___x_3187_, v_k_3185_, v_v_3186_);
return v___x_3188_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_3189_; size_t v___x_3190_; size_t v___x_3191_; 
v___x_3189_ = ((size_t)5ULL);
v___x_3190_ = ((size_t)1ULL);
v___x_3191_ = lean_usize_shift_left(v___x_3190_, v___x_3189_);
return v___x_3191_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_3192_; size_t v___x_3193_; size_t v___x_3194_; 
v___x_3192_ = ((size_t)1ULL);
v___x_3193_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_3194_ = lean_usize_sub(v___x_3193_, v___x_3192_);
return v___x_3194_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_3195_; 
v___x_3195_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_3195_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(lean_object* v_x_3196_, size_t v_x_3197_, size_t v_x_3198_, lean_object* v_x_3199_, lean_object* v_x_3200_){
_start:
{
if (lean_obj_tag(v_x_3196_) == 0)
{
lean_object* v_es_3201_; size_t v___x_3202_; size_t v___x_3203_; size_t v___x_3204_; size_t v___x_3205_; lean_object* v_j_3206_; lean_object* v___x_3207_; uint8_t v___x_3208_; 
v_es_3201_ = lean_ctor_get(v_x_3196_, 0);
v___x_3202_ = ((size_t)5ULL);
v___x_3203_ = ((size_t)1ULL);
v___x_3204_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_3205_ = lean_usize_land(v_x_3197_, v___x_3204_);
v_j_3206_ = lean_usize_to_nat(v___x_3205_);
v___x_3207_ = lean_array_get_size(v_es_3201_);
v___x_3208_ = lean_nat_dec_lt(v_j_3206_, v___x_3207_);
if (v___x_3208_ == 0)
{
lean_dec(v_j_3206_);
lean_dec(v_x_3200_);
lean_dec(v_x_3199_);
return v_x_3196_;
}
else
{
lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3245_; 
lean_inc_ref(v_es_3201_);
v_isSharedCheck_3245_ = !lean_is_exclusive(v_x_3196_);
if (v_isSharedCheck_3245_ == 0)
{
lean_object* v_unused_3246_; 
v_unused_3246_ = lean_ctor_get(v_x_3196_, 0);
lean_dec(v_unused_3246_);
v___x_3210_ = v_x_3196_;
v_isShared_3211_ = v_isSharedCheck_3245_;
goto v_resetjp_3209_;
}
else
{
lean_dec(v_x_3196_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3245_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v_v_3212_; lean_object* v___x_3213_; lean_object* v_xs_x27_3214_; lean_object* v___y_3216_; 
v_v_3212_ = lean_array_fget(v_es_3201_, v_j_3206_);
v___x_3213_ = lean_box(0);
v_xs_x27_3214_ = lean_array_fset(v_es_3201_, v_j_3206_, v___x_3213_);
switch(lean_obj_tag(v_v_3212_))
{
case 0:
{
lean_object* v_key_3221_; lean_object* v_val_3222_; lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3232_; 
v_key_3221_ = lean_ctor_get(v_v_3212_, 0);
v_val_3222_ = lean_ctor_get(v_v_3212_, 1);
v_isSharedCheck_3232_ = !lean_is_exclusive(v_v_3212_);
if (v_isSharedCheck_3232_ == 0)
{
v___x_3224_ = v_v_3212_;
v_isShared_3225_ = v_isSharedCheck_3232_;
goto v_resetjp_3223_;
}
else
{
lean_inc(v_val_3222_);
lean_inc(v_key_3221_);
lean_dec(v_v_3212_);
v___x_3224_ = lean_box(0);
v_isShared_3225_ = v_isSharedCheck_3232_;
goto v_resetjp_3223_;
}
v_resetjp_3223_:
{
uint8_t v___x_3226_; 
v___x_3226_ = l_Lean_instBEqMVarId_beq(v_x_3199_, v_key_3221_);
if (v___x_3226_ == 0)
{
lean_object* v___x_3227_; lean_object* v___x_3228_; 
lean_del_object(v___x_3224_);
v___x_3227_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3221_, v_val_3222_, v_x_3199_, v_x_3200_);
v___x_3228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3228_, 0, v___x_3227_);
v___y_3216_ = v___x_3228_;
goto v___jp_3215_;
}
else
{
lean_object* v___x_3230_; 
lean_dec(v_val_3222_);
lean_dec(v_key_3221_);
if (v_isShared_3225_ == 0)
{
lean_ctor_set(v___x_3224_, 1, v_x_3200_);
lean_ctor_set(v___x_3224_, 0, v_x_3199_);
v___x_3230_ = v___x_3224_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3231_; 
v_reuseFailAlloc_3231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3231_, 0, v_x_3199_);
lean_ctor_set(v_reuseFailAlloc_3231_, 1, v_x_3200_);
v___x_3230_ = v_reuseFailAlloc_3231_;
goto v_reusejp_3229_;
}
v_reusejp_3229_:
{
v___y_3216_ = v___x_3230_;
goto v___jp_3215_;
}
}
}
}
case 1:
{
lean_object* v_node_3233_; lean_object* v___x_3235_; uint8_t v_isShared_3236_; uint8_t v_isSharedCheck_3243_; 
v_node_3233_ = lean_ctor_get(v_v_3212_, 0);
v_isSharedCheck_3243_ = !lean_is_exclusive(v_v_3212_);
if (v_isSharedCheck_3243_ == 0)
{
v___x_3235_ = v_v_3212_;
v_isShared_3236_ = v_isSharedCheck_3243_;
goto v_resetjp_3234_;
}
else
{
lean_inc(v_node_3233_);
lean_dec(v_v_3212_);
v___x_3235_ = lean_box(0);
v_isShared_3236_ = v_isSharedCheck_3243_;
goto v_resetjp_3234_;
}
v_resetjp_3234_:
{
size_t v___x_3237_; size_t v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3241_; 
v___x_3237_ = lean_usize_shift_right(v_x_3197_, v___x_3202_);
v___x_3238_ = lean_usize_add(v_x_3198_, v___x_3203_);
v___x_3239_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_node_3233_, v___x_3237_, v___x_3238_, v_x_3199_, v_x_3200_);
if (v_isShared_3236_ == 0)
{
lean_ctor_set(v___x_3235_, 0, v___x_3239_);
v___x_3241_ = v___x_3235_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v___x_3239_);
v___x_3241_ = v_reuseFailAlloc_3242_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
v___y_3216_ = v___x_3241_;
goto v___jp_3215_;
}
}
}
default: 
{
lean_object* v___x_3244_; 
v___x_3244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3244_, 0, v_x_3199_);
lean_ctor_set(v___x_3244_, 1, v_x_3200_);
v___y_3216_ = v___x_3244_;
goto v___jp_3215_;
}
}
v___jp_3215_:
{
lean_object* v___x_3217_; lean_object* v___x_3219_; 
v___x_3217_ = lean_array_fset(v_xs_x27_3214_, v_j_3206_, v___y_3216_);
lean_dec(v_j_3206_);
if (v_isShared_3211_ == 0)
{
lean_ctor_set(v___x_3210_, 0, v___x_3217_);
v___x_3219_ = v___x_3210_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v___x_3217_);
v___x_3219_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
return v___x_3219_;
}
}
}
}
}
else
{
lean_object* v_ks_3247_; lean_object* v_vs_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3268_; 
v_ks_3247_ = lean_ctor_get(v_x_3196_, 0);
v_vs_3248_ = lean_ctor_get(v_x_3196_, 1);
v_isSharedCheck_3268_ = !lean_is_exclusive(v_x_3196_);
if (v_isSharedCheck_3268_ == 0)
{
v___x_3250_ = v_x_3196_;
v_isShared_3251_ = v_isSharedCheck_3268_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_vs_3248_);
lean_inc(v_ks_3247_);
lean_dec(v_x_3196_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3268_;
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
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v_ks_3247_);
lean_ctor_set(v_reuseFailAlloc_3267_, 1, v_vs_3248_);
v___x_3253_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
lean_object* v_newNode_3254_; uint8_t v___y_3256_; size_t v___x_3262_; uint8_t v___x_3263_; 
v_newNode_3254_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(v___x_3253_, v_x_3199_, v_x_3200_);
v___x_3262_ = ((size_t)7ULL);
v___x_3263_ = lean_usize_dec_le(v___x_3262_, v_x_3198_);
if (v___x_3263_ == 0)
{
lean_object* v___x_3264_; lean_object* v___x_3265_; uint8_t v___x_3266_; 
v___x_3264_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3254_);
v___x_3265_ = lean_unsigned_to_nat(4u);
v___x_3266_ = lean_nat_dec_lt(v___x_3264_, v___x_3265_);
lean_dec(v___x_3264_);
v___y_3256_ = v___x_3266_;
goto v___jp_3255_;
}
else
{
v___y_3256_ = v___x_3263_;
goto v___jp_3255_;
}
v___jp_3255_:
{
if (v___y_3256_ == 0)
{
lean_object* v_ks_3257_; lean_object* v_vs_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; 
v_ks_3257_ = lean_ctor_get(v_newNode_3254_, 0);
lean_inc_ref(v_ks_3257_);
v_vs_3258_ = lean_ctor_get(v_newNode_3254_, 1);
lean_inc_ref(v_vs_3258_);
lean_dec_ref(v_newNode_3254_);
v___x_3259_ = lean_unsigned_to_nat(0u);
v___x_3260_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__2);
v___x_3261_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(v_x_3198_, v_ks_3257_, v_vs_3258_, v___x_3259_, v___x_3260_);
lean_dec_ref(v_vs_3258_);
lean_dec_ref(v_ks_3257_);
return v___x_3261_;
}
else
{
return v_newNode_3254_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(size_t v_depth_3269_, lean_object* v_keys_3270_, lean_object* v_vals_3271_, lean_object* v_i_3272_, lean_object* v_entries_3273_){
_start:
{
lean_object* v___x_3274_; uint8_t v___x_3275_; 
v___x_3274_ = lean_array_get_size(v_keys_3270_);
v___x_3275_ = lean_nat_dec_lt(v_i_3272_, v___x_3274_);
if (v___x_3275_ == 0)
{
lean_dec(v_i_3272_);
return v_entries_3273_;
}
else
{
lean_object* v_k_3276_; lean_object* v_v_3277_; uint64_t v___x_3278_; size_t v_h_3279_; size_t v___x_3280_; lean_object* v___x_3281_; size_t v___x_3282_; size_t v___x_3283_; size_t v___x_3284_; size_t v_h_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; 
v_k_3276_ = lean_array_fget_borrowed(v_keys_3270_, v_i_3272_);
v_v_3277_ = lean_array_fget_borrowed(v_vals_3271_, v_i_3272_);
v___x_3278_ = l_Lean_instHashableMVarId_hash(v_k_3276_);
v_h_3279_ = lean_uint64_to_usize(v___x_3278_);
v___x_3280_ = ((size_t)5ULL);
v___x_3281_ = lean_unsigned_to_nat(1u);
v___x_3282_ = ((size_t)1ULL);
v___x_3283_ = lean_usize_sub(v_depth_3269_, v___x_3282_);
v___x_3284_ = lean_usize_mul(v___x_3280_, v___x_3283_);
v_h_3285_ = lean_usize_shift_right(v_h_3279_, v___x_3284_);
v___x_3286_ = lean_nat_add(v_i_3272_, v___x_3281_);
lean_dec(v_i_3272_);
lean_inc(v_v_3277_);
lean_inc(v_k_3276_);
v___x_3287_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_entries_3273_, v_h_3285_, v_depth_3269_, v_k_3276_, v_v_3277_);
v_i_3272_ = v___x_3286_;
v_entries_3273_ = v___x_3287_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_depth_3289_, lean_object* v_keys_3290_, lean_object* v_vals_3291_, lean_object* v_i_3292_, lean_object* v_entries_3293_){
_start:
{
size_t v_depth_boxed_3294_; lean_object* v_res_3295_; 
v_depth_boxed_3294_ = lean_unbox_usize(v_depth_3289_);
lean_dec(v_depth_3289_);
v_res_3295_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_boxed_3294_, v_keys_3290_, v_vals_3291_, v_i_3292_, v_entries_3293_);
lean_dec_ref(v_vals_3291_);
lean_dec_ref(v_keys_3290_);
return v_res_3295_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_3296_, lean_object* v_x_3297_, lean_object* v_x_3298_, lean_object* v_x_3299_, lean_object* v_x_3300_){
_start:
{
size_t v_x_5084__boxed_3301_; size_t v_x_5085__boxed_3302_; lean_object* v_res_3303_; 
v_x_5084__boxed_3301_ = lean_unbox_usize(v_x_3297_);
lean_dec(v_x_3297_);
v_x_5085__boxed_3302_ = lean_unbox_usize(v_x_3298_);
lean_dec(v_x_3298_);
v_res_3303_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_x_3296_, v_x_5084__boxed_3301_, v_x_5085__boxed_3302_, v_x_3299_, v_x_3300_);
return v_res_3303_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(lean_object* v_x_3304_, lean_object* v_x_3305_, lean_object* v_x_3306_){
_start:
{
uint64_t v___x_3307_; size_t v___x_3308_; size_t v___x_3309_; lean_object* v___x_3310_; 
v___x_3307_ = l_Lean_instHashableMVarId_hash(v_x_3305_);
v___x_3308_ = lean_uint64_to_usize(v___x_3307_);
v___x_3309_ = ((size_t)1ULL);
v___x_3310_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_x_3304_, v___x_3308_, v___x_3309_, v_x_3305_, v_x_3306_);
return v___x_3310_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(lean_object* v_mvarId_3311_, lean_object* v_val_3312_, lean_object* v___y_3313_){
_start:
{
lean_object* v___x_3315_; lean_object* v_mctx_3316_; lean_object* v_cache_3317_; lean_object* v_zetaDeltaFVarIds_3318_; lean_object* v_postponed_3319_; lean_object* v_diag_3320_; lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3348_; 
v___x_3315_ = lean_st_ref_take(v___y_3313_);
v_mctx_3316_ = lean_ctor_get(v___x_3315_, 0);
v_cache_3317_ = lean_ctor_get(v___x_3315_, 1);
v_zetaDeltaFVarIds_3318_ = lean_ctor_get(v___x_3315_, 2);
v_postponed_3319_ = lean_ctor_get(v___x_3315_, 3);
v_diag_3320_ = lean_ctor_get(v___x_3315_, 4);
v_isSharedCheck_3348_ = !lean_is_exclusive(v___x_3315_);
if (v_isSharedCheck_3348_ == 0)
{
v___x_3322_ = v___x_3315_;
v_isShared_3323_ = v_isSharedCheck_3348_;
goto v_resetjp_3321_;
}
else
{
lean_inc(v_diag_3320_);
lean_inc(v_postponed_3319_);
lean_inc(v_zetaDeltaFVarIds_3318_);
lean_inc(v_cache_3317_);
lean_inc(v_mctx_3316_);
lean_dec(v___x_3315_);
v___x_3322_ = lean_box(0);
v_isShared_3323_ = v_isSharedCheck_3348_;
goto v_resetjp_3321_;
}
v_resetjp_3321_:
{
lean_object* v_depth_3324_; lean_object* v_levelAssignDepth_3325_; lean_object* v_lmvarCounter_3326_; lean_object* v_mvarCounter_3327_; lean_object* v_lDecls_3328_; lean_object* v_decls_3329_; lean_object* v_userNames_3330_; lean_object* v_lAssignment_3331_; lean_object* v_eAssignment_3332_; lean_object* v_dAssignment_3333_; lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3347_; 
v_depth_3324_ = lean_ctor_get(v_mctx_3316_, 0);
v_levelAssignDepth_3325_ = lean_ctor_get(v_mctx_3316_, 1);
v_lmvarCounter_3326_ = lean_ctor_get(v_mctx_3316_, 2);
v_mvarCounter_3327_ = lean_ctor_get(v_mctx_3316_, 3);
v_lDecls_3328_ = lean_ctor_get(v_mctx_3316_, 4);
v_decls_3329_ = lean_ctor_get(v_mctx_3316_, 5);
v_userNames_3330_ = lean_ctor_get(v_mctx_3316_, 6);
v_lAssignment_3331_ = lean_ctor_get(v_mctx_3316_, 7);
v_eAssignment_3332_ = lean_ctor_get(v_mctx_3316_, 8);
v_dAssignment_3333_ = lean_ctor_get(v_mctx_3316_, 9);
v_isSharedCheck_3347_ = !lean_is_exclusive(v_mctx_3316_);
if (v_isSharedCheck_3347_ == 0)
{
v___x_3335_ = v_mctx_3316_;
v_isShared_3336_ = v_isSharedCheck_3347_;
goto v_resetjp_3334_;
}
else
{
lean_inc(v_dAssignment_3333_);
lean_inc(v_eAssignment_3332_);
lean_inc(v_lAssignment_3331_);
lean_inc(v_userNames_3330_);
lean_inc(v_decls_3329_);
lean_inc(v_lDecls_3328_);
lean_inc(v_mvarCounter_3327_);
lean_inc(v_lmvarCounter_3326_);
lean_inc(v_levelAssignDepth_3325_);
lean_inc(v_depth_3324_);
lean_dec(v_mctx_3316_);
v___x_3335_ = lean_box(0);
v_isShared_3336_ = v_isSharedCheck_3347_;
goto v_resetjp_3334_;
}
v_resetjp_3334_:
{
lean_object* v___x_3337_; lean_object* v___x_3339_; 
v___x_3337_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(v_eAssignment_3332_, v_mvarId_3311_, v_val_3312_);
if (v_isShared_3336_ == 0)
{
lean_ctor_set(v___x_3335_, 8, v___x_3337_);
v___x_3339_ = v___x_3335_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v_depth_3324_);
lean_ctor_set(v_reuseFailAlloc_3346_, 1, v_levelAssignDepth_3325_);
lean_ctor_set(v_reuseFailAlloc_3346_, 2, v_lmvarCounter_3326_);
lean_ctor_set(v_reuseFailAlloc_3346_, 3, v_mvarCounter_3327_);
lean_ctor_set(v_reuseFailAlloc_3346_, 4, v_lDecls_3328_);
lean_ctor_set(v_reuseFailAlloc_3346_, 5, v_decls_3329_);
lean_ctor_set(v_reuseFailAlloc_3346_, 6, v_userNames_3330_);
lean_ctor_set(v_reuseFailAlloc_3346_, 7, v_lAssignment_3331_);
lean_ctor_set(v_reuseFailAlloc_3346_, 8, v___x_3337_);
lean_ctor_set(v_reuseFailAlloc_3346_, 9, v_dAssignment_3333_);
v___x_3339_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
lean_object* v___x_3341_; 
if (v_isShared_3323_ == 0)
{
lean_ctor_set(v___x_3322_, 0, v___x_3339_);
v___x_3341_ = v___x_3322_;
goto v_reusejp_3340_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v___x_3339_);
lean_ctor_set(v_reuseFailAlloc_3345_, 1, v_cache_3317_);
lean_ctor_set(v_reuseFailAlloc_3345_, 2, v_zetaDeltaFVarIds_3318_);
lean_ctor_set(v_reuseFailAlloc_3345_, 3, v_postponed_3319_);
lean_ctor_set(v_reuseFailAlloc_3345_, 4, v_diag_3320_);
v___x_3341_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3340_;
}
v_reusejp_3340_:
{
lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; 
v___x_3342_ = lean_st_ref_set(v___y_3313_, v___x_3341_);
v___x_3343_ = lean_box(0);
v___x_3344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3344_, 0, v___x_3343_);
return v___x_3344_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg___boxed(lean_object* v_mvarId_3349_, lean_object* v_val_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_){
_start:
{
lean_object* v_res_3353_; 
v_res_3353_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(v_mvarId_3349_, v_val_3350_, v___y_3351_);
lean_dec(v___y_3351_);
return v_res_3353_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; 
v___x_3359_ = lean_box(0);
v___x_3360_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__2));
v___x_3361_ = l_Lean_mkConst(v___x_3360_, v___x_3359_);
return v___x_3361_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6(void){
_start:
{
lean_object* v___x_3367_; lean_object* v___x_3368_; 
v___x_3367_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__5));
v___x_3368_ = l_Lean_stringToMessageData(v___x_3367_);
return v___x_3368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0(lean_object* v_ctorVal_3369_, lean_object* v_xs_3370_, lean_object* v_type_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_){
_start:
{
lean_object* v___x_3377_; lean_object* v___x_3378_; 
v___x_3377_ = lean_box(0);
v___x_3378_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_3371_, v___x_3377_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
if (lean_obj_tag(v___x_3378_) == 0)
{
lean_object* v_a_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; uint8_t v___x_3383_; uint8_t v___x_3384_; lean_object* v___y_3386_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; 
v_a_3379_ = lean_ctor_get(v___x_3378_, 0);
lean_inc(v_a_3379_);
lean_dec_ref(v___x_3378_);
v___x_3380_ = l_Lean_Expr_mvarId_x21(v_a_3379_);
v___x_3381_ = lean_box(0);
v___x_3382_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3);
v___x_3383_ = 1;
v___x_3384_ = 0;
v___x_3397_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__4));
v___x_3398_ = lean_box(0);
v___x_3399_ = l_Lean_MVarId_apply(v___x_3380_, v___x_3382_, v___x_3397_, v___x_3398_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
if (lean_obj_tag(v___x_3399_) == 0)
{
lean_object* v_a_3400_; lean_object* v___y_3402_; lean_object* v___y_3403_; lean_object* v___y_3404_; lean_object* v___y_3405_; 
v_a_3400_ = lean_ctor_get(v___x_3399_, 0);
lean_inc(v_a_3400_);
lean_dec_ref(v___x_3399_);
if (lean_obj_tag(v_a_3400_) == 1)
{
lean_object* v_tail_3414_; 
v_tail_3414_ = lean_ctor_get(v_a_3400_, 1);
lean_inc(v_tail_3414_);
if (lean_obj_tag(v_tail_3414_) == 1)
{
lean_object* v_tail_3415_; 
v_tail_3415_ = lean_ctor_get(v_tail_3414_, 1);
if (lean_obj_tag(v_tail_3415_) == 0)
{
lean_object* v_toConstantVal_3416_; lean_object* v_head_3417_; lean_object* v_head_3418_; lean_object* v_name_3419_; lean_object* v_levelParams_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; 
v_toConstantVal_3416_ = lean_ctor_get(v_ctorVal_3369_, 0);
lean_inc_ref(v_toConstantVal_3416_);
lean_dec_ref(v_ctorVal_3369_);
v_head_3417_ = lean_ctor_get(v_a_3400_, 0);
lean_inc(v_head_3417_);
lean_dec_ref(v_a_3400_);
v_head_3418_ = lean_ctor_get(v_tail_3414_, 0);
lean_inc(v_head_3418_);
lean_dec_ref(v_tail_3414_);
v_name_3419_ = lean_ctor_get(v_toConstantVal_3416_, 0);
lean_inc_n(v_name_3419_, 2);
v_levelParams_3420_ = lean_ctor_get(v_toConstantVal_3416_, 1);
lean_inc(v_levelParams_3420_);
lean_dec_ref(v_toConstantVal_3416_);
v___x_3421_ = l_Lean_Meta_mkInjectiveTheoremNameFor(v_name_3419_);
v___x_3422_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(v_levelParams_3420_, v___x_3381_);
v___x_3423_ = l_Lean_mkConst(v___x_3421_, v___x_3422_);
v___x_3424_ = l_Lean_mkAppN(v___x_3423_, v_xs_3370_);
v___x_3425_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(v_head_3417_, v___x_3424_, v___y_3373_);
lean_dec_ref(v___x_3425_);
v___x_3426_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1(v_head_3418_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
if (lean_obj_tag(v___x_3426_) == 0)
{
lean_object* v_a_3427_; lean_object* v___x_3428_; 
v_a_3427_ = lean_ctor_get(v___x_3426_, 0);
lean_inc(v_a_3427_);
lean_dec_ref(v___x_3426_);
v___x_3428_ = l_Lean_MVarId_refl(v_a_3427_, v___x_3383_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
if (lean_obj_tag(v___x_3428_) == 0)
{
lean_dec(v_name_3419_);
v___y_3386_ = v___x_3428_;
goto v___jp_3385_;
}
else
{
lean_object* v_a_3429_; uint8_t v___y_3431_; uint8_t v___x_3434_; 
v_a_3429_ = lean_ctor_get(v___x_3428_, 0);
lean_inc(v_a_3429_);
v___x_3434_ = l_Lean_Exception_isInterrupt(v_a_3429_);
if (v___x_3434_ == 0)
{
uint8_t v___x_3435_; 
v___x_3435_ = l_Lean_Exception_isRuntime(v_a_3429_);
v___y_3431_ = v___x_3435_;
goto v___jp_3430_;
}
else
{
lean_dec(v_a_3429_);
v___y_3431_ = v___x_3434_;
goto v___jp_3430_;
}
v___jp_3430_:
{
if (v___y_3431_ == 0)
{
lean_object* v___x_3432_; lean_object* v___x_3433_; 
lean_dec_ref(v___x_3428_);
v___x_3432_ = l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(v_name_3419_);
v___x_3433_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_3432_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
v___y_3386_ = v___x_3433_;
goto v___jp_3385_;
}
else
{
lean_dec(v_name_3419_);
v___y_3386_ = v___x_3428_;
goto v___jp_3385_;
}
}
}
}
else
{
lean_object* v_a_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3443_; 
lean_dec(v_name_3419_);
lean_dec(v_a_3379_);
v_a_3436_ = lean_ctor_get(v___x_3426_, 0);
v_isSharedCheck_3443_ = !lean_is_exclusive(v___x_3426_);
if (v_isSharedCheck_3443_ == 0)
{
v___x_3438_ = v___x_3426_;
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_a_3436_);
lean_dec(v___x_3426_);
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
else
{
lean_dec_ref(v_tail_3414_);
lean_dec_ref(v_a_3400_);
lean_dec(v_a_3379_);
v___y_3402_ = v___y_3372_;
v___y_3403_ = v___y_3373_;
v___y_3404_ = v___y_3374_;
v___y_3405_ = v___y_3375_;
goto v___jp_3401_;
}
}
else
{
lean_dec(v_tail_3414_);
lean_dec_ref(v_a_3400_);
lean_dec(v_a_3379_);
v___y_3402_ = v___y_3372_;
v___y_3403_ = v___y_3373_;
v___y_3404_ = v___y_3374_;
v___y_3405_ = v___y_3375_;
goto v___jp_3401_;
}
}
else
{
lean_dec(v_a_3400_);
lean_dec(v_a_3379_);
v___y_3402_ = v___y_3372_;
v___y_3403_ = v___y_3373_;
v___y_3404_ = v___y_3374_;
v___y_3405_ = v___y_3375_;
goto v___jp_3401_;
}
v___jp_3401_:
{
lean_object* v_toConstantVal_3406_; lean_object* v_name_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; 
v_toConstantVal_3406_ = lean_ctor_get(v_ctorVal_3369_, 0);
lean_inc_ref(v_toConstantVal_3406_);
lean_dec_ref(v_ctorVal_3369_);
v_name_3407_ = lean_ctor_get(v_toConstantVal_3406_, 0);
lean_inc(v_name_3407_);
lean_dec_ref(v_toConstantVal_3406_);
v___x_3408_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6);
v___x_3409_ = l_Lean_MessageData_ofName(v_name_3407_);
v___x_3410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3410_, 0, v___x_3408_);
lean_ctor_set(v___x_3410_, 1, v___x_3409_);
v___x_3411_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_3412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3412_, 0, v___x_3410_);
lean_ctor_set(v___x_3412_, 1, v___x_3411_);
v___x_3413_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_3412_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_);
return v___x_3413_;
}
}
else
{
lean_object* v_a_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3451_; 
lean_dec(v_a_3379_);
lean_dec_ref(v_ctorVal_3369_);
v_a_3444_ = lean_ctor_get(v___x_3399_, 0);
v_isSharedCheck_3451_ = !lean_is_exclusive(v___x_3399_);
if (v_isSharedCheck_3451_ == 0)
{
v___x_3446_ = v___x_3399_;
v_isShared_3447_ = v_isSharedCheck_3451_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_a_3444_);
lean_dec(v___x_3399_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3451_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v___x_3449_; 
if (v_isShared_3447_ == 0)
{
v___x_3449_ = v___x_3446_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v_a_3444_);
v___x_3449_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
return v___x_3449_;
}
}
}
v___jp_3385_:
{
if (lean_obj_tag(v___y_3386_) == 0)
{
uint8_t v___x_3387_; lean_object* v___x_3388_; 
lean_dec_ref(v___y_3386_);
v___x_3387_ = 1;
v___x_3388_ = l_Lean_Meta_mkLambdaFVars(v_xs_3370_, v_a_3379_, v___x_3384_, v___x_3383_, v___x_3384_, v___x_3383_, v___x_3387_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
return v___x_3388_;
}
else
{
lean_object* v_a_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3396_; 
lean_dec(v_a_3379_);
v_a_3389_ = lean_ctor_get(v___y_3386_, 0);
v_isSharedCheck_3396_ = !lean_is_exclusive(v___y_3386_);
if (v_isSharedCheck_3396_ == 0)
{
v___x_3391_ = v___y_3386_;
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
else
{
lean_inc(v_a_3389_);
lean_dec(v___y_3386_);
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
}
else
{
lean_dec_ref(v_ctorVal_3369_);
return v___x_3378_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___boxed(lean_object* v_ctorVal_3452_, lean_object* v_xs_3453_, lean_object* v_type_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_){
_start:
{
lean_object* v_res_3460_; 
v_res_3460_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0(v_ctorVal_3452_, v_xs_3453_, v_type_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_);
lean_dec(v___y_3458_);
lean_dec_ref(v___y_3457_);
lean_dec(v___y_3456_);
lean_dec_ref(v___y_3455_);
lean_dec_ref(v_xs_3453_);
return v_res_3460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(lean_object* v_ctorVal_3461_, lean_object* v_targetType_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_, lean_object* v_a_3465_, lean_object* v_a_3466_){
_start:
{
lean_object* v___f_3468_; uint8_t v___x_3469_; lean_object* v___x_3470_; 
v___f_3468_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3468_, 0, v_ctorVal_3461_);
v___x_3469_ = 0;
v___x_3470_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_targetType_3462_, v___f_3468_, v___x_3469_, v___x_3469_, v_a_3463_, v_a_3464_, v_a_3465_, v_a_3466_);
return v___x_3470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___boxed(lean_object* v_ctorVal_3471_, lean_object* v_targetType_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_){
_start:
{
lean_object* v_res_3478_; 
v_res_3478_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3471_, v_targetType_3472_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_);
lean_dec(v_a_3476_);
lean_dec_ref(v_a_3475_);
lean_dec(v_a_3474_);
lean_dec_ref(v_a_3473_);
return v_res_3478_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0(lean_object* v_mvarId_3479_, lean_object* v_val_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_){
_start:
{
lean_object* v___x_3486_; 
v___x_3486_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(v_mvarId_3479_, v_val_3480_, v___y_3482_);
return v___x_3486_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___boxed(lean_object* v_mvarId_3487_, lean_object* v_val_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_){
_start:
{
lean_object* v_res_3494_; 
v_res_3494_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0(v_mvarId_3487_, v_val_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_);
lean_dec(v___y_3492_);
lean_dec_ref(v___y_3491_);
lean_dec(v___y_3490_);
lean_dec_ref(v___y_3489_);
return v_res_3494_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0(lean_object* v_00_u03b2_3495_, lean_object* v_x_3496_, lean_object* v_x_3497_, lean_object* v_x_3498_){
_start:
{
lean_object* v___x_3499_; 
v___x_3499_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(v_x_3496_, v_x_3497_, v_x_3498_);
return v___x_3499_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3500_, lean_object* v_x_3501_, size_t v_x_3502_, size_t v_x_3503_, lean_object* v_x_3504_, lean_object* v_x_3505_){
_start:
{
lean_object* v___x_3506_; 
v___x_3506_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_x_3501_, v_x_3502_, v_x_3503_, v_x_3504_, v_x_3505_);
return v___x_3506_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3507_, lean_object* v_x_3508_, lean_object* v_x_3509_, lean_object* v_x_3510_, lean_object* v_x_3511_, lean_object* v_x_3512_){
_start:
{
size_t v_x_5548__boxed_3513_; size_t v_x_5549__boxed_3514_; lean_object* v_res_3515_; 
v_x_5548__boxed_3513_ = lean_unbox_usize(v_x_3509_);
lean_dec(v_x_3509_);
v_x_5549__boxed_3514_ = lean_unbox_usize(v_x_3510_);
lean_dec(v_x_3510_);
v_res_3515_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1(v_00_u03b2_3507_, v_x_3508_, v_x_5548__boxed_3513_, v_x_5549__boxed_3514_, v_x_3511_, v_x_3512_);
return v_res_3515_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_3516_, lean_object* v_n_3517_, lean_object* v_k_3518_, lean_object* v_v_3519_){
_start:
{
lean_object* v___x_3520_; 
v___x_3520_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(v_n_3517_, v_k_3518_, v_v_3519_);
return v___x_3520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_3521_, size_t v_depth_3522_, lean_object* v_keys_3523_, lean_object* v_vals_3524_, lean_object* v_heq_3525_, lean_object* v_i_3526_, lean_object* v_entries_3527_){
_start:
{
lean_object* v___x_3528_; 
v___x_3528_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_3522_, v_keys_3523_, v_vals_3524_, v_i_3526_, v_entries_3527_);
return v___x_3528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_3529_, lean_object* v_depth_3530_, lean_object* v_keys_3531_, lean_object* v_vals_3532_, lean_object* v_heq_3533_, lean_object* v_i_3534_, lean_object* v_entries_3535_){
_start:
{
size_t v_depth_boxed_3536_; lean_object* v_res_3537_; 
v_depth_boxed_3536_ = lean_unbox_usize(v_depth_3530_);
lean_dec(v_depth_3530_);
v_res_3537_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_3529_, v_depth_boxed_3536_, v_keys_3531_, v_vals_3532_, v_heq_3533_, v_i_3534_, v_entries_3535_);
lean_dec_ref(v_vals_3532_);
lean_dec_ref(v_keys_3531_);
return v_res_3537_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_3538_, lean_object* v_x_3539_, lean_object* v_x_3540_, lean_object* v_x_3541_, lean_object* v_x_3542_){
_start:
{
lean_object* v___x_3543_; 
v___x_3543_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_x_3539_, v_x_3540_, v_x_3541_, v_x_3542_);
return v___x_3543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(lean_object* v_ctorVal_3544_, lean_object* v_val_3545_, lean_object* v_name_3546_, lean_object* v_levelParams_3547_, uint8_t v___x_3548_, uint8_t v_hasTrace_3549_, lean_object* v_____r_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_){
_start:
{
lean_object* v___x_3556_; 
lean_inc_ref(v_val_3545_);
v___x_3556_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3544_, v_val_3545_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_);
if (lean_obj_tag(v___x_3556_) == 0)
{
lean_object* v_a_3557_; lean_object* v___x_3558_; lean_object* v_a_3559_; lean_object* v___x_3560_; lean_object* v_a_3561_; lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3577_; 
v_a_3557_ = lean_ctor_get(v___x_3556_, 0);
lean_inc(v_a_3557_);
lean_dec_ref(v___x_3556_);
v___x_3558_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3545_, v___y_3552_);
v_a_3559_ = lean_ctor_get(v___x_3558_, 0);
lean_inc(v_a_3559_);
lean_dec_ref(v___x_3558_);
v___x_3560_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3557_, v___y_3552_);
v_a_3561_ = lean_ctor_get(v___x_3560_, 0);
v_isSharedCheck_3577_ = !lean_is_exclusive(v___x_3560_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3563_ = v___x_3560_;
v_isShared_3564_ = v_isSharedCheck_3577_;
goto v_resetjp_3562_;
}
else
{
lean_inc(v_a_3561_);
lean_dec(v___x_3560_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3577_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3570_; 
lean_inc_n(v_name_3546_, 2);
v___x_3565_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3565_, 0, v_name_3546_);
lean_ctor_set(v___x_3565_, 1, v_levelParams_3547_);
lean_ctor_set(v___x_3565_, 2, v_a_3559_);
v___x_3566_ = lean_box(0);
v___x_3567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3567_, 0, v_name_3546_);
lean_ctor_set(v___x_3567_, 1, v___x_3566_);
v___x_3568_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3568_, 0, v___x_3565_);
lean_ctor_set(v___x_3568_, 1, v_a_3561_);
lean_ctor_set(v___x_3568_, 2, v___x_3567_);
if (v_isShared_3564_ == 0)
{
lean_ctor_set_tag(v___x_3563_, 2);
lean_ctor_set(v___x_3563_, 0, v___x_3568_);
v___x_3570_ = v___x_3563_;
goto v_reusejp_3569_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v___x_3568_);
v___x_3570_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3569_;
}
v_reusejp_3569_:
{
lean_object* v___x_3571_; 
v___x_3571_ = l_Lean_addDecl(v___x_3570_, v___x_3548_, v___y_3553_, v___y_3554_);
if (lean_obj_tag(v___x_3571_) == 0)
{
lean_object* v___x_3572_; uint8_t v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; 
lean_dec_ref(v___x_3571_);
v___x_3572_ = l_Lean_Meta_simpExtension;
v___x_3573_ = 0;
v___x_3574_ = lean_unsigned_to_nat(1000u);
v___x_3575_ = l_Lean_Meta_addSimpTheorem(v___x_3572_, v_name_3546_, v_hasTrace_3549_, v___x_3548_, v___x_3573_, v___x_3574_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_);
return v___x_3575_;
}
else
{
lean_dec(v_name_3546_);
return v___x_3571_;
}
}
}
}
else
{
lean_object* v_a_3578_; lean_object* v___x_3580_; uint8_t v_isShared_3581_; uint8_t v_isSharedCheck_3585_; 
lean_dec(v_levelParams_3547_);
lean_dec(v_name_3546_);
lean_dec_ref(v_val_3545_);
v_a_3578_ = lean_ctor_get(v___x_3556_, 0);
v_isSharedCheck_3585_ = !lean_is_exclusive(v___x_3556_);
if (v_isSharedCheck_3585_ == 0)
{
v___x_3580_ = v___x_3556_;
v_isShared_3581_ = v_isSharedCheck_3585_;
goto v_resetjp_3579_;
}
else
{
lean_inc(v_a_3578_);
lean_dec(v___x_3556_);
v___x_3580_ = lean_box(0);
v_isShared_3581_ = v_isSharedCheck_3585_;
goto v_resetjp_3579_;
}
v_resetjp_3579_:
{
lean_object* v___x_3583_; 
if (v_isShared_3581_ == 0)
{
v___x_3583_ = v___x_3580_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v_a_3578_);
v___x_3583_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
return v___x_3583_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1___boxed(lean_object* v_ctorVal_3586_, lean_object* v_val_3587_, lean_object* v_name_3588_, lean_object* v_levelParams_3589_, lean_object* v___x_3590_, lean_object* v_hasTrace_3591_, lean_object* v_____r_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_){
_start:
{
uint8_t v___x_9094__boxed_3598_; uint8_t v_hasTrace_boxed_3599_; lean_object* v_res_3600_; 
v___x_9094__boxed_3598_ = lean_unbox(v___x_3590_);
v_hasTrace_boxed_3599_ = lean_unbox(v_hasTrace_3591_);
v_res_3600_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(v_ctorVal_3586_, v_val_3587_, v_name_3588_, v_levelParams_3589_, v___x_9094__boxed_3598_, v_hasTrace_boxed_3599_, v_____r_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_);
lean_dec(v___y_3596_);
lean_dec_ref(v___y_3595_);
lean_dec(v___y_3594_);
lean_dec_ref(v___y_3593_);
return v_res_3600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(lean_object* v_ctorVal_3601_, lean_object* v_val_3602_, lean_object* v_name_3603_, lean_object* v_levelParams_3604_, uint8_t v___x_3605_, lean_object* v_____r_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_){
_start:
{
lean_object* v___x_3612_; 
lean_inc_ref(v_val_3602_);
v___x_3612_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3601_, v_val_3602_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_);
if (lean_obj_tag(v___x_3612_) == 0)
{
lean_object* v_a_3613_; lean_object* v___x_3614_; lean_object* v_a_3615_; lean_object* v___x_3616_; lean_object* v_a_3617_; lean_object* v___x_3619_; uint8_t v_isShared_3620_; uint8_t v_isSharedCheck_3634_; 
v_a_3613_ = lean_ctor_get(v___x_3612_, 0);
lean_inc(v_a_3613_);
lean_dec_ref(v___x_3612_);
v___x_3614_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3602_, v___y_3608_);
v_a_3615_ = lean_ctor_get(v___x_3614_, 0);
lean_inc(v_a_3615_);
lean_dec_ref(v___x_3614_);
v___x_3616_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3613_, v___y_3608_);
v_a_3617_ = lean_ctor_get(v___x_3616_, 0);
v_isSharedCheck_3634_ = !lean_is_exclusive(v___x_3616_);
if (v_isSharedCheck_3634_ == 0)
{
v___x_3619_ = v___x_3616_;
v_isShared_3620_ = v_isSharedCheck_3634_;
goto v_resetjp_3618_;
}
else
{
lean_inc(v_a_3617_);
lean_dec(v___x_3616_);
v___x_3619_ = lean_box(0);
v_isShared_3620_ = v_isSharedCheck_3634_;
goto v_resetjp_3618_;
}
v_resetjp_3618_:
{
lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3626_; 
lean_inc_n(v_name_3603_, 2);
v___x_3621_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3621_, 0, v_name_3603_);
lean_ctor_set(v___x_3621_, 1, v_levelParams_3604_);
lean_ctor_set(v___x_3621_, 2, v_a_3615_);
v___x_3622_ = lean_box(0);
v___x_3623_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3623_, 0, v_name_3603_);
lean_ctor_set(v___x_3623_, 1, v___x_3622_);
v___x_3624_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3624_, 0, v___x_3621_);
lean_ctor_set(v___x_3624_, 1, v_a_3617_);
lean_ctor_set(v___x_3624_, 2, v___x_3623_);
if (v_isShared_3620_ == 0)
{
lean_ctor_set_tag(v___x_3619_, 2);
lean_ctor_set(v___x_3619_, 0, v___x_3624_);
v___x_3626_ = v___x_3619_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v___x_3624_);
v___x_3626_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3625_;
}
v_reusejp_3625_:
{
uint8_t v___x_3627_; lean_object* v___x_3628_; 
v___x_3627_ = 0;
v___x_3628_ = l_Lean_addDecl(v___x_3626_, v___x_3627_, v___y_3609_, v___y_3610_);
if (lean_obj_tag(v___x_3628_) == 0)
{
lean_object* v___x_3629_; uint8_t v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; 
lean_dec_ref(v___x_3628_);
v___x_3629_ = l_Lean_Meta_simpExtension;
v___x_3630_ = 0;
v___x_3631_ = lean_unsigned_to_nat(1000u);
v___x_3632_ = l_Lean_Meta_addSimpTheorem(v___x_3629_, v_name_3603_, v___x_3605_, v___x_3627_, v___x_3630_, v___x_3631_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_);
return v___x_3632_;
}
else
{
lean_dec(v_name_3603_);
return v___x_3628_;
}
}
}
}
else
{
lean_object* v_a_3635_; lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3642_; 
lean_dec(v_levelParams_3604_);
lean_dec(v_name_3603_);
lean_dec_ref(v_val_3602_);
v_a_3635_ = lean_ctor_get(v___x_3612_, 0);
v_isSharedCheck_3642_ = !lean_is_exclusive(v___x_3612_);
if (v_isSharedCheck_3642_ == 0)
{
v___x_3637_ = v___x_3612_;
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
else
{
lean_inc(v_a_3635_);
lean_dec(v___x_3612_);
v___x_3637_ = lean_box(0);
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
v_resetjp_3636_:
{
lean_object* v___x_3640_; 
if (v_isShared_3638_ == 0)
{
v___x_3640_ = v___x_3637_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3641_; 
v_reuseFailAlloc_3641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3641_, 0, v_a_3635_);
v___x_3640_ = v_reuseFailAlloc_3641_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
return v___x_3640_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0___boxed(lean_object* v_ctorVal_3643_, lean_object* v_val_3644_, lean_object* v_name_3645_, lean_object* v_levelParams_3646_, lean_object* v___x_3647_, lean_object* v_____r_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_){
_start:
{
uint8_t v___x_9182__boxed_3654_; lean_object* v_res_3655_; 
v___x_9182__boxed_3654_ = lean_unbox(v___x_3647_);
v_res_3655_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(v_ctorVal_3643_, v_val_3644_, v_name_3645_, v_levelParams_3646_, v___x_9182__boxed_3654_, v_____r_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec(v___y_3650_);
lean_dec_ref(v___y_3649_);
return v_res_3655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(lean_object* v_ctorVal_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_){
_start:
{
lean_object* v_toConstantVal_3662_; lean_object* v_options_3663_; lean_object* v_name_3664_; lean_object* v_levelParams_3665_; lean_object* v___x_3667_; uint8_t v_isShared_3668_; uint8_t v_isSharedCheck_3885_; 
v_toConstantVal_3662_ = lean_ctor_get(v_ctorVal_3656_, 0);
lean_inc_ref(v_toConstantVal_3662_);
v_options_3663_ = lean_ctor_get(v_a_3659_, 2);
v_name_3664_ = lean_ctor_get(v_toConstantVal_3662_, 0);
v_levelParams_3665_ = lean_ctor_get(v_toConstantVal_3662_, 1);
v_isSharedCheck_3885_ = !lean_is_exclusive(v_toConstantVal_3662_);
if (v_isSharedCheck_3885_ == 0)
{
lean_object* v_unused_3886_; 
v_unused_3886_ = lean_ctor_get(v_toConstantVal_3662_, 2);
lean_dec(v_unused_3886_);
v___x_3667_ = v_toConstantVal_3662_;
v_isShared_3668_ = v_isSharedCheck_3885_;
goto v_resetjp_3666_;
}
else
{
lean_inc(v_levelParams_3665_);
lean_inc(v_name_3664_);
lean_dec(v_toConstantVal_3662_);
v___x_3667_ = lean_box(0);
v_isShared_3668_ = v_isSharedCheck_3885_;
goto v_resetjp_3666_;
}
v_resetjp_3666_:
{
lean_object* v_inheritedTraceOptions_3669_; uint8_t v_hasTrace_3670_; lean_object* v_name_3671_; 
v_inheritedTraceOptions_3669_ = lean_ctor_get(v_a_3659_, 13);
v_hasTrace_3670_ = lean_ctor_get_uint8(v_options_3663_, sizeof(void*)*1);
v_name_3671_ = l_Lean_Meta_mkInjectiveEqTheoremNameFor(v_name_3664_);
if (v_hasTrace_3670_ == 0)
{
lean_object* v___x_3672_; 
lean_inc_ref(v_ctorVal_3656_);
v___x_3672_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
if (lean_obj_tag(v___x_3672_) == 0)
{
lean_object* v_a_3673_; lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3715_; 
v_a_3673_ = lean_ctor_get(v___x_3672_, 0);
v_isSharedCheck_3715_ = !lean_is_exclusive(v___x_3672_);
if (v_isSharedCheck_3715_ == 0)
{
v___x_3675_ = v___x_3672_;
v_isShared_3676_ = v_isSharedCheck_3715_;
goto v_resetjp_3674_;
}
else
{
lean_inc(v_a_3673_);
lean_dec(v___x_3672_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_3715_;
goto v_resetjp_3674_;
}
v_resetjp_3674_:
{
if (lean_obj_tag(v_a_3673_) == 1)
{
lean_object* v_val_3677_; lean_object* v___x_3678_; 
lean_del_object(v___x_3675_);
v_val_3677_ = lean_ctor_get(v_a_3673_, 0);
lean_inc_n(v_val_3677_, 2);
lean_dec_ref(v_a_3673_);
v___x_3678_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3656_, v_val_3677_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
if (lean_obj_tag(v___x_3678_) == 0)
{
lean_object* v_a_3679_; lean_object* v___x_3680_; lean_object* v_a_3681_; lean_object* v___x_3682_; lean_object* v_a_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3702_; 
v_a_3679_ = lean_ctor_get(v___x_3678_, 0);
lean_inc(v_a_3679_);
lean_dec_ref(v___x_3678_);
v___x_3680_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3677_, v_a_3658_);
v_a_3681_ = lean_ctor_get(v___x_3680_, 0);
lean_inc(v_a_3681_);
lean_dec_ref(v___x_3680_);
v___x_3682_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3679_, v_a_3658_);
v_a_3683_ = lean_ctor_get(v___x_3682_, 0);
v_isSharedCheck_3702_ = !lean_is_exclusive(v___x_3682_);
if (v_isSharedCheck_3702_ == 0)
{
v___x_3685_ = v___x_3682_;
v_isShared_3686_ = v_isSharedCheck_3702_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_a_3683_);
lean_dec(v___x_3682_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3702_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
lean_object* v___x_3688_; 
lean_inc(v_name_3671_);
if (v_isShared_3668_ == 0)
{
lean_ctor_set(v___x_3667_, 2, v_a_3681_);
lean_ctor_set(v___x_3667_, 0, v_name_3671_);
v___x_3688_ = v___x_3667_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v_name_3671_);
lean_ctor_set(v_reuseFailAlloc_3701_, 1, v_levelParams_3665_);
lean_ctor_set(v_reuseFailAlloc_3701_, 2, v_a_3681_);
v___x_3688_ = v_reuseFailAlloc_3701_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3693_; 
v___x_3689_ = lean_box(0);
lean_inc(v_name_3671_);
v___x_3690_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3690_, 0, v_name_3671_);
lean_ctor_set(v___x_3690_, 1, v___x_3689_);
v___x_3691_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3691_, 0, v___x_3688_);
lean_ctor_set(v___x_3691_, 1, v_a_3683_);
lean_ctor_set(v___x_3691_, 2, v___x_3690_);
if (v_isShared_3686_ == 0)
{
lean_ctor_set_tag(v___x_3685_, 2);
lean_ctor_set(v___x_3685_, 0, v___x_3691_);
v___x_3693_ = v___x_3685_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v___x_3691_);
v___x_3693_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
lean_object* v___x_3694_; 
v___x_3694_ = l_Lean_addDecl(v___x_3693_, v_hasTrace_3670_, v_a_3659_, v_a_3660_);
if (lean_obj_tag(v___x_3694_) == 0)
{
lean_object* v___x_3695_; uint8_t v___x_3696_; uint8_t v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; 
lean_dec_ref(v___x_3694_);
v___x_3695_ = l_Lean_Meta_simpExtension;
v___x_3696_ = 1;
v___x_3697_ = 0;
v___x_3698_ = lean_unsigned_to_nat(1000u);
v___x_3699_ = l_Lean_Meta_addSimpTheorem(v___x_3695_, v_name_3671_, v___x_3696_, v_hasTrace_3670_, v___x_3697_, v___x_3698_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
return v___x_3699_;
}
else
{
lean_dec(v_name_3671_);
return v___x_3694_;
}
}
}
}
}
else
{
lean_object* v_a_3703_; lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3710_; 
lean_dec(v_val_3677_);
lean_dec(v_name_3671_);
lean_del_object(v___x_3667_);
lean_dec(v_levelParams_3665_);
v_a_3703_ = lean_ctor_get(v___x_3678_, 0);
v_isSharedCheck_3710_ = !lean_is_exclusive(v___x_3678_);
if (v_isSharedCheck_3710_ == 0)
{
v___x_3705_ = v___x_3678_;
v_isShared_3706_ = v_isSharedCheck_3710_;
goto v_resetjp_3704_;
}
else
{
lean_inc(v_a_3703_);
lean_dec(v___x_3678_);
v___x_3705_ = lean_box(0);
v_isShared_3706_ = v_isSharedCheck_3710_;
goto v_resetjp_3704_;
}
v_resetjp_3704_:
{
lean_object* v___x_3708_; 
if (v_isShared_3706_ == 0)
{
v___x_3708_ = v___x_3705_;
goto v_reusejp_3707_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v_a_3703_);
v___x_3708_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3707_;
}
v_reusejp_3707_:
{
return v___x_3708_;
}
}
}
}
else
{
lean_object* v___x_3711_; lean_object* v___x_3713_; 
lean_dec(v_a_3673_);
lean_dec(v_name_3671_);
lean_del_object(v___x_3667_);
lean_dec(v_levelParams_3665_);
lean_dec_ref(v_ctorVal_3656_);
v___x_3711_ = lean_box(0);
if (v_isShared_3676_ == 0)
{
lean_ctor_set(v___x_3675_, 0, v___x_3711_);
v___x_3713_ = v___x_3675_;
goto v_reusejp_3712_;
}
else
{
lean_object* v_reuseFailAlloc_3714_; 
v_reuseFailAlloc_3714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3714_, 0, v___x_3711_);
v___x_3713_ = v_reuseFailAlloc_3714_;
goto v_reusejp_3712_;
}
v_reusejp_3712_:
{
return v___x_3713_;
}
}
}
}
else
{
lean_object* v_a_3716_; lean_object* v___x_3718_; uint8_t v_isShared_3719_; uint8_t v_isSharedCheck_3723_; 
lean_dec(v_name_3671_);
lean_del_object(v___x_3667_);
lean_dec(v_levelParams_3665_);
lean_dec_ref(v_ctorVal_3656_);
v_a_3716_ = lean_ctor_get(v___x_3672_, 0);
v_isSharedCheck_3723_ = !lean_is_exclusive(v___x_3672_);
if (v_isSharedCheck_3723_ == 0)
{
v___x_3718_ = v___x_3672_;
v_isShared_3719_ = v_isSharedCheck_3723_;
goto v_resetjp_3717_;
}
else
{
lean_inc(v_a_3716_);
lean_dec(v___x_3672_);
v___x_3718_ = lean_box(0);
v_isShared_3719_ = v_isSharedCheck_3723_;
goto v_resetjp_3717_;
}
v_resetjp_3717_:
{
lean_object* v___x_3721_; 
if (v_isShared_3719_ == 0)
{
v___x_3721_ = v___x_3718_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3722_; 
v_reuseFailAlloc_3722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3722_, 0, v_a_3716_);
v___x_3721_ = v_reuseFailAlloc_3722_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
return v___x_3721_;
}
}
}
}
else
{
lean_object* v___f_3724_; lean_object* v_cls_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; uint8_t v___x_3728_; lean_object* v___y_3730_; lean_object* v___y_3731_; lean_object* v_a_3732_; lean_object* v___y_3742_; lean_object* v___y_3743_; lean_object* v_a_3744_; lean_object* v___y_3747_; lean_object* v___y_3748_; lean_object* v_a_3749_; lean_object* v___y_3752_; lean_object* v___y_3753_; lean_object* v___y_3754_; lean_object* v___y_3758_; lean_object* v___y_3759_; lean_object* v_a_3760_; lean_object* v___y_3773_; lean_object* v___y_3774_; lean_object* v_a_3775_; lean_object* v___y_3778_; lean_object* v___y_3779_; lean_object* v_a_3780_; lean_object* v___y_3783_; lean_object* v___y_3784_; lean_object* v___y_3785_; 
lean_inc(v_name_3671_);
v___f_3724_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3724_, 0, v_name_3671_);
v_cls_3725_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_3726_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_3727_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_3728_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3669_, v_options_3663_, v___x_3727_);
if (v___x_3728_ == 0)
{
lean_object* v___x_3823_; uint8_t v___x_3824_; 
v___x_3823_ = l_Lean_trace_profiler;
v___x_3824_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_3663_, v___x_3823_);
if (v___x_3824_ == 0)
{
lean_object* v___x_3825_; 
lean_dec_ref(v___f_3724_);
lean_inc_ref(v_ctorVal_3656_);
v___x_3825_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
if (lean_obj_tag(v___x_3825_) == 0)
{
lean_object* v_a_3826_; lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3876_; 
v_a_3826_ = lean_ctor_get(v___x_3825_, 0);
v_isSharedCheck_3876_ = !lean_is_exclusive(v___x_3825_);
if (v_isSharedCheck_3876_ == 0)
{
v___x_3828_ = v___x_3825_;
v_isShared_3829_ = v_isSharedCheck_3876_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_a_3826_);
lean_dec(v___x_3825_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_3876_;
goto v_resetjp_3827_;
}
v_resetjp_3827_:
{
if (lean_obj_tag(v_a_3826_) == 1)
{
lean_object* v_val_3830_; lean_object* v___y_3832_; lean_object* v___y_3833_; lean_object* v___y_3834_; lean_object* v___y_3835_; 
lean_del_object(v___x_3828_);
v_val_3830_ = lean_ctor_get(v_a_3826_, 0);
lean_inc(v_val_3830_);
lean_dec_ref(v_a_3826_);
if (v___x_3728_ == 0)
{
v___y_3832_ = v_a_3657_;
v___y_3833_ = v_a_3658_;
v___y_3834_ = v_a_3659_;
v___y_3835_ = v_a_3660_;
goto v___jp_3831_;
}
else
{
lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; 
v___x_3868_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
lean_inc(v_val_3830_);
v___x_3869_ = l_Lean_MessageData_ofExpr(v_val_3830_);
v___x_3870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3870_, 0, v___x_3868_);
lean_ctor_set(v___x_3870_, 1, v___x_3869_);
v___x_3871_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_3725_, v___x_3870_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
if (lean_obj_tag(v___x_3871_) == 0)
{
lean_dec_ref(v___x_3871_);
v___y_3832_ = v_a_3657_;
v___y_3833_ = v_a_3658_;
v___y_3834_ = v_a_3659_;
v___y_3835_ = v_a_3660_;
goto v___jp_3831_;
}
else
{
lean_dec(v_val_3830_);
lean_dec(v_name_3671_);
lean_del_object(v___x_3667_);
lean_dec(v_levelParams_3665_);
lean_dec_ref(v_ctorVal_3656_);
return v___x_3871_;
}
}
v___jp_3831_:
{
lean_object* v___x_3836_; 
lean_inc(v_val_3830_);
v___x_3836_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3656_, v_val_3830_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_);
if (lean_obj_tag(v___x_3836_) == 0)
{
lean_object* v_a_3837_; lean_object* v___x_3838_; lean_object* v_a_3839_; lean_object* v___x_3840_; lean_object* v_a_3841_; lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3859_; 
v_a_3837_ = lean_ctor_get(v___x_3836_, 0);
lean_inc(v_a_3837_);
lean_dec_ref(v___x_3836_);
v___x_3838_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3830_, v___y_3833_);
v_a_3839_ = lean_ctor_get(v___x_3838_, 0);
lean_inc(v_a_3839_);
lean_dec_ref(v___x_3838_);
v___x_3840_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3837_, v___y_3833_);
v_a_3841_ = lean_ctor_get(v___x_3840_, 0);
v_isSharedCheck_3859_ = !lean_is_exclusive(v___x_3840_);
if (v_isSharedCheck_3859_ == 0)
{
v___x_3843_ = v___x_3840_;
v_isShared_3844_ = v_isSharedCheck_3859_;
goto v_resetjp_3842_;
}
else
{
lean_inc(v_a_3841_);
lean_dec(v___x_3840_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3859_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
lean_object* v___x_3846_; 
lean_inc(v_name_3671_);
if (v_isShared_3668_ == 0)
{
lean_ctor_set(v___x_3667_, 2, v_a_3839_);
lean_ctor_set(v___x_3667_, 0, v_name_3671_);
v___x_3846_ = v___x_3667_;
goto v_reusejp_3845_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v_name_3671_);
lean_ctor_set(v_reuseFailAlloc_3858_, 1, v_levelParams_3665_);
lean_ctor_set(v_reuseFailAlloc_3858_, 2, v_a_3839_);
v___x_3846_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3845_;
}
v_reusejp_3845_:
{
lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3851_; 
v___x_3847_ = lean_box(0);
lean_inc(v_name_3671_);
v___x_3848_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3848_, 0, v_name_3671_);
lean_ctor_set(v___x_3848_, 1, v___x_3847_);
v___x_3849_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3849_, 0, v___x_3846_);
lean_ctor_set(v___x_3849_, 1, v_a_3841_);
lean_ctor_set(v___x_3849_, 2, v___x_3848_);
if (v_isShared_3844_ == 0)
{
lean_ctor_set_tag(v___x_3843_, 2);
lean_ctor_set(v___x_3843_, 0, v___x_3849_);
v___x_3851_ = v___x_3843_;
goto v_reusejp_3850_;
}
else
{
lean_object* v_reuseFailAlloc_3857_; 
v_reuseFailAlloc_3857_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3857_, 0, v___x_3849_);
v___x_3851_ = v_reuseFailAlloc_3857_;
goto v_reusejp_3850_;
}
v_reusejp_3850_:
{
lean_object* v___x_3852_; 
v___x_3852_ = l_Lean_addDecl(v___x_3851_, v___x_3824_, v___y_3834_, v___y_3835_);
if (lean_obj_tag(v___x_3852_) == 0)
{
lean_object* v___x_3853_; uint8_t v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; 
lean_dec_ref(v___x_3852_);
v___x_3853_ = l_Lean_Meta_simpExtension;
v___x_3854_ = 0;
v___x_3855_ = lean_unsigned_to_nat(1000u);
v___x_3856_ = l_Lean_Meta_addSimpTheorem(v___x_3853_, v_name_3671_, v_hasTrace_3670_, v___x_3824_, v___x_3854_, v___x_3855_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_);
return v___x_3856_;
}
else
{
lean_dec(v_name_3671_);
return v___x_3852_;
}
}
}
}
}
else
{
lean_object* v_a_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3867_; 
lean_dec(v_val_3830_);
lean_dec(v_name_3671_);
lean_del_object(v___x_3667_);
lean_dec(v_levelParams_3665_);
v_a_3860_ = lean_ctor_get(v___x_3836_, 0);
v_isSharedCheck_3867_ = !lean_is_exclusive(v___x_3836_);
if (v_isSharedCheck_3867_ == 0)
{
v___x_3862_ = v___x_3836_;
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_a_3860_);
lean_dec(v___x_3836_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
v_resetjp_3861_:
{
lean_object* v___x_3865_; 
if (v_isShared_3863_ == 0)
{
v___x_3865_ = v___x_3862_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v_a_3860_);
v___x_3865_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
return v___x_3865_;
}
}
}
}
}
else
{
lean_object* v___x_3872_; lean_object* v___x_3874_; 
lean_dec(v_a_3826_);
lean_dec(v_name_3671_);
lean_del_object(v___x_3667_);
lean_dec(v_levelParams_3665_);
lean_dec_ref(v_ctorVal_3656_);
v___x_3872_ = lean_box(0);
if (v_isShared_3829_ == 0)
{
lean_ctor_set(v___x_3828_, 0, v___x_3872_);
v___x_3874_ = v___x_3828_;
goto v_reusejp_3873_;
}
else
{
lean_object* v_reuseFailAlloc_3875_; 
v_reuseFailAlloc_3875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3875_, 0, v___x_3872_);
v___x_3874_ = v_reuseFailAlloc_3875_;
goto v_reusejp_3873_;
}
v_reusejp_3873_:
{
return v___x_3874_;
}
}
}
}
else
{
lean_object* v_a_3877_; lean_object* v___x_3879_; uint8_t v_isShared_3880_; uint8_t v_isSharedCheck_3884_; 
lean_dec(v_name_3671_);
lean_del_object(v___x_3667_);
lean_dec(v_levelParams_3665_);
lean_dec_ref(v_ctorVal_3656_);
v_a_3877_ = lean_ctor_get(v___x_3825_, 0);
v_isSharedCheck_3884_ = !lean_is_exclusive(v___x_3825_);
if (v_isSharedCheck_3884_ == 0)
{
v___x_3879_ = v___x_3825_;
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
else
{
lean_inc(v_a_3877_);
lean_dec(v___x_3825_);
v___x_3879_ = lean_box(0);
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
v_resetjp_3878_:
{
lean_object* v___x_3882_; 
if (v_isShared_3880_ == 0)
{
v___x_3882_ = v___x_3879_;
goto v_reusejp_3881_;
}
else
{
lean_object* v_reuseFailAlloc_3883_; 
v_reuseFailAlloc_3883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3883_, 0, v_a_3877_);
v___x_3882_ = v_reuseFailAlloc_3883_;
goto v_reusejp_3881_;
}
v_reusejp_3881_:
{
return v___x_3882_;
}
}
}
}
else
{
lean_del_object(v___x_3667_);
goto v___jp_3788_;
}
}
else
{
lean_del_object(v___x_3667_);
goto v___jp_3788_;
}
v___jp_3729_:
{
lean_object* v___x_3733_; double v___x_3734_; double v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; 
v___x_3733_ = lean_io_get_num_heartbeats();
v___x_3734_ = lean_float_of_nat(v___y_3731_);
v___x_3735_ = lean_float_of_nat(v___x_3733_);
v___x_3736_ = lean_box_float(v___x_3734_);
v___x_3737_ = lean_box_float(v___x_3735_);
v___x_3738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3738_, 0, v___x_3736_);
lean_ctor_set(v___x_3738_, 1, v___x_3737_);
v___x_3739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3739_, 0, v_a_3732_);
lean_ctor_set(v___x_3739_, 1, v___x_3738_);
v___x_3740_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_3725_, v_hasTrace_3670_, v___x_3726_, v_options_3663_, v___x_3728_, v___y_3730_, v___f_3724_, v___x_3739_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
return v___x_3740_;
}
v___jp_3741_:
{
lean_object* v___x_3745_; 
v___x_3745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3745_, 0, v_a_3744_);
v___y_3730_ = v___y_3742_;
v___y_3731_ = v___y_3743_;
v_a_3732_ = v___x_3745_;
goto v___jp_3729_;
}
v___jp_3746_:
{
lean_object* v___x_3750_; 
v___x_3750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3750_, 0, v_a_3749_);
v___y_3730_ = v___y_3747_;
v___y_3731_ = v___y_3748_;
v_a_3732_ = v___x_3750_;
goto v___jp_3729_;
}
v___jp_3751_:
{
if (lean_obj_tag(v___y_3754_) == 0)
{
lean_object* v_a_3755_; 
v_a_3755_ = lean_ctor_get(v___y_3754_, 0);
lean_inc(v_a_3755_);
lean_dec_ref(v___y_3754_);
v___y_3747_ = v___y_3752_;
v___y_3748_ = v___y_3753_;
v_a_3749_ = v_a_3755_;
goto v___jp_3746_;
}
else
{
lean_object* v_a_3756_; 
v_a_3756_ = lean_ctor_get(v___y_3754_, 0);
lean_inc(v_a_3756_);
lean_dec_ref(v___y_3754_);
v___y_3742_ = v___y_3752_;
v___y_3743_ = v___y_3753_;
v_a_3744_ = v_a_3756_;
goto v___jp_3741_;
}
}
v___jp_3757_:
{
lean_object* v___x_3761_; double v___x_3762_; double v___x_3763_; double v___x_3764_; double v___x_3765_; double v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; 
v___x_3761_ = lean_io_mono_nanos_now();
v___x_3762_ = lean_float_of_nat(v___y_3758_);
v___x_3763_ = lean_float_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0);
v___x_3764_ = lean_float_div(v___x_3762_, v___x_3763_);
v___x_3765_ = lean_float_of_nat(v___x_3761_);
v___x_3766_ = lean_float_div(v___x_3765_, v___x_3763_);
v___x_3767_ = lean_box_float(v___x_3764_);
v___x_3768_ = lean_box_float(v___x_3766_);
v___x_3769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3769_, 0, v___x_3767_);
lean_ctor_set(v___x_3769_, 1, v___x_3768_);
v___x_3770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3770_, 0, v_a_3760_);
lean_ctor_set(v___x_3770_, 1, v___x_3769_);
v___x_3771_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_3725_, v_hasTrace_3670_, v___x_3726_, v_options_3663_, v___x_3728_, v___y_3759_, v___f_3724_, v___x_3770_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
return v___x_3771_;
}
v___jp_3772_:
{
lean_object* v___x_3776_; 
v___x_3776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3776_, 0, v_a_3775_);
v___y_3758_ = v___y_3773_;
v___y_3759_ = v___y_3774_;
v_a_3760_ = v___x_3776_;
goto v___jp_3757_;
}
v___jp_3777_:
{
lean_object* v___x_3781_; 
v___x_3781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3781_, 0, v_a_3780_);
v___y_3758_ = v___y_3778_;
v___y_3759_ = v___y_3779_;
v_a_3760_ = v___x_3781_;
goto v___jp_3757_;
}
v___jp_3782_:
{
if (lean_obj_tag(v___y_3785_) == 0)
{
lean_object* v_a_3786_; 
v_a_3786_ = lean_ctor_get(v___y_3785_, 0);
lean_inc(v_a_3786_);
lean_dec_ref(v___y_3785_);
v___y_3773_ = v___y_3783_;
v___y_3774_ = v___y_3784_;
v_a_3775_ = v_a_3786_;
goto v___jp_3772_;
}
else
{
lean_object* v_a_3787_; 
v_a_3787_ = lean_ctor_get(v___y_3785_, 0);
lean_inc(v_a_3787_);
lean_dec_ref(v___y_3785_);
v___y_3778_ = v___y_3783_;
v___y_3779_ = v___y_3784_;
v_a_3780_ = v_a_3787_;
goto v___jp_3777_;
}
}
v___jp_3788_:
{
lean_object* v___x_3789_; lean_object* v_a_3790_; lean_object* v___x_3791_; uint8_t v___x_3792_; 
v___x_3789_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v_a_3660_);
v_a_3790_ = lean_ctor_get(v___x_3789_, 0);
lean_inc(v_a_3790_);
lean_dec_ref(v___x_3789_);
v___x_3791_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3792_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_3663_, v___x_3791_);
if (v___x_3792_ == 0)
{
lean_object* v___x_3793_; lean_object* v___x_3794_; 
v___x_3793_ = lean_io_mono_nanos_now();
lean_inc_ref(v_ctorVal_3656_);
v___x_3794_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
if (lean_obj_tag(v___x_3794_) == 0)
{
lean_object* v_a_3795_; 
v_a_3795_ = lean_ctor_get(v___x_3794_, 0);
lean_inc(v_a_3795_);
lean_dec_ref(v___x_3794_);
if (lean_obj_tag(v_a_3795_) == 1)
{
if (v___x_3728_ == 0)
{
lean_object* v_val_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; 
v_val_3796_ = lean_ctor_get(v_a_3795_, 0);
lean_inc(v_val_3796_);
lean_dec_ref(v_a_3795_);
v___x_3797_ = lean_box(0);
v___x_3798_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(v_ctorVal_3656_, v_val_3796_, v_name_3671_, v_levelParams_3665_, v___x_3792_, v_hasTrace_3670_, v___x_3797_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
v___y_3783_ = v___x_3793_;
v___y_3784_ = v_a_3790_;
v___y_3785_ = v___x_3798_;
goto v___jp_3782_;
}
else
{
lean_object* v_val_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; 
v_val_3799_ = lean_ctor_get(v_a_3795_, 0);
lean_inc_n(v_val_3799_, 2);
lean_dec_ref(v_a_3795_);
v___x_3800_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_3801_ = l_Lean_MessageData_ofExpr(v_val_3799_);
v___x_3802_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3802_, 0, v___x_3800_);
lean_ctor_set(v___x_3802_, 1, v___x_3801_);
v___x_3803_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_3725_, v___x_3802_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
if (lean_obj_tag(v___x_3803_) == 0)
{
lean_object* v_a_3804_; lean_object* v___x_3805_; 
v_a_3804_ = lean_ctor_get(v___x_3803_, 0);
lean_inc(v_a_3804_);
lean_dec_ref(v___x_3803_);
v___x_3805_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(v_ctorVal_3656_, v_val_3799_, v_name_3671_, v_levelParams_3665_, v___x_3792_, v_hasTrace_3670_, v_a_3804_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
v___y_3783_ = v___x_3793_;
v___y_3784_ = v_a_3790_;
v___y_3785_ = v___x_3805_;
goto v___jp_3782_;
}
else
{
lean_dec(v_val_3799_);
lean_dec(v_name_3671_);
lean_dec(v_levelParams_3665_);
lean_dec_ref(v_ctorVal_3656_);
v___y_3783_ = v___x_3793_;
v___y_3784_ = v_a_3790_;
v___y_3785_ = v___x_3803_;
goto v___jp_3782_;
}
}
}
else
{
lean_object* v___x_3806_; 
lean_dec(v_a_3795_);
lean_dec(v_name_3671_);
lean_dec(v_levelParams_3665_);
lean_dec_ref(v_ctorVal_3656_);
v___x_3806_ = lean_box(0);
v___y_3773_ = v___x_3793_;
v___y_3774_ = v_a_3790_;
v_a_3775_ = v___x_3806_;
goto v___jp_3772_;
}
}
else
{
lean_object* v_a_3807_; 
lean_dec(v_name_3671_);
lean_dec(v_levelParams_3665_);
lean_dec_ref(v_ctorVal_3656_);
v_a_3807_ = lean_ctor_get(v___x_3794_, 0);
lean_inc(v_a_3807_);
lean_dec_ref(v___x_3794_);
v___y_3778_ = v___x_3793_;
v___y_3779_ = v_a_3790_;
v_a_3780_ = v_a_3807_;
goto v___jp_3777_;
}
}
else
{
lean_object* v___x_3808_; lean_object* v___x_3809_; 
v___x_3808_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_ctorVal_3656_);
v___x_3809_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
if (lean_obj_tag(v___x_3809_) == 0)
{
lean_object* v_a_3810_; 
v_a_3810_ = lean_ctor_get(v___x_3809_, 0);
lean_inc(v_a_3810_);
lean_dec_ref(v___x_3809_);
if (lean_obj_tag(v_a_3810_) == 1)
{
if (v___x_3728_ == 0)
{
lean_object* v_val_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; 
v_val_3811_ = lean_ctor_get(v_a_3810_, 0);
lean_inc(v_val_3811_);
lean_dec_ref(v_a_3810_);
v___x_3812_ = lean_box(0);
v___x_3813_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(v_ctorVal_3656_, v_val_3811_, v_name_3671_, v_levelParams_3665_, v___x_3792_, v___x_3812_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
v___y_3752_ = v_a_3790_;
v___y_3753_ = v___x_3808_;
v___y_3754_ = v___x_3813_;
goto v___jp_3751_;
}
else
{
lean_object* v_val_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; 
v_val_3814_ = lean_ctor_get(v_a_3810_, 0);
lean_inc_n(v_val_3814_, 2);
lean_dec_ref(v_a_3810_);
v___x_3815_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_3816_ = l_Lean_MessageData_ofExpr(v_val_3814_);
v___x_3817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3817_, 0, v___x_3815_);
lean_ctor_set(v___x_3817_, 1, v___x_3816_);
v___x_3818_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_3725_, v___x_3817_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
if (lean_obj_tag(v___x_3818_) == 0)
{
lean_object* v_a_3819_; lean_object* v___x_3820_; 
v_a_3819_ = lean_ctor_get(v___x_3818_, 0);
lean_inc(v_a_3819_);
lean_dec_ref(v___x_3818_);
v___x_3820_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(v_ctorVal_3656_, v_val_3814_, v_name_3671_, v_levelParams_3665_, v___x_3792_, v_a_3819_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
v___y_3752_ = v_a_3790_;
v___y_3753_ = v___x_3808_;
v___y_3754_ = v___x_3820_;
goto v___jp_3751_;
}
else
{
lean_dec(v_val_3814_);
lean_dec(v_name_3671_);
lean_dec(v_levelParams_3665_);
lean_dec_ref(v_ctorVal_3656_);
v___y_3752_ = v_a_3790_;
v___y_3753_ = v___x_3808_;
v___y_3754_ = v___x_3818_;
goto v___jp_3751_;
}
}
}
else
{
lean_object* v___x_3821_; 
lean_dec(v_a_3810_);
lean_dec(v_name_3671_);
lean_dec(v_levelParams_3665_);
lean_dec_ref(v_ctorVal_3656_);
v___x_3821_ = lean_box(0);
v___y_3747_ = v_a_3790_;
v___y_3748_ = v___x_3808_;
v_a_3749_ = v___x_3821_;
goto v___jp_3746_;
}
}
else
{
lean_object* v_a_3822_; 
lean_dec(v_name_3671_);
lean_dec(v_levelParams_3665_);
lean_dec_ref(v_ctorVal_3656_);
v_a_3822_ = lean_ctor_get(v___x_3809_, 0);
lean_inc(v_a_3822_);
lean_dec_ref(v___x_3809_);
v___y_3742_ = v_a_3790_;
v___y_3743_ = v___x_3808_;
v_a_3744_ = v_a_3822_;
goto v___jp_3741_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___boxed(lean_object* v_ctorVal_3887_, lean_object* v_a_3888_, lean_object* v_a_3889_, lean_object* v_a_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_){
_start:
{
lean_object* v_res_3893_; 
v_res_3893_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(v_ctorVal_3887_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_);
lean_dec(v_a_3891_);
lean_dec_ref(v_a_3890_);
lean_dec(v_a_3889_);
lean_dec_ref(v_a_3888_);
return v_res_3893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(lean_object* v_name_3894_, lean_object* v_decl_3895_, lean_object* v_ref_3896_){
_start:
{
lean_object* v_defValue_3898_; lean_object* v_descr_3899_; lean_object* v_deprecation_x3f_3900_; lean_object* v___x_3901_; uint8_t v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; 
v_defValue_3898_ = lean_ctor_get(v_decl_3895_, 0);
v_descr_3899_ = lean_ctor_get(v_decl_3895_, 1);
v_deprecation_x3f_3900_ = lean_ctor_get(v_decl_3895_, 2);
v___x_3901_ = lean_alloc_ctor(1, 0, 1);
v___x_3902_ = lean_unbox(v_defValue_3898_);
lean_ctor_set_uint8(v___x_3901_, 0, v___x_3902_);
lean_inc(v_deprecation_x3f_3900_);
lean_inc_ref(v_descr_3899_);
lean_inc_n(v_name_3894_, 2);
v___x_3903_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3903_, 0, v_name_3894_);
lean_ctor_set(v___x_3903_, 1, v_ref_3896_);
lean_ctor_set(v___x_3903_, 2, v___x_3901_);
lean_ctor_set(v___x_3903_, 3, v_descr_3899_);
lean_ctor_set(v___x_3903_, 4, v_deprecation_x3f_3900_);
v___x_3904_ = lean_register_option(v_name_3894_, v___x_3903_);
if (lean_obj_tag(v___x_3904_) == 0)
{
lean_object* v___x_3906_; uint8_t v_isShared_3907_; uint8_t v_isSharedCheck_3912_; 
v_isSharedCheck_3912_ = !lean_is_exclusive(v___x_3904_);
if (v_isSharedCheck_3912_ == 0)
{
lean_object* v_unused_3913_; 
v_unused_3913_ = lean_ctor_get(v___x_3904_, 0);
lean_dec(v_unused_3913_);
v___x_3906_ = v___x_3904_;
v_isShared_3907_ = v_isSharedCheck_3912_;
goto v_resetjp_3905_;
}
else
{
lean_dec(v___x_3904_);
v___x_3906_ = lean_box(0);
v_isShared_3907_ = v_isSharedCheck_3912_;
goto v_resetjp_3905_;
}
v_resetjp_3905_:
{
lean_object* v___x_3908_; lean_object* v___x_3910_; 
lean_inc(v_defValue_3898_);
v___x_3908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3908_, 0, v_name_3894_);
lean_ctor_set(v___x_3908_, 1, v_defValue_3898_);
if (v_isShared_3907_ == 0)
{
lean_ctor_set(v___x_3906_, 0, v___x_3908_);
v___x_3910_ = v___x_3906_;
goto v_reusejp_3909_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v___x_3908_);
v___x_3910_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3909_;
}
v_reusejp_3909_:
{
return v___x_3910_;
}
}
}
else
{
lean_object* v_a_3914_; lean_object* v___x_3916_; uint8_t v_isShared_3917_; uint8_t v_isSharedCheck_3921_; 
lean_dec(v_name_3894_);
v_a_3914_ = lean_ctor_get(v___x_3904_, 0);
v_isSharedCheck_3921_ = !lean_is_exclusive(v___x_3904_);
if (v_isSharedCheck_3921_ == 0)
{
v___x_3916_ = v___x_3904_;
v_isShared_3917_ = v_isSharedCheck_3921_;
goto v_resetjp_3915_;
}
else
{
lean_inc(v_a_3914_);
lean_dec(v___x_3904_);
v___x_3916_ = lean_box(0);
v_isShared_3917_ = v_isSharedCheck_3921_;
goto v_resetjp_3915_;
}
v_resetjp_3915_:
{
lean_object* v___x_3919_; 
if (v_isShared_3917_ == 0)
{
v___x_3919_ = v___x_3916_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v_a_3914_);
v___x_3919_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
return v___x_3919_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_3922_, lean_object* v_decl_3923_, lean_object* v_ref_3924_, lean_object* v_a_3925_){
_start:
{
lean_object* v_res_3926_; 
v_res_3926_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(v_name_3922_, v_decl_3923_, v_ref_3924_);
lean_dec_ref(v_decl_3923_);
return v_res_3926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; 
v___x_3941_ = ((lean_object*)(l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_));
v___x_3942_ = ((lean_object*)(l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_));
v___x_3943_ = ((lean_object*)(l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_));
v___x_3944_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(v___x_3941_, v___x_3942_, v___x_3943_);
return v___x_3944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4____boxed(lean_object* v_a_3945_){
_start:
{
lean_object* v_res_3946_; 
v_res_3946_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_();
return v_res_3946_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(lean_object* v___y_3947_, uint8_t v_isExporting_3948_, lean_object* v___x_3949_, lean_object* v___y_3950_, lean_object* v___x_3951_, lean_object* v_a_x3f_3952_){
_start:
{
lean_object* v___x_3954_; lean_object* v_env_3955_; lean_object* v_nextMacroScope_3956_; lean_object* v_ngen_3957_; lean_object* v_auxDeclNGen_3958_; lean_object* v_traceState_3959_; lean_object* v_messages_3960_; lean_object* v_infoState_3961_; lean_object* v_snapshotTasks_3962_; lean_object* v___x_3964_; uint8_t v_isShared_3965_; uint8_t v_isSharedCheck_3987_; 
v___x_3954_ = lean_st_ref_take(v___y_3947_);
v_env_3955_ = lean_ctor_get(v___x_3954_, 0);
v_nextMacroScope_3956_ = lean_ctor_get(v___x_3954_, 1);
v_ngen_3957_ = lean_ctor_get(v___x_3954_, 2);
v_auxDeclNGen_3958_ = lean_ctor_get(v___x_3954_, 3);
v_traceState_3959_ = lean_ctor_get(v___x_3954_, 4);
v_messages_3960_ = lean_ctor_get(v___x_3954_, 6);
v_infoState_3961_ = lean_ctor_get(v___x_3954_, 7);
v_snapshotTasks_3962_ = lean_ctor_get(v___x_3954_, 8);
v_isSharedCheck_3987_ = !lean_is_exclusive(v___x_3954_);
if (v_isSharedCheck_3987_ == 0)
{
lean_object* v_unused_3988_; 
v_unused_3988_ = lean_ctor_get(v___x_3954_, 5);
lean_dec(v_unused_3988_);
v___x_3964_ = v___x_3954_;
v_isShared_3965_ = v_isSharedCheck_3987_;
goto v_resetjp_3963_;
}
else
{
lean_inc(v_snapshotTasks_3962_);
lean_inc(v_infoState_3961_);
lean_inc(v_messages_3960_);
lean_inc(v_traceState_3959_);
lean_inc(v_auxDeclNGen_3958_);
lean_inc(v_ngen_3957_);
lean_inc(v_nextMacroScope_3956_);
lean_inc(v_env_3955_);
lean_dec(v___x_3954_);
v___x_3964_ = lean_box(0);
v_isShared_3965_ = v_isSharedCheck_3987_;
goto v_resetjp_3963_;
}
v_resetjp_3963_:
{
lean_object* v___x_3966_; lean_object* v___x_3968_; 
v___x_3966_ = l_Lean_Environment_setExporting(v_env_3955_, v_isExporting_3948_);
if (v_isShared_3965_ == 0)
{
lean_ctor_set(v___x_3964_, 5, v___x_3949_);
lean_ctor_set(v___x_3964_, 0, v___x_3966_);
v___x_3968_ = v___x_3964_;
goto v_reusejp_3967_;
}
else
{
lean_object* v_reuseFailAlloc_3986_; 
v_reuseFailAlloc_3986_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v___x_3966_);
lean_ctor_set(v_reuseFailAlloc_3986_, 1, v_nextMacroScope_3956_);
lean_ctor_set(v_reuseFailAlloc_3986_, 2, v_ngen_3957_);
lean_ctor_set(v_reuseFailAlloc_3986_, 3, v_auxDeclNGen_3958_);
lean_ctor_set(v_reuseFailAlloc_3986_, 4, v_traceState_3959_);
lean_ctor_set(v_reuseFailAlloc_3986_, 5, v___x_3949_);
lean_ctor_set(v_reuseFailAlloc_3986_, 6, v_messages_3960_);
lean_ctor_set(v_reuseFailAlloc_3986_, 7, v_infoState_3961_);
lean_ctor_set(v_reuseFailAlloc_3986_, 8, v_snapshotTasks_3962_);
v___x_3968_ = v_reuseFailAlloc_3986_;
goto v_reusejp_3967_;
}
v_reusejp_3967_:
{
lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v_mctx_3971_; lean_object* v_zetaDeltaFVarIds_3972_; lean_object* v_postponed_3973_; lean_object* v_diag_3974_; lean_object* v___x_3976_; uint8_t v_isShared_3977_; uint8_t v_isSharedCheck_3984_; 
v___x_3969_ = lean_st_ref_set(v___y_3947_, v___x_3968_);
v___x_3970_ = lean_st_ref_take(v___y_3950_);
v_mctx_3971_ = lean_ctor_get(v___x_3970_, 0);
v_zetaDeltaFVarIds_3972_ = lean_ctor_get(v___x_3970_, 2);
v_postponed_3973_ = lean_ctor_get(v___x_3970_, 3);
v_diag_3974_ = lean_ctor_get(v___x_3970_, 4);
v_isSharedCheck_3984_ = !lean_is_exclusive(v___x_3970_);
if (v_isSharedCheck_3984_ == 0)
{
lean_object* v_unused_3985_; 
v_unused_3985_ = lean_ctor_get(v___x_3970_, 1);
lean_dec(v_unused_3985_);
v___x_3976_ = v___x_3970_;
v_isShared_3977_ = v_isSharedCheck_3984_;
goto v_resetjp_3975_;
}
else
{
lean_inc(v_diag_3974_);
lean_inc(v_postponed_3973_);
lean_inc(v_zetaDeltaFVarIds_3972_);
lean_inc(v_mctx_3971_);
lean_dec(v___x_3970_);
v___x_3976_ = lean_box(0);
v_isShared_3977_ = v_isSharedCheck_3984_;
goto v_resetjp_3975_;
}
v_resetjp_3975_:
{
lean_object* v___x_3979_; 
if (v_isShared_3977_ == 0)
{
lean_ctor_set(v___x_3976_, 1, v___x_3951_);
v___x_3979_ = v___x_3976_;
goto v_reusejp_3978_;
}
else
{
lean_object* v_reuseFailAlloc_3983_; 
v_reuseFailAlloc_3983_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3983_, 0, v_mctx_3971_);
lean_ctor_set(v_reuseFailAlloc_3983_, 1, v___x_3951_);
lean_ctor_set(v_reuseFailAlloc_3983_, 2, v_zetaDeltaFVarIds_3972_);
lean_ctor_set(v_reuseFailAlloc_3983_, 3, v_postponed_3973_);
lean_ctor_set(v_reuseFailAlloc_3983_, 4, v_diag_3974_);
v___x_3979_ = v_reuseFailAlloc_3983_;
goto v_reusejp_3978_;
}
v_reusejp_3978_:
{
lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; 
v___x_3980_ = lean_st_ref_set(v___y_3950_, v___x_3979_);
v___x_3981_ = lean_box(0);
v___x_3982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3982_, 0, v___x_3981_);
return v___x_3982_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0___boxed(lean_object* v___y_3989_, lean_object* v_isExporting_3990_, lean_object* v___x_3991_, lean_object* v___y_3992_, lean_object* v___x_3993_, lean_object* v_a_x3f_3994_, lean_object* v___y_3995_){
_start:
{
uint8_t v_isExporting_boxed_3996_; lean_object* v_res_3997_; 
v_isExporting_boxed_3996_ = lean_unbox(v_isExporting_3990_);
v_res_3997_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(v___y_3989_, v_isExporting_boxed_3996_, v___x_3991_, v___y_3992_, v___x_3993_, v_a_x3f_3994_);
lean_dec(v_a_x3f_3994_);
lean_dec(v___y_3992_);
lean_dec(v___y_3989_);
return v_res_3997_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_3998_; 
v___x_3998_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3998_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_3999_; lean_object* v___x_4000_; 
v___x_3999_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0);
v___x_4000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4000_, 0, v___x_3999_);
return v___x_4000_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_4001_; lean_object* v___x_4002_; 
v___x_4001_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1);
v___x_4002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4002_, 0, v___x_4001_);
lean_ctor_set(v___x_4002_, 1, v___x_4001_);
return v___x_4002_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_4003_; lean_object* v___x_4004_; 
v___x_4003_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1);
v___x_4004_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4004_, 0, v___x_4003_);
lean_ctor_set(v___x_4004_, 1, v___x_4003_);
lean_ctor_set(v___x_4004_, 2, v___x_4003_);
lean_ctor_set(v___x_4004_, 3, v___x_4003_);
lean_ctor_set(v___x_4004_, 4, v___x_4003_);
lean_ctor_set(v___x_4004_, 5, v___x_4003_);
return v___x_4004_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(lean_object* v_x_4005_, uint8_t v_isExporting_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_){
_start:
{
lean_object* v___x_4012_; lean_object* v_env_4013_; uint8_t v_isExporting_4014_; lean_object* v___x_4015_; lean_object* v_env_4016_; lean_object* v_nextMacroScope_4017_; lean_object* v_ngen_4018_; lean_object* v_auxDeclNGen_4019_; lean_object* v_traceState_4020_; lean_object* v_messages_4021_; lean_object* v_infoState_4022_; lean_object* v_snapshotTasks_4023_; lean_object* v___x_4025_; uint8_t v_isShared_4026_; uint8_t v_isSharedCheck_4077_; 
v___x_4012_ = lean_st_ref_get(v___y_4010_);
v_env_4013_ = lean_ctor_get(v___x_4012_, 0);
lean_inc_ref(v_env_4013_);
lean_dec(v___x_4012_);
v_isExporting_4014_ = lean_ctor_get_uint8(v_env_4013_, sizeof(void*)*8);
lean_dec_ref(v_env_4013_);
v___x_4015_ = lean_st_ref_take(v___y_4010_);
v_env_4016_ = lean_ctor_get(v___x_4015_, 0);
v_nextMacroScope_4017_ = lean_ctor_get(v___x_4015_, 1);
v_ngen_4018_ = lean_ctor_get(v___x_4015_, 2);
v_auxDeclNGen_4019_ = lean_ctor_get(v___x_4015_, 3);
v_traceState_4020_ = lean_ctor_get(v___x_4015_, 4);
v_messages_4021_ = lean_ctor_get(v___x_4015_, 6);
v_infoState_4022_ = lean_ctor_get(v___x_4015_, 7);
v_snapshotTasks_4023_ = lean_ctor_get(v___x_4015_, 8);
v_isSharedCheck_4077_ = !lean_is_exclusive(v___x_4015_);
if (v_isSharedCheck_4077_ == 0)
{
lean_object* v_unused_4078_; 
v_unused_4078_ = lean_ctor_get(v___x_4015_, 5);
lean_dec(v_unused_4078_);
v___x_4025_ = v___x_4015_;
v_isShared_4026_ = v_isSharedCheck_4077_;
goto v_resetjp_4024_;
}
else
{
lean_inc(v_snapshotTasks_4023_);
lean_inc(v_infoState_4022_);
lean_inc(v_messages_4021_);
lean_inc(v_traceState_4020_);
lean_inc(v_auxDeclNGen_4019_);
lean_inc(v_ngen_4018_);
lean_inc(v_nextMacroScope_4017_);
lean_inc(v_env_4016_);
lean_dec(v___x_4015_);
v___x_4025_ = lean_box(0);
v_isShared_4026_ = v_isSharedCheck_4077_;
goto v_resetjp_4024_;
}
v_resetjp_4024_:
{
lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4030_; 
v___x_4027_ = l_Lean_Environment_setExporting(v_env_4016_, v_isExporting_4006_);
v___x_4028_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2);
if (v_isShared_4026_ == 0)
{
lean_ctor_set(v___x_4025_, 5, v___x_4028_);
lean_ctor_set(v___x_4025_, 0, v___x_4027_);
v___x_4030_ = v___x_4025_;
goto v_reusejp_4029_;
}
else
{
lean_object* v_reuseFailAlloc_4076_; 
v_reuseFailAlloc_4076_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4076_, 0, v___x_4027_);
lean_ctor_set(v_reuseFailAlloc_4076_, 1, v_nextMacroScope_4017_);
lean_ctor_set(v_reuseFailAlloc_4076_, 2, v_ngen_4018_);
lean_ctor_set(v_reuseFailAlloc_4076_, 3, v_auxDeclNGen_4019_);
lean_ctor_set(v_reuseFailAlloc_4076_, 4, v_traceState_4020_);
lean_ctor_set(v_reuseFailAlloc_4076_, 5, v___x_4028_);
lean_ctor_set(v_reuseFailAlloc_4076_, 6, v_messages_4021_);
lean_ctor_set(v_reuseFailAlloc_4076_, 7, v_infoState_4022_);
lean_ctor_set(v_reuseFailAlloc_4076_, 8, v_snapshotTasks_4023_);
v___x_4030_ = v_reuseFailAlloc_4076_;
goto v_reusejp_4029_;
}
v_reusejp_4029_:
{
lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v_mctx_4033_; lean_object* v_zetaDeltaFVarIds_4034_; lean_object* v_postponed_4035_; lean_object* v_diag_4036_; lean_object* v___x_4038_; uint8_t v_isShared_4039_; uint8_t v_isSharedCheck_4074_; 
v___x_4031_ = lean_st_ref_set(v___y_4010_, v___x_4030_);
v___x_4032_ = lean_st_ref_take(v___y_4008_);
v_mctx_4033_ = lean_ctor_get(v___x_4032_, 0);
v_zetaDeltaFVarIds_4034_ = lean_ctor_get(v___x_4032_, 2);
v_postponed_4035_ = lean_ctor_get(v___x_4032_, 3);
v_diag_4036_ = lean_ctor_get(v___x_4032_, 4);
v_isSharedCheck_4074_ = !lean_is_exclusive(v___x_4032_);
if (v_isSharedCheck_4074_ == 0)
{
lean_object* v_unused_4075_; 
v_unused_4075_ = lean_ctor_get(v___x_4032_, 1);
lean_dec(v_unused_4075_);
v___x_4038_ = v___x_4032_;
v_isShared_4039_ = v_isSharedCheck_4074_;
goto v_resetjp_4037_;
}
else
{
lean_inc(v_diag_4036_);
lean_inc(v_postponed_4035_);
lean_inc(v_zetaDeltaFVarIds_4034_);
lean_inc(v_mctx_4033_);
lean_dec(v___x_4032_);
v___x_4038_ = lean_box(0);
v_isShared_4039_ = v_isSharedCheck_4074_;
goto v_resetjp_4037_;
}
v_resetjp_4037_:
{
lean_object* v___x_4040_; lean_object* v___x_4042_; 
v___x_4040_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3);
if (v_isShared_4039_ == 0)
{
lean_ctor_set(v___x_4038_, 1, v___x_4040_);
v___x_4042_ = v___x_4038_;
goto v_reusejp_4041_;
}
else
{
lean_object* v_reuseFailAlloc_4073_; 
v_reuseFailAlloc_4073_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4073_, 0, v_mctx_4033_);
lean_ctor_set(v_reuseFailAlloc_4073_, 1, v___x_4040_);
lean_ctor_set(v_reuseFailAlloc_4073_, 2, v_zetaDeltaFVarIds_4034_);
lean_ctor_set(v_reuseFailAlloc_4073_, 3, v_postponed_4035_);
lean_ctor_set(v_reuseFailAlloc_4073_, 4, v_diag_4036_);
v___x_4042_ = v_reuseFailAlloc_4073_;
goto v_reusejp_4041_;
}
v_reusejp_4041_:
{
lean_object* v___x_4043_; lean_object* v_r_4044_; 
v___x_4043_ = lean_st_ref_set(v___y_4008_, v___x_4042_);
lean_inc(v___y_4010_);
lean_inc_ref(v___y_4009_);
lean_inc(v___y_4008_);
lean_inc_ref(v___y_4007_);
v_r_4044_ = lean_apply_5(v_x_4005_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_, lean_box(0));
if (lean_obj_tag(v_r_4044_) == 0)
{
lean_object* v_a_4045_; lean_object* v___x_4047_; uint8_t v_isShared_4048_; uint8_t v_isSharedCheck_4061_; 
v_a_4045_ = lean_ctor_get(v_r_4044_, 0);
v_isSharedCheck_4061_ = !lean_is_exclusive(v_r_4044_);
if (v_isSharedCheck_4061_ == 0)
{
v___x_4047_ = v_r_4044_;
v_isShared_4048_ = v_isSharedCheck_4061_;
goto v_resetjp_4046_;
}
else
{
lean_inc(v_a_4045_);
lean_dec(v_r_4044_);
v___x_4047_ = lean_box(0);
v_isShared_4048_ = v_isSharedCheck_4061_;
goto v_resetjp_4046_;
}
v_resetjp_4046_:
{
lean_object* v___x_4050_; 
lean_inc(v_a_4045_);
if (v_isShared_4048_ == 0)
{
lean_ctor_set_tag(v___x_4047_, 1);
v___x_4050_ = v___x_4047_;
goto v_reusejp_4049_;
}
else
{
lean_object* v_reuseFailAlloc_4060_; 
v_reuseFailAlloc_4060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4060_, 0, v_a_4045_);
v___x_4050_ = v_reuseFailAlloc_4060_;
goto v_reusejp_4049_;
}
v_reusejp_4049_:
{
lean_object* v___x_4051_; lean_object* v___x_4053_; uint8_t v_isShared_4054_; uint8_t v_isSharedCheck_4058_; 
v___x_4051_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(v___y_4010_, v_isExporting_4014_, v___x_4028_, v___y_4008_, v___x_4040_, v___x_4050_);
lean_dec_ref(v___x_4050_);
v_isSharedCheck_4058_ = !lean_is_exclusive(v___x_4051_);
if (v_isSharedCheck_4058_ == 0)
{
lean_object* v_unused_4059_; 
v_unused_4059_ = lean_ctor_get(v___x_4051_, 0);
lean_dec(v_unused_4059_);
v___x_4053_ = v___x_4051_;
v_isShared_4054_ = v_isSharedCheck_4058_;
goto v_resetjp_4052_;
}
else
{
lean_dec(v___x_4051_);
v___x_4053_ = lean_box(0);
v_isShared_4054_ = v_isSharedCheck_4058_;
goto v_resetjp_4052_;
}
v_resetjp_4052_:
{
lean_object* v___x_4056_; 
if (v_isShared_4054_ == 0)
{
lean_ctor_set(v___x_4053_, 0, v_a_4045_);
v___x_4056_ = v___x_4053_;
goto v_reusejp_4055_;
}
else
{
lean_object* v_reuseFailAlloc_4057_; 
v_reuseFailAlloc_4057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4057_, 0, v_a_4045_);
v___x_4056_ = v_reuseFailAlloc_4057_;
goto v_reusejp_4055_;
}
v_reusejp_4055_:
{
return v___x_4056_;
}
}
}
}
}
else
{
lean_object* v_a_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4066_; uint8_t v_isShared_4067_; uint8_t v_isSharedCheck_4071_; 
v_a_4062_ = lean_ctor_get(v_r_4044_, 0);
lean_inc(v_a_4062_);
lean_dec_ref(v_r_4044_);
v___x_4063_ = lean_box(0);
v___x_4064_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(v___y_4010_, v_isExporting_4014_, v___x_4028_, v___y_4008_, v___x_4040_, v___x_4063_);
v_isSharedCheck_4071_ = !lean_is_exclusive(v___x_4064_);
if (v_isSharedCheck_4071_ == 0)
{
lean_object* v_unused_4072_; 
v_unused_4072_ = lean_ctor_get(v___x_4064_, 0);
lean_dec(v_unused_4072_);
v___x_4066_ = v___x_4064_;
v_isShared_4067_ = v_isSharedCheck_4071_;
goto v_resetjp_4065_;
}
else
{
lean_dec(v___x_4064_);
v___x_4066_ = lean_box(0);
v_isShared_4067_ = v_isSharedCheck_4071_;
goto v_resetjp_4065_;
}
v_resetjp_4065_:
{
lean_object* v___x_4069_; 
if (v_isShared_4067_ == 0)
{
lean_ctor_set_tag(v___x_4066_, 1);
lean_ctor_set(v___x_4066_, 0, v_a_4062_);
v___x_4069_ = v___x_4066_;
goto v_reusejp_4068_;
}
else
{
lean_object* v_reuseFailAlloc_4070_; 
v_reuseFailAlloc_4070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4070_, 0, v_a_4062_);
v___x_4069_ = v_reuseFailAlloc_4070_;
goto v_reusejp_4068_;
}
v_reusejp_4068_:
{
return v___x_4069_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___boxed(lean_object* v_x_4079_, lean_object* v_isExporting_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_){
_start:
{
uint8_t v_isExporting_boxed_4086_; lean_object* v_res_4087_; 
v_isExporting_boxed_4086_ = lean_unbox(v_isExporting_4080_);
v_res_4087_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(v_x_4079_, v_isExporting_boxed_4086_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_);
lean_dec(v___y_4084_);
lean_dec_ref(v___y_4083_);
lean_dec(v___y_4082_);
lean_dec_ref(v___y_4081_);
return v_res_4087_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2(lean_object* v_00_u03b1_4088_, lean_object* v_x_4089_, uint8_t v_isExporting_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_){
_start:
{
lean_object* v___x_4096_; 
v___x_4096_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(v_x_4089_, v_isExporting_4090_, v___y_4091_, v___y_4092_, v___y_4093_, v___y_4094_);
return v___x_4096_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___boxed(lean_object* v_00_u03b1_4097_, lean_object* v_x_4098_, lean_object* v_isExporting_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_){
_start:
{
uint8_t v_isExporting_boxed_4105_; lean_object* v_res_4106_; 
v_isExporting_boxed_4105_ = lean_unbox(v_isExporting_4099_);
v_res_4106_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2(v_00_u03b1_4097_, v_x_4098_, v_isExporting_boxed_4105_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_);
lean_dec(v___y_4103_);
lean_dec_ref(v___y_4102_);
lean_dec(v___y_4101_);
lean_dec_ref(v___y_4100_);
return v_res_4106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(lean_object* v_lctx_4107_, lean_object* v_localInsts_4108_, lean_object* v_x_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_){
_start:
{
lean_object* v___x_4115_; 
v___x_4115_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_4107_, v_localInsts_4108_, v_x_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_);
if (lean_obj_tag(v___x_4115_) == 0)
{
lean_object* v_a_4116_; lean_object* v___x_4118_; uint8_t v_isShared_4119_; uint8_t v_isSharedCheck_4123_; 
v_a_4116_ = lean_ctor_get(v___x_4115_, 0);
v_isSharedCheck_4123_ = !lean_is_exclusive(v___x_4115_);
if (v_isSharedCheck_4123_ == 0)
{
v___x_4118_ = v___x_4115_;
v_isShared_4119_ = v_isSharedCheck_4123_;
goto v_resetjp_4117_;
}
else
{
lean_inc(v_a_4116_);
lean_dec(v___x_4115_);
v___x_4118_ = lean_box(0);
v_isShared_4119_ = v_isSharedCheck_4123_;
goto v_resetjp_4117_;
}
v_resetjp_4117_:
{
lean_object* v___x_4121_; 
if (v_isShared_4119_ == 0)
{
v___x_4121_ = v___x_4118_;
goto v_reusejp_4120_;
}
else
{
lean_object* v_reuseFailAlloc_4122_; 
v_reuseFailAlloc_4122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4122_, 0, v_a_4116_);
v___x_4121_ = v_reuseFailAlloc_4122_;
goto v_reusejp_4120_;
}
v_reusejp_4120_:
{
return v___x_4121_;
}
}
}
else
{
lean_object* v_a_4124_; lean_object* v___x_4126_; uint8_t v_isShared_4127_; uint8_t v_isSharedCheck_4131_; 
v_a_4124_ = lean_ctor_get(v___x_4115_, 0);
v_isSharedCheck_4131_ = !lean_is_exclusive(v___x_4115_);
if (v_isSharedCheck_4131_ == 0)
{
v___x_4126_ = v___x_4115_;
v_isShared_4127_ = v_isSharedCheck_4131_;
goto v_resetjp_4125_;
}
else
{
lean_inc(v_a_4124_);
lean_dec(v___x_4115_);
v___x_4126_ = lean_box(0);
v_isShared_4127_ = v_isSharedCheck_4131_;
goto v_resetjp_4125_;
}
v_resetjp_4125_:
{
lean_object* v___x_4129_; 
if (v_isShared_4127_ == 0)
{
v___x_4129_ = v___x_4126_;
goto v_reusejp_4128_;
}
else
{
lean_object* v_reuseFailAlloc_4130_; 
v_reuseFailAlloc_4130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4130_, 0, v_a_4124_);
v___x_4129_ = v_reuseFailAlloc_4130_;
goto v_reusejp_4128_;
}
v_reusejp_4128_:
{
return v___x_4129_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg___boxed(lean_object* v_lctx_4132_, lean_object* v_localInsts_4133_, lean_object* v_x_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_){
_start:
{
lean_object* v_res_4140_; 
v_res_4140_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v_lctx_4132_, v_localInsts_4133_, v_x_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_);
lean_dec(v___y_4138_);
lean_dec_ref(v___y_4137_);
lean_dec(v___y_4136_);
lean_dec_ref(v___y_4135_);
return v_res_4140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4(lean_object* v_00_u03b1_4141_, lean_object* v_lctx_4142_, lean_object* v_localInsts_4143_, lean_object* v_x_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_){
_start:
{
lean_object* v___x_4150_; 
v___x_4150_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v_lctx_4142_, v_localInsts_4143_, v_x_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_);
return v___x_4150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___boxed(lean_object* v_00_u03b1_4151_, lean_object* v_lctx_4152_, lean_object* v_localInsts_4153_, lean_object* v_x_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_){
_start:
{
lean_object* v_res_4160_; 
v_res_4160_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4(v_00_u03b1_4151_, v_lctx_4152_, v_localInsts_4153_, v_x_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_);
lean_dec(v___y_4158_);
lean_dec_ref(v___y_4157_);
lean_dec(v___y_4156_);
lean_dec_ref(v___y_4155_);
return v_res_4160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__0(lean_object* v_declName_4161_, lean_object* v_x_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_){
_start:
{
lean_object* v___x_4168_; lean_object* v___x_4169_; 
v___x_4168_ = l_Lean_MessageData_ofName(v_declName_4161_);
v___x_4169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4169_, 0, v___x_4168_);
return v___x_4169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__0___boxed(lean_object* v_declName_4170_, lean_object* v_x_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_){
_start:
{
lean_object* v_res_4177_; 
v_res_4177_ = l_Lean_Meta_mkInjectiveTheorems___lam__0(v_declName_4170_, v_x_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_);
lean_dec(v___y_4175_);
lean_dec_ref(v___y_4174_);
lean_dec(v___y_4173_);
lean_dec_ref(v___y_4172_);
lean_dec_ref(v_x_4171_);
return v_res_4177_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_4178_; 
v___x_4178_ = l_instMonadEIO(lean_box(0));
return v___x_4178_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(lean_object* v_msg_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_){
_start:
{
lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v_toApplicative_4191_; lean_object* v___x_4193_; uint8_t v_isShared_4194_; uint8_t v_isSharedCheck_4252_; 
v___x_4189_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0);
v___x_4190_ = l_StateRefT_x27_instMonad___redArg(v___x_4189_);
v_toApplicative_4191_ = lean_ctor_get(v___x_4190_, 0);
v_isSharedCheck_4252_ = !lean_is_exclusive(v___x_4190_);
if (v_isSharedCheck_4252_ == 0)
{
lean_object* v_unused_4253_; 
v_unused_4253_ = lean_ctor_get(v___x_4190_, 1);
lean_dec(v_unused_4253_);
v___x_4193_ = v___x_4190_;
v_isShared_4194_ = v_isSharedCheck_4252_;
goto v_resetjp_4192_;
}
else
{
lean_inc(v_toApplicative_4191_);
lean_dec(v___x_4190_);
v___x_4193_ = lean_box(0);
v_isShared_4194_ = v_isSharedCheck_4252_;
goto v_resetjp_4192_;
}
v_resetjp_4192_:
{
lean_object* v_toFunctor_4195_; lean_object* v_toSeq_4196_; lean_object* v_toSeqLeft_4197_; lean_object* v_toSeqRight_4198_; lean_object* v___x_4200_; uint8_t v_isShared_4201_; uint8_t v_isSharedCheck_4250_; 
v_toFunctor_4195_ = lean_ctor_get(v_toApplicative_4191_, 0);
v_toSeq_4196_ = lean_ctor_get(v_toApplicative_4191_, 2);
v_toSeqLeft_4197_ = lean_ctor_get(v_toApplicative_4191_, 3);
v_toSeqRight_4198_ = lean_ctor_get(v_toApplicative_4191_, 4);
v_isSharedCheck_4250_ = !lean_is_exclusive(v_toApplicative_4191_);
if (v_isSharedCheck_4250_ == 0)
{
lean_object* v_unused_4251_; 
v_unused_4251_ = lean_ctor_get(v_toApplicative_4191_, 1);
lean_dec(v_unused_4251_);
v___x_4200_ = v_toApplicative_4191_;
v_isShared_4201_ = v_isSharedCheck_4250_;
goto v_resetjp_4199_;
}
else
{
lean_inc(v_toSeqRight_4198_);
lean_inc(v_toSeqLeft_4197_);
lean_inc(v_toSeq_4196_);
lean_inc(v_toFunctor_4195_);
lean_dec(v_toApplicative_4191_);
v___x_4200_ = lean_box(0);
v_isShared_4201_ = v_isSharedCheck_4250_;
goto v_resetjp_4199_;
}
v_resetjp_4199_:
{
lean_object* v___f_4202_; lean_object* v___f_4203_; lean_object* v___f_4204_; lean_object* v___f_4205_; lean_object* v___x_4206_; lean_object* v___f_4207_; lean_object* v___f_4208_; lean_object* v___f_4209_; lean_object* v___x_4211_; 
v___f_4202_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__1));
v___f_4203_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__2));
lean_inc_ref(v_toFunctor_4195_);
v___f_4204_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4204_, 0, v_toFunctor_4195_);
v___f_4205_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4205_, 0, v_toFunctor_4195_);
v___x_4206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4206_, 0, v___f_4204_);
lean_ctor_set(v___x_4206_, 1, v___f_4205_);
v___f_4207_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4207_, 0, v_toSeqRight_4198_);
v___f_4208_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4208_, 0, v_toSeqLeft_4197_);
v___f_4209_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4209_, 0, v_toSeq_4196_);
if (v_isShared_4201_ == 0)
{
lean_ctor_set(v___x_4200_, 4, v___f_4207_);
lean_ctor_set(v___x_4200_, 3, v___f_4208_);
lean_ctor_set(v___x_4200_, 2, v___f_4209_);
lean_ctor_set(v___x_4200_, 1, v___f_4202_);
lean_ctor_set(v___x_4200_, 0, v___x_4206_);
v___x_4211_ = v___x_4200_;
goto v_reusejp_4210_;
}
else
{
lean_object* v_reuseFailAlloc_4249_; 
v_reuseFailAlloc_4249_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4249_, 0, v___x_4206_);
lean_ctor_set(v_reuseFailAlloc_4249_, 1, v___f_4202_);
lean_ctor_set(v_reuseFailAlloc_4249_, 2, v___f_4209_);
lean_ctor_set(v_reuseFailAlloc_4249_, 3, v___f_4208_);
lean_ctor_set(v_reuseFailAlloc_4249_, 4, v___f_4207_);
v___x_4211_ = v_reuseFailAlloc_4249_;
goto v_reusejp_4210_;
}
v_reusejp_4210_:
{
lean_object* v___x_4213_; 
if (v_isShared_4194_ == 0)
{
lean_ctor_set(v___x_4193_, 1, v___f_4203_);
lean_ctor_set(v___x_4193_, 0, v___x_4211_);
v___x_4213_ = v___x_4193_;
goto v_reusejp_4212_;
}
else
{
lean_object* v_reuseFailAlloc_4248_; 
v_reuseFailAlloc_4248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4248_, 0, v___x_4211_);
lean_ctor_set(v_reuseFailAlloc_4248_, 1, v___f_4203_);
v___x_4213_ = v_reuseFailAlloc_4248_;
goto v_reusejp_4212_;
}
v_reusejp_4212_:
{
lean_object* v___x_4214_; lean_object* v_toApplicative_4215_; lean_object* v___x_4217_; uint8_t v_isShared_4218_; uint8_t v_isSharedCheck_4246_; 
v___x_4214_ = l_StateRefT_x27_instMonad___redArg(v___x_4213_);
v_toApplicative_4215_ = lean_ctor_get(v___x_4214_, 0);
v_isSharedCheck_4246_ = !lean_is_exclusive(v___x_4214_);
if (v_isSharedCheck_4246_ == 0)
{
lean_object* v_unused_4247_; 
v_unused_4247_ = lean_ctor_get(v___x_4214_, 1);
lean_dec(v_unused_4247_);
v___x_4217_ = v___x_4214_;
v_isShared_4218_ = v_isSharedCheck_4246_;
goto v_resetjp_4216_;
}
else
{
lean_inc(v_toApplicative_4215_);
lean_dec(v___x_4214_);
v___x_4217_ = lean_box(0);
v_isShared_4218_ = v_isSharedCheck_4246_;
goto v_resetjp_4216_;
}
v_resetjp_4216_:
{
lean_object* v_toFunctor_4219_; lean_object* v_toSeq_4220_; lean_object* v_toSeqLeft_4221_; lean_object* v_toSeqRight_4222_; lean_object* v___x_4224_; uint8_t v_isShared_4225_; uint8_t v_isSharedCheck_4244_; 
v_toFunctor_4219_ = lean_ctor_get(v_toApplicative_4215_, 0);
v_toSeq_4220_ = lean_ctor_get(v_toApplicative_4215_, 2);
v_toSeqLeft_4221_ = lean_ctor_get(v_toApplicative_4215_, 3);
v_toSeqRight_4222_ = lean_ctor_get(v_toApplicative_4215_, 4);
v_isSharedCheck_4244_ = !lean_is_exclusive(v_toApplicative_4215_);
if (v_isSharedCheck_4244_ == 0)
{
lean_object* v_unused_4245_; 
v_unused_4245_ = lean_ctor_get(v_toApplicative_4215_, 1);
lean_dec(v_unused_4245_);
v___x_4224_ = v_toApplicative_4215_;
v_isShared_4225_ = v_isSharedCheck_4244_;
goto v_resetjp_4223_;
}
else
{
lean_inc(v_toSeqRight_4222_);
lean_inc(v_toSeqLeft_4221_);
lean_inc(v_toSeq_4220_);
lean_inc(v_toFunctor_4219_);
lean_dec(v_toApplicative_4215_);
v___x_4224_ = lean_box(0);
v_isShared_4225_ = v_isSharedCheck_4244_;
goto v_resetjp_4223_;
}
v_resetjp_4223_:
{
lean_object* v___f_4226_; lean_object* v___f_4227_; lean_object* v___f_4228_; lean_object* v___f_4229_; lean_object* v___x_4230_; lean_object* v___f_4231_; lean_object* v___f_4232_; lean_object* v___f_4233_; lean_object* v___x_4235_; 
v___f_4226_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__3));
v___f_4227_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__4));
lean_inc_ref(v_toFunctor_4219_);
v___f_4228_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4228_, 0, v_toFunctor_4219_);
v___f_4229_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4229_, 0, v_toFunctor_4219_);
v___x_4230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4230_, 0, v___f_4228_);
lean_ctor_set(v___x_4230_, 1, v___f_4229_);
v___f_4231_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4231_, 0, v_toSeqRight_4222_);
v___f_4232_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4232_, 0, v_toSeqLeft_4221_);
v___f_4233_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4233_, 0, v_toSeq_4220_);
if (v_isShared_4225_ == 0)
{
lean_ctor_set(v___x_4224_, 4, v___f_4231_);
lean_ctor_set(v___x_4224_, 3, v___f_4232_);
lean_ctor_set(v___x_4224_, 2, v___f_4233_);
lean_ctor_set(v___x_4224_, 1, v___f_4226_);
lean_ctor_set(v___x_4224_, 0, v___x_4230_);
v___x_4235_ = v___x_4224_;
goto v_reusejp_4234_;
}
else
{
lean_object* v_reuseFailAlloc_4243_; 
v_reuseFailAlloc_4243_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4243_, 0, v___x_4230_);
lean_ctor_set(v_reuseFailAlloc_4243_, 1, v___f_4226_);
lean_ctor_set(v_reuseFailAlloc_4243_, 2, v___f_4233_);
lean_ctor_set(v_reuseFailAlloc_4243_, 3, v___f_4232_);
lean_ctor_set(v_reuseFailAlloc_4243_, 4, v___f_4231_);
v___x_4235_ = v_reuseFailAlloc_4243_;
goto v_reusejp_4234_;
}
v_reusejp_4234_:
{
lean_object* v___x_4237_; 
if (v_isShared_4218_ == 0)
{
lean_ctor_set(v___x_4217_, 1, v___f_4227_);
lean_ctor_set(v___x_4217_, 0, v___x_4235_);
v___x_4237_ = v___x_4217_;
goto v_reusejp_4236_;
}
else
{
lean_object* v_reuseFailAlloc_4242_; 
v_reuseFailAlloc_4242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4242_, 0, v___x_4235_);
lean_ctor_set(v_reuseFailAlloc_4242_, 1, v___f_4227_);
v___x_4237_ = v_reuseFailAlloc_4242_;
goto v_reusejp_4236_;
}
v_reusejp_4236_:
{
lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_19007__overap_4240_; lean_object* v___x_4241_; 
v___x_4238_ = lean_box(0);
v___x_4239_ = l_instInhabitedOfMonad___redArg(v___x_4237_, v___x_4238_);
v___x_19007__overap_4240_ = lean_panic_fn_borrowed(v___x_4239_, v_msg_4183_);
lean_dec(v___x_4239_);
lean_inc(v___y_4187_);
lean_inc_ref(v___y_4186_);
lean_inc(v___y_4185_);
lean_inc_ref(v___y_4184_);
v___x_4241_ = lean_apply_5(v___x_19007__overap_4240_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_, lean_box(0));
return v___x_4241_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___boxed(lean_object* v_msg_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_){
_start:
{
lean_object* v_res_4260_; 
v_res_4260_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(v_msg_4254_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_);
lean_dec(v___y_4258_);
lean_dec_ref(v___y_4257_);
lean_dec(v___y_4256_);
lean_dec_ref(v___y_4255_);
return v_res_4260_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1(void){
_start:
{
lean_object* v___x_4262_; lean_object* v___x_4263_; 
v___x_4262_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__0));
v___x_4263_ = l_Lean_stringToMessageData(v___x_4262_);
return v___x_4263_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4(void){
_start:
{
lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; 
v___x_4266_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__2));
v___x_4267_ = lean_unsigned_to_nat(11u);
v___x_4268_ = lean_unsigned_to_nat(122u);
v___x_4269_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__3));
v___x_4270_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__2));
v___x_4271_ = l_mkPanicMessageWithDecl(v___x_4270_, v___x_4269_, v___x_4268_, v___x_4267_, v___x_4266_);
return v___x_4271_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(lean_object* v_constName_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_){
_start:
{
lean_object* v___x_4286_; lean_object* v_env_4287_; uint8_t v___x_4288_; lean_object* v___x_4289_; 
v___x_4286_ = lean_st_ref_get(v___y_4276_);
v_env_4287_ = lean_ctor_get(v___x_4286_, 0);
lean_inc_ref(v_env_4287_);
lean_dec(v___x_4286_);
v___x_4288_ = 0;
lean_inc(v_constName_4272_);
v___x_4289_ = l_Lean_Environment_findAsync_x3f(v_env_4287_, v_constName_4272_, v___x_4288_);
if (lean_obj_tag(v___x_4289_) == 1)
{
lean_object* v_val_4290_; uint8_t v_kind_4291_; 
v_val_4290_ = lean_ctor_get(v___x_4289_, 0);
lean_inc(v_val_4290_);
lean_dec_ref(v___x_4289_);
v_kind_4291_ = lean_ctor_get_uint8(v_val_4290_, sizeof(void*)*3);
if (v_kind_4291_ == 6)
{
lean_object* v___x_4292_; 
v___x_4292_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_4290_);
if (lean_obj_tag(v___x_4292_) == 6)
{
lean_object* v_val_4293_; lean_object* v___x_4295_; uint8_t v_isShared_4296_; uint8_t v_isSharedCheck_4300_; 
lean_dec(v_constName_4272_);
v_val_4293_ = lean_ctor_get(v___x_4292_, 0);
v_isSharedCheck_4300_ = !lean_is_exclusive(v___x_4292_);
if (v_isSharedCheck_4300_ == 0)
{
v___x_4295_ = v___x_4292_;
v_isShared_4296_ = v_isSharedCheck_4300_;
goto v_resetjp_4294_;
}
else
{
lean_inc(v_val_4293_);
lean_dec(v___x_4292_);
v___x_4295_ = lean_box(0);
v_isShared_4296_ = v_isSharedCheck_4300_;
goto v_resetjp_4294_;
}
v_resetjp_4294_:
{
lean_object* v___x_4298_; 
if (v_isShared_4296_ == 0)
{
lean_ctor_set_tag(v___x_4295_, 0);
v___x_4298_ = v___x_4295_;
goto v_reusejp_4297_;
}
else
{
lean_object* v_reuseFailAlloc_4299_; 
v_reuseFailAlloc_4299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4299_, 0, v_val_4293_);
v___x_4298_ = v_reuseFailAlloc_4299_;
goto v_reusejp_4297_;
}
v_reusejp_4297_:
{
return v___x_4298_;
}
}
}
else
{
lean_object* v___x_4301_; lean_object* v___x_4302_; 
lean_dec_ref(v___x_4292_);
v___x_4301_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4);
v___x_4302_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(v___x_4301_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_);
if (lean_obj_tag(v___x_4302_) == 0)
{
lean_object* v_a_4303_; lean_object* v___x_4305_; uint8_t v_isShared_4306_; uint8_t v_isSharedCheck_4311_; 
v_a_4303_ = lean_ctor_get(v___x_4302_, 0);
v_isSharedCheck_4311_ = !lean_is_exclusive(v___x_4302_);
if (v_isSharedCheck_4311_ == 0)
{
v___x_4305_ = v___x_4302_;
v_isShared_4306_ = v_isSharedCheck_4311_;
goto v_resetjp_4304_;
}
else
{
lean_inc(v_a_4303_);
lean_dec(v___x_4302_);
v___x_4305_ = lean_box(0);
v_isShared_4306_ = v_isSharedCheck_4311_;
goto v_resetjp_4304_;
}
v_resetjp_4304_:
{
if (lean_obj_tag(v_a_4303_) == 0)
{
lean_del_object(v___x_4305_);
goto v___jp_4278_;
}
else
{
lean_object* v_val_4307_; lean_object* v___x_4309_; 
lean_dec(v_constName_4272_);
v_val_4307_ = lean_ctor_get(v_a_4303_, 0);
lean_inc(v_val_4307_);
lean_dec_ref(v_a_4303_);
if (v_isShared_4306_ == 0)
{
lean_ctor_set(v___x_4305_, 0, v_val_4307_);
v___x_4309_ = v___x_4305_;
goto v_reusejp_4308_;
}
else
{
lean_object* v_reuseFailAlloc_4310_; 
v_reuseFailAlloc_4310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4310_, 0, v_val_4307_);
v___x_4309_ = v_reuseFailAlloc_4310_;
goto v_reusejp_4308_;
}
v_reusejp_4308_:
{
return v___x_4309_;
}
}
}
}
else
{
lean_object* v_a_4312_; lean_object* v___x_4314_; uint8_t v_isShared_4315_; uint8_t v_isSharedCheck_4319_; 
lean_dec(v_constName_4272_);
v_a_4312_ = lean_ctor_get(v___x_4302_, 0);
v_isSharedCheck_4319_ = !lean_is_exclusive(v___x_4302_);
if (v_isSharedCheck_4319_ == 0)
{
v___x_4314_ = v___x_4302_;
v_isShared_4315_ = v_isSharedCheck_4319_;
goto v_resetjp_4313_;
}
else
{
lean_inc(v_a_4312_);
lean_dec(v___x_4302_);
v___x_4314_ = lean_box(0);
v_isShared_4315_ = v_isSharedCheck_4319_;
goto v_resetjp_4313_;
}
v_resetjp_4313_:
{
lean_object* v___x_4317_; 
if (v_isShared_4315_ == 0)
{
v___x_4317_ = v___x_4314_;
goto v_reusejp_4316_;
}
else
{
lean_object* v_reuseFailAlloc_4318_; 
v_reuseFailAlloc_4318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4318_, 0, v_a_4312_);
v___x_4317_ = v_reuseFailAlloc_4318_;
goto v_reusejp_4316_;
}
v_reusejp_4316_:
{
return v___x_4317_;
}
}
}
}
}
else
{
lean_dec(v_val_4290_);
goto v___jp_4278_;
}
}
else
{
lean_dec(v___x_4289_);
goto v___jp_4278_;
}
v___jp_4278_:
{
lean_object* v___x_4279_; uint8_t v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; 
v___x_4279_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_4280_ = 0;
v___x_4281_ = l_Lean_MessageData_ofConstName(v_constName_4272_, v___x_4280_);
v___x_4282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4282_, 0, v___x_4279_);
lean_ctor_set(v___x_4282_, 1, v___x_4281_);
v___x_4283_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1);
v___x_4284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4284_, 0, v___x_4282_);
lean_ctor_set(v___x_4284_, 1, v___x_4283_);
v___x_4285_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_4284_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_);
return v___x_4285_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___boxed(lean_object* v_constName_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_){
_start:
{
lean_object* v_res_4326_; 
v_res_4326_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(v_constName_4320_, v___y_4321_, v___y_4322_, v___y_4323_, v___y_4324_);
lean_dec(v___y_4324_);
lean_dec_ref(v___y_4323_);
lean_dec(v___y_4322_);
lean_dec_ref(v___y_4321_);
return v_res_4326_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0(lean_object* v_head_4327_, lean_object* v___x_4328_, lean_object* v___x_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_){
_start:
{
lean_object* v___x_4335_; 
v___x_4335_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(v_head_4327_, v___y_4330_, v___y_4331_, v___y_4332_, v___y_4333_);
if (lean_obj_tag(v___x_4335_) == 0)
{
lean_object* v_a_4336_; lean_object* v___x_4338_; uint8_t v_isShared_4339_; uint8_t v_isSharedCheck_4347_; 
v_a_4336_ = lean_ctor_get(v___x_4335_, 0);
v_isSharedCheck_4347_ = !lean_is_exclusive(v___x_4335_);
if (v_isSharedCheck_4347_ == 0)
{
v___x_4338_ = v___x_4335_;
v_isShared_4339_ = v_isSharedCheck_4347_;
goto v_resetjp_4337_;
}
else
{
lean_inc(v_a_4336_);
lean_dec(v___x_4335_);
v___x_4338_ = lean_box(0);
v_isShared_4339_ = v_isSharedCheck_4347_;
goto v_resetjp_4337_;
}
v_resetjp_4337_:
{
lean_object* v_numFields_4340_; uint8_t v___x_4341_; 
v_numFields_4340_ = lean_ctor_get(v_a_4336_, 4);
v___x_4341_ = lean_nat_dec_lt(v___x_4328_, v_numFields_4340_);
if (v___x_4341_ == 0)
{
lean_object* v___x_4343_; 
lean_dec(v_a_4336_);
if (v_isShared_4339_ == 0)
{
lean_ctor_set(v___x_4338_, 0, v___x_4329_);
v___x_4343_ = v___x_4338_;
goto v_reusejp_4342_;
}
else
{
lean_object* v_reuseFailAlloc_4344_; 
v_reuseFailAlloc_4344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4344_, 0, v___x_4329_);
v___x_4343_ = v_reuseFailAlloc_4344_;
goto v_reusejp_4342_;
}
v_reusejp_4342_:
{
return v___x_4343_;
}
}
else
{
lean_object* v___x_4345_; 
lean_del_object(v___x_4338_);
lean_inc(v_a_4336_);
v___x_4345_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(v_a_4336_, v___y_4330_, v___y_4331_, v___y_4332_, v___y_4333_);
if (lean_obj_tag(v___x_4345_) == 0)
{
lean_object* v___x_4346_; 
lean_dec_ref(v___x_4345_);
v___x_4346_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(v_a_4336_, v___y_4330_, v___y_4331_, v___y_4332_, v___y_4333_);
return v___x_4346_;
}
else
{
lean_dec(v_a_4336_);
return v___x_4345_;
}
}
}
}
else
{
lean_object* v_a_4348_; lean_object* v___x_4350_; uint8_t v_isShared_4351_; uint8_t v_isSharedCheck_4355_; 
v_a_4348_ = lean_ctor_get(v___x_4335_, 0);
v_isSharedCheck_4355_ = !lean_is_exclusive(v___x_4335_);
if (v_isSharedCheck_4355_ == 0)
{
v___x_4350_ = v___x_4335_;
v_isShared_4351_ = v_isSharedCheck_4355_;
goto v_resetjp_4349_;
}
else
{
lean_inc(v_a_4348_);
lean_dec(v___x_4335_);
v___x_4350_ = lean_box(0);
v_isShared_4351_ = v_isSharedCheck_4355_;
goto v_resetjp_4349_;
}
v_resetjp_4349_:
{
lean_object* v___x_4353_; 
if (v_isShared_4351_ == 0)
{
v___x_4353_ = v___x_4350_;
goto v_reusejp_4352_;
}
else
{
lean_object* v_reuseFailAlloc_4354_; 
v_reuseFailAlloc_4354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4354_, 0, v_a_4348_);
v___x_4353_ = v_reuseFailAlloc_4354_;
goto v_reusejp_4352_;
}
v_reusejp_4352_:
{
return v___x_4353_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0___boxed(lean_object* v_head_4356_, lean_object* v___x_4357_, lean_object* v___x_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_){
_start:
{
lean_object* v_res_4364_; 
v_res_4364_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0(v_head_4356_, v___x_4357_, v___x_4358_, v___y_4359_, v___y_4360_, v___y_4361_, v___y_4362_);
lean_dec(v___y_4362_);
lean_dec_ref(v___y_4361_);
lean_dec(v___y_4360_);
lean_dec_ref(v___y_4359_);
lean_dec(v___x_4357_);
return v_res_4364_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(uint8_t v___y_4365_, uint8_t v___x_4366_, lean_object* v_as_x27_4367_, lean_object* v_b_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_){
_start:
{
if (lean_obj_tag(v_as_x27_4367_) == 0)
{
lean_object* v___x_4374_; 
v___x_4374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4374_, 0, v_b_4368_);
return v___x_4374_;
}
else
{
lean_object* v_head_4375_; lean_object* v_tail_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___f_4379_; uint8_t v___y_4381_; uint8_t v___x_4384_; 
v_head_4375_ = lean_ctor_get(v_as_x27_4367_, 0);
lean_inc_n(v_head_4375_, 2);
v_tail_4376_ = lean_ctor_get(v_as_x27_4367_, 1);
lean_inc(v_tail_4376_);
lean_dec_ref(v_as_x27_4367_);
v___x_4377_ = lean_unsigned_to_nat(0u);
v___x_4378_ = lean_box(0);
v___f_4379_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4379_, 0, v_head_4375_);
lean_closure_set(v___f_4379_, 1, v___x_4377_);
lean_closure_set(v___f_4379_, 2, v___x_4378_);
v___x_4384_ = l_Lean_isPrivateName(v_head_4375_);
lean_dec(v_head_4375_);
if (v___x_4384_ == 0)
{
v___y_4381_ = v___y_4365_;
goto v___jp_4380_;
}
else
{
v___y_4381_ = v___x_4366_;
goto v___jp_4380_;
}
v___jp_4380_:
{
lean_object* v___x_4382_; 
v___x_4382_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(v___f_4379_, v___y_4381_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_);
if (lean_obj_tag(v___x_4382_) == 0)
{
lean_dec_ref(v___x_4382_);
v_as_x27_4367_ = v_tail_4376_;
v_b_4368_ = v___x_4378_;
goto _start;
}
else
{
lean_dec(v_tail_4376_);
return v___x_4382_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___boxed(lean_object* v___y_4385_, lean_object* v___x_4386_, lean_object* v_as_x27_4387_, lean_object* v_b_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_){
_start:
{
uint8_t v___y_20116__boxed_4394_; uint8_t v___x_20117__boxed_4395_; lean_object* v_res_4396_; 
v___y_20116__boxed_4394_ = lean_unbox(v___y_4385_);
v___x_20117__boxed_4395_ = lean_unbox(v___x_4386_);
v_res_4396_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___y_20116__boxed_4394_, v___x_20117__boxed_4395_, v_as_x27_4387_, v_b_4388_, v___y_4389_, v___y_4390_, v___y_4391_, v___y_4392_);
lean_dec(v___y_4392_);
lean_dec_ref(v___y_4391_);
lean_dec(v___y_4390_);
lean_dec_ref(v___y_4389_);
return v_res_4396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__1(uint8_t v___y_4397_, uint8_t v_hasTrace_4398_, lean_object* v_ctors_4399_, lean_object* v___x_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_){
_start:
{
lean_object* v___x_4406_; 
v___x_4406_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___y_4397_, v_hasTrace_4398_, v_ctors_4399_, v___x_4400_, v___y_4401_, v___y_4402_, v___y_4403_, v___y_4404_);
if (lean_obj_tag(v___x_4406_) == 0)
{
lean_object* v___x_4408_; uint8_t v_isShared_4409_; uint8_t v_isSharedCheck_4413_; 
v_isSharedCheck_4413_ = !lean_is_exclusive(v___x_4406_);
if (v_isSharedCheck_4413_ == 0)
{
lean_object* v_unused_4414_; 
v_unused_4414_ = lean_ctor_get(v___x_4406_, 0);
lean_dec(v_unused_4414_);
v___x_4408_ = v___x_4406_;
v_isShared_4409_ = v_isSharedCheck_4413_;
goto v_resetjp_4407_;
}
else
{
lean_dec(v___x_4406_);
v___x_4408_ = lean_box(0);
v_isShared_4409_ = v_isSharedCheck_4413_;
goto v_resetjp_4407_;
}
v_resetjp_4407_:
{
lean_object* v___x_4411_; 
if (v_isShared_4409_ == 0)
{
lean_ctor_set(v___x_4408_, 0, v___x_4400_);
v___x_4411_ = v___x_4408_;
goto v_reusejp_4410_;
}
else
{
lean_object* v_reuseFailAlloc_4412_; 
v_reuseFailAlloc_4412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4412_, 0, v___x_4400_);
v___x_4411_ = v_reuseFailAlloc_4412_;
goto v_reusejp_4410_;
}
v_reusejp_4410_:
{
return v___x_4411_;
}
}
}
else
{
return v___x_4406_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed(lean_object* v___y_4415_, lean_object* v_hasTrace_4416_, lean_object* v_ctors_4417_, lean_object* v___x_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_){
_start:
{
uint8_t v___y_20161__boxed_4424_; uint8_t v_hasTrace_boxed_4425_; lean_object* v_res_4426_; 
v___y_20161__boxed_4424_ = lean_unbox(v___y_4415_);
v_hasTrace_boxed_4425_ = lean_unbox(v_hasTrace_4416_);
v_res_4426_ = l_Lean_Meta_mkInjectiveTheorems___lam__1(v___y_20161__boxed_4424_, v_hasTrace_boxed_4425_, v_ctors_4417_, v___x_4418_, v___y_4419_, v___y_4420_, v___y_4421_, v___y_4422_);
lean_dec(v___y_4422_);
lean_dec_ref(v___y_4421_);
lean_dec(v___y_4420_);
lean_dec_ref(v___y_4419_);
return v_res_4426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__2(uint8_t v_hasTrace_4427_, uint8_t v___x_4428_, lean_object* v_ctors_4429_, lean_object* v___x_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_){
_start:
{
lean_object* v___x_4436_; 
v___x_4436_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v_hasTrace_4427_, v___x_4428_, v_ctors_4429_, v___x_4430_, v___y_4431_, v___y_4432_, v___y_4433_, v___y_4434_);
if (lean_obj_tag(v___x_4436_) == 0)
{
lean_object* v___x_4438_; uint8_t v_isShared_4439_; uint8_t v_isSharedCheck_4443_; 
v_isSharedCheck_4443_ = !lean_is_exclusive(v___x_4436_);
if (v_isSharedCheck_4443_ == 0)
{
lean_object* v_unused_4444_; 
v_unused_4444_ = lean_ctor_get(v___x_4436_, 0);
lean_dec(v_unused_4444_);
v___x_4438_ = v___x_4436_;
v_isShared_4439_ = v_isSharedCheck_4443_;
goto v_resetjp_4437_;
}
else
{
lean_dec(v___x_4436_);
v___x_4438_ = lean_box(0);
v_isShared_4439_ = v_isSharedCheck_4443_;
goto v_resetjp_4437_;
}
v_resetjp_4437_:
{
lean_object* v___x_4441_; 
if (v_isShared_4439_ == 0)
{
lean_ctor_set(v___x_4438_, 0, v___x_4430_);
v___x_4441_ = v___x_4438_;
goto v_reusejp_4440_;
}
else
{
lean_object* v_reuseFailAlloc_4442_; 
v_reuseFailAlloc_4442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4442_, 0, v___x_4430_);
v___x_4441_ = v_reuseFailAlloc_4442_;
goto v_reusejp_4440_;
}
v_reusejp_4440_:
{
return v___x_4441_;
}
}
}
else
{
return v___x_4436_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__2___boxed(lean_object* v_hasTrace_4445_, lean_object* v___x_4446_, lean_object* v_ctors_4447_, lean_object* v___x_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_){
_start:
{
uint8_t v_hasTrace_boxed_4454_; uint8_t v___x_20202__boxed_4455_; lean_object* v_res_4456_; 
v_hasTrace_boxed_4454_ = lean_unbox(v_hasTrace_4445_);
v___x_20202__boxed_4455_ = lean_unbox(v___x_4446_);
v_res_4456_ = l_Lean_Meta_mkInjectiveTheorems___lam__2(v_hasTrace_boxed_4454_, v___x_20202__boxed_4455_, v_ctors_4447_, v___x_4448_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_);
lean_dec(v___y_4452_);
lean_dec_ref(v___y_4451_);
lean_dec(v___y_4450_);
lean_dec_ref(v___y_4449_);
return v_res_4456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__3(uint8_t v___x_4457_, uint8_t v_isUnsafe_4458_, lean_object* v_ctors_4459_, lean_object* v___x_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_){
_start:
{
lean_object* v___x_4466_; 
v___x_4466_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___x_4457_, v_isUnsafe_4458_, v_ctors_4459_, v___x_4460_, v___y_4461_, v___y_4462_, v___y_4463_, v___y_4464_);
if (lean_obj_tag(v___x_4466_) == 0)
{
lean_object* v___x_4468_; uint8_t v_isShared_4469_; uint8_t v_isSharedCheck_4473_; 
v_isSharedCheck_4473_ = !lean_is_exclusive(v___x_4466_);
if (v_isSharedCheck_4473_ == 0)
{
lean_object* v_unused_4474_; 
v_unused_4474_ = lean_ctor_get(v___x_4466_, 0);
lean_dec(v_unused_4474_);
v___x_4468_ = v___x_4466_;
v_isShared_4469_ = v_isSharedCheck_4473_;
goto v_resetjp_4467_;
}
else
{
lean_dec(v___x_4466_);
v___x_4468_ = lean_box(0);
v_isShared_4469_ = v_isSharedCheck_4473_;
goto v_resetjp_4467_;
}
v_resetjp_4467_:
{
lean_object* v___x_4471_; 
if (v_isShared_4469_ == 0)
{
lean_ctor_set(v___x_4468_, 0, v___x_4460_);
v___x_4471_ = v___x_4468_;
goto v_reusejp_4470_;
}
else
{
lean_object* v_reuseFailAlloc_4472_; 
v_reuseFailAlloc_4472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4472_, 0, v___x_4460_);
v___x_4471_ = v_reuseFailAlloc_4472_;
goto v_reusejp_4470_;
}
v_reusejp_4470_:
{
return v___x_4471_;
}
}
}
else
{
return v___x_4466_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__3___boxed(lean_object* v___x_4475_, lean_object* v_isUnsafe_4476_, lean_object* v_ctors_4477_, lean_object* v___x_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_){
_start:
{
uint8_t v___x_20243__boxed_4484_; uint8_t v_isUnsafe_boxed_4485_; lean_object* v_res_4486_; 
v___x_20243__boxed_4484_ = lean_unbox(v___x_4475_);
v_isUnsafe_boxed_4485_ = lean_unbox(v_isUnsafe_4476_);
v_res_4486_ = l_Lean_Meta_mkInjectiveTheorems___lam__3(v___x_20243__boxed_4484_, v_isUnsafe_boxed_4485_, v_ctors_4477_, v___x_4478_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_);
lean_dec(v___y_4482_);
lean_dec_ref(v___y_4481_);
lean_dec(v___y_4480_);
lean_dec_ref(v___y_4479_);
return v_res_4486_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4488_; lean_object* v___x_4489_; 
v___x_4488_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__0));
v___x_4489_ = l_Lean_stringToMessageData(v___x_4488_);
return v___x_4489_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(lean_object* v_constName_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_){
_start:
{
lean_object* v___x_4496_; lean_object* v_env_4497_; lean_object* v___x_4498_; 
v___x_4496_ = lean_st_ref_get(v___y_4494_);
v_env_4497_ = lean_ctor_get(v___x_4496_, 0);
lean_inc_ref(v_env_4497_);
lean_dec(v___x_4496_);
lean_inc(v_constName_4490_);
v___x_4498_ = l_Lean_isInductiveCore_x3f(v_env_4497_, v_constName_4490_);
if (lean_obj_tag(v___x_4498_) == 0)
{
lean_object* v___x_4499_; uint8_t v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; 
v___x_4499_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_4500_ = 0;
v___x_4501_ = l_Lean_MessageData_ofConstName(v_constName_4490_, v___x_4500_);
v___x_4502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4502_, 0, v___x_4499_);
lean_ctor_set(v___x_4502_, 1, v___x_4501_);
v___x_4503_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1);
v___x_4504_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4504_, 0, v___x_4502_);
lean_ctor_set(v___x_4504_, 1, v___x_4503_);
v___x_4505_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_4504_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_);
return v___x_4505_;
}
else
{
lean_object* v_val_4506_; lean_object* v___x_4508_; uint8_t v_isShared_4509_; uint8_t v_isSharedCheck_4513_; 
lean_dec(v_constName_4490_);
v_val_4506_ = lean_ctor_get(v___x_4498_, 0);
v_isSharedCheck_4513_ = !lean_is_exclusive(v___x_4498_);
if (v_isSharedCheck_4513_ == 0)
{
v___x_4508_ = v___x_4498_;
v_isShared_4509_ = v_isSharedCheck_4513_;
goto v_resetjp_4507_;
}
else
{
lean_inc(v_val_4506_);
lean_dec(v___x_4498_);
v___x_4508_ = lean_box(0);
v_isShared_4509_ = v_isSharedCheck_4513_;
goto v_resetjp_4507_;
}
v_resetjp_4507_:
{
lean_object* v___x_4511_; 
if (v_isShared_4509_ == 0)
{
lean_ctor_set_tag(v___x_4508_, 0);
v___x_4511_ = v___x_4508_;
goto v_reusejp_4510_;
}
else
{
lean_object* v_reuseFailAlloc_4512_; 
v_reuseFailAlloc_4512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4512_, 0, v_val_4506_);
v___x_4511_ = v_reuseFailAlloc_4512_;
goto v_reusejp_4510_;
}
v_reusejp_4510_:
{
return v___x_4511_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___boxed(lean_object* v_constName_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_){
_start:
{
lean_object* v_res_4520_; 
v_res_4520_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_constName_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_);
lean_dec(v___y_4518_);
lean_dec_ref(v___y_4517_);
lean_dec(v___y_4516_);
lean_dec_ref(v___y_4515_);
return v_res_4520_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__0(void){
_start:
{
lean_object* v___x_4521_; 
v___x_4521_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4521_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__1(void){
_start:
{
lean_object* v___x_4522_; lean_object* v___x_4523_; 
v___x_4522_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__0, &l_Lean_Meta_mkInjectiveTheorems___closed__0_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__0);
v___x_4523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4523_, 0, v___x_4522_);
return v___x_4523_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__2(void){
_start:
{
lean_object* v___x_4524_; lean_object* v___x_4525_; lean_object* v___x_4526_; 
v___x_4524_ = lean_unsigned_to_nat(32u);
v___x_4525_ = lean_mk_empty_array_with_capacity(v___x_4524_);
v___x_4526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4526_, 0, v___x_4525_);
return v___x_4526_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__3(void){
_start:
{
size_t v___x_4527_; lean_object* v___x_4528_; lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; lean_object* v___x_4532_; 
v___x_4527_ = ((size_t)5ULL);
v___x_4528_ = lean_unsigned_to_nat(0u);
v___x_4529_ = lean_unsigned_to_nat(32u);
v___x_4530_ = lean_mk_empty_array_with_capacity(v___x_4529_);
v___x_4531_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__2, &l_Lean_Meta_mkInjectiveTheorems___closed__2_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__2);
v___x_4532_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4532_, 0, v___x_4531_);
lean_ctor_set(v___x_4532_, 1, v___x_4530_);
lean_ctor_set(v___x_4532_, 2, v___x_4528_);
lean_ctor_set(v___x_4532_, 3, v___x_4528_);
lean_ctor_set_usize(v___x_4532_, 4, v___x_4527_);
return v___x_4532_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__4(void){
_start:
{
lean_object* v___x_4533_; lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; 
v___x_4533_ = lean_box(1);
v___x_4534_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_4535_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_4536_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4536_, 0, v___x_4535_);
lean_ctor_set(v___x_4536_, 1, v___x_4534_);
lean_ctor_set(v___x_4536_, 2, v___x_4533_);
return v___x_4536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems(lean_object* v_declName_4539_, lean_object* v_a_4540_, lean_object* v_a_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_){
_start:
{
lean_object* v___x_4545_; lean_object* v___x_4546_; 
v___x_4545_ = lean_st_ref_get(v_a_4543_);
lean_inc(v_declName_4539_);
v___x_4546_ = l_Lean_Meta_isInductivePredicate(v_declName_4539_, v_a_4540_, v_a_4541_, v_a_4542_, v_a_4543_);
if (lean_obj_tag(v___x_4546_) == 0)
{
lean_object* v_a_4547_; lean_object* v___x_4549_; uint8_t v_isShared_4550_; uint8_t v_isSharedCheck_4743_; 
v_a_4547_ = lean_ctor_get(v___x_4546_, 0);
v_isSharedCheck_4743_ = !lean_is_exclusive(v___x_4546_);
if (v_isSharedCheck_4743_ == 0)
{
v___x_4549_ = v___x_4546_;
v_isShared_4550_ = v_isSharedCheck_4743_;
goto v_resetjp_4548_;
}
else
{
lean_inc(v_a_4547_);
lean_dec(v___x_4546_);
v___x_4549_ = lean_box(0);
v_isShared_4550_ = v_isSharedCheck_4743_;
goto v_resetjp_4548_;
}
v_resetjp_4548_:
{
lean_object* v_env_4556_; lean_object* v___f_4557_; lean_object* v___x_4558_; uint8_t v___x_4559_; uint8_t v___y_4561_; lean_object* v___y_4562_; lean_object* v___y_4563_; lean_object* v___y_4564_; lean_object* v___y_4565_; lean_object* v___y_4566_; lean_object* v_a_4567_; uint8_t v___y_4577_; lean_object* v___y_4578_; lean_object* v___y_4579_; lean_object* v___y_4580_; lean_object* v___y_4581_; lean_object* v___y_4582_; lean_object* v_a_4583_; uint8_t v___y_4586_; lean_object* v___y_4587_; lean_object* v___y_4588_; lean_object* v___y_4589_; lean_object* v___y_4590_; lean_object* v___y_4591_; lean_object* v_a_4592_; uint8_t v___y_4595_; lean_object* v___y_4596_; lean_object* v___y_4597_; lean_object* v___y_4598_; lean_object* v___y_4599_; lean_object* v___y_4600_; lean_object* v_a_4601_; uint8_t v___y_4614_; lean_object* v___y_4615_; lean_object* v___y_4616_; lean_object* v___y_4617_; lean_object* v___y_4618_; lean_object* v___y_4619_; lean_object* v_a_4620_; uint8_t v___y_4623_; lean_object* v___y_4624_; lean_object* v___y_4625_; lean_object* v___y_4626_; lean_object* v___y_4627_; lean_object* v___y_4628_; lean_object* v_a_4629_; uint8_t v___y_4632_; uint8_t v___y_4633_; lean_object* v___y_4634_; lean_object* v___y_4635_; lean_object* v___y_4636_; uint8_t v___y_4674_; uint8_t v___x_4739_; 
v_env_4556_ = lean_ctor_get(v___x_4545_, 0);
lean_inc_ref(v_env_4556_);
lean_dec(v___x_4545_);
lean_inc(v_declName_4539_);
v___f_4557_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4557_, 0, v_declName_4539_);
v___x_4558_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__2));
v___x_4559_ = 1;
v___x_4739_ = l_Lean_Environment_contains(v_env_4556_, v___x_4558_, v___x_4559_);
if (v___x_4739_ == 0)
{
v___y_4674_ = v___x_4739_;
goto v___jp_4673_;
}
else
{
lean_object* v_options_4740_; lean_object* v___x_4741_; uint8_t v___x_4742_; 
v_options_4740_ = lean_ctor_get(v_a_4542_, 2);
v___x_4741_ = l_Lean_Meta_genInjectivity;
v___x_4742_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_4740_, v___x_4741_);
v___y_4674_ = v___x_4742_;
goto v___jp_4673_;
}
v___jp_4551_:
{
lean_object* v___x_4552_; lean_object* v___x_4554_; 
v___x_4552_ = lean_box(0);
if (v_isShared_4550_ == 0)
{
lean_ctor_set(v___x_4549_, 0, v___x_4552_);
v___x_4554_ = v___x_4549_;
goto v_reusejp_4553_;
}
else
{
lean_object* v_reuseFailAlloc_4555_; 
v_reuseFailAlloc_4555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4555_, 0, v___x_4552_);
v___x_4554_ = v_reuseFailAlloc_4555_;
goto v_reusejp_4553_;
}
v_reusejp_4553_:
{
return v___x_4554_;
}
}
v___jp_4560_:
{
lean_object* v___x_4568_; double v___x_4569_; double v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; 
v___x_4568_ = lean_io_get_num_heartbeats();
v___x_4569_ = lean_float_of_nat(v___y_4565_);
v___x_4570_ = lean_float_of_nat(v___x_4568_);
v___x_4571_ = lean_box_float(v___x_4569_);
v___x_4572_ = lean_box_float(v___x_4570_);
v___x_4573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4573_, 0, v___x_4571_);
lean_ctor_set(v___x_4573_, 1, v___x_4572_);
v___x_4574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4574_, 0, v_a_4567_);
lean_ctor_set(v___x_4574_, 1, v___x_4573_);
lean_inc_ref(v___y_4562_);
lean_inc(v___y_4563_);
v___x_4575_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v___y_4563_, v___x_4559_, v___y_4562_, v___y_4564_, v___y_4561_, v___y_4566_, v___f_4557_, v___x_4574_, v_a_4540_, v_a_4541_, v_a_4542_, v_a_4543_);
return v___x_4575_;
}
v___jp_4576_:
{
lean_object* v___x_4584_; 
v___x_4584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4584_, 0, v_a_4583_);
v___y_4561_ = v___y_4577_;
v___y_4562_ = v___y_4578_;
v___y_4563_ = v___y_4579_;
v___y_4564_ = v___y_4580_;
v___y_4565_ = v___y_4581_;
v___y_4566_ = v___y_4582_;
v_a_4567_ = v___x_4584_;
goto v___jp_4560_;
}
v___jp_4585_:
{
lean_object* v___x_4593_; 
v___x_4593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4593_, 0, v_a_4592_);
v___y_4561_ = v___y_4586_;
v___y_4562_ = v___y_4587_;
v___y_4563_ = v___y_4588_;
v___y_4564_ = v___y_4589_;
v___y_4565_ = v___y_4590_;
v___y_4566_ = v___y_4591_;
v_a_4567_ = v___x_4593_;
goto v___jp_4560_;
}
v___jp_4594_:
{
lean_object* v___x_4602_; double v___x_4603_; double v___x_4604_; double v___x_4605_; double v___x_4606_; double v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; 
v___x_4602_ = lean_io_mono_nanos_now();
v___x_4603_ = lean_float_of_nat(v___y_4597_);
v___x_4604_ = lean_float_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0);
v___x_4605_ = lean_float_div(v___x_4603_, v___x_4604_);
v___x_4606_ = lean_float_of_nat(v___x_4602_);
v___x_4607_ = lean_float_div(v___x_4606_, v___x_4604_);
v___x_4608_ = lean_box_float(v___x_4605_);
v___x_4609_ = lean_box_float(v___x_4607_);
v___x_4610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4610_, 0, v___x_4608_);
lean_ctor_set(v___x_4610_, 1, v___x_4609_);
v___x_4611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4611_, 0, v_a_4601_);
lean_ctor_set(v___x_4611_, 1, v___x_4610_);
lean_inc_ref(v___y_4596_);
lean_inc(v___y_4598_);
v___x_4612_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v___y_4598_, v___x_4559_, v___y_4596_, v___y_4599_, v___y_4595_, v___y_4600_, v___f_4557_, v___x_4611_, v_a_4540_, v_a_4541_, v_a_4542_, v_a_4543_);
return v___x_4612_;
}
v___jp_4613_:
{
lean_object* v___x_4621_; 
v___x_4621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4621_, 0, v_a_4620_);
v___y_4595_ = v___y_4614_;
v___y_4596_ = v___y_4615_;
v___y_4597_ = v___y_4616_;
v___y_4598_ = v___y_4617_;
v___y_4599_ = v___y_4618_;
v___y_4600_ = v___y_4619_;
v_a_4601_ = v___x_4621_;
goto v___jp_4594_;
}
v___jp_4622_:
{
lean_object* v___x_4630_; 
v___x_4630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4630_, 0, v_a_4629_);
v___y_4595_ = v___y_4623_;
v___y_4596_ = v___y_4624_;
v___y_4597_ = v___y_4625_;
v___y_4598_ = v___y_4626_;
v___y_4599_ = v___y_4627_;
v___y_4600_ = v___y_4628_;
v_a_4601_ = v___x_4630_;
goto v___jp_4594_;
}
v___jp_4631_:
{
lean_object* v___x_4637_; lean_object* v_a_4638_; lean_object* v___x_4639_; uint8_t v___x_4640_; 
v___x_4637_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v_a_4543_);
v_a_4638_ = lean_ctor_get(v___x_4637_, 0);
lean_inc(v_a_4638_);
lean_dec_ref(v___x_4637_);
v___x_4639_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4640_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v___y_4636_, v___x_4639_);
if (v___x_4640_ == 0)
{
lean_object* v___x_4641_; lean_object* v___x_4642_; 
v___x_4641_ = lean_io_mono_nanos_now();
v___x_4642_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4539_, v_a_4540_, v_a_4541_, v_a_4542_, v_a_4543_);
if (lean_obj_tag(v___x_4642_) == 0)
{
lean_object* v_a_4643_; uint8_t v_isUnsafe_4644_; 
v_a_4643_ = lean_ctor_get(v___x_4642_, 0);
lean_inc(v_a_4643_);
lean_dec_ref(v___x_4642_);
v_isUnsafe_4644_ = lean_ctor_get_uint8(v_a_4643_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4644_ == 0)
{
lean_object* v_ctors_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___f_4651_; lean_object* v___x_4652_; 
v_ctors_4645_ = lean_ctor_get(v_a_4643_, 4);
lean_inc(v_ctors_4645_);
lean_dec(v_a_4643_);
v___x_4646_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4647_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4648_ = lean_box(0);
v___x_4649_ = lean_box(v___y_4632_);
v___x_4650_ = lean_box(v___x_4640_);
v___f_4651_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__2___boxed), 9, 4);
lean_closure_set(v___f_4651_, 0, v___x_4649_);
lean_closure_set(v___f_4651_, 1, v___x_4650_);
lean_closure_set(v___f_4651_, 2, v_ctors_4645_);
lean_closure_set(v___f_4651_, 3, v___x_4648_);
v___x_4652_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4646_, v___x_4647_, v___f_4651_, v_a_4540_, v_a_4541_, v_a_4542_, v_a_4543_);
if (lean_obj_tag(v___x_4652_) == 0)
{
lean_object* v_a_4653_; 
v_a_4653_ = lean_ctor_get(v___x_4652_, 0);
lean_inc(v_a_4653_);
lean_dec_ref(v___x_4652_);
v___y_4614_ = v___y_4633_;
v___y_4615_ = v___y_4634_;
v___y_4616_ = v___x_4641_;
v___y_4617_ = v___y_4635_;
v___y_4618_ = v___y_4636_;
v___y_4619_ = v_a_4638_;
v_a_4620_ = v_a_4653_;
goto v___jp_4613_;
}
else
{
lean_object* v_a_4654_; 
v_a_4654_ = lean_ctor_get(v___x_4652_, 0);
lean_inc(v_a_4654_);
lean_dec_ref(v___x_4652_);
v___y_4623_ = v___y_4633_;
v___y_4624_ = v___y_4634_;
v___y_4625_ = v___x_4641_;
v___y_4626_ = v___y_4635_;
v___y_4627_ = v___y_4636_;
v___y_4628_ = v_a_4638_;
v_a_4629_ = v_a_4654_;
goto v___jp_4622_;
}
}
else
{
lean_object* v___x_4655_; 
lean_dec(v_a_4643_);
v___x_4655_ = lean_box(0);
v___y_4614_ = v___y_4633_;
v___y_4615_ = v___y_4634_;
v___y_4616_ = v___x_4641_;
v___y_4617_ = v___y_4635_;
v___y_4618_ = v___y_4636_;
v___y_4619_ = v_a_4638_;
v_a_4620_ = v___x_4655_;
goto v___jp_4613_;
}
}
else
{
lean_object* v_a_4656_; 
v_a_4656_ = lean_ctor_get(v___x_4642_, 0);
lean_inc(v_a_4656_);
lean_dec_ref(v___x_4642_);
v___y_4623_ = v___y_4633_;
v___y_4624_ = v___y_4634_;
v___y_4625_ = v___x_4641_;
v___y_4626_ = v___y_4635_;
v___y_4627_ = v___y_4636_;
v___y_4628_ = v_a_4638_;
v_a_4629_ = v_a_4656_;
goto v___jp_4622_;
}
}
else
{
lean_object* v___x_4657_; lean_object* v___x_4658_; 
v___x_4657_ = lean_io_get_num_heartbeats();
v___x_4658_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4539_, v_a_4540_, v_a_4541_, v_a_4542_, v_a_4543_);
if (lean_obj_tag(v___x_4658_) == 0)
{
lean_object* v_a_4659_; uint8_t v_isUnsafe_4660_; 
v_a_4659_ = lean_ctor_get(v___x_4658_, 0);
lean_inc(v_a_4659_);
lean_dec_ref(v___x_4658_);
v_isUnsafe_4660_ = lean_ctor_get_uint8(v_a_4659_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4660_ == 0)
{
lean_object* v_ctors_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___f_4667_; lean_object* v___x_4668_; 
v_ctors_4661_ = lean_ctor_get(v_a_4659_, 4);
lean_inc(v_ctors_4661_);
lean_dec(v_a_4659_);
v___x_4662_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4663_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4664_ = lean_box(0);
v___x_4665_ = lean_box(v___x_4640_);
v___x_4666_ = lean_box(v_isUnsafe_4660_);
v___f_4667_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__3___boxed), 9, 4);
lean_closure_set(v___f_4667_, 0, v___x_4665_);
lean_closure_set(v___f_4667_, 1, v___x_4666_);
lean_closure_set(v___f_4667_, 2, v_ctors_4661_);
lean_closure_set(v___f_4667_, 3, v___x_4664_);
v___x_4668_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4662_, v___x_4663_, v___f_4667_, v_a_4540_, v_a_4541_, v_a_4542_, v_a_4543_);
if (lean_obj_tag(v___x_4668_) == 0)
{
lean_object* v_a_4669_; 
v_a_4669_ = lean_ctor_get(v___x_4668_, 0);
lean_inc(v_a_4669_);
lean_dec_ref(v___x_4668_);
v___y_4577_ = v___y_4633_;
v___y_4578_ = v___y_4634_;
v___y_4579_ = v___y_4635_;
v___y_4580_ = v___y_4636_;
v___y_4581_ = v___x_4657_;
v___y_4582_ = v_a_4638_;
v_a_4583_ = v_a_4669_;
goto v___jp_4576_;
}
else
{
lean_object* v_a_4670_; 
v_a_4670_ = lean_ctor_get(v___x_4668_, 0);
lean_inc(v_a_4670_);
lean_dec_ref(v___x_4668_);
v___y_4586_ = v___y_4633_;
v___y_4587_ = v___y_4634_;
v___y_4588_ = v___y_4635_;
v___y_4589_ = v___y_4636_;
v___y_4590_ = v___x_4657_;
v___y_4591_ = v_a_4638_;
v_a_4592_ = v_a_4670_;
goto v___jp_4585_;
}
}
else
{
lean_object* v___x_4671_; 
lean_dec(v_a_4659_);
v___x_4671_ = lean_box(0);
v___y_4577_ = v___y_4633_;
v___y_4578_ = v___y_4634_;
v___y_4579_ = v___y_4635_;
v___y_4580_ = v___y_4636_;
v___y_4581_ = v___x_4657_;
v___y_4582_ = v_a_4638_;
v_a_4583_ = v___x_4671_;
goto v___jp_4576_;
}
}
else
{
lean_object* v_a_4672_; 
v_a_4672_ = lean_ctor_get(v___x_4658_, 0);
lean_inc(v_a_4672_);
lean_dec_ref(v___x_4658_);
v___y_4586_ = v___y_4633_;
v___y_4587_ = v___y_4634_;
v___y_4588_ = v___y_4635_;
v___y_4589_ = v___y_4636_;
v___y_4590_ = v___x_4657_;
v___y_4591_ = v_a_4638_;
v_a_4592_ = v_a_4672_;
goto v___jp_4585_;
}
}
}
v___jp_4673_:
{
if (v___y_4674_ == 0)
{
lean_dec_ref(v___f_4557_);
lean_dec(v_a_4547_);
lean_dec(v_declName_4539_);
goto v___jp_4551_;
}
else
{
uint8_t v___x_4675_; 
v___x_4675_ = lean_unbox(v_a_4547_);
lean_dec(v_a_4547_);
if (v___x_4675_ == 0)
{
lean_object* v_options_4676_; uint8_t v_hasTrace_4677_; 
lean_del_object(v___x_4549_);
v_options_4676_ = lean_ctor_get(v_a_4542_, 2);
v_hasTrace_4677_ = lean_ctor_get_uint8(v_options_4676_, sizeof(void*)*1);
if (v_hasTrace_4677_ == 0)
{
lean_object* v___x_4678_; 
lean_dec_ref(v___f_4557_);
v___x_4678_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4539_, v_a_4540_, v_a_4541_, v_a_4542_, v_a_4543_);
if (lean_obj_tag(v___x_4678_) == 0)
{
lean_object* v_a_4679_; lean_object* v___x_4681_; uint8_t v_isShared_4682_; uint8_t v_isSharedCheck_4696_; 
v_a_4679_ = lean_ctor_get(v___x_4678_, 0);
v_isSharedCheck_4696_ = !lean_is_exclusive(v___x_4678_);
if (v_isSharedCheck_4696_ == 0)
{
v___x_4681_ = v___x_4678_;
v_isShared_4682_ = v_isSharedCheck_4696_;
goto v_resetjp_4680_;
}
else
{
lean_inc(v_a_4679_);
lean_dec(v___x_4678_);
v___x_4681_ = lean_box(0);
v_isShared_4682_ = v_isSharedCheck_4696_;
goto v_resetjp_4680_;
}
v_resetjp_4680_:
{
uint8_t v_isUnsafe_4683_; 
v_isUnsafe_4683_ = lean_ctor_get_uint8(v_a_4679_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4683_ == 0)
{
lean_object* v_ctors_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___f_4690_; lean_object* v___x_4691_; 
lean_del_object(v___x_4681_);
v_ctors_4684_ = lean_ctor_get(v_a_4679_, 4);
lean_inc(v_ctors_4684_);
lean_dec(v_a_4679_);
v___x_4685_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4686_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4687_ = lean_box(0);
v___x_4688_ = lean_box(v___y_4674_);
v___x_4689_ = lean_box(v_hasTrace_4677_);
v___f_4690_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed), 9, 4);
lean_closure_set(v___f_4690_, 0, v___x_4688_);
lean_closure_set(v___f_4690_, 1, v___x_4689_);
lean_closure_set(v___f_4690_, 2, v_ctors_4684_);
lean_closure_set(v___f_4690_, 3, v___x_4687_);
v___x_4691_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4685_, v___x_4686_, v___f_4690_, v_a_4540_, v_a_4541_, v_a_4542_, v_a_4543_);
return v___x_4691_;
}
else
{
lean_object* v___x_4692_; lean_object* v___x_4694_; 
lean_dec(v_a_4679_);
v___x_4692_ = lean_box(0);
if (v_isShared_4682_ == 0)
{
lean_ctor_set(v___x_4681_, 0, v___x_4692_);
v___x_4694_ = v___x_4681_;
goto v_reusejp_4693_;
}
else
{
lean_object* v_reuseFailAlloc_4695_; 
v_reuseFailAlloc_4695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4695_, 0, v___x_4692_);
v___x_4694_ = v_reuseFailAlloc_4695_;
goto v_reusejp_4693_;
}
v_reusejp_4693_:
{
return v___x_4694_;
}
}
}
}
else
{
lean_object* v_a_4697_; lean_object* v___x_4699_; uint8_t v_isShared_4700_; uint8_t v_isSharedCheck_4704_; 
v_a_4697_ = lean_ctor_get(v___x_4678_, 0);
v_isSharedCheck_4704_ = !lean_is_exclusive(v___x_4678_);
if (v_isSharedCheck_4704_ == 0)
{
v___x_4699_ = v___x_4678_;
v_isShared_4700_ = v_isSharedCheck_4704_;
goto v_resetjp_4698_;
}
else
{
lean_inc(v_a_4697_);
lean_dec(v___x_4678_);
v___x_4699_ = lean_box(0);
v_isShared_4700_ = v_isSharedCheck_4704_;
goto v_resetjp_4698_;
}
v_resetjp_4698_:
{
lean_object* v___x_4702_; 
if (v_isShared_4700_ == 0)
{
v___x_4702_ = v___x_4699_;
goto v_reusejp_4701_;
}
else
{
lean_object* v_reuseFailAlloc_4703_; 
v_reuseFailAlloc_4703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4703_, 0, v_a_4697_);
v___x_4702_ = v_reuseFailAlloc_4703_;
goto v_reusejp_4701_;
}
v_reusejp_4701_:
{
return v___x_4702_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; uint8_t v___x_4709_; 
v_inheritedTraceOptions_4705_ = lean_ctor_get(v_a_4542_, 13);
v___x_4706_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_4707_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_4708_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_4709_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4705_, v_options_4676_, v___x_4708_);
if (v___x_4709_ == 0)
{
lean_object* v___x_4710_; uint8_t v___x_4711_; 
v___x_4710_ = l_Lean_trace_profiler;
v___x_4711_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_4676_, v___x_4710_);
if (v___x_4711_ == 0)
{
lean_object* v___x_4712_; 
lean_dec_ref(v___f_4557_);
v___x_4712_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4539_, v_a_4540_, v_a_4541_, v_a_4542_, v_a_4543_);
if (lean_obj_tag(v___x_4712_) == 0)
{
lean_object* v_a_4713_; lean_object* v___x_4715_; uint8_t v_isShared_4716_; uint8_t v_isSharedCheck_4730_; 
v_a_4713_ = lean_ctor_get(v___x_4712_, 0);
v_isSharedCheck_4730_ = !lean_is_exclusive(v___x_4712_);
if (v_isSharedCheck_4730_ == 0)
{
v___x_4715_ = v___x_4712_;
v_isShared_4716_ = v_isSharedCheck_4730_;
goto v_resetjp_4714_;
}
else
{
lean_inc(v_a_4713_);
lean_dec(v___x_4712_);
v___x_4715_ = lean_box(0);
v_isShared_4716_ = v_isSharedCheck_4730_;
goto v_resetjp_4714_;
}
v_resetjp_4714_:
{
uint8_t v_isUnsafe_4717_; 
v_isUnsafe_4717_ = lean_ctor_get_uint8(v_a_4713_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4717_ == 0)
{
lean_object* v_ctors_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v___f_4724_; lean_object* v___x_4725_; 
lean_del_object(v___x_4715_);
v_ctors_4718_ = lean_ctor_get(v_a_4713_, 4);
lean_inc(v_ctors_4718_);
lean_dec(v_a_4713_);
v___x_4719_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4720_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4721_ = lean_box(0);
v___x_4722_ = lean_box(v_hasTrace_4677_);
v___x_4723_ = lean_box(v___x_4711_);
v___f_4724_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__2___boxed), 9, 4);
lean_closure_set(v___f_4724_, 0, v___x_4722_);
lean_closure_set(v___f_4724_, 1, v___x_4723_);
lean_closure_set(v___f_4724_, 2, v_ctors_4718_);
lean_closure_set(v___f_4724_, 3, v___x_4721_);
v___x_4725_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4719_, v___x_4720_, v___f_4724_, v_a_4540_, v_a_4541_, v_a_4542_, v_a_4543_);
return v___x_4725_;
}
else
{
lean_object* v___x_4726_; lean_object* v___x_4728_; 
lean_dec(v_a_4713_);
v___x_4726_ = lean_box(0);
if (v_isShared_4716_ == 0)
{
lean_ctor_set(v___x_4715_, 0, v___x_4726_);
v___x_4728_ = v___x_4715_;
goto v_reusejp_4727_;
}
else
{
lean_object* v_reuseFailAlloc_4729_; 
v_reuseFailAlloc_4729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4729_, 0, v___x_4726_);
v___x_4728_ = v_reuseFailAlloc_4729_;
goto v_reusejp_4727_;
}
v_reusejp_4727_:
{
return v___x_4728_;
}
}
}
}
else
{
lean_object* v_a_4731_; lean_object* v___x_4733_; uint8_t v_isShared_4734_; uint8_t v_isSharedCheck_4738_; 
v_a_4731_ = lean_ctor_get(v___x_4712_, 0);
v_isSharedCheck_4738_ = !lean_is_exclusive(v___x_4712_);
if (v_isSharedCheck_4738_ == 0)
{
v___x_4733_ = v___x_4712_;
v_isShared_4734_ = v_isSharedCheck_4738_;
goto v_resetjp_4732_;
}
else
{
lean_inc(v_a_4731_);
lean_dec(v___x_4712_);
v___x_4733_ = lean_box(0);
v_isShared_4734_ = v_isSharedCheck_4738_;
goto v_resetjp_4732_;
}
v_resetjp_4732_:
{
lean_object* v___x_4736_; 
if (v_isShared_4734_ == 0)
{
v___x_4736_ = v___x_4733_;
goto v_reusejp_4735_;
}
else
{
lean_object* v_reuseFailAlloc_4737_; 
v_reuseFailAlloc_4737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4737_, 0, v_a_4731_);
v___x_4736_ = v_reuseFailAlloc_4737_;
goto v_reusejp_4735_;
}
v_reusejp_4735_:
{
return v___x_4736_;
}
}
}
}
else
{
v___y_4632_ = v_hasTrace_4677_;
v___y_4633_ = v___x_4709_;
v___y_4634_ = v___x_4707_;
v___y_4635_ = v___x_4706_;
v___y_4636_ = v_options_4676_;
goto v___jp_4631_;
}
}
else
{
v___y_4632_ = v_hasTrace_4677_;
v___y_4633_ = v___x_4709_;
v___y_4634_ = v___x_4707_;
v___y_4635_ = v___x_4706_;
v___y_4636_ = v_options_4676_;
goto v___jp_4631_;
}
}
}
else
{
lean_dec_ref(v___f_4557_);
lean_dec(v_declName_4539_);
goto v___jp_4551_;
}
}
}
}
}
else
{
lean_object* v_a_4744_; lean_object* v___x_4746_; uint8_t v_isShared_4747_; uint8_t v_isSharedCheck_4751_; 
lean_dec(v___x_4545_);
lean_dec(v_declName_4539_);
v_a_4744_ = lean_ctor_get(v___x_4546_, 0);
v_isSharedCheck_4751_ = !lean_is_exclusive(v___x_4546_);
if (v_isSharedCheck_4751_ == 0)
{
v___x_4746_ = v___x_4546_;
v_isShared_4747_ = v_isSharedCheck_4751_;
goto v_resetjp_4745_;
}
else
{
lean_inc(v_a_4744_);
lean_dec(v___x_4546_);
v___x_4746_ = lean_box(0);
v_isShared_4747_ = v_isSharedCheck_4751_;
goto v_resetjp_4745_;
}
v_resetjp_4745_:
{
lean_object* v___x_4749_; 
if (v_isShared_4747_ == 0)
{
v___x_4749_ = v___x_4746_;
goto v_reusejp_4748_;
}
else
{
lean_object* v_reuseFailAlloc_4750_; 
v_reuseFailAlloc_4750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4750_, 0, v_a_4744_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___boxed(lean_object* v_declName_4752_, lean_object* v_a_4753_, lean_object* v_a_4754_, lean_object* v_a_4755_, lean_object* v_a_4756_, lean_object* v_a_4757_){
_start:
{
lean_object* v_res_4758_; 
v_res_4758_ = l_Lean_Meta_mkInjectiveTheorems(v_declName_4752_, v_a_4753_, v_a_4754_, v_a_4755_, v_a_4756_);
lean_dec(v_a_4756_);
lean_dec_ref(v_a_4755_);
lean_dec(v_a_4754_);
lean_dec_ref(v_a_4753_);
return v_res_4758_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3(uint8_t v___y_4759_, uint8_t v___x_4760_, lean_object* v_as_4761_, lean_object* v_as_x27_4762_, lean_object* v_b_4763_, lean_object* v_a_4764_, lean_object* v___y_4765_, lean_object* v___y_4766_, lean_object* v___y_4767_, lean_object* v___y_4768_){
_start:
{
lean_object* v___x_4770_; 
v___x_4770_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___y_4759_, v___x_4760_, v_as_x27_4762_, v_b_4763_, v___y_4765_, v___y_4766_, v___y_4767_, v___y_4768_);
return v___x_4770_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___boxed(lean_object* v___y_4771_, lean_object* v___x_4772_, lean_object* v_as_4773_, lean_object* v_as_x27_4774_, lean_object* v_b_4775_, lean_object* v_a_4776_, lean_object* v___y_4777_, lean_object* v___y_4778_, lean_object* v___y_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_){
_start:
{
uint8_t v___y_20870__boxed_4782_; uint8_t v___x_20871__boxed_4783_; lean_object* v_res_4784_; 
v___y_20870__boxed_4782_ = lean_unbox(v___y_4771_);
v___x_20871__boxed_4783_ = lean_unbox(v___x_4772_);
v_res_4784_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3(v___y_20870__boxed_4782_, v___x_20871__boxed_4783_, v_as_4773_, v_as_x27_4774_, v_b_4775_, v_a_4776_, v___y_4777_, v___y_4778_, v___y_4779_, v___y_4780_);
lean_dec(v___y_4780_);
lean_dec_ref(v___y_4779_);
lean_dec(v___y_4778_);
lean_dec_ref(v___y_4777_);
lean_dec(v_as_4773_);
return v_res_4784_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4825_; lean_object* v___x_4826_; lean_object* v___x_4827_; 
v___x_4825_ = lean_unsigned_to_nat(4172903888u);
v___x_4826_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_));
v___x_4827_ = l_Lean_Name_num___override(v___x_4826_, v___x_4825_);
return v___x_4827_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; 
v___x_4829_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_));
v___x_4830_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4831_ = l_Lean_Name_str___override(v___x_4830_, v___x_4829_);
return v___x_4831_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; 
v___x_4833_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_));
v___x_4834_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4835_ = l_Lean_Name_str___override(v___x_4834_, v___x_4833_);
return v___x_4835_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; 
v___x_4836_ = lean_unsigned_to_nat(2u);
v___x_4837_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4838_ = l_Lean_Name_num___override(v___x_4837_, v___x_4836_);
return v___x_4838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4840_; uint8_t v___x_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; 
v___x_4840_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_4841_ = 0;
v___x_4842_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4843_ = l_Lean_registerTraceClass(v___x_4840_, v___x_4841_, v___x_4842_);
return v___x_4843_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2____boxed(lean_object* v_a_4844_){
_start:
{
lean_object* v_res_4845_; 
v_res_4845_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_();
return v_res_4845_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(lean_object* v_a_4846_, lean_object* v_b_4847_){
_start:
{
lean_object* v_array_4848_; lean_object* v_start_4849_; lean_object* v_stop_4850_; lean_object* v___x_4852_; uint8_t v_isShared_4853_; uint8_t v_isSharedCheck_4863_; 
v_array_4848_ = lean_ctor_get(v_a_4846_, 0);
v_start_4849_ = lean_ctor_get(v_a_4846_, 1);
v_stop_4850_ = lean_ctor_get(v_a_4846_, 2);
v_isSharedCheck_4863_ = !lean_is_exclusive(v_a_4846_);
if (v_isSharedCheck_4863_ == 0)
{
v___x_4852_ = v_a_4846_;
v_isShared_4853_ = v_isSharedCheck_4863_;
goto v_resetjp_4851_;
}
else
{
lean_inc(v_stop_4850_);
lean_inc(v_start_4849_);
lean_inc(v_array_4848_);
lean_dec(v_a_4846_);
v___x_4852_ = lean_box(0);
v_isShared_4853_ = v_isSharedCheck_4863_;
goto v_resetjp_4851_;
}
v_resetjp_4851_:
{
uint8_t v___x_4854_; 
v___x_4854_ = lean_nat_dec_lt(v_start_4849_, v_stop_4850_);
if (v___x_4854_ == 0)
{
lean_del_object(v___x_4852_);
lean_dec(v_stop_4850_);
lean_dec(v_start_4849_);
lean_dec_ref(v_array_4848_);
return v_b_4847_;
}
else
{
lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4858_; 
v___x_4855_ = lean_unsigned_to_nat(1u);
v___x_4856_ = lean_nat_add(v_start_4849_, v___x_4855_);
lean_inc_ref(v_array_4848_);
if (v_isShared_4853_ == 0)
{
lean_ctor_set(v___x_4852_, 1, v___x_4856_);
v___x_4858_ = v___x_4852_;
goto v_reusejp_4857_;
}
else
{
lean_object* v_reuseFailAlloc_4862_; 
v_reuseFailAlloc_4862_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4862_, 0, v_array_4848_);
lean_ctor_set(v_reuseFailAlloc_4862_, 1, v___x_4856_);
lean_ctor_set(v_reuseFailAlloc_4862_, 2, v_stop_4850_);
v___x_4858_ = v_reuseFailAlloc_4862_;
goto v_reusejp_4857_;
}
v_reusejp_4857_:
{
lean_object* v___x_4859_; lean_object* v___x_4860_; 
v___x_4859_ = lean_array_fget(v_array_4848_, v_start_4849_);
lean_dec(v_start_4849_);
lean_dec_ref(v_array_4848_);
v___x_4860_ = lean_array_push(v_b_4847_, v___x_4859_);
v_a_4846_ = v___x_4858_;
v_b_4847_ = v___x_4860_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_4864_; 
v___x_4864_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4864_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_4865_; lean_object* v___x_4866_; 
v___x_4865_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_4866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4866_, 0, v___x_4865_);
return v___x_4866_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; 
v___x_4867_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_4868_ = lean_unsigned_to_nat(0u);
v___x_4869_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4869_, 0, v___x_4868_);
lean_ctor_set(v___x_4869_, 1, v___x_4868_);
lean_ctor_set(v___x_4869_, 2, v___x_4868_);
lean_ctor_set(v___x_4869_, 3, v___x_4868_);
lean_ctor_set(v___x_4869_, 4, v___x_4867_);
lean_ctor_set(v___x_4869_, 5, v___x_4867_);
lean_ctor_set(v___x_4869_, 6, v___x_4867_);
lean_ctor_set(v___x_4869_, 7, v___x_4867_);
lean_ctor_set(v___x_4869_, 8, v___x_4867_);
lean_ctor_set(v___x_4869_, 9, v___x_4867_);
return v___x_4869_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_4870_; lean_object* v___x_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; 
v___x_4870_ = lean_box(1);
v___x_4871_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_4872_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_4873_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4873_, 0, v___x_4872_);
lean_ctor_set(v___x_4873_, 1, v___x_4871_);
lean_ctor_set(v___x_4873_, 2, v___x_4870_);
return v___x_4873_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_4875_; lean_object* v___x_4876_; 
v___x_4875_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4));
v___x_4876_ = l_Lean_stringToMessageData(v___x_4875_);
return v___x_4876_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_4878_; lean_object* v___x_4879_; 
v___x_4878_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_4879_ = l_Lean_stringToMessageData(v___x_4878_);
return v___x_4879_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_4881_; lean_object* v___x_4882_; 
v___x_4881_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_4882_ = l_Lean_stringToMessageData(v___x_4881_);
return v___x_4882_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_4884_; lean_object* v___x_4885_; 
v___x_4884_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_4885_ = l_Lean_stringToMessageData(v___x_4884_);
return v___x_4885_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_4887_; lean_object* v___x_4888_; 
v___x_4887_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_4888_ = l_Lean_stringToMessageData(v___x_4887_);
return v___x_4888_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15(void){
_start:
{
lean_object* v___x_4890_; lean_object* v___x_4891_; 
v___x_4890_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14));
v___x_4891_ = l_Lean_stringToMessageData(v___x_4890_);
return v___x_4891_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17(void){
_start:
{
lean_object* v___x_4893_; lean_object* v___x_4894_; 
v___x_4893_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16));
v___x_4894_ = l_Lean_stringToMessageData(v___x_4893_);
return v___x_4894_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_4895_, lean_object* v_declHint_4896_, lean_object* v___y_4897_){
_start:
{
lean_object* v___x_4899_; lean_object* v_env_4900_; uint8_t v___x_4901_; 
v___x_4899_ = lean_st_ref_get(v___y_4897_);
v_env_4900_ = lean_ctor_get(v___x_4899_, 0);
lean_inc_ref(v_env_4900_);
lean_dec(v___x_4899_);
v___x_4901_ = l_Lean_Name_isAnonymous(v_declHint_4896_);
if (v___x_4901_ == 0)
{
uint8_t v_isExporting_4902_; 
v_isExporting_4902_ = lean_ctor_get_uint8(v_env_4900_, sizeof(void*)*8);
if (v_isExporting_4902_ == 0)
{
lean_object* v___x_4903_; 
lean_dec_ref(v_env_4900_);
lean_dec(v_declHint_4896_);
v___x_4903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4903_, 0, v_msg_4895_);
return v___x_4903_;
}
else
{
lean_object* v___x_4904_; uint8_t v___x_4905_; 
lean_inc_ref(v_env_4900_);
v___x_4904_ = l_Lean_Environment_setExporting(v_env_4900_, v___x_4901_);
lean_inc(v_declHint_4896_);
lean_inc_ref(v___x_4904_);
v___x_4905_ = l_Lean_Environment_contains(v___x_4904_, v_declHint_4896_, v_isExporting_4902_);
if (v___x_4905_ == 0)
{
lean_object* v___x_4906_; 
lean_dec_ref(v___x_4904_);
lean_dec_ref(v_env_4900_);
lean_dec(v_declHint_4896_);
v___x_4906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4906_, 0, v_msg_4895_);
return v___x_4906_;
}
else
{
lean_object* v___x_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; lean_object* v___x_4910_; lean_object* v___x_4911_; lean_object* v_c_4912_; lean_object* v___x_4913_; 
v___x_4907_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_4908_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_4909_ = l_Lean_Options_empty;
v___x_4910_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4910_, 0, v___x_4904_);
lean_ctor_set(v___x_4910_, 1, v___x_4907_);
lean_ctor_set(v___x_4910_, 2, v___x_4908_);
lean_ctor_set(v___x_4910_, 3, v___x_4909_);
lean_inc(v_declHint_4896_);
v___x_4911_ = l_Lean_MessageData_ofConstName(v_declHint_4896_, v___x_4901_);
v_c_4912_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_4912_, 0, v___x_4910_);
lean_ctor_set(v_c_4912_, 1, v___x_4911_);
v___x_4913_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4900_, v_declHint_4896_);
if (lean_obj_tag(v___x_4913_) == 0)
{
lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; 
lean_dec_ref(v_env_4900_);
lean_dec(v_declHint_4896_);
v___x_4914_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_4915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4915_, 0, v___x_4914_);
lean_ctor_set(v___x_4915_, 1, v_c_4912_);
v___x_4916_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_4917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4917_, 0, v___x_4915_);
lean_ctor_set(v___x_4917_, 1, v___x_4916_);
v___x_4918_ = l_Lean_MessageData_note(v___x_4917_);
v___x_4919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4919_, 0, v_msg_4895_);
lean_ctor_set(v___x_4919_, 1, v___x_4918_);
v___x_4920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4920_, 0, v___x_4919_);
return v___x_4920_;
}
else
{
lean_object* v_val_4921_; lean_object* v___x_4923_; uint8_t v_isShared_4924_; uint8_t v_isSharedCheck_4956_; 
v_val_4921_ = lean_ctor_get(v___x_4913_, 0);
v_isSharedCheck_4956_ = !lean_is_exclusive(v___x_4913_);
if (v_isSharedCheck_4956_ == 0)
{
v___x_4923_ = v___x_4913_;
v_isShared_4924_ = v_isSharedCheck_4956_;
goto v_resetjp_4922_;
}
else
{
lean_inc(v_val_4921_);
lean_dec(v___x_4913_);
v___x_4923_ = lean_box(0);
v_isShared_4924_ = v_isSharedCheck_4956_;
goto v_resetjp_4922_;
}
v_resetjp_4922_:
{
lean_object* v___x_4925_; lean_object* v___x_4926_; lean_object* v___x_4927_; lean_object* v_mod_4928_; uint8_t v___x_4929_; 
v___x_4925_ = lean_box(0);
v___x_4926_ = l_Lean_Environment_header(v_env_4900_);
lean_dec_ref(v_env_4900_);
v___x_4927_ = l_Lean_EnvironmentHeader_moduleNames(v___x_4926_);
v_mod_4928_ = lean_array_get(v___x_4925_, v___x_4927_, v_val_4921_);
lean_dec(v_val_4921_);
lean_dec_ref(v___x_4927_);
v___x_4929_ = l_Lean_isPrivateName(v_declHint_4896_);
lean_dec(v_declHint_4896_);
if (v___x_4929_ == 0)
{
lean_object* v___x_4930_; lean_object* v___x_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4939_; lean_object* v___x_4941_; 
v___x_4930_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_4931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4931_, 0, v___x_4930_);
lean_ctor_set(v___x_4931_, 1, v_c_4912_);
v___x_4932_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_4933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4933_, 0, v___x_4931_);
lean_ctor_set(v___x_4933_, 1, v___x_4932_);
v___x_4934_ = l_Lean_MessageData_ofName(v_mod_4928_);
v___x_4935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4935_, 0, v___x_4933_);
lean_ctor_set(v___x_4935_, 1, v___x_4934_);
v___x_4936_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_4937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4937_, 0, v___x_4935_);
lean_ctor_set(v___x_4937_, 1, v___x_4936_);
v___x_4938_ = l_Lean_MessageData_note(v___x_4937_);
v___x_4939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4939_, 0, v_msg_4895_);
lean_ctor_set(v___x_4939_, 1, v___x_4938_);
if (v_isShared_4924_ == 0)
{
lean_ctor_set_tag(v___x_4923_, 0);
lean_ctor_set(v___x_4923_, 0, v___x_4939_);
v___x_4941_ = v___x_4923_;
goto v_reusejp_4940_;
}
else
{
lean_object* v_reuseFailAlloc_4942_; 
v_reuseFailAlloc_4942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4942_, 0, v___x_4939_);
v___x_4941_ = v_reuseFailAlloc_4942_;
goto v_reusejp_4940_;
}
v_reusejp_4940_:
{
return v___x_4941_;
}
}
else
{
lean_object* v___x_4943_; lean_object* v___x_4944_; lean_object* v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; lean_object* v___x_4954_; 
v___x_4943_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_4944_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4944_, 0, v___x_4943_);
lean_ctor_set(v___x_4944_, 1, v_c_4912_);
v___x_4945_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_4946_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4946_, 0, v___x_4944_);
lean_ctor_set(v___x_4946_, 1, v___x_4945_);
v___x_4947_ = l_Lean_MessageData_ofName(v_mod_4928_);
v___x_4948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4948_, 0, v___x_4946_);
lean_ctor_set(v___x_4948_, 1, v___x_4947_);
v___x_4949_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_4950_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4950_, 0, v___x_4948_);
lean_ctor_set(v___x_4950_, 1, v___x_4949_);
v___x_4951_ = l_Lean_MessageData_note(v___x_4950_);
v___x_4952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4952_, 0, v_msg_4895_);
lean_ctor_set(v___x_4952_, 1, v___x_4951_);
if (v_isShared_4924_ == 0)
{
lean_ctor_set_tag(v___x_4923_, 0);
lean_ctor_set(v___x_4923_, 0, v___x_4952_);
v___x_4954_ = v___x_4923_;
goto v_reusejp_4953_;
}
else
{
lean_object* v_reuseFailAlloc_4955_; 
v_reuseFailAlloc_4955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4955_, 0, v___x_4952_);
v___x_4954_ = v_reuseFailAlloc_4955_;
goto v_reusejp_4953_;
}
v_reusejp_4953_:
{
return v___x_4954_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4957_; 
lean_dec_ref(v_env_4900_);
lean_dec(v_declHint_4896_);
v___x_4957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4957_, 0, v_msg_4895_);
return v___x_4957_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_4958_, lean_object* v_declHint_4959_, lean_object* v___y_4960_, lean_object* v___y_4961_){
_start:
{
lean_object* v_res_4962_; 
v_res_4962_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_4958_, v_declHint_4959_, v___y_4960_);
lean_dec(v___y_4960_);
return v_res_4962_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_msg_4963_, lean_object* v_declHint_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_, lean_object* v___y_4967_, lean_object* v___y_4968_){
_start:
{
lean_object* v___x_4970_; lean_object* v_a_4971_; lean_object* v___x_4973_; uint8_t v_isShared_4974_; uint8_t v_isSharedCheck_4980_; 
v___x_4970_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_4963_, v_declHint_4964_, v___y_4968_);
v_a_4971_ = lean_ctor_get(v___x_4970_, 0);
v_isSharedCheck_4980_ = !lean_is_exclusive(v___x_4970_);
if (v_isSharedCheck_4980_ == 0)
{
v___x_4973_ = v___x_4970_;
v_isShared_4974_ = v_isSharedCheck_4980_;
goto v_resetjp_4972_;
}
else
{
lean_inc(v_a_4971_);
lean_dec(v___x_4970_);
v___x_4973_ = lean_box(0);
v_isShared_4974_ = v_isSharedCheck_4980_;
goto v_resetjp_4972_;
}
v_resetjp_4972_:
{
lean_object* v___x_4975_; lean_object* v___x_4976_; lean_object* v___x_4978_; 
v___x_4975_ = l_Lean_unknownIdentifierMessageTag;
v___x_4976_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_4976_, 0, v___x_4975_);
lean_ctor_set(v___x_4976_, 1, v_a_4971_);
if (v_isShared_4974_ == 0)
{
lean_ctor_set(v___x_4973_, 0, v___x_4976_);
v___x_4978_ = v___x_4973_;
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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v_msg_4981_, lean_object* v_declHint_4982_, lean_object* v___y_4983_, lean_object* v___y_4984_, lean_object* v___y_4985_, lean_object* v___y_4986_, lean_object* v___y_4987_){
_start:
{
lean_object* v_res_4988_; 
v_res_4988_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_4981_, v_declHint_4982_, v___y_4983_, v___y_4984_, v___y_4985_, v___y_4986_);
lean_dec(v___y_4986_);
lean_dec_ref(v___y_4985_);
lean_dec(v___y_4984_);
lean_dec_ref(v___y_4983_);
return v_res_4988_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_4989_, lean_object* v_msg_4990_, lean_object* v___y_4991_, lean_object* v___y_4992_, lean_object* v___y_4993_, lean_object* v___y_4994_){
_start:
{
lean_object* v_fileName_4996_; lean_object* v_fileMap_4997_; lean_object* v_options_4998_; lean_object* v_currRecDepth_4999_; lean_object* v_maxRecDepth_5000_; lean_object* v_ref_5001_; lean_object* v_currNamespace_5002_; lean_object* v_openDecls_5003_; lean_object* v_initHeartbeats_5004_; lean_object* v_maxHeartbeats_5005_; lean_object* v_quotContext_5006_; lean_object* v_currMacroScope_5007_; uint8_t v_diag_5008_; lean_object* v_cancelTk_x3f_5009_; uint8_t v_suppressElabErrors_5010_; lean_object* v_inheritedTraceOptions_5011_; lean_object* v_ref_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; 
v_fileName_4996_ = lean_ctor_get(v___y_4993_, 0);
v_fileMap_4997_ = lean_ctor_get(v___y_4993_, 1);
v_options_4998_ = lean_ctor_get(v___y_4993_, 2);
v_currRecDepth_4999_ = lean_ctor_get(v___y_4993_, 3);
v_maxRecDepth_5000_ = lean_ctor_get(v___y_4993_, 4);
v_ref_5001_ = lean_ctor_get(v___y_4993_, 5);
v_currNamespace_5002_ = lean_ctor_get(v___y_4993_, 6);
v_openDecls_5003_ = lean_ctor_get(v___y_4993_, 7);
v_initHeartbeats_5004_ = lean_ctor_get(v___y_4993_, 8);
v_maxHeartbeats_5005_ = lean_ctor_get(v___y_4993_, 9);
v_quotContext_5006_ = lean_ctor_get(v___y_4993_, 10);
v_currMacroScope_5007_ = lean_ctor_get(v___y_4993_, 11);
v_diag_5008_ = lean_ctor_get_uint8(v___y_4993_, sizeof(void*)*14);
v_cancelTk_x3f_5009_ = lean_ctor_get(v___y_4993_, 12);
v_suppressElabErrors_5010_ = lean_ctor_get_uint8(v___y_4993_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_5011_ = lean_ctor_get(v___y_4993_, 13);
v_ref_5012_ = l_Lean_replaceRef(v_ref_4989_, v_ref_5001_);
lean_inc_ref(v_inheritedTraceOptions_5011_);
lean_inc(v_cancelTk_x3f_5009_);
lean_inc(v_currMacroScope_5007_);
lean_inc(v_quotContext_5006_);
lean_inc(v_maxHeartbeats_5005_);
lean_inc(v_initHeartbeats_5004_);
lean_inc(v_openDecls_5003_);
lean_inc(v_currNamespace_5002_);
lean_inc(v_maxRecDepth_5000_);
lean_inc(v_currRecDepth_4999_);
lean_inc_ref(v_options_4998_);
lean_inc_ref(v_fileMap_4997_);
lean_inc_ref(v_fileName_4996_);
v___x_5013_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_5013_, 0, v_fileName_4996_);
lean_ctor_set(v___x_5013_, 1, v_fileMap_4997_);
lean_ctor_set(v___x_5013_, 2, v_options_4998_);
lean_ctor_set(v___x_5013_, 3, v_currRecDepth_4999_);
lean_ctor_set(v___x_5013_, 4, v_maxRecDepth_5000_);
lean_ctor_set(v___x_5013_, 5, v_ref_5012_);
lean_ctor_set(v___x_5013_, 6, v_currNamespace_5002_);
lean_ctor_set(v___x_5013_, 7, v_openDecls_5003_);
lean_ctor_set(v___x_5013_, 8, v_initHeartbeats_5004_);
lean_ctor_set(v___x_5013_, 9, v_maxHeartbeats_5005_);
lean_ctor_set(v___x_5013_, 10, v_quotContext_5006_);
lean_ctor_set(v___x_5013_, 11, v_currMacroScope_5007_);
lean_ctor_set(v___x_5013_, 12, v_cancelTk_x3f_5009_);
lean_ctor_set(v___x_5013_, 13, v_inheritedTraceOptions_5011_);
lean_ctor_set_uint8(v___x_5013_, sizeof(void*)*14, v_diag_5008_);
lean_ctor_set_uint8(v___x_5013_, sizeof(void*)*14 + 1, v_suppressElabErrors_5010_);
v___x_5014_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v_msg_4990_, v___y_4991_, v___y_4992_, v___x_5013_, v___y_4994_);
lean_dec_ref(v___x_5013_);
return v___x_5014_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_5015_, lean_object* v_msg_5016_, lean_object* v___y_5017_, lean_object* v___y_5018_, lean_object* v___y_5019_, lean_object* v___y_5020_, lean_object* v___y_5021_){
_start:
{
lean_object* v_res_5022_; 
v_res_5022_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5015_, v_msg_5016_, v___y_5017_, v___y_5018_, v___y_5019_, v___y_5020_);
lean_dec(v___y_5020_);
lean_dec_ref(v___y_5019_);
lean_dec(v___y_5018_);
lean_dec_ref(v___y_5017_);
lean_dec(v_ref_5015_);
return v_res_5022_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_5023_, lean_object* v_msg_5024_, lean_object* v_declHint_5025_, lean_object* v___y_5026_, lean_object* v___y_5027_, lean_object* v___y_5028_, lean_object* v___y_5029_){
_start:
{
lean_object* v___x_5031_; lean_object* v_a_5032_; lean_object* v___x_5033_; 
v___x_5031_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_5024_, v_declHint_5025_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_);
v_a_5032_ = lean_ctor_get(v___x_5031_, 0);
lean_inc(v_a_5032_);
lean_dec_ref(v___x_5031_);
v___x_5033_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5023_, v_a_5032_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_);
return v___x_5033_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_5034_, lean_object* v_msg_5035_, lean_object* v_declHint_5036_, lean_object* v___y_5037_, lean_object* v___y_5038_, lean_object* v___y_5039_, lean_object* v___y_5040_, lean_object* v___y_5041_){
_start:
{
lean_object* v_res_5042_; 
v_res_5042_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5034_, v_msg_5035_, v_declHint_5036_, v___y_5037_, v___y_5038_, v___y_5039_, v___y_5040_);
lean_dec(v___y_5040_);
lean_dec_ref(v___y_5039_);
lean_dec(v___y_5038_);
lean_dec_ref(v___y_5037_);
lean_dec(v_ref_5034_);
return v_res_5042_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_5044_; lean_object* v___x_5045_; 
v___x_5044_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_5045_ = l_Lean_stringToMessageData(v___x_5044_);
return v___x_5045_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_5046_, lean_object* v_constName_5047_, lean_object* v___y_5048_, lean_object* v___y_5049_, lean_object* v___y_5050_, lean_object* v___y_5051_){
_start:
{
lean_object* v___x_5053_; uint8_t v___x_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; lean_object* v___x_5057_; lean_object* v___x_5058_; lean_object* v___x_5059_; 
v___x_5053_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_5054_ = 0;
lean_inc(v_constName_5047_);
v___x_5055_ = l_Lean_MessageData_ofConstName(v_constName_5047_, v___x_5054_);
v___x_5056_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5056_, 0, v___x_5053_);
lean_ctor_set(v___x_5056_, 1, v___x_5055_);
v___x_5057_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_5058_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5058_, 0, v___x_5056_);
lean_ctor_set(v___x_5058_, 1, v___x_5057_);
v___x_5059_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5046_, v___x_5058_, v_constName_5047_, v___y_5048_, v___y_5049_, v___y_5050_, v___y_5051_);
return v___x_5059_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_5060_, lean_object* v_constName_5061_, lean_object* v___y_5062_, lean_object* v___y_5063_, lean_object* v___y_5064_, lean_object* v___y_5065_, lean_object* v___y_5066_){
_start:
{
lean_object* v_res_5067_; 
v_res_5067_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(v_ref_5060_, v_constName_5061_, v___y_5062_, v___y_5063_, v___y_5064_, v___y_5065_);
lean_dec(v___y_5065_);
lean_dec_ref(v___y_5064_);
lean_dec(v___y_5063_);
lean_dec_ref(v___y_5062_);
lean_dec(v_ref_5060_);
return v_res_5067_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(lean_object* v_constName_5068_, lean_object* v___y_5069_, lean_object* v___y_5070_, lean_object* v___y_5071_, lean_object* v___y_5072_){
_start:
{
lean_object* v_ref_5074_; lean_object* v___x_5075_; 
v_ref_5074_ = lean_ctor_get(v___y_5071_, 5);
v___x_5075_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(v_ref_5074_, v_constName_5068_, v___y_5069_, v___y_5070_, v___y_5071_, v___y_5072_);
return v___x_5075_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_constName_5076_, lean_object* v___y_5077_, lean_object* v___y_5078_, lean_object* v___y_5079_, lean_object* v___y_5080_, lean_object* v___y_5081_){
_start:
{
lean_object* v_res_5082_; 
v_res_5082_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(v_constName_5076_, v___y_5077_, v___y_5078_, v___y_5079_, v___y_5080_);
lean_dec(v___y_5080_);
lean_dec_ref(v___y_5079_);
lean_dec(v___y_5078_);
lean_dec_ref(v___y_5077_);
return v_res_5082_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(lean_object* v_constName_5083_, lean_object* v___y_5084_, lean_object* v___y_5085_, lean_object* v___y_5086_, lean_object* v___y_5087_){
_start:
{
lean_object* v___x_5089_; lean_object* v_env_5090_; uint8_t v___x_5091_; lean_object* v___x_5092_; 
v___x_5089_ = lean_st_ref_get(v___y_5087_);
v_env_5090_ = lean_ctor_get(v___x_5089_, 0);
lean_inc_ref(v_env_5090_);
lean_dec(v___x_5089_);
v___x_5091_ = 0;
lean_inc(v_constName_5083_);
v___x_5092_ = l_Lean_Environment_find_x3f(v_env_5090_, v_constName_5083_, v___x_5091_);
if (lean_obj_tag(v___x_5092_) == 0)
{
lean_object* v___x_5093_; 
v___x_5093_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(v_constName_5083_, v___y_5084_, v___y_5085_, v___y_5086_, v___y_5087_);
return v___x_5093_;
}
else
{
lean_object* v_val_5094_; lean_object* v___x_5096_; uint8_t v_isShared_5097_; uint8_t v_isSharedCheck_5101_; 
lean_dec(v_constName_5083_);
v_val_5094_ = lean_ctor_get(v___x_5092_, 0);
v_isSharedCheck_5101_ = !lean_is_exclusive(v___x_5092_);
if (v_isSharedCheck_5101_ == 0)
{
v___x_5096_ = v___x_5092_;
v_isShared_5097_ = v_isSharedCheck_5101_;
goto v_resetjp_5095_;
}
else
{
lean_inc(v_val_5094_);
lean_dec(v___x_5092_);
v___x_5096_ = lean_box(0);
v_isShared_5097_ = v_isSharedCheck_5101_;
goto v_resetjp_5095_;
}
v_resetjp_5095_:
{
lean_object* v___x_5099_; 
if (v_isShared_5097_ == 0)
{
lean_ctor_set_tag(v___x_5096_, 0);
v___x_5099_ = v___x_5096_;
goto v_reusejp_5098_;
}
else
{
lean_object* v_reuseFailAlloc_5100_; 
v_reuseFailAlloc_5100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5100_, 0, v_val_5094_);
v___x_5099_ = v_reuseFailAlloc_5100_;
goto v_reusejp_5098_;
}
v_reusejp_5098_:
{
return v___x_5099_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0___boxed(lean_object* v_constName_5102_, lean_object* v___y_5103_, lean_object* v___y_5104_, lean_object* v___y_5105_, lean_object* v___y_5106_, lean_object* v___y_5107_){
_start:
{
lean_object* v_res_5108_; 
v_res_5108_ = l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(v_constName_5102_, v___y_5103_, v___y_5104_, v___y_5105_, v___y_5106_);
lean_dec(v___y_5106_);
lean_dec_ref(v___y_5105_);
lean_dec(v___y_5104_);
lean_dec_ref(v___y_5103_);
return v_res_5108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(lean_object* v_x_5111_, lean_object* v_x_5112_, lean_object* v_x_5113_, lean_object* v___y_5114_, lean_object* v___y_5115_, lean_object* v___y_5116_, lean_object* v___y_5117_){
_start:
{
if (lean_obj_tag(v_x_5111_) == 5)
{
lean_object* v_fn_5119_; lean_object* v_arg_5120_; lean_object* v___x_5121_; lean_object* v___x_5122_; lean_object* v___x_5123_; 
v_fn_5119_ = lean_ctor_get(v_x_5111_, 0);
lean_inc_ref(v_fn_5119_);
v_arg_5120_ = lean_ctor_get(v_x_5111_, 1);
lean_inc_ref(v_arg_5120_);
lean_dec_ref(v_x_5111_);
v___x_5121_ = lean_array_set(v_x_5112_, v_x_5113_, v_arg_5120_);
v___x_5122_ = lean_unsigned_to_nat(1u);
v___x_5123_ = lean_nat_sub(v_x_5113_, v___x_5122_);
lean_dec(v_x_5113_);
v_x_5111_ = v_fn_5119_;
v_x_5112_ = v___x_5121_;
v_x_5113_ = v___x_5123_;
goto _start;
}
else
{
lean_dec(v_x_5113_);
if (lean_obj_tag(v_x_5111_) == 4)
{
lean_object* v_declName_5125_; lean_object* v___x_5126_; 
v_declName_5125_ = lean_ctor_get(v_x_5111_, 0);
lean_inc(v_declName_5125_);
lean_dec_ref(v_x_5111_);
v___x_5126_ = l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(v_declName_5125_, v___y_5114_, v___y_5115_, v___y_5116_, v___y_5117_);
if (lean_obj_tag(v___x_5126_) == 0)
{
lean_object* v_a_5127_; lean_object* v___x_5129_; uint8_t v_isShared_5130_; uint8_t v_isSharedCheck_5158_; 
v_a_5127_ = lean_ctor_get(v___x_5126_, 0);
v_isSharedCheck_5158_ = !lean_is_exclusive(v___x_5126_);
if (v_isSharedCheck_5158_ == 0)
{
v___x_5129_ = v___x_5126_;
v_isShared_5130_ = v_isSharedCheck_5158_;
goto v_resetjp_5128_;
}
else
{
lean_inc(v_a_5127_);
lean_dec(v___x_5126_);
v___x_5129_ = lean_box(0);
v_isShared_5130_ = v_isSharedCheck_5158_;
goto v_resetjp_5128_;
}
v_resetjp_5128_:
{
lean_object* v_lower_5132_; lean_object* v_upper_5133_; 
if (lean_obj_tag(v_a_5127_) == 5)
{
lean_object* v_val_5141_; lean_object* v___x_5143_; uint8_t v_isShared_5144_; uint8_t v_isSharedCheck_5155_; 
v_val_5141_ = lean_ctor_get(v_a_5127_, 0);
v_isSharedCheck_5155_ = !lean_is_exclusive(v_a_5127_);
if (v_isSharedCheck_5155_ == 0)
{
v___x_5143_ = v_a_5127_;
v_isShared_5144_ = v_isSharedCheck_5155_;
goto v_resetjp_5142_;
}
else
{
lean_inc(v_val_5141_);
lean_dec(v_a_5127_);
v___x_5143_ = lean_box(0);
v_isShared_5144_ = v_isSharedCheck_5155_;
goto v_resetjp_5142_;
}
v_resetjp_5142_:
{
lean_object* v_numParams_5145_; lean_object* v_numIndices_5146_; lean_object* v___x_5147_; uint8_t v___x_5148_; 
v_numParams_5145_ = lean_ctor_get(v_val_5141_, 1);
lean_inc(v_numParams_5145_);
v_numIndices_5146_ = lean_ctor_get(v_val_5141_, 2);
lean_inc(v_numIndices_5146_);
lean_dec_ref(v_val_5141_);
v___x_5147_ = lean_unsigned_to_nat(0u);
v___x_5148_ = lean_nat_dec_eq(v_numIndices_5146_, v___x_5147_);
lean_dec(v_numIndices_5146_);
if (v___x_5148_ == 0)
{
lean_object* v___x_5149_; uint8_t v___x_5150_; 
lean_del_object(v___x_5143_);
v___x_5149_ = lean_array_get_size(v_x_5112_);
v___x_5150_ = lean_nat_dec_le(v_numParams_5145_, v___x_5147_);
if (v___x_5150_ == 0)
{
v_lower_5132_ = v_numParams_5145_;
v_upper_5133_ = v___x_5149_;
goto v___jp_5131_;
}
else
{
lean_dec(v_numParams_5145_);
v_lower_5132_ = v___x_5147_;
v_upper_5133_ = v___x_5149_;
goto v___jp_5131_;
}
}
else
{
lean_object* v___x_5151_; lean_object* v___x_5153_; 
lean_dec(v_numParams_5145_);
lean_del_object(v___x_5129_);
lean_dec_ref(v_x_5112_);
v___x_5151_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2___closed__0));
if (v_isShared_5144_ == 0)
{
lean_ctor_set_tag(v___x_5143_, 0);
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
lean_object* v___x_5156_; lean_object* v___x_5157_; 
lean_del_object(v___x_5129_);
lean_dec(v_a_5127_);
lean_dec_ref(v_x_5112_);
v___x_5156_ = lean_box(0);
v___x_5157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5157_, 0, v___x_5156_);
return v___x_5157_;
}
v___jp_5131_:
{
lean_object* v___x_5134_; lean_object* v___x_5135_; lean_object* v___x_5136_; lean_object* v___x_5137_; lean_object* v___x_5139_; 
v___x_5134_ = l_Array_toSubarray___redArg(v_x_5112_, v_lower_5132_, v_upper_5133_);
v___x_5135_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_5136_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(v___x_5134_, v___x_5135_);
v___x_5137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5137_, 0, v___x_5136_);
if (v_isShared_5130_ == 0)
{
lean_ctor_set(v___x_5129_, 0, v___x_5137_);
v___x_5139_ = v___x_5129_;
goto v_reusejp_5138_;
}
else
{
lean_object* v_reuseFailAlloc_5140_; 
v_reuseFailAlloc_5140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5140_, 0, v___x_5137_);
v___x_5139_ = v_reuseFailAlloc_5140_;
goto v_reusejp_5138_;
}
v_reusejp_5138_:
{
return v___x_5139_;
}
}
}
}
else
{
lean_object* v_a_5159_; lean_object* v___x_5161_; uint8_t v_isShared_5162_; uint8_t v_isSharedCheck_5166_; 
lean_dec_ref(v_x_5112_);
v_a_5159_ = lean_ctor_get(v___x_5126_, 0);
v_isSharedCheck_5166_ = !lean_is_exclusive(v___x_5126_);
if (v_isSharedCheck_5166_ == 0)
{
v___x_5161_ = v___x_5126_;
v_isShared_5162_ = v_isSharedCheck_5166_;
goto v_resetjp_5160_;
}
else
{
lean_inc(v_a_5159_);
lean_dec(v___x_5126_);
v___x_5161_ = lean_box(0);
v_isShared_5162_ = v_isSharedCheck_5166_;
goto v_resetjp_5160_;
}
v_resetjp_5160_:
{
lean_object* v___x_5164_; 
if (v_isShared_5162_ == 0)
{
v___x_5164_ = v___x_5161_;
goto v_reusejp_5163_;
}
else
{
lean_object* v_reuseFailAlloc_5165_; 
v_reuseFailAlloc_5165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5165_, 0, v_a_5159_);
v___x_5164_ = v_reuseFailAlloc_5165_;
goto v_reusejp_5163_;
}
v_reusejp_5163_:
{
return v___x_5164_;
}
}
}
}
else
{
lean_object* v___x_5167_; lean_object* v___x_5168_; 
lean_dec_ref(v_x_5112_);
lean_dec_ref(v_x_5111_);
v___x_5167_ = lean_box(0);
v___x_5168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5168_, 0, v___x_5167_);
return v___x_5168_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2___boxed(lean_object* v_x_5169_, lean_object* v_x_5170_, lean_object* v_x_5171_, lean_object* v___y_5172_, lean_object* v___y_5173_, lean_object* v___y_5174_, lean_object* v___y_5175_, lean_object* v___y_5176_){
_start:
{
lean_object* v_res_5177_; 
v_res_5177_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(v_x_5169_, v_x_5170_, v_x_5171_, v___y_5172_, v___y_5173_, v___y_5174_, v___y_5175_);
lean_dec(v___y_5175_);
lean_dec_ref(v___y_5174_);
lean_dec(v___y_5173_);
lean_dec_ref(v___y_5172_);
return v_res_5177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorAppIndices_x3f(lean_object* v_ctorApp_5178_, lean_object* v_a_5179_, lean_object* v_a_5180_, lean_object* v_a_5181_, lean_object* v_a_5182_){
_start:
{
lean_object* v___x_5184_; 
lean_inc(v_a_5182_);
lean_inc_ref(v_a_5181_);
lean_inc(v_a_5180_);
lean_inc_ref(v_a_5179_);
v___x_5184_ = lean_infer_type(v_ctorApp_5178_, v_a_5179_, v_a_5180_, v_a_5181_, v_a_5182_);
if (lean_obj_tag(v___x_5184_) == 0)
{
lean_object* v_a_5185_; lean_object* v___x_5186_; 
v_a_5185_ = lean_ctor_get(v___x_5184_, 0);
lean_inc(v_a_5185_);
lean_dec_ref(v___x_5184_);
v___x_5186_ = l_Lean_Meta_whnfD(v_a_5185_, v_a_5179_, v_a_5180_, v_a_5181_, v_a_5182_);
if (lean_obj_tag(v___x_5186_) == 0)
{
lean_object* v_a_5187_; lean_object* v_dummy_5188_; lean_object* v_nargs_5189_; lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; lean_object* v___x_5193_; 
v_a_5187_ = lean_ctor_get(v___x_5186_, 0);
lean_inc(v_a_5187_);
lean_dec_ref(v___x_5186_);
v_dummy_5188_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0);
v_nargs_5189_ = l_Lean_Expr_getAppNumArgs(v_a_5187_);
lean_inc(v_nargs_5189_);
v___x_5190_ = lean_mk_array(v_nargs_5189_, v_dummy_5188_);
v___x_5191_ = lean_unsigned_to_nat(1u);
v___x_5192_ = lean_nat_sub(v_nargs_5189_, v___x_5191_);
lean_dec(v_nargs_5189_);
v___x_5193_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(v_a_5187_, v___x_5190_, v___x_5192_, v_a_5179_, v_a_5180_, v_a_5181_, v_a_5182_);
return v___x_5193_;
}
else
{
lean_object* v_a_5194_; lean_object* v___x_5196_; uint8_t v_isShared_5197_; uint8_t v_isSharedCheck_5201_; 
v_a_5194_ = lean_ctor_get(v___x_5186_, 0);
v_isSharedCheck_5201_ = !lean_is_exclusive(v___x_5186_);
if (v_isSharedCheck_5201_ == 0)
{
v___x_5196_ = v___x_5186_;
v_isShared_5197_ = v_isSharedCheck_5201_;
goto v_resetjp_5195_;
}
else
{
lean_inc(v_a_5194_);
lean_dec(v___x_5186_);
v___x_5196_ = lean_box(0);
v_isShared_5197_ = v_isSharedCheck_5201_;
goto v_resetjp_5195_;
}
v_resetjp_5195_:
{
lean_object* v___x_5199_; 
if (v_isShared_5197_ == 0)
{
v___x_5199_ = v___x_5196_;
goto v_reusejp_5198_;
}
else
{
lean_object* v_reuseFailAlloc_5200_; 
v_reuseFailAlloc_5200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5200_, 0, v_a_5194_);
v___x_5199_ = v_reuseFailAlloc_5200_;
goto v_reusejp_5198_;
}
v_reusejp_5198_:
{
return v___x_5199_;
}
}
}
}
else
{
lean_object* v_a_5202_; lean_object* v___x_5204_; uint8_t v_isShared_5205_; uint8_t v_isSharedCheck_5209_; 
v_a_5202_ = lean_ctor_get(v___x_5184_, 0);
v_isSharedCheck_5209_ = !lean_is_exclusive(v___x_5184_);
if (v_isSharedCheck_5209_ == 0)
{
v___x_5204_ = v___x_5184_;
v_isShared_5205_ = v_isSharedCheck_5209_;
goto v_resetjp_5203_;
}
else
{
lean_inc(v_a_5202_);
lean_dec(v___x_5184_);
v___x_5204_ = lean_box(0);
v_isShared_5205_ = v_isSharedCheck_5209_;
goto v_resetjp_5203_;
}
v_resetjp_5203_:
{
lean_object* v___x_5207_; 
if (v_isShared_5205_ == 0)
{
v___x_5207_ = v___x_5204_;
goto v_reusejp_5206_;
}
else
{
lean_object* v_reuseFailAlloc_5208_; 
v_reuseFailAlloc_5208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5208_, 0, v_a_5202_);
v___x_5207_ = v_reuseFailAlloc_5208_;
goto v_reusejp_5206_;
}
v_reusejp_5206_:
{
return v___x_5207_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorAppIndices_x3f___boxed(lean_object* v_ctorApp_5210_, lean_object* v_a_5211_, lean_object* v_a_5212_, lean_object* v_a_5213_, lean_object* v_a_5214_, lean_object* v_a_5215_){
_start:
{
lean_object* v_res_5216_; 
v_res_5216_ = l_Lean_Meta_getCtorAppIndices_x3f(v_ctorApp_5210_, v_a_5211_, v_a_5212_, v_a_5213_, v_a_5214_);
lean_dec(v_a_5214_);
lean_dec_ref(v_a_5213_);
lean_dec(v_a_5212_);
lean_dec_ref(v_a_5211_);
return v_res_5216_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1(lean_object* v_inst_5217_, lean_object* v_R_5218_, lean_object* v_a_5219_, lean_object* v_b_5220_){
_start:
{
lean_object* v___x_5221_; 
v___x_5221_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(v_a_5219_, v_b_5220_);
return v___x_5221_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0(lean_object* v_00_u03b1_5222_, lean_object* v_constName_5223_, lean_object* v___y_5224_, lean_object* v___y_5225_, lean_object* v___y_5226_, lean_object* v___y_5227_){
_start:
{
lean_object* v___x_5229_; 
v___x_5229_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(v_constName_5223_, v___y_5224_, v___y_5225_, v___y_5226_, v___y_5227_);
return v___x_5229_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b1_5230_, lean_object* v_constName_5231_, lean_object* v___y_5232_, lean_object* v___y_5233_, lean_object* v___y_5234_, lean_object* v___y_5235_, lean_object* v___y_5236_){
_start:
{
lean_object* v_res_5237_; 
v_res_5237_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0(v_00_u03b1_5230_, v_constName_5231_, v___y_5232_, v___y_5233_, v___y_5234_, v___y_5235_);
lean_dec(v___y_5235_);
lean_dec_ref(v___y_5234_);
lean_dec(v___y_5233_);
lean_dec_ref(v___y_5232_);
return v_res_5237_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_5238_, lean_object* v_ref_5239_, lean_object* v_constName_5240_, lean_object* v___y_5241_, lean_object* v___y_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_){
_start:
{
lean_object* v___x_5246_; 
v___x_5246_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(v_ref_5239_, v_constName_5240_, v___y_5241_, v___y_5242_, v___y_5243_, v___y_5244_);
return v___x_5246_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_5247_, lean_object* v_ref_5248_, lean_object* v_constName_5249_, lean_object* v___y_5250_, lean_object* v___y_5251_, lean_object* v___y_5252_, lean_object* v___y_5253_, lean_object* v___y_5254_){
_start:
{
lean_object* v_res_5255_; 
v_res_5255_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1(v_00_u03b1_5247_, v_ref_5248_, v_constName_5249_, v___y_5250_, v___y_5251_, v___y_5252_, v___y_5253_);
lean_dec(v___y_5253_);
lean_dec_ref(v___y_5252_);
lean_dec(v___y_5251_);
lean_dec_ref(v___y_5250_);
lean_dec(v_ref_5248_);
return v_res_5255_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_5256_, lean_object* v_ref_5257_, lean_object* v_msg_5258_, lean_object* v_declHint_5259_, lean_object* v___y_5260_, lean_object* v___y_5261_, lean_object* v___y_5262_, lean_object* v___y_5263_){
_start:
{
lean_object* v___x_5265_; 
v___x_5265_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5257_, v_msg_5258_, v_declHint_5259_, v___y_5260_, v___y_5261_, v___y_5262_, v___y_5263_);
return v___x_5265_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_5266_, lean_object* v_ref_5267_, lean_object* v_msg_5268_, lean_object* v_declHint_5269_, lean_object* v___y_5270_, lean_object* v___y_5271_, lean_object* v___y_5272_, lean_object* v___y_5273_, lean_object* v___y_5274_){
_start:
{
lean_object* v_res_5275_; 
v_res_5275_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_5266_, v_ref_5267_, v_msg_5268_, v_declHint_5269_, v___y_5270_, v___y_5271_, v___y_5272_, v___y_5273_);
lean_dec(v___y_5273_);
lean_dec_ref(v___y_5272_);
lean_dec(v___y_5271_);
lean_dec_ref(v___y_5270_);
lean_dec(v_ref_5267_);
return v_res_5275_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_msg_5276_, lean_object* v_declHint_5277_, lean_object* v___y_5278_, lean_object* v___y_5279_, lean_object* v___y_5280_, lean_object* v___y_5281_){
_start:
{
lean_object* v___x_5283_; 
v___x_5283_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_5276_, v_declHint_5277_, v___y_5281_);
return v___x_5283_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_5284_, lean_object* v_declHint_5285_, lean_object* v___y_5286_, lean_object* v___y_5287_, lean_object* v___y_5288_, lean_object* v___y_5289_, lean_object* v___y_5290_){
_start:
{
lean_object* v_res_5291_; 
v_res_5291_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_5284_, v_declHint_5285_, v___y_5286_, v___y_5287_, v___y_5288_, v___y_5289_);
lean_dec(v___y_5289_);
lean_dec_ref(v___y_5288_);
lean_dec(v___y_5287_);
lean_dec_ref(v___y_5286_);
return v_res_5291_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_5292_, lean_object* v_ref_5293_, lean_object* v_msg_5294_, lean_object* v___y_5295_, lean_object* v___y_5296_, lean_object* v___y_5297_, lean_object* v___y_5298_){
_start:
{
lean_object* v___x_5300_; 
v___x_5300_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5293_, v_msg_5294_, v___y_5295_, v___y_5296_, v___y_5297_, v___y_5298_);
return v___x_5300_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_5301_, lean_object* v_ref_5302_, lean_object* v_msg_5303_, lean_object* v___y_5304_, lean_object* v___y_5305_, lean_object* v___y_5306_, lean_object* v___y_5307_, lean_object* v___y_5308_){
_start:
{
lean_object* v_res_5309_; 
v_res_5309_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_5301_, v_ref_5302_, v_msg_5303_, v___y_5304_, v___y_5305_, v___y_5306_, v___y_5307_);
lean_dec(v___y_5307_);
lean_dec_ref(v___y_5306_);
lean_dec(v___y_5305_);
lean_dec_ref(v___y_5304_);
lean_dec(v_ref_5302_);
return v_res_5309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0___boxed(lean_object* v_i_5310_, lean_object* v_body_5311_, lean_object* v_args2_5312_, lean_object* v_ctorVal_5313_, lean_object* v_args1_5314_, lean_object* v_k_5315_, lean_object* v_arg2_5316_, lean_object* v___y_5317_, lean_object* v___y_5318_, lean_object* v___y_5319_, lean_object* v___y_5320_, lean_object* v___y_5321_){
_start:
{
lean_object* v_res_5322_; 
v_res_5322_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0(v_i_5310_, v_body_5311_, v_args2_5312_, v_ctorVal_5313_, v_args1_5314_, v_k_5315_, v_arg2_5316_, v___y_5317_, v___y_5318_, v___y_5319_, v___y_5320_);
lean_dec(v___y_5320_);
lean_dec_ref(v___y_5319_);
lean_dec(v___y_5318_);
lean_dec_ref(v___y_5317_);
lean_dec_ref(v_body_5311_);
lean_dec(v_i_5310_);
return v_res_5322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(lean_object* v_ctorVal_5323_, lean_object* v_args1_5324_, lean_object* v_k_5325_, lean_object* v_i_5326_, lean_object* v_type_5327_, lean_object* v_args2_5328_, lean_object* v_a_5329_, lean_object* v_a_5330_, lean_object* v_a_5331_, lean_object* v_a_5332_){
_start:
{
lean_object* v___x_5334_; uint8_t v___x_5335_; 
v___x_5334_ = lean_array_get_size(v_args1_5324_);
v___x_5335_ = lean_nat_dec_lt(v_i_5326_, v___x_5334_);
if (v___x_5335_ == 0)
{
lean_object* v___x_5336_; 
lean_dec_ref(v_type_5327_);
lean_dec(v_i_5326_);
lean_dec_ref(v_args1_5324_);
lean_dec_ref(v_ctorVal_5323_);
lean_inc(v_a_5332_);
lean_inc_ref(v_a_5331_);
lean_inc(v_a_5330_);
lean_inc_ref(v_a_5329_);
v___x_5336_ = lean_apply_6(v_k_5325_, v_args2_5328_, v_a_5329_, v_a_5330_, v_a_5331_, v_a_5332_, lean_box(0));
return v___x_5336_;
}
else
{
lean_object* v___x_5337_; 
lean_inc(v_a_5332_);
lean_inc_ref(v_a_5331_);
lean_inc(v_a_5330_);
lean_inc_ref(v_a_5329_);
v___x_5337_ = lean_whnf(v_type_5327_, v_a_5329_, v_a_5330_, v_a_5331_, v_a_5332_);
if (lean_obj_tag(v___x_5337_) == 0)
{
lean_object* v_a_5338_; 
v_a_5338_ = lean_ctor_get(v___x_5337_, 0);
lean_inc(v_a_5338_);
lean_dec_ref(v___x_5337_);
if (lean_obj_tag(v_a_5338_) == 7)
{
lean_object* v_binderName_5339_; lean_object* v_binderType_5340_; lean_object* v_body_5341_; lean_object* v___f_5342_; uint8_t v___x_5343_; uint8_t v___x_5344_; lean_object* v___x_5345_; 
v_binderName_5339_ = lean_ctor_get(v_a_5338_, 0);
lean_inc(v_binderName_5339_);
v_binderType_5340_ = lean_ctor_get(v_a_5338_, 1);
lean_inc_ref(v_binderType_5340_);
v_body_5341_ = lean_ctor_get(v_a_5338_, 2);
lean_inc_ref(v_body_5341_);
lean_dec_ref(v_a_5338_);
v___f_5342_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0___boxed), 12, 6);
lean_closure_set(v___f_5342_, 0, v_i_5326_);
lean_closure_set(v___f_5342_, 1, v_body_5341_);
lean_closure_set(v___f_5342_, 2, v_args2_5328_);
lean_closure_set(v___f_5342_, 3, v_ctorVal_5323_);
lean_closure_set(v___f_5342_, 4, v_args1_5324_);
lean_closure_set(v___f_5342_, 5, v_k_5325_);
v___x_5343_ = 1;
v___x_5344_ = 0;
v___x_5345_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_binderName_5339_, v___x_5343_, v_binderType_5340_, v___f_5342_, v___x_5344_, v_a_5329_, v_a_5330_, v_a_5331_, v_a_5332_);
return v___x_5345_;
}
else
{
lean_object* v_toConstantVal_5346_; lean_object* v_name_5347_; lean_object* v___x_5348_; lean_object* v___x_5349_; lean_object* v___x_5350_; lean_object* v___x_5351_; lean_object* v___x_5352_; lean_object* v___x_5353_; 
lean_dec(v_a_5338_);
lean_dec_ref(v_args2_5328_);
lean_dec(v_i_5326_);
lean_dec_ref(v_k_5325_);
lean_dec_ref(v_args1_5324_);
v_toConstantVal_5346_ = lean_ctor_get(v_ctorVal_5323_, 0);
lean_inc_ref(v_toConstantVal_5346_);
lean_dec_ref(v_ctorVal_5323_);
v_name_5347_ = lean_ctor_get(v_toConstantVal_5346_, 0);
lean_inc(v_name_5347_);
lean_dec_ref(v_toConstantVal_5346_);
v___x_5348_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1);
v___x_5349_ = l_Lean_MessageData_ofName(v_name_5347_);
v___x_5350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5350_, 0, v___x_5348_);
lean_ctor_set(v___x_5350_, 1, v___x_5349_);
v___x_5351_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_5352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5352_, 0, v___x_5350_);
lean_ctor_set(v___x_5352_, 1, v___x_5351_);
v___x_5353_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_5352_, v_a_5329_, v_a_5330_, v_a_5331_, v_a_5332_);
return v___x_5353_;
}
}
else
{
lean_object* v_a_5354_; lean_object* v___x_5356_; uint8_t v_isShared_5357_; uint8_t v_isSharedCheck_5361_; 
lean_dec_ref(v_args2_5328_);
lean_dec(v_i_5326_);
lean_dec_ref(v_k_5325_);
lean_dec_ref(v_args1_5324_);
lean_dec_ref(v_ctorVal_5323_);
v_a_5354_ = lean_ctor_get(v___x_5337_, 0);
v_isSharedCheck_5361_ = !lean_is_exclusive(v___x_5337_);
if (v_isSharedCheck_5361_ == 0)
{
v___x_5356_ = v___x_5337_;
v_isShared_5357_ = v_isSharedCheck_5361_;
goto v_resetjp_5355_;
}
else
{
lean_inc(v_a_5354_);
lean_dec(v___x_5337_);
v___x_5356_ = lean_box(0);
v_isShared_5357_ = v_isSharedCheck_5361_;
goto v_resetjp_5355_;
}
v_resetjp_5355_:
{
lean_object* v___x_5359_; 
if (v_isShared_5357_ == 0)
{
v___x_5359_ = v___x_5356_;
goto v_reusejp_5358_;
}
else
{
lean_object* v_reuseFailAlloc_5360_; 
v_reuseFailAlloc_5360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5360_, 0, v_a_5354_);
v___x_5359_ = v_reuseFailAlloc_5360_;
goto v_reusejp_5358_;
}
v_reusejp_5358_:
{
return v___x_5359_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0(lean_object* v_i_5362_, lean_object* v_body_5363_, lean_object* v_args2_5364_, lean_object* v_ctorVal_5365_, lean_object* v_args1_5366_, lean_object* v_k_5367_, lean_object* v_arg2_5368_, lean_object* v___y_5369_, lean_object* v___y_5370_, lean_object* v___y_5371_, lean_object* v___y_5372_){
_start:
{
lean_object* v___x_5374_; lean_object* v___x_5375_; lean_object* v___x_5376_; lean_object* v___x_5377_; lean_object* v___x_5378_; 
v___x_5374_ = lean_unsigned_to_nat(1u);
v___x_5375_ = lean_nat_add(v_i_5362_, v___x_5374_);
v___x_5376_ = lean_expr_instantiate1(v_body_5363_, v_arg2_5368_);
v___x_5377_ = lean_array_push(v_args2_5364_, v_arg2_5368_);
v___x_5378_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(v_ctorVal_5365_, v_args1_5366_, v_k_5367_, v___x_5375_, v___x_5376_, v___x_5377_, v___y_5369_, v___y_5370_, v___y_5371_, v___y_5372_);
return v___x_5378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___boxed(lean_object* v_ctorVal_5379_, lean_object* v_args1_5380_, lean_object* v_k_5381_, lean_object* v_i_5382_, lean_object* v_type_5383_, lean_object* v_args2_5384_, lean_object* v_a_5385_, lean_object* v_a_5386_, lean_object* v_a_5387_, lean_object* v_a_5388_, lean_object* v_a_5389_){
_start:
{
lean_object* v_res_5390_; 
v_res_5390_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(v_ctorVal_5379_, v_args1_5380_, v_k_5381_, v_i_5382_, v_type_5383_, v_args2_5384_, v_a_5385_, v_a_5386_, v_a_5387_, v_a_5388_);
lean_dec(v_a_5388_);
lean_dec_ref(v_a_5387_);
lean_dec(v_a_5386_);
lean_dec_ref(v_a_5385_);
return v_res_5390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0(lean_object* v_name_5391_, lean_object* v_us_5392_, lean_object* v_args1_5393_, lean_object* v___x_5394_, lean_object* v_numParams_5395_, lean_object* v___x_5396_, lean_object* v_args2_5397_, lean_object* v___y_5398_, lean_object* v___y_5399_, lean_object* v___y_5400_, lean_object* v___y_5401_){
_start:
{
lean_object* v___x_5403_; lean_object* v___x_5404_; lean_object* v___x_5405_; lean_object* v___x_5406_; 
lean_inc(v_us_5392_);
v___x_5403_ = l_Lean_mkConst(v_name_5391_, v_us_5392_);
lean_inc_ref(v___x_5403_);
v___x_5404_ = l_Lean_mkAppN(v___x_5403_, v_args1_5393_);
v___x_5405_ = l_Lean_mkAppN(v___x_5403_, v_args2_5397_);
lean_inc_ref(v___x_5405_);
lean_inc_ref(v___x_5404_);
v___x_5406_ = l_Lean_Meta_mkEqHEq(v___x_5404_, v___x_5405_, v___y_5398_, v___y_5399_, v___y_5400_, v___y_5401_);
if (lean_obj_tag(v___x_5406_) == 0)
{
lean_object* v_a_5407_; lean_object* v___x_5408_; uint8_t v___x_5409_; lean_object* v___x_5410_; 
v_a_5407_ = lean_ctor_get(v___x_5406_, 0);
lean_inc(v_a_5407_);
lean_dec_ref(v___x_5406_);
lean_inc_ref_n(v_args2_5397_, 2);
v___x_5408_ = l_Array_toSubarray___redArg(v_args2_5397_, v___x_5394_, v_numParams_5395_);
v___x_5409_ = 1;
v___x_5410_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v_args1_5393_, v_args2_5397_, v___x_5409_, v___y_5398_, v___y_5399_, v___y_5400_, v___y_5401_);
if (lean_obj_tag(v___x_5410_) == 0)
{
lean_object* v_a_5411_; lean_object* v___x_5413_; uint8_t v_isShared_5414_; uint8_t v_isSharedCheck_5531_; 
v_a_5411_ = lean_ctor_get(v___x_5410_, 0);
v_isSharedCheck_5531_ = !lean_is_exclusive(v___x_5410_);
if (v_isSharedCheck_5531_ == 0)
{
v___x_5413_ = v___x_5410_;
v_isShared_5414_ = v_isSharedCheck_5531_;
goto v_resetjp_5412_;
}
else
{
lean_inc(v_a_5411_);
lean_dec(v___x_5410_);
v___x_5413_ = lean_box(0);
v_isShared_5414_ = v_isSharedCheck_5531_;
goto v_resetjp_5412_;
}
v_resetjp_5412_:
{
lean_object* v___x_5415_; 
v___x_5415_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f(v_a_5411_);
if (lean_obj_tag(v___x_5415_) == 1)
{
lean_object* v_val_5416_; lean_object* v___x_5417_; 
lean_del_object(v___x_5413_);
v_val_5416_ = lean_ctor_get(v___x_5415_, 0);
lean_inc(v_val_5416_);
lean_dec_ref(v___x_5415_);
v___x_5417_ = l_Lean_mkArrow(v_a_5407_, v_val_5416_, v___y_5400_, v___y_5401_);
if (lean_obj_tag(v___x_5417_) == 0)
{
lean_object* v_a_5418_; lean_object* v___x_5419_; 
v_a_5418_ = lean_ctor_get(v___x_5417_, 0);
lean_inc(v_a_5418_);
lean_dec_ref(v___x_5417_);
v___x_5419_ = l_Lean_Meta_getCtorAppIndices_x3f(v___x_5404_, v___y_5398_, v___y_5399_, v___y_5400_, v___y_5401_);
if (lean_obj_tag(v___x_5419_) == 0)
{
lean_object* v_a_5420_; lean_object* v___x_5422_; uint8_t v_isShared_5423_; uint8_t v_isSharedCheck_5510_; 
v_a_5420_ = lean_ctor_get(v___x_5419_, 0);
v_isSharedCheck_5510_ = !lean_is_exclusive(v___x_5419_);
if (v_isSharedCheck_5510_ == 0)
{
v___x_5422_ = v___x_5419_;
v_isShared_5423_ = v_isSharedCheck_5510_;
goto v_resetjp_5421_;
}
else
{
lean_inc(v_a_5420_);
lean_dec(v___x_5419_);
v___x_5422_ = lean_box(0);
v_isShared_5423_ = v_isSharedCheck_5510_;
goto v_resetjp_5421_;
}
v_resetjp_5421_:
{
if (lean_obj_tag(v_a_5420_) == 1)
{
lean_object* v_val_5424_; lean_object* v___x_5425_; 
lean_del_object(v___x_5422_);
v_val_5424_ = lean_ctor_get(v_a_5420_, 0);
lean_inc(v_val_5424_);
lean_dec_ref(v_a_5420_);
v___x_5425_ = l_Lean_Meta_getCtorAppIndices_x3f(v___x_5405_, v___y_5398_, v___y_5399_, v___y_5400_, v___y_5401_);
if (lean_obj_tag(v___x_5425_) == 0)
{
lean_object* v_a_5426_; lean_object* v___x_5428_; uint8_t v_isShared_5429_; uint8_t v_isSharedCheck_5497_; 
v_a_5426_ = lean_ctor_get(v___x_5425_, 0);
v_isSharedCheck_5497_ = !lean_is_exclusive(v___x_5425_);
if (v_isSharedCheck_5497_ == 0)
{
v___x_5428_ = v___x_5425_;
v_isShared_5429_ = v_isSharedCheck_5497_;
goto v_resetjp_5427_;
}
else
{
lean_inc(v_a_5426_);
lean_dec(v___x_5425_);
v___x_5428_ = lean_box(0);
v_isShared_5429_ = v_isSharedCheck_5497_;
goto v_resetjp_5427_;
}
v_resetjp_5427_:
{
if (lean_obj_tag(v_a_5426_) == 1)
{
lean_object* v_val_5430_; lean_object* v___x_5432_; uint8_t v_isShared_5433_; uint8_t v_isSharedCheck_5492_; 
lean_del_object(v___x_5428_);
v_val_5430_ = lean_ctor_get(v_a_5426_, 0);
v_isSharedCheck_5492_ = !lean_is_exclusive(v_a_5426_);
if (v_isSharedCheck_5492_ == 0)
{
v___x_5432_ = v_a_5426_;
v_isShared_5433_ = v_isSharedCheck_5492_;
goto v_resetjp_5431_;
}
else
{
lean_inc(v_val_5430_);
lean_dec(v_a_5426_);
v___x_5432_ = lean_box(0);
v_isShared_5433_ = v_isSharedCheck_5492_;
goto v_resetjp_5431_;
}
v_resetjp_5431_:
{
lean_object* v___x_5434_; lean_object* v___x_5435_; lean_object* v___x_5436_; lean_object* v___x_5437_; uint8_t v___x_5438_; lean_object* v___x_5439_; 
v___x_5434_ = l_Subarray_copy___redArg(v___x_5396_);
v___x_5435_ = l_Array_append___redArg(v___x_5434_, v_val_5424_);
v___x_5436_ = l_Subarray_copy___redArg(v___x_5408_);
v___x_5437_ = l_Array_append___redArg(v___x_5436_, v_val_5430_);
lean_dec(v_val_5430_);
v___x_5438_ = 0;
v___x_5439_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v___x_5435_, v___x_5437_, v___x_5438_, v___y_5398_, v___y_5399_, v___y_5400_, v___y_5401_);
lean_dec_ref(v___x_5435_);
if (lean_obj_tag(v___x_5439_) == 0)
{
lean_object* v_a_5440_; lean_object* v___x_5441_; 
v_a_5440_ = lean_ctor_get(v___x_5439_, 0);
lean_inc(v_a_5440_);
lean_dec_ref(v___x_5439_);
v___x_5441_ = l_Lean_mkArrowN(v_a_5440_, v_a_5418_, v___y_5400_, v___y_5401_);
lean_dec(v_a_5440_);
if (lean_obj_tag(v___x_5441_) == 0)
{
lean_object* v_a_5442_; uint8_t v___x_5443_; lean_object* v___x_5444_; 
v_a_5442_ = lean_ctor_get(v___x_5441_, 0);
lean_inc(v_a_5442_);
lean_dec_ref(v___x_5441_);
v___x_5443_ = 1;
v___x_5444_ = l_Lean_Meta_mkForallFVars(v_args2_5397_, v_a_5442_, v___x_5438_, v___x_5409_, v___x_5409_, v___x_5443_, v___y_5398_, v___y_5399_, v___y_5400_, v___y_5401_);
lean_dec_ref(v_args2_5397_);
if (lean_obj_tag(v___x_5444_) == 0)
{
lean_object* v_a_5445_; lean_object* v___x_5446_; 
v_a_5445_ = lean_ctor_get(v___x_5444_, 0);
lean_inc(v_a_5445_);
lean_dec_ref(v___x_5444_);
v___x_5446_ = l_Lean_Meta_mkForallFVars(v_args1_5393_, v_a_5445_, v___x_5438_, v___x_5409_, v___x_5409_, v___x_5443_, v___y_5398_, v___y_5399_, v___y_5400_, v___y_5401_);
if (lean_obj_tag(v___x_5446_) == 0)
{
lean_object* v_a_5447_; lean_object* v___x_5449_; uint8_t v_isShared_5450_; uint8_t v_isSharedCheck_5459_; 
v_a_5447_ = lean_ctor_get(v___x_5446_, 0);
v_isSharedCheck_5459_ = !lean_is_exclusive(v___x_5446_);
if (v_isSharedCheck_5459_ == 0)
{
v___x_5449_ = v___x_5446_;
v_isShared_5450_ = v_isSharedCheck_5459_;
goto v_resetjp_5448_;
}
else
{
lean_inc(v_a_5447_);
lean_dec(v___x_5446_);
v___x_5449_ = lean_box(0);
v_isShared_5450_ = v_isSharedCheck_5459_;
goto v_resetjp_5448_;
}
v_resetjp_5448_:
{
lean_object* v___x_5451_; lean_object* v___x_5452_; lean_object* v___x_5454_; 
v___x_5451_ = lean_array_get_size(v_val_5424_);
lean_dec(v_val_5424_);
v___x_5452_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5452_, 0, v_a_5447_);
lean_ctor_set(v___x_5452_, 1, v_us_5392_);
lean_ctor_set(v___x_5452_, 2, v___x_5451_);
if (v_isShared_5433_ == 0)
{
lean_ctor_set(v___x_5432_, 0, v___x_5452_);
v___x_5454_ = v___x_5432_;
goto v_reusejp_5453_;
}
else
{
lean_object* v_reuseFailAlloc_5458_; 
v_reuseFailAlloc_5458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5458_, 0, v___x_5452_);
v___x_5454_ = v_reuseFailAlloc_5458_;
goto v_reusejp_5453_;
}
v_reusejp_5453_:
{
lean_object* v___x_5456_; 
if (v_isShared_5450_ == 0)
{
lean_ctor_set(v___x_5449_, 0, v___x_5454_);
v___x_5456_ = v___x_5449_;
goto v_reusejp_5455_;
}
else
{
lean_object* v_reuseFailAlloc_5457_; 
v_reuseFailAlloc_5457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5457_, 0, v___x_5454_);
v___x_5456_ = v_reuseFailAlloc_5457_;
goto v_reusejp_5455_;
}
v_reusejp_5455_:
{
return v___x_5456_;
}
}
}
}
else
{
lean_object* v_a_5460_; lean_object* v___x_5462_; uint8_t v_isShared_5463_; uint8_t v_isSharedCheck_5467_; 
lean_del_object(v___x_5432_);
lean_dec(v_val_5424_);
lean_dec(v_us_5392_);
v_a_5460_ = lean_ctor_get(v___x_5446_, 0);
v_isSharedCheck_5467_ = !lean_is_exclusive(v___x_5446_);
if (v_isSharedCheck_5467_ == 0)
{
v___x_5462_ = v___x_5446_;
v_isShared_5463_ = v_isSharedCheck_5467_;
goto v_resetjp_5461_;
}
else
{
lean_inc(v_a_5460_);
lean_dec(v___x_5446_);
v___x_5462_ = lean_box(0);
v_isShared_5463_ = v_isSharedCheck_5467_;
goto v_resetjp_5461_;
}
v_resetjp_5461_:
{
lean_object* v___x_5465_; 
if (v_isShared_5463_ == 0)
{
v___x_5465_ = v___x_5462_;
goto v_reusejp_5464_;
}
else
{
lean_object* v_reuseFailAlloc_5466_; 
v_reuseFailAlloc_5466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5466_, 0, v_a_5460_);
v___x_5465_ = v_reuseFailAlloc_5466_;
goto v_reusejp_5464_;
}
v_reusejp_5464_:
{
return v___x_5465_;
}
}
}
}
else
{
lean_object* v_a_5468_; lean_object* v___x_5470_; uint8_t v_isShared_5471_; uint8_t v_isSharedCheck_5475_; 
lean_del_object(v___x_5432_);
lean_dec(v_val_5424_);
lean_dec(v_us_5392_);
v_a_5468_ = lean_ctor_get(v___x_5444_, 0);
v_isSharedCheck_5475_ = !lean_is_exclusive(v___x_5444_);
if (v_isSharedCheck_5475_ == 0)
{
v___x_5470_ = v___x_5444_;
v_isShared_5471_ = v_isSharedCheck_5475_;
goto v_resetjp_5469_;
}
else
{
lean_inc(v_a_5468_);
lean_dec(v___x_5444_);
v___x_5470_ = lean_box(0);
v_isShared_5471_ = v_isSharedCheck_5475_;
goto v_resetjp_5469_;
}
v_resetjp_5469_:
{
lean_object* v___x_5473_; 
if (v_isShared_5471_ == 0)
{
v___x_5473_ = v___x_5470_;
goto v_reusejp_5472_;
}
else
{
lean_object* v_reuseFailAlloc_5474_; 
v_reuseFailAlloc_5474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5474_, 0, v_a_5468_);
v___x_5473_ = v_reuseFailAlloc_5474_;
goto v_reusejp_5472_;
}
v_reusejp_5472_:
{
return v___x_5473_;
}
}
}
}
else
{
lean_object* v_a_5476_; lean_object* v___x_5478_; uint8_t v_isShared_5479_; uint8_t v_isSharedCheck_5483_; 
lean_del_object(v___x_5432_);
lean_dec(v_val_5424_);
lean_dec_ref(v_args2_5397_);
lean_dec(v_us_5392_);
v_a_5476_ = lean_ctor_get(v___x_5441_, 0);
v_isSharedCheck_5483_ = !lean_is_exclusive(v___x_5441_);
if (v_isSharedCheck_5483_ == 0)
{
v___x_5478_ = v___x_5441_;
v_isShared_5479_ = v_isSharedCheck_5483_;
goto v_resetjp_5477_;
}
else
{
lean_inc(v_a_5476_);
lean_dec(v___x_5441_);
v___x_5478_ = lean_box(0);
v_isShared_5479_ = v_isSharedCheck_5483_;
goto v_resetjp_5477_;
}
v_resetjp_5477_:
{
lean_object* v___x_5481_; 
if (v_isShared_5479_ == 0)
{
v___x_5481_ = v___x_5478_;
goto v_reusejp_5480_;
}
else
{
lean_object* v_reuseFailAlloc_5482_; 
v_reuseFailAlloc_5482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5482_, 0, v_a_5476_);
v___x_5481_ = v_reuseFailAlloc_5482_;
goto v_reusejp_5480_;
}
v_reusejp_5480_:
{
return v___x_5481_;
}
}
}
}
else
{
lean_object* v_a_5484_; lean_object* v___x_5486_; uint8_t v_isShared_5487_; uint8_t v_isSharedCheck_5491_; 
lean_del_object(v___x_5432_);
lean_dec(v_val_5424_);
lean_dec(v_a_5418_);
lean_dec_ref(v_args2_5397_);
lean_dec(v_us_5392_);
v_a_5484_ = lean_ctor_get(v___x_5439_, 0);
v_isSharedCheck_5491_ = !lean_is_exclusive(v___x_5439_);
if (v_isSharedCheck_5491_ == 0)
{
v___x_5486_ = v___x_5439_;
v_isShared_5487_ = v_isSharedCheck_5491_;
goto v_resetjp_5485_;
}
else
{
lean_inc(v_a_5484_);
lean_dec(v___x_5439_);
v___x_5486_ = lean_box(0);
v_isShared_5487_ = v_isSharedCheck_5491_;
goto v_resetjp_5485_;
}
v_resetjp_5485_:
{
lean_object* v___x_5489_; 
if (v_isShared_5487_ == 0)
{
v___x_5489_ = v___x_5486_;
goto v_reusejp_5488_;
}
else
{
lean_object* v_reuseFailAlloc_5490_; 
v_reuseFailAlloc_5490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5490_, 0, v_a_5484_);
v___x_5489_ = v_reuseFailAlloc_5490_;
goto v_reusejp_5488_;
}
v_reusejp_5488_:
{
return v___x_5489_;
}
}
}
}
}
else
{
lean_object* v___x_5493_; lean_object* v___x_5495_; 
lean_dec(v_a_5426_);
lean_dec(v_val_5424_);
lean_dec(v_a_5418_);
lean_dec_ref(v___x_5408_);
lean_dec_ref(v_args2_5397_);
lean_dec_ref(v___x_5396_);
lean_dec(v_us_5392_);
v___x_5493_ = lean_box(0);
if (v_isShared_5429_ == 0)
{
lean_ctor_set(v___x_5428_, 0, v___x_5493_);
v___x_5495_ = v___x_5428_;
goto v_reusejp_5494_;
}
else
{
lean_object* v_reuseFailAlloc_5496_; 
v_reuseFailAlloc_5496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5496_, 0, v___x_5493_);
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
lean_dec(v_val_5424_);
lean_dec(v_a_5418_);
lean_dec_ref(v___x_5408_);
lean_dec_ref(v_args2_5397_);
lean_dec_ref(v___x_5396_);
lean_dec(v_us_5392_);
v_a_5498_ = lean_ctor_get(v___x_5425_, 0);
v_isSharedCheck_5505_ = !lean_is_exclusive(v___x_5425_);
if (v_isSharedCheck_5505_ == 0)
{
v___x_5500_ = v___x_5425_;
v_isShared_5501_ = v_isSharedCheck_5505_;
goto v_resetjp_5499_;
}
else
{
lean_inc(v_a_5498_);
lean_dec(v___x_5425_);
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
else
{
lean_object* v___x_5506_; lean_object* v___x_5508_; 
lean_dec(v_a_5420_);
lean_dec(v_a_5418_);
lean_dec_ref(v___x_5408_);
lean_dec_ref(v___x_5405_);
lean_dec_ref(v_args2_5397_);
lean_dec_ref(v___x_5396_);
lean_dec(v_us_5392_);
v___x_5506_ = lean_box(0);
if (v_isShared_5423_ == 0)
{
lean_ctor_set(v___x_5422_, 0, v___x_5506_);
v___x_5508_ = v___x_5422_;
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
lean_dec(v_a_5418_);
lean_dec_ref(v___x_5408_);
lean_dec_ref(v___x_5405_);
lean_dec_ref(v_args2_5397_);
lean_dec_ref(v___x_5396_);
lean_dec(v_us_5392_);
v_a_5511_ = lean_ctor_get(v___x_5419_, 0);
v_isSharedCheck_5518_ = !lean_is_exclusive(v___x_5419_);
if (v_isSharedCheck_5518_ == 0)
{
v___x_5513_ = v___x_5419_;
v_isShared_5514_ = v_isSharedCheck_5518_;
goto v_resetjp_5512_;
}
else
{
lean_inc(v_a_5511_);
lean_dec(v___x_5419_);
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
lean_object* v_a_5519_; lean_object* v___x_5521_; uint8_t v_isShared_5522_; uint8_t v_isSharedCheck_5526_; 
lean_dec_ref(v___x_5408_);
lean_dec_ref(v___x_5405_);
lean_dec_ref(v___x_5404_);
lean_dec_ref(v_args2_5397_);
lean_dec_ref(v___x_5396_);
lean_dec(v_us_5392_);
v_a_5519_ = lean_ctor_get(v___x_5417_, 0);
v_isSharedCheck_5526_ = !lean_is_exclusive(v___x_5417_);
if (v_isSharedCheck_5526_ == 0)
{
v___x_5521_ = v___x_5417_;
v_isShared_5522_ = v_isSharedCheck_5526_;
goto v_resetjp_5520_;
}
else
{
lean_inc(v_a_5519_);
lean_dec(v___x_5417_);
v___x_5521_ = lean_box(0);
v_isShared_5522_ = v_isSharedCheck_5526_;
goto v_resetjp_5520_;
}
v_resetjp_5520_:
{
lean_object* v___x_5524_; 
if (v_isShared_5522_ == 0)
{
v___x_5524_ = v___x_5521_;
goto v_reusejp_5523_;
}
else
{
lean_object* v_reuseFailAlloc_5525_; 
v_reuseFailAlloc_5525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5525_, 0, v_a_5519_);
v___x_5524_ = v_reuseFailAlloc_5525_;
goto v_reusejp_5523_;
}
v_reusejp_5523_:
{
return v___x_5524_;
}
}
}
}
else
{
lean_object* v___x_5527_; lean_object* v___x_5529_; 
lean_dec(v___x_5415_);
lean_dec_ref(v___x_5408_);
lean_dec(v_a_5407_);
lean_dec_ref(v___x_5405_);
lean_dec_ref(v___x_5404_);
lean_dec_ref(v_args2_5397_);
lean_dec_ref(v___x_5396_);
lean_dec(v_us_5392_);
v___x_5527_ = lean_box(0);
if (v_isShared_5414_ == 0)
{
lean_ctor_set(v___x_5413_, 0, v___x_5527_);
v___x_5529_ = v___x_5413_;
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
lean_dec_ref(v___x_5408_);
lean_dec(v_a_5407_);
lean_dec_ref(v___x_5405_);
lean_dec_ref(v___x_5404_);
lean_dec_ref(v_args2_5397_);
lean_dec_ref(v___x_5396_);
lean_dec(v_us_5392_);
v_a_5532_ = lean_ctor_get(v___x_5410_, 0);
v_isSharedCheck_5539_ = !lean_is_exclusive(v___x_5410_);
if (v_isSharedCheck_5539_ == 0)
{
v___x_5534_ = v___x_5410_;
v_isShared_5535_ = v_isSharedCheck_5539_;
goto v_resetjp_5533_;
}
else
{
lean_inc(v_a_5532_);
lean_dec(v___x_5410_);
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
lean_object* v_a_5540_; lean_object* v___x_5542_; uint8_t v_isShared_5543_; uint8_t v_isSharedCheck_5547_; 
lean_dec_ref(v___x_5405_);
lean_dec_ref(v___x_5404_);
lean_dec_ref(v_args2_5397_);
lean_dec_ref(v___x_5396_);
lean_dec(v_numParams_5395_);
lean_dec(v___x_5394_);
lean_dec(v_us_5392_);
v_a_5540_ = lean_ctor_get(v___x_5406_, 0);
v_isSharedCheck_5547_ = !lean_is_exclusive(v___x_5406_);
if (v_isSharedCheck_5547_ == 0)
{
v___x_5542_ = v___x_5406_;
v_isShared_5543_ = v_isSharedCheck_5547_;
goto v_resetjp_5541_;
}
else
{
lean_inc(v_a_5540_);
lean_dec(v___x_5406_);
v___x_5542_ = lean_box(0);
v_isShared_5543_ = v_isSharedCheck_5547_;
goto v_resetjp_5541_;
}
v_resetjp_5541_:
{
lean_object* v___x_5545_; 
if (v_isShared_5543_ == 0)
{
v___x_5545_ = v___x_5542_;
goto v_reusejp_5544_;
}
else
{
lean_object* v_reuseFailAlloc_5546_; 
v_reuseFailAlloc_5546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5546_, 0, v_a_5540_);
v___x_5545_ = v_reuseFailAlloc_5546_;
goto v_reusejp_5544_;
}
v_reusejp_5544_:
{
return v___x_5545_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0___boxed(lean_object* v_name_5548_, lean_object* v_us_5549_, lean_object* v_args1_5550_, lean_object* v___x_5551_, lean_object* v_numParams_5552_, lean_object* v___x_5553_, lean_object* v_args2_5554_, lean_object* v___y_5555_, lean_object* v___y_5556_, lean_object* v___y_5557_, lean_object* v___y_5558_, lean_object* v___y_5559_){
_start:
{
lean_object* v_res_5560_; 
v_res_5560_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0(v_name_5548_, v_us_5549_, v_args1_5550_, v___x_5551_, v_numParams_5552_, v___x_5553_, v_args2_5554_, v___y_5555_, v___y_5556_, v___y_5557_, v___y_5558_);
lean_dec(v___y_5558_);
lean_dec_ref(v___y_5557_);
lean_dec(v___y_5556_);
lean_dec_ref(v___y_5555_);
lean_dec_ref(v_args1_5550_);
return v_res_5560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1(lean_object* v_numParams_5561_, lean_object* v_name_5562_, lean_object* v_us_5563_, lean_object* v_ctorVal_5564_, lean_object* v_a_5565_, lean_object* v_args1_5566_, lean_object* v_x_5567_, lean_object* v___y_5568_, lean_object* v___y_5569_, lean_object* v___y_5570_, lean_object* v___y_5571_){
_start:
{
lean_object* v___x_5573_; lean_object* v___x_5574_; lean_object* v___f_5575_; lean_object* v___x_5576_; lean_object* v___x_5577_; lean_object* v___x_5578_; 
v___x_5573_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_5561_);
lean_inc_ref_n(v_args1_5566_, 3);
v___x_5574_ = l_Array_toSubarray___redArg(v_args1_5566_, v___x_5573_, v_numParams_5561_);
v___f_5575_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0___boxed), 12, 6);
lean_closure_set(v___f_5575_, 0, v_name_5562_);
lean_closure_set(v___f_5575_, 1, v_us_5563_);
lean_closure_set(v___f_5575_, 2, v_args1_5566_);
lean_closure_set(v___f_5575_, 3, v___x_5573_);
lean_closure_set(v___f_5575_, 4, v_numParams_5561_);
lean_closure_set(v___f_5575_, 5, v___x_5574_);
v___x_5576_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_5577_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___boxed), 11, 6);
lean_closure_set(v___x_5577_, 0, v_ctorVal_5564_);
lean_closure_set(v___x_5577_, 1, v_args1_5566_);
lean_closure_set(v___x_5577_, 2, v___f_5575_);
lean_closure_set(v___x_5577_, 3, v___x_5573_);
lean_closure_set(v___x_5577_, 4, v_a_5565_);
lean_closure_set(v___x_5577_, 5, v___x_5576_);
v___x_5578_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v_args1_5566_, v___x_5577_, v___y_5568_, v___y_5569_, v___y_5570_, v___y_5571_);
return v___x_5578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1___boxed(lean_object* v_numParams_5579_, lean_object* v_name_5580_, lean_object* v_us_5581_, lean_object* v_ctorVal_5582_, lean_object* v_a_5583_, lean_object* v_args1_5584_, lean_object* v_x_5585_, lean_object* v___y_5586_, lean_object* v___y_5587_, lean_object* v___y_5588_, lean_object* v___y_5589_, lean_object* v___y_5590_){
_start:
{
lean_object* v_res_5591_; 
v_res_5591_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1(v_numParams_5579_, v_name_5580_, v_us_5581_, v_ctorVal_5582_, v_a_5583_, v_args1_5584_, v_x_5585_, v___y_5586_, v___y_5587_, v___y_5588_, v___y_5589_);
lean_dec(v___y_5589_);
lean_dec_ref(v___y_5588_);
lean_dec(v___y_5587_);
lean_dec_ref(v___y_5586_);
lean_dec_ref(v_x_5585_);
return v_res_5591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(lean_object* v_ctorVal_5592_, lean_object* v_a_5593_, lean_object* v_a_5594_, lean_object* v_a_5595_, lean_object* v_a_5596_){
_start:
{
lean_object* v_toConstantVal_5598_; lean_object* v_numParams_5599_; lean_object* v_name_5600_; lean_object* v_levelParams_5601_; lean_object* v_type_5602_; lean_object* v___x_5603_; 
v_toConstantVal_5598_ = lean_ctor_get(v_ctorVal_5592_, 0);
v_numParams_5599_ = lean_ctor_get(v_ctorVal_5592_, 3);
lean_inc(v_numParams_5599_);
v_name_5600_ = lean_ctor_get(v_toConstantVal_5598_, 0);
lean_inc(v_name_5600_);
v_levelParams_5601_ = lean_ctor_get(v_toConstantVal_5598_, 1);
v_type_5602_ = lean_ctor_get(v_toConstantVal_5598_, 2);
lean_inc_ref(v_type_5602_);
v___x_5603_ = l_Lean_Meta_elimOptParam(v_type_5602_, v_a_5595_, v_a_5596_);
if (lean_obj_tag(v___x_5603_) == 0)
{
lean_object* v_a_5604_; lean_object* v___x_5605_; lean_object* v_us_5606_; lean_object* v___f_5607_; uint8_t v___x_5608_; lean_object* v___x_5609_; 
v_a_5604_ = lean_ctor_get(v___x_5603_, 0);
lean_inc_n(v_a_5604_, 2);
lean_dec_ref(v___x_5603_);
v___x_5605_ = lean_box(0);
lean_inc(v_levelParams_5601_);
v_us_5606_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(v_levelParams_5601_, v___x_5605_);
v___f_5607_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1___boxed), 12, 5);
lean_closure_set(v___f_5607_, 0, v_numParams_5599_);
lean_closure_set(v___f_5607_, 1, v_name_5600_);
lean_closure_set(v___f_5607_, 2, v_us_5606_);
lean_closure_set(v___f_5607_, 3, v_ctorVal_5592_);
lean_closure_set(v___f_5607_, 4, v_a_5604_);
v___x_5608_ = 0;
v___x_5609_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_a_5604_, v___f_5607_, v___x_5608_, v_a_5593_, v_a_5594_, v_a_5595_, v_a_5596_);
return v___x_5609_;
}
else
{
lean_object* v_a_5610_; lean_object* v___x_5612_; uint8_t v_isShared_5613_; uint8_t v_isSharedCheck_5617_; 
lean_dec(v_name_5600_);
lean_dec(v_numParams_5599_);
lean_dec_ref(v_ctorVal_5592_);
v_a_5610_ = lean_ctor_get(v___x_5603_, 0);
v_isSharedCheck_5617_ = !lean_is_exclusive(v___x_5603_);
if (v_isSharedCheck_5617_ == 0)
{
v___x_5612_ = v___x_5603_;
v_isShared_5613_ = v_isSharedCheck_5617_;
goto v_resetjp_5611_;
}
else
{
lean_inc(v_a_5610_);
lean_dec(v___x_5603_);
v___x_5612_ = lean_box(0);
v_isShared_5613_ = v_isSharedCheck_5617_;
goto v_resetjp_5611_;
}
v_resetjp_5611_:
{
lean_object* v___x_5615_; 
if (v_isShared_5613_ == 0)
{
v___x_5615_ = v___x_5612_;
goto v_reusejp_5614_;
}
else
{
lean_object* v_reuseFailAlloc_5616_; 
v_reuseFailAlloc_5616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5616_, 0, v_a_5610_);
v___x_5615_ = v_reuseFailAlloc_5616_;
goto v_reusejp_5614_;
}
v_reusejp_5614_:
{
return v___x_5615_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___boxed(lean_object* v_ctorVal_5618_, lean_object* v_a_5619_, lean_object* v_a_5620_, lean_object* v_a_5621_, lean_object* v_a_5622_, lean_object* v_a_5623_){
_start:
{
lean_object* v_res_5624_; 
v_res_5624_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(v_ctorVal_5618_, v_a_5619_, v_a_5620_, v_a_5621_, v_a_5622_);
lean_dec(v_a_5622_);
lean_dec_ref(v_a_5621_);
lean_dec(v_a_5620_);
lean_dec_ref(v_a_5619_);
return v_res_5624_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1(void){
_start:
{
lean_object* v___x_5626_; lean_object* v___x_5627_; 
v___x_5626_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__0));
v___x_5627_ = l_Lean_stringToMessageData(v___x_5626_);
return v___x_5627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(lean_object* v_ctorVal_5628_, lean_object* v_a_5629_, lean_object* v_a_5630_, lean_object* v_a_5631_, lean_object* v_a_5632_){
_start:
{
lean_object* v_toConstantVal_5634_; lean_object* v_name_5635_; lean_object* v___x_5636_; lean_object* v___x_5637_; lean_object* v___x_5638_; lean_object* v___x_5639_; lean_object* v___x_5640_; lean_object* v___x_5641_; 
v_toConstantVal_5634_ = lean_ctor_get(v_ctorVal_5628_, 0);
lean_inc_ref(v_toConstantVal_5634_);
lean_dec_ref(v_ctorVal_5628_);
v_name_5635_ = lean_ctor_get(v_toConstantVal_5634_, 0);
lean_inc(v_name_5635_);
lean_dec_ref(v_toConstantVal_5634_);
v___x_5636_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1);
v___x_5637_ = l_Lean_MessageData_ofName(v_name_5635_);
v___x_5638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5638_, 0, v___x_5636_);
lean_ctor_set(v___x_5638_, 1, v___x_5637_);
v___x_5639_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_5640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5640_, 0, v___x_5638_);
lean_ctor_set(v___x_5640_, 1, v___x_5639_);
v___x_5641_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_5640_, v_a_5629_, v_a_5630_, v_a_5631_, v_a_5632_);
return v___x_5641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___boxed(lean_object* v_ctorVal_5642_, lean_object* v_a_5643_, lean_object* v_a_5644_, lean_object* v_a_5645_, lean_object* v_a_5646_, lean_object* v_a_5647_){
_start:
{
lean_object* v_res_5648_; 
v_res_5648_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5642_, v_a_5643_, v_a_5644_, v_a_5645_, v_a_5646_);
lean_dec(v_a_5646_);
lean_dec_ref(v_a_5645_);
lean_dec(v_a_5644_);
lean_dec_ref(v_a_5643_);
return v_res_5648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj(lean_object* v_00_u03b1_5649_, lean_object* v_ctorVal_5650_, lean_object* v_a_5651_, lean_object* v_a_5652_, lean_object* v_a_5653_, lean_object* v_a_5654_){
_start:
{
lean_object* v___x_5656_; 
v___x_5656_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5650_, v_a_5651_, v_a_5652_, v_a_5653_, v_a_5654_);
return v___x_5656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___boxed(lean_object* v_00_u03b1_5657_, lean_object* v_ctorVal_5658_, lean_object* v_a_5659_, lean_object* v_a_5660_, lean_object* v_a_5661_, lean_object* v_a_5662_, lean_object* v_a_5663_){
_start:
{
lean_object* v_res_5664_; 
v_res_5664_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj(v_00_u03b1_5657_, v_ctorVal_5658_, v_a_5659_, v_a_5660_, v_a_5661_, v_a_5662_);
lean_dec(v_a_5662_);
lean_dec_ref(v_a_5661_);
lean_dec(v_a_5660_);
lean_dec_ref(v_a_5659_);
return v_res_5664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(lean_object* v_ctorVal_5670_, size_t v_sz_5671_, size_t v_i_5672_, lean_object* v_bs_5673_, lean_object* v___y_5674_, lean_object* v___y_5675_, lean_object* v___y_5676_, lean_object* v___y_5677_){
_start:
{
uint8_t v___x_5679_; 
v___x_5679_ = lean_usize_dec_lt(v_i_5672_, v_sz_5671_);
if (v___x_5679_ == 0)
{
lean_object* v___x_5680_; 
lean_dec_ref(v_ctorVal_5670_);
v___x_5680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5680_, 0, v_bs_5673_);
return v___x_5680_;
}
else
{
lean_object* v_v_5681_; lean_object* v___x_5682_; 
v_v_5681_ = lean_array_uget_borrowed(v_bs_5673_, v_i_5672_);
lean_inc(v___y_5677_);
lean_inc_ref(v___y_5676_);
lean_inc(v___y_5675_);
lean_inc_ref(v___y_5674_);
lean_inc(v_v_5681_);
v___x_5682_ = lean_infer_type(v_v_5681_, v___y_5674_, v___y_5675_, v___y_5676_, v___y_5677_);
if (lean_obj_tag(v___x_5682_) == 0)
{
lean_object* v_a_5683_; lean_object* v___x_5684_; 
v_a_5683_ = lean_ctor_get(v___x_5682_, 0);
lean_inc(v_a_5683_);
lean_dec_ref(v___x_5682_);
v___x_5684_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_5683_, v___y_5675_);
if (lean_obj_tag(v___x_5684_) == 0)
{
lean_object* v_a_5685_; lean_object* v___x_5686_; lean_object* v_bs_x27_5687_; lean_object* v_a_5689_; lean_object* v___y_5695_; lean_object* v_lhs_5706_; lean_object* v_rhs_5707_; lean_object* v___x_5709_; uint8_t v___x_5710_; 
v_a_5685_ = lean_ctor_get(v___x_5684_, 0);
lean_inc(v_a_5685_);
lean_dec_ref(v___x_5684_);
v___x_5686_ = lean_unsigned_to_nat(0u);
v_bs_x27_5687_ = lean_array_uset(v_bs_5673_, v_i_5672_, v___x_5686_);
v___x_5709_ = l_Lean_Expr_cleanupAnnotations(v_a_5685_);
v___x_5710_ = l_Lean_Expr_isApp(v___x_5709_);
if (v___x_5710_ == 0)
{
lean_object* v___x_5711_; 
lean_dec_ref(v___x_5709_);
lean_inc_ref(v_ctorVal_5670_);
v___x_5711_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5670_, v___y_5674_, v___y_5675_, v___y_5676_, v___y_5677_);
v___y_5695_ = v___x_5711_;
goto v___jp_5694_;
}
else
{
lean_object* v_arg_5712_; lean_object* v___x_5713_; uint8_t v___x_5714_; 
v_arg_5712_ = lean_ctor_get(v___x_5709_, 1);
lean_inc_ref(v_arg_5712_);
v___x_5713_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5709_);
v___x_5714_ = l_Lean_Expr_isApp(v___x_5713_);
if (v___x_5714_ == 0)
{
lean_object* v___x_5715_; 
lean_dec_ref(v___x_5713_);
lean_dec_ref(v_arg_5712_);
lean_inc_ref(v_ctorVal_5670_);
v___x_5715_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5670_, v___y_5674_, v___y_5675_, v___y_5676_, v___y_5677_);
v___y_5695_ = v___x_5715_;
goto v___jp_5694_;
}
else
{
lean_object* v_arg_5716_; lean_object* v___x_5717_; uint8_t v___x_5718_; 
v_arg_5716_ = lean_ctor_get(v___x_5713_, 1);
lean_inc_ref(v_arg_5716_);
v___x_5717_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5713_);
v___x_5718_ = l_Lean_Expr_isApp(v___x_5717_);
if (v___x_5718_ == 0)
{
lean_object* v___x_5719_; 
lean_dec_ref(v___x_5717_);
lean_dec_ref(v_arg_5716_);
lean_dec_ref(v_arg_5712_);
lean_inc_ref(v_ctorVal_5670_);
v___x_5719_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5670_, v___y_5674_, v___y_5675_, v___y_5676_, v___y_5677_);
v___y_5695_ = v___x_5719_;
goto v___jp_5694_;
}
else
{
lean_object* v_arg_5720_; lean_object* v___x_5721_; lean_object* v___x_5722_; uint8_t v___x_5723_; 
v_arg_5720_ = lean_ctor_get(v___x_5717_, 1);
lean_inc_ref(v_arg_5720_);
v___x_5721_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5717_);
v___x_5722_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__0));
v___x_5723_ = l_Lean_Expr_isConstOf(v___x_5721_, v___x_5722_);
if (v___x_5723_ == 0)
{
uint8_t v___x_5724_; 
lean_dec_ref(v_arg_5716_);
v___x_5724_ = l_Lean_Expr_isApp(v___x_5721_);
if (v___x_5724_ == 0)
{
lean_object* v___x_5725_; 
lean_dec_ref(v___x_5721_);
lean_dec_ref(v_arg_5720_);
lean_dec_ref(v_arg_5712_);
lean_inc_ref(v_ctorVal_5670_);
v___x_5725_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5670_, v___y_5674_, v___y_5675_, v___y_5676_, v___y_5677_);
v___y_5695_ = v___x_5725_;
goto v___jp_5694_;
}
else
{
lean_object* v___x_5726_; lean_object* v___x_5727_; uint8_t v___x_5728_; 
v___x_5726_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5721_);
v___x_5727_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__2));
v___x_5728_ = l_Lean_Expr_isConstOf(v___x_5726_, v___x_5727_);
lean_dec_ref(v___x_5726_);
if (v___x_5728_ == 0)
{
lean_object* v___x_5729_; 
lean_dec_ref(v_arg_5720_);
lean_dec_ref(v_arg_5712_);
lean_inc_ref(v_ctorVal_5670_);
v___x_5729_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5670_, v___y_5674_, v___y_5675_, v___y_5676_, v___y_5677_);
v___y_5695_ = v___x_5729_;
goto v___jp_5694_;
}
else
{
v_lhs_5706_ = v_arg_5720_;
v_rhs_5707_ = v_arg_5712_;
goto v___jp_5705_;
}
}
}
else
{
lean_dec_ref(v___x_5721_);
lean_dec_ref(v_arg_5720_);
v_lhs_5706_ = v_arg_5716_;
v_rhs_5707_ = v_arg_5712_;
goto v___jp_5705_;
}
}
}
}
v___jp_5688_:
{
size_t v___x_5690_; size_t v___x_5691_; lean_object* v___x_5692_; 
v___x_5690_ = ((size_t)1ULL);
v___x_5691_ = lean_usize_add(v_i_5672_, v___x_5690_);
v___x_5692_ = lean_array_uset(v_bs_x27_5687_, v_i_5672_, v_a_5689_);
v_i_5672_ = v___x_5691_;
v_bs_5673_ = v___x_5692_;
goto _start;
}
v___jp_5694_:
{
if (lean_obj_tag(v___y_5695_) == 0)
{
lean_object* v_a_5696_; 
v_a_5696_ = lean_ctor_get(v___y_5695_, 0);
lean_inc(v_a_5696_);
lean_dec_ref(v___y_5695_);
v_a_5689_ = v_a_5696_;
goto v___jp_5688_;
}
else
{
lean_object* v_a_5697_; lean_object* v___x_5699_; uint8_t v_isShared_5700_; uint8_t v_isSharedCheck_5704_; 
lean_dec_ref(v_bs_x27_5687_);
lean_dec_ref(v_ctorVal_5670_);
v_a_5697_ = lean_ctor_get(v___y_5695_, 0);
v_isSharedCheck_5704_ = !lean_is_exclusive(v___y_5695_);
if (v_isSharedCheck_5704_ == 0)
{
v___x_5699_ = v___y_5695_;
v_isShared_5700_ = v_isSharedCheck_5704_;
goto v_resetjp_5698_;
}
else
{
lean_inc(v_a_5697_);
lean_dec(v___y_5695_);
v___x_5699_ = lean_box(0);
v_isShared_5700_ = v_isSharedCheck_5704_;
goto v_resetjp_5698_;
}
v_resetjp_5698_:
{
lean_object* v___x_5702_; 
if (v_isShared_5700_ == 0)
{
v___x_5702_ = v___x_5699_;
goto v_reusejp_5701_;
}
else
{
lean_object* v_reuseFailAlloc_5703_; 
v_reuseFailAlloc_5703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5703_, 0, v_a_5697_);
v___x_5702_ = v_reuseFailAlloc_5703_;
goto v_reusejp_5701_;
}
v_reusejp_5701_:
{
return v___x_5702_;
}
}
}
}
v___jp_5705_:
{
lean_object* v___x_5708_; 
v___x_5708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5708_, 0, v_lhs_5706_);
lean_ctor_set(v___x_5708_, 1, v_rhs_5707_);
v_a_5689_ = v___x_5708_;
goto v___jp_5688_;
}
}
else
{
lean_object* v_a_5730_; lean_object* v___x_5732_; uint8_t v_isShared_5733_; uint8_t v_isSharedCheck_5737_; 
lean_dec_ref(v_bs_5673_);
lean_dec_ref(v_ctorVal_5670_);
v_a_5730_ = lean_ctor_get(v___x_5684_, 0);
v_isSharedCheck_5737_ = !lean_is_exclusive(v___x_5684_);
if (v_isSharedCheck_5737_ == 0)
{
v___x_5732_ = v___x_5684_;
v_isShared_5733_ = v_isSharedCheck_5737_;
goto v_resetjp_5731_;
}
else
{
lean_inc(v_a_5730_);
lean_dec(v___x_5684_);
v___x_5732_ = lean_box(0);
v_isShared_5733_ = v_isSharedCheck_5737_;
goto v_resetjp_5731_;
}
v_resetjp_5731_:
{
lean_object* v___x_5735_; 
if (v_isShared_5733_ == 0)
{
v___x_5735_ = v___x_5732_;
goto v_reusejp_5734_;
}
else
{
lean_object* v_reuseFailAlloc_5736_; 
v_reuseFailAlloc_5736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5736_, 0, v_a_5730_);
v___x_5735_ = v_reuseFailAlloc_5736_;
goto v_reusejp_5734_;
}
v_reusejp_5734_:
{
return v___x_5735_;
}
}
}
}
else
{
lean_object* v_a_5738_; lean_object* v___x_5740_; uint8_t v_isShared_5741_; uint8_t v_isSharedCheck_5745_; 
lean_dec_ref(v_bs_5673_);
lean_dec_ref(v_ctorVal_5670_);
v_a_5738_ = lean_ctor_get(v___x_5682_, 0);
v_isSharedCheck_5745_ = !lean_is_exclusive(v___x_5682_);
if (v_isSharedCheck_5745_ == 0)
{
v___x_5740_ = v___x_5682_;
v_isShared_5741_ = v_isSharedCheck_5745_;
goto v_resetjp_5739_;
}
else
{
lean_inc(v_a_5738_);
lean_dec(v___x_5682_);
v___x_5740_ = lean_box(0);
v_isShared_5741_ = v_isSharedCheck_5745_;
goto v_resetjp_5739_;
}
v_resetjp_5739_:
{
lean_object* v___x_5743_; 
if (v_isShared_5741_ == 0)
{
v___x_5743_ = v___x_5740_;
goto v_reusejp_5742_;
}
else
{
lean_object* v_reuseFailAlloc_5744_; 
v_reuseFailAlloc_5744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5744_, 0, v_a_5738_);
v___x_5743_ = v_reuseFailAlloc_5744_;
goto v_reusejp_5742_;
}
v_reusejp_5742_:
{
return v___x_5743_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___boxed(lean_object* v_ctorVal_5746_, lean_object* v_sz_5747_, lean_object* v_i_5748_, lean_object* v_bs_5749_, lean_object* v___y_5750_, lean_object* v___y_5751_, lean_object* v___y_5752_, lean_object* v___y_5753_, lean_object* v___y_5754_){
_start:
{
size_t v_sz_boxed_5755_; size_t v_i_boxed_5756_; lean_object* v_res_5757_; 
v_sz_boxed_5755_ = lean_unbox_usize(v_sz_5747_);
lean_dec(v_sz_5747_);
v_i_boxed_5756_ = lean_unbox_usize(v_i_5748_);
lean_dec(v_i_5748_);
v_res_5757_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(v_ctorVal_5746_, v_sz_boxed_5755_, v_i_boxed_5756_, v_bs_5749_, v___y_5750_, v___y_5751_, v___y_5752_, v___y_5753_);
lean_dec(v___y_5753_);
lean_dec_ref(v___y_5752_);
lean_dec(v___y_5751_);
lean_dec_ref(v___y_5750_);
return v_res_5757_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5759_; lean_object* v___x_5760_; 
v___x_5759_ = lean_unsigned_to_nat(0u);
v___x_5760_ = l_Lean_Level_ofNat(v___x_5759_);
return v___x_5760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0(lean_object* v_ctorVal_5761_, lean_object* v_us_5762_, lean_object* v_numIndices_5763_, lean_object* v_xs_5764_, lean_object* v_type_5765_, lean_object* v___y_5766_, lean_object* v___y_5767_, lean_object* v___y_5768_, lean_object* v___y_5769_){
_start:
{
lean_object* v_toConstantVal_5771_; lean_object* v_induct_5772_; lean_object* v_numParams_5773_; lean_object* v___x_5774_; lean_object* v_noConfusionName_5775_; lean_object* v___x_5776_; lean_object* v___x_5777_; lean_object* v___x_5778_; lean_object* v_noConfusion_5779_; lean_object* v_noConfusion_5780_; lean_object* v_lower_5782_; lean_object* v_upper_5783_; lean_object* v___x_5890_; lean_object* v___x_5891_; lean_object* v___x_5892_; lean_object* v___x_5893_; lean_object* v_n_5894_; uint8_t v___x_5895_; 
v_toConstantVal_5771_ = lean_ctor_get(v_ctorVal_5761_, 0);
v_induct_5772_ = lean_ctor_get(v_ctorVal_5761_, 1);
v_numParams_5773_ = lean_ctor_get(v_ctorVal_5761_, 3);
v___x_5774_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__0));
lean_inc(v_induct_5772_);
v_noConfusionName_5775_ = l_Lean_Name_str___override(v_induct_5772_, v___x_5774_);
v___x_5776_ = lean_unsigned_to_nat(0u);
v___x_5777_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1);
v___x_5778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5778_, 0, v___x_5777_);
lean_ctor_set(v___x_5778_, 1, v_us_5762_);
v_noConfusion_5779_ = l_Lean_mkConst(v_noConfusionName_5775_, v___x_5778_);
v_noConfusion_5780_ = l_Lean_Expr_app___override(v_noConfusion_5779_, v_type_5765_);
v___x_5890_ = lean_array_get_size(v_xs_5764_);
v___x_5891_ = lean_nat_sub(v___x_5890_, v_numParams_5773_);
v___x_5892_ = lean_nat_sub(v___x_5891_, v_numIndices_5763_);
lean_dec(v___x_5891_);
v___x_5893_ = lean_unsigned_to_nat(1u);
v_n_5894_ = lean_nat_sub(v___x_5892_, v___x_5893_);
lean_dec(v___x_5892_);
v___x_5895_ = lean_nat_dec_le(v_n_5894_, v___x_5776_);
if (v___x_5895_ == 0)
{
v_lower_5782_ = v_n_5894_;
v_upper_5783_ = v___x_5890_;
goto v___jp_5781_;
}
else
{
lean_dec(v_n_5894_);
v_lower_5782_ = v___x_5776_;
v_upper_5783_ = v___x_5890_;
goto v___jp_5781_;
}
v___jp_5781_:
{
lean_object* v___x_5784_; lean_object* v___x_5785_; lean_object* v_eqs_5786_; size_t v_sz_5787_; size_t v___x_5788_; lean_object* v___x_5789_; 
lean_inc_ref(v_xs_5764_);
v___x_5784_ = l_Array_toSubarray___redArg(v_xs_5764_, v_lower_5782_, v_upper_5783_);
v___x_5785_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v_eqs_5786_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(v___x_5784_, v___x_5785_);
v_sz_5787_ = lean_array_size(v_eqs_5786_);
v___x_5788_ = ((size_t)0ULL);
lean_inc_ref(v_eqs_5786_);
lean_inc_ref(v_ctorVal_5761_);
v___x_5789_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(v_ctorVal_5761_, v_sz_5787_, v___x_5788_, v_eqs_5786_, v___y_5766_, v___y_5767_, v___y_5768_, v___y_5769_);
if (lean_obj_tag(v___x_5789_) == 0)
{
lean_object* v_a_5790_; lean_object* v___x_5791_; lean_object* v_fst_5792_; lean_object* v_snd_5793_; lean_object* v___x_5794_; lean_object* v___x_5795_; lean_object* v___x_5796_; lean_object* v___x_5797_; 
v_a_5790_ = lean_ctor_get(v___x_5789_, 0);
lean_inc(v_a_5790_);
lean_dec_ref(v___x_5789_);
v___x_5791_ = l_Array_unzip___redArg(v_a_5790_);
lean_dec(v_a_5790_);
v_fst_5792_ = lean_ctor_get(v___x_5791_, 0);
lean_inc(v_fst_5792_);
v_snd_5793_ = lean_ctor_get(v___x_5791_, 1);
lean_inc(v_snd_5793_);
lean_dec_ref(v___x_5791_);
v___x_5794_ = l_Lean_mkAppN(v_noConfusion_5780_, v_fst_5792_);
lean_dec(v_fst_5792_);
v___x_5795_ = l_Lean_mkAppN(v___x_5794_, v_snd_5793_);
lean_dec(v_snd_5793_);
v___x_5796_ = l_Lean_mkAppN(v___x_5795_, v_eqs_5786_);
lean_dec_ref(v_eqs_5786_);
lean_inc(v___y_5769_);
lean_inc_ref(v___y_5768_);
lean_inc(v___y_5767_);
lean_inc_ref(v___y_5766_);
lean_inc_ref(v___x_5796_);
v___x_5797_ = lean_infer_type(v___x_5796_, v___y_5766_, v___y_5767_, v___y_5768_, v___y_5769_);
if (lean_obj_tag(v___x_5797_) == 0)
{
lean_object* v_a_5798_; lean_object* v___x_5799_; 
v_a_5798_ = lean_ctor_get(v___x_5797_, 0);
lean_inc(v_a_5798_);
lean_dec_ref(v___x_5797_);
lean_inc(v___y_5769_);
lean_inc_ref(v___y_5768_);
lean_inc(v___y_5767_);
lean_inc_ref(v___y_5766_);
v___x_5799_ = lean_whnf(v_a_5798_, v___y_5766_, v___y_5767_, v___y_5768_, v___y_5769_);
if (lean_obj_tag(v___x_5799_) == 0)
{
lean_object* v_a_5800_; 
v_a_5800_ = lean_ctor_get(v___x_5799_, 0);
lean_inc(v_a_5800_);
lean_dec_ref(v___x_5799_);
if (lean_obj_tag(v_a_5800_) == 7)
{
lean_object* v_binderType_5801_; lean_object* v___x_5802_; lean_object* v___x_5803_; 
lean_inc_ref(v_toConstantVal_5771_);
lean_dec_ref(v_ctorVal_5761_);
v_binderType_5801_ = lean_ctor_get(v_a_5800_, 1);
lean_inc_ref(v_binderType_5801_);
lean_dec_ref(v_a_5800_);
v___x_5802_ = lean_box(0);
v___x_5803_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_binderType_5801_, v___x_5802_, v___y_5766_, v___y_5767_, v___y_5768_, v___y_5769_);
if (lean_obj_tag(v___x_5803_) == 0)
{
lean_object* v_a_5804_; lean_object* v___x_5805_; lean_object* v___x_5806_; 
v_a_5804_ = lean_ctor_get(v___x_5803_, 0);
lean_inc(v_a_5804_);
lean_dec_ref(v___x_5803_);
v___x_5805_ = l_Lean_Expr_mvarId_x21(v_a_5804_);
v___x_5806_ = l_Lean_MVarId_intros(v___x_5805_, v___y_5766_, v___y_5767_, v___y_5768_, v___y_5769_);
if (lean_obj_tag(v___x_5806_) == 0)
{
lean_object* v_a_5807_; lean_object* v_snd_5808_; lean_object* v_name_5809_; lean_object* v___x_5810_; 
v_a_5807_ = lean_ctor_get(v___x_5806_, 0);
lean_inc(v_a_5807_);
lean_dec_ref(v___x_5806_);
v_snd_5808_ = lean_ctor_get(v_a_5807_, 1);
lean_inc(v_snd_5808_);
lean_dec(v_a_5807_);
v_name_5809_ = lean_ctor_get(v_toConstantVal_5771_, 0);
lean_inc(v_name_5809_);
lean_dec_ref(v_toConstantVal_5771_);
v___x_5810_ = l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(v_snd_5808_, v_name_5809_, v___y_5766_, v___y_5767_, v___y_5768_, v___y_5769_);
if (lean_obj_tag(v___x_5810_) == 0)
{
lean_object* v___x_5811_; lean_object* v___x_5812_; lean_object* v_a_5813_; lean_object* v___x_5815_; uint8_t v_isShared_5816_; uint8_t v_isSharedCheck_5840_; 
lean_dec_ref(v___x_5810_);
v___x_5811_ = l_Lean_Expr_app___override(v___x_5796_, v_a_5804_);
v___x_5812_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v___x_5811_, v___y_5767_);
v_a_5813_ = lean_ctor_get(v___x_5812_, 0);
v_isSharedCheck_5840_ = !lean_is_exclusive(v___x_5812_);
if (v_isSharedCheck_5840_ == 0)
{
v___x_5815_ = v___x_5812_;
v_isShared_5816_ = v_isSharedCheck_5840_;
goto v_resetjp_5814_;
}
else
{
lean_inc(v_a_5813_);
lean_dec(v___x_5812_);
v___x_5815_ = lean_box(0);
v_isShared_5816_ = v_isSharedCheck_5840_;
goto v_resetjp_5814_;
}
v_resetjp_5814_:
{
uint8_t v___x_5817_; uint8_t v___x_5818_; uint8_t v___x_5819_; lean_object* v___x_5820_; 
v___x_5817_ = 0;
v___x_5818_ = 1;
v___x_5819_ = 1;
v___x_5820_ = l_Lean_Meta_mkLambdaFVars(v_xs_5764_, v_a_5813_, v___x_5817_, v___x_5818_, v___x_5817_, v___x_5818_, v___x_5819_, v___y_5766_, v___y_5767_, v___y_5768_, v___y_5769_);
lean_dec_ref(v_xs_5764_);
if (lean_obj_tag(v___x_5820_) == 0)
{
lean_object* v_a_5821_; lean_object* v___x_5823_; uint8_t v_isShared_5824_; uint8_t v_isSharedCheck_5831_; 
v_a_5821_ = lean_ctor_get(v___x_5820_, 0);
v_isSharedCheck_5831_ = !lean_is_exclusive(v___x_5820_);
if (v_isSharedCheck_5831_ == 0)
{
v___x_5823_ = v___x_5820_;
v_isShared_5824_ = v_isSharedCheck_5831_;
goto v_resetjp_5822_;
}
else
{
lean_inc(v_a_5821_);
lean_dec(v___x_5820_);
v___x_5823_ = lean_box(0);
v_isShared_5824_ = v_isSharedCheck_5831_;
goto v_resetjp_5822_;
}
v_resetjp_5822_:
{
lean_object* v___x_5826_; 
if (v_isShared_5816_ == 0)
{
lean_ctor_set_tag(v___x_5815_, 1);
lean_ctor_set(v___x_5815_, 0, v_a_5821_);
v___x_5826_ = v___x_5815_;
goto v_reusejp_5825_;
}
else
{
lean_object* v_reuseFailAlloc_5830_; 
v_reuseFailAlloc_5830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5830_, 0, v_a_5821_);
v___x_5826_ = v_reuseFailAlloc_5830_;
goto v_reusejp_5825_;
}
v_reusejp_5825_:
{
lean_object* v___x_5828_; 
if (v_isShared_5824_ == 0)
{
lean_ctor_set(v___x_5823_, 0, v___x_5826_);
v___x_5828_ = v___x_5823_;
goto v_reusejp_5827_;
}
else
{
lean_object* v_reuseFailAlloc_5829_; 
v_reuseFailAlloc_5829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5829_, 0, v___x_5826_);
v___x_5828_ = v_reuseFailAlloc_5829_;
goto v_reusejp_5827_;
}
v_reusejp_5827_:
{
return v___x_5828_;
}
}
}
}
else
{
lean_object* v_a_5832_; lean_object* v___x_5834_; uint8_t v_isShared_5835_; uint8_t v_isSharedCheck_5839_; 
lean_del_object(v___x_5815_);
v_a_5832_ = lean_ctor_get(v___x_5820_, 0);
v_isSharedCheck_5839_ = !lean_is_exclusive(v___x_5820_);
if (v_isSharedCheck_5839_ == 0)
{
v___x_5834_ = v___x_5820_;
v_isShared_5835_ = v_isSharedCheck_5839_;
goto v_resetjp_5833_;
}
else
{
lean_inc(v_a_5832_);
lean_dec(v___x_5820_);
v___x_5834_ = lean_box(0);
v_isShared_5835_ = v_isSharedCheck_5839_;
goto v_resetjp_5833_;
}
v_resetjp_5833_:
{
lean_object* v___x_5837_; 
if (v_isShared_5835_ == 0)
{
v___x_5837_ = v___x_5834_;
goto v_reusejp_5836_;
}
else
{
lean_object* v_reuseFailAlloc_5838_; 
v_reuseFailAlloc_5838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5838_, 0, v_a_5832_);
v___x_5837_ = v_reuseFailAlloc_5838_;
goto v_reusejp_5836_;
}
v_reusejp_5836_:
{
return v___x_5837_;
}
}
}
}
}
else
{
lean_object* v_a_5841_; lean_object* v___x_5843_; uint8_t v_isShared_5844_; uint8_t v_isSharedCheck_5848_; 
lean_dec(v_a_5804_);
lean_dec_ref(v___x_5796_);
lean_dec_ref(v_xs_5764_);
v_a_5841_ = lean_ctor_get(v___x_5810_, 0);
v_isSharedCheck_5848_ = !lean_is_exclusive(v___x_5810_);
if (v_isSharedCheck_5848_ == 0)
{
v___x_5843_ = v___x_5810_;
v_isShared_5844_ = v_isSharedCheck_5848_;
goto v_resetjp_5842_;
}
else
{
lean_inc(v_a_5841_);
lean_dec(v___x_5810_);
v___x_5843_ = lean_box(0);
v_isShared_5844_ = v_isSharedCheck_5848_;
goto v_resetjp_5842_;
}
v_resetjp_5842_:
{
lean_object* v___x_5846_; 
if (v_isShared_5844_ == 0)
{
v___x_5846_ = v___x_5843_;
goto v_reusejp_5845_;
}
else
{
lean_object* v_reuseFailAlloc_5847_; 
v_reuseFailAlloc_5847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5847_, 0, v_a_5841_);
v___x_5846_ = v_reuseFailAlloc_5847_;
goto v_reusejp_5845_;
}
v_reusejp_5845_:
{
return v___x_5846_;
}
}
}
}
else
{
lean_object* v_a_5849_; lean_object* v___x_5851_; uint8_t v_isShared_5852_; uint8_t v_isSharedCheck_5856_; 
lean_dec(v_a_5804_);
lean_dec_ref(v___x_5796_);
lean_dec_ref(v_toConstantVal_5771_);
lean_dec_ref(v_xs_5764_);
v_a_5849_ = lean_ctor_get(v___x_5806_, 0);
v_isSharedCheck_5856_ = !lean_is_exclusive(v___x_5806_);
if (v_isSharedCheck_5856_ == 0)
{
v___x_5851_ = v___x_5806_;
v_isShared_5852_ = v_isSharedCheck_5856_;
goto v_resetjp_5850_;
}
else
{
lean_inc(v_a_5849_);
lean_dec(v___x_5806_);
v___x_5851_ = lean_box(0);
v_isShared_5852_ = v_isSharedCheck_5856_;
goto v_resetjp_5850_;
}
v_resetjp_5850_:
{
lean_object* v___x_5854_; 
if (v_isShared_5852_ == 0)
{
v___x_5854_ = v___x_5851_;
goto v_reusejp_5853_;
}
else
{
lean_object* v_reuseFailAlloc_5855_; 
v_reuseFailAlloc_5855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5855_, 0, v_a_5849_);
v___x_5854_ = v_reuseFailAlloc_5855_;
goto v_reusejp_5853_;
}
v_reusejp_5853_:
{
return v___x_5854_;
}
}
}
}
else
{
lean_object* v_a_5857_; lean_object* v___x_5859_; uint8_t v_isShared_5860_; uint8_t v_isSharedCheck_5864_; 
lean_dec_ref(v___x_5796_);
lean_dec_ref(v_toConstantVal_5771_);
lean_dec_ref(v_xs_5764_);
v_a_5857_ = lean_ctor_get(v___x_5803_, 0);
v_isSharedCheck_5864_ = !lean_is_exclusive(v___x_5803_);
if (v_isSharedCheck_5864_ == 0)
{
v___x_5859_ = v___x_5803_;
v_isShared_5860_ = v_isSharedCheck_5864_;
goto v_resetjp_5858_;
}
else
{
lean_inc(v_a_5857_);
lean_dec(v___x_5803_);
v___x_5859_ = lean_box(0);
v_isShared_5860_ = v_isSharedCheck_5864_;
goto v_resetjp_5858_;
}
v_resetjp_5858_:
{
lean_object* v___x_5862_; 
if (v_isShared_5860_ == 0)
{
v___x_5862_ = v___x_5859_;
goto v_reusejp_5861_;
}
else
{
lean_object* v_reuseFailAlloc_5863_; 
v_reuseFailAlloc_5863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5863_, 0, v_a_5857_);
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
lean_object* v___x_5865_; 
lean_dec(v_a_5800_);
lean_dec_ref(v___x_5796_);
lean_dec_ref(v_xs_5764_);
v___x_5865_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5761_, v___y_5766_, v___y_5767_, v___y_5768_, v___y_5769_);
return v___x_5865_;
}
}
else
{
lean_object* v_a_5866_; lean_object* v___x_5868_; uint8_t v_isShared_5869_; uint8_t v_isSharedCheck_5873_; 
lean_dec_ref(v___x_5796_);
lean_dec_ref(v_xs_5764_);
lean_dec_ref(v_ctorVal_5761_);
v_a_5866_ = lean_ctor_get(v___x_5799_, 0);
v_isSharedCheck_5873_ = !lean_is_exclusive(v___x_5799_);
if (v_isSharedCheck_5873_ == 0)
{
v___x_5868_ = v___x_5799_;
v_isShared_5869_ = v_isSharedCheck_5873_;
goto v_resetjp_5867_;
}
else
{
lean_inc(v_a_5866_);
lean_dec(v___x_5799_);
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
else
{
lean_object* v_a_5874_; lean_object* v___x_5876_; uint8_t v_isShared_5877_; uint8_t v_isSharedCheck_5881_; 
lean_dec_ref(v___x_5796_);
lean_dec_ref(v_xs_5764_);
lean_dec_ref(v_ctorVal_5761_);
v_a_5874_ = lean_ctor_get(v___x_5797_, 0);
v_isSharedCheck_5881_ = !lean_is_exclusive(v___x_5797_);
if (v_isSharedCheck_5881_ == 0)
{
v___x_5876_ = v___x_5797_;
v_isShared_5877_ = v_isSharedCheck_5881_;
goto v_resetjp_5875_;
}
else
{
lean_inc(v_a_5874_);
lean_dec(v___x_5797_);
v___x_5876_ = lean_box(0);
v_isShared_5877_ = v_isSharedCheck_5881_;
goto v_resetjp_5875_;
}
v_resetjp_5875_:
{
lean_object* v___x_5879_; 
if (v_isShared_5877_ == 0)
{
v___x_5879_ = v___x_5876_;
goto v_reusejp_5878_;
}
else
{
lean_object* v_reuseFailAlloc_5880_; 
v_reuseFailAlloc_5880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5880_, 0, v_a_5874_);
v___x_5879_ = v_reuseFailAlloc_5880_;
goto v_reusejp_5878_;
}
v_reusejp_5878_:
{
return v___x_5879_;
}
}
}
}
else
{
lean_object* v_a_5882_; lean_object* v___x_5884_; uint8_t v_isShared_5885_; uint8_t v_isSharedCheck_5889_; 
lean_dec_ref(v_eqs_5786_);
lean_dec_ref(v_noConfusion_5780_);
lean_dec_ref(v_xs_5764_);
lean_dec_ref(v_ctorVal_5761_);
v_a_5882_ = lean_ctor_get(v___x_5789_, 0);
v_isSharedCheck_5889_ = !lean_is_exclusive(v___x_5789_);
if (v_isSharedCheck_5889_ == 0)
{
v___x_5884_ = v___x_5789_;
v_isShared_5885_ = v_isSharedCheck_5889_;
goto v_resetjp_5883_;
}
else
{
lean_inc(v_a_5882_);
lean_dec(v___x_5789_);
v___x_5884_ = lean_box(0);
v_isShared_5885_ = v_isSharedCheck_5889_;
goto v_resetjp_5883_;
}
v_resetjp_5883_:
{
lean_object* v___x_5887_; 
if (v_isShared_5885_ == 0)
{
v___x_5887_ = v___x_5884_;
goto v_reusejp_5886_;
}
else
{
lean_object* v_reuseFailAlloc_5888_; 
v_reuseFailAlloc_5888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5888_, 0, v_a_5882_);
v___x_5887_ = v_reuseFailAlloc_5888_;
goto v_reusejp_5886_;
}
v_reusejp_5886_:
{
return v___x_5887_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___boxed(lean_object* v_ctorVal_5896_, lean_object* v_us_5897_, lean_object* v_numIndices_5898_, lean_object* v_xs_5899_, lean_object* v_type_5900_, lean_object* v___y_5901_, lean_object* v___y_5902_, lean_object* v___y_5903_, lean_object* v___y_5904_, lean_object* v___y_5905_){
_start:
{
lean_object* v_res_5906_; 
v_res_5906_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0(v_ctorVal_5896_, v_us_5897_, v_numIndices_5898_, v_xs_5899_, v_type_5900_, v___y_5901_, v___y_5902_, v___y_5903_, v___y_5904_);
lean_dec(v___y_5904_);
lean_dec_ref(v___y_5903_);
lean_dec(v___y_5902_);
lean_dec_ref(v___y_5901_);
lean_dec(v_numIndices_5898_);
return v_res_5906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(lean_object* v_ctorVal_5907_, lean_object* v_typeInfo_5908_, lean_object* v_a_5909_, lean_object* v_a_5910_, lean_object* v_a_5911_, lean_object* v_a_5912_){
_start:
{
lean_object* v_thmType_5914_; lean_object* v_us_5915_; lean_object* v_numIndices_5916_; lean_object* v___f_5917_; uint8_t v___x_5918_; lean_object* v___x_5919_; 
v_thmType_5914_ = lean_ctor_get(v_typeInfo_5908_, 0);
lean_inc_ref(v_thmType_5914_);
v_us_5915_ = lean_ctor_get(v_typeInfo_5908_, 1);
lean_inc(v_us_5915_);
v_numIndices_5916_ = lean_ctor_get(v_typeInfo_5908_, 2);
lean_inc(v_numIndices_5916_);
lean_dec_ref(v_typeInfo_5908_);
v___f_5917_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___boxed), 10, 3);
lean_closure_set(v___f_5917_, 0, v_ctorVal_5907_);
lean_closure_set(v___f_5917_, 1, v_us_5915_);
lean_closure_set(v___f_5917_, 2, v_numIndices_5916_);
v___x_5918_ = 0;
v___x_5919_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_thmType_5914_, v___f_5917_, v___x_5918_, v___x_5918_, v_a_5909_, v_a_5910_, v_a_5911_, v_a_5912_);
return v___x_5919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___boxed(lean_object* v_ctorVal_5920_, lean_object* v_typeInfo_5921_, lean_object* v_a_5922_, lean_object* v_a_5923_, lean_object* v_a_5924_, lean_object* v_a_5925_, lean_object* v_a_5926_){
_start:
{
lean_object* v_res_5927_; 
v_res_5927_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(v_ctorVal_5920_, v_typeInfo_5921_, v_a_5922_, v_a_5923_, v_a_5924_, v_a_5925_);
lean_dec(v_a_5925_);
lean_dec_ref(v_a_5924_);
lean_dec(v_a_5923_);
lean_dec_ref(v_a_5922_);
return v_res_5927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHInjectiveTheoremNameFor(lean_object* v_ctorName_5930_){
_start:
{
lean_object* v___x_5931_; lean_object* v___x_5932_; 
v___x_5931_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0));
v___x_5932_ = l_Lean_Name_str___override(v_ctorName_5930_, v___x_5931_);
return v___x_5932_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(lean_object* v_thmName_5933_, lean_object* v_ctorVal_5934_, lean_object* v_a_5935_, lean_object* v_a_5936_, lean_object* v_a_5937_, lean_object* v_a_5938_){
_start:
{
lean_object* v___x_5940_; 
lean_inc_ref(v_ctorVal_5934_);
v___x_5940_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(v_ctorVal_5934_, v_a_5935_, v_a_5936_, v_a_5937_, v_a_5938_);
if (lean_obj_tag(v___x_5940_) == 0)
{
lean_object* v_a_5941_; lean_object* v___x_5943_; uint8_t v_isShared_5944_; uint8_t v_isSharedCheck_6002_; 
v_a_5941_ = lean_ctor_get(v___x_5940_, 0);
v_isSharedCheck_6002_ = !lean_is_exclusive(v___x_5940_);
if (v_isSharedCheck_6002_ == 0)
{
v___x_5943_ = v___x_5940_;
v_isShared_5944_ = v_isSharedCheck_6002_;
goto v_resetjp_5942_;
}
else
{
lean_inc(v_a_5941_);
lean_dec(v___x_5940_);
v___x_5943_ = lean_box(0);
v_isShared_5944_ = v_isSharedCheck_6002_;
goto v_resetjp_5942_;
}
v_resetjp_5942_:
{
if (lean_obj_tag(v_a_5941_) == 1)
{
lean_object* v_val_5945_; lean_object* v___x_5946_; 
lean_del_object(v___x_5943_);
v_val_5945_ = lean_ctor_get(v_a_5941_, 0);
lean_inc_n(v_val_5945_, 2);
lean_dec_ref(v_a_5941_);
lean_inc_ref(v_ctorVal_5934_);
v___x_5946_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(v_ctorVal_5934_, v_val_5945_, v_a_5935_, v_a_5936_, v_a_5937_, v_a_5938_);
if (lean_obj_tag(v___x_5946_) == 0)
{
lean_object* v_a_5947_; lean_object* v___x_5949_; uint8_t v_isShared_5950_; uint8_t v_isSharedCheck_5989_; 
v_a_5947_ = lean_ctor_get(v___x_5946_, 0);
v_isSharedCheck_5989_ = !lean_is_exclusive(v___x_5946_);
if (v_isSharedCheck_5989_ == 0)
{
v___x_5949_ = v___x_5946_;
v_isShared_5950_ = v_isSharedCheck_5989_;
goto v_resetjp_5948_;
}
else
{
lean_inc(v_a_5947_);
lean_dec(v___x_5946_);
v___x_5949_ = lean_box(0);
v_isShared_5950_ = v_isSharedCheck_5989_;
goto v_resetjp_5948_;
}
v_resetjp_5948_:
{
if (lean_obj_tag(v_a_5947_) == 1)
{
lean_object* v_toConstantVal_5951_; lean_object* v_val_5952_; lean_object* v___x_5954_; uint8_t v_isShared_5955_; uint8_t v_isSharedCheck_5984_; 
v_toConstantVal_5951_ = lean_ctor_get(v_ctorVal_5934_, 0);
lean_inc_ref(v_toConstantVal_5951_);
lean_dec_ref(v_ctorVal_5934_);
v_val_5952_ = lean_ctor_get(v_a_5947_, 0);
v_isSharedCheck_5984_ = !lean_is_exclusive(v_a_5947_);
if (v_isSharedCheck_5984_ == 0)
{
v___x_5954_ = v_a_5947_;
v_isShared_5955_ = v_isSharedCheck_5984_;
goto v_resetjp_5953_;
}
else
{
lean_inc(v_val_5952_);
lean_dec(v_a_5947_);
v___x_5954_ = lean_box(0);
v_isShared_5955_ = v_isSharedCheck_5984_;
goto v_resetjp_5953_;
}
v_resetjp_5953_:
{
lean_object* v_levelParams_5956_; lean_object* v___x_5958_; uint8_t v_isShared_5959_; uint8_t v_isSharedCheck_5981_; 
v_levelParams_5956_ = lean_ctor_get(v_toConstantVal_5951_, 1);
v_isSharedCheck_5981_ = !lean_is_exclusive(v_toConstantVal_5951_);
if (v_isSharedCheck_5981_ == 0)
{
lean_object* v_unused_5982_; lean_object* v_unused_5983_; 
v_unused_5982_ = lean_ctor_get(v_toConstantVal_5951_, 2);
lean_dec(v_unused_5982_);
v_unused_5983_ = lean_ctor_get(v_toConstantVal_5951_, 0);
lean_dec(v_unused_5983_);
v___x_5958_ = v_toConstantVal_5951_;
v_isShared_5959_ = v_isSharedCheck_5981_;
goto v_resetjp_5957_;
}
else
{
lean_inc(v_levelParams_5956_);
lean_dec(v_toConstantVal_5951_);
v___x_5958_ = lean_box(0);
v_isShared_5959_ = v_isSharedCheck_5981_;
goto v_resetjp_5957_;
}
v_resetjp_5957_:
{
lean_object* v_thmType_5960_; lean_object* v___x_5962_; uint8_t v_isShared_5963_; uint8_t v_isSharedCheck_5978_; 
v_thmType_5960_ = lean_ctor_get(v_val_5945_, 0);
v_isSharedCheck_5978_ = !lean_is_exclusive(v_val_5945_);
if (v_isSharedCheck_5978_ == 0)
{
lean_object* v_unused_5979_; lean_object* v_unused_5980_; 
v_unused_5979_ = lean_ctor_get(v_val_5945_, 2);
lean_dec(v_unused_5979_);
v_unused_5980_ = lean_ctor_get(v_val_5945_, 1);
lean_dec(v_unused_5980_);
v___x_5962_ = v_val_5945_;
v_isShared_5963_ = v_isSharedCheck_5978_;
goto v_resetjp_5961_;
}
else
{
lean_inc(v_thmType_5960_);
lean_dec(v_val_5945_);
v___x_5962_ = lean_box(0);
v_isShared_5963_ = v_isSharedCheck_5978_;
goto v_resetjp_5961_;
}
v_resetjp_5961_:
{
lean_object* v___x_5965_; 
lean_inc(v_thmName_5933_);
if (v_isShared_5959_ == 0)
{
lean_ctor_set(v___x_5958_, 2, v_thmType_5960_);
lean_ctor_set(v___x_5958_, 0, v_thmName_5933_);
v___x_5965_ = v___x_5958_;
goto v_reusejp_5964_;
}
else
{
lean_object* v_reuseFailAlloc_5977_; 
v_reuseFailAlloc_5977_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5977_, 0, v_thmName_5933_);
lean_ctor_set(v_reuseFailAlloc_5977_, 1, v_levelParams_5956_);
lean_ctor_set(v_reuseFailAlloc_5977_, 2, v_thmType_5960_);
v___x_5965_ = v_reuseFailAlloc_5977_;
goto v_reusejp_5964_;
}
v_reusejp_5964_:
{
lean_object* v___x_5966_; lean_object* v___x_5967_; lean_object* v___x_5969_; 
v___x_5966_ = lean_box(0);
v___x_5967_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5967_, 0, v_thmName_5933_);
lean_ctor_set(v___x_5967_, 1, v___x_5966_);
if (v_isShared_5963_ == 0)
{
lean_ctor_set(v___x_5962_, 2, v___x_5967_);
lean_ctor_set(v___x_5962_, 1, v_val_5952_);
lean_ctor_set(v___x_5962_, 0, v___x_5965_);
v___x_5969_ = v___x_5962_;
goto v_reusejp_5968_;
}
else
{
lean_object* v_reuseFailAlloc_5976_; 
v_reuseFailAlloc_5976_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5976_, 0, v___x_5965_);
lean_ctor_set(v_reuseFailAlloc_5976_, 1, v_val_5952_);
lean_ctor_set(v_reuseFailAlloc_5976_, 2, v___x_5967_);
v___x_5969_ = v_reuseFailAlloc_5976_;
goto v_reusejp_5968_;
}
v_reusejp_5968_:
{
lean_object* v___x_5971_; 
if (v_isShared_5955_ == 0)
{
lean_ctor_set(v___x_5954_, 0, v___x_5969_);
v___x_5971_ = v___x_5954_;
goto v_reusejp_5970_;
}
else
{
lean_object* v_reuseFailAlloc_5975_; 
v_reuseFailAlloc_5975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5975_, 0, v___x_5969_);
v___x_5971_ = v_reuseFailAlloc_5975_;
goto v_reusejp_5970_;
}
v_reusejp_5970_:
{
lean_object* v___x_5973_; 
if (v_isShared_5950_ == 0)
{
lean_ctor_set(v___x_5949_, 0, v___x_5971_);
v___x_5973_ = v___x_5949_;
goto v_reusejp_5972_;
}
else
{
lean_object* v_reuseFailAlloc_5974_; 
v_reuseFailAlloc_5974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5974_, 0, v___x_5971_);
v___x_5973_ = v_reuseFailAlloc_5974_;
goto v_reusejp_5972_;
}
v_reusejp_5972_:
{
return v___x_5973_;
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
lean_object* v___x_5985_; lean_object* v___x_5987_; 
lean_dec(v_a_5947_);
lean_dec(v_val_5945_);
lean_dec_ref(v_ctorVal_5934_);
lean_dec(v_thmName_5933_);
v___x_5985_ = lean_box(0);
if (v_isShared_5950_ == 0)
{
lean_ctor_set(v___x_5949_, 0, v___x_5985_);
v___x_5987_ = v___x_5949_;
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
else
{
lean_object* v_a_5990_; lean_object* v___x_5992_; uint8_t v_isShared_5993_; uint8_t v_isSharedCheck_5997_; 
lean_dec(v_val_5945_);
lean_dec_ref(v_ctorVal_5934_);
lean_dec(v_thmName_5933_);
v_a_5990_ = lean_ctor_get(v___x_5946_, 0);
v_isSharedCheck_5997_ = !lean_is_exclusive(v___x_5946_);
if (v_isSharedCheck_5997_ == 0)
{
v___x_5992_ = v___x_5946_;
v_isShared_5993_ = v_isSharedCheck_5997_;
goto v_resetjp_5991_;
}
else
{
lean_inc(v_a_5990_);
lean_dec(v___x_5946_);
v___x_5992_ = lean_box(0);
v_isShared_5993_ = v_isSharedCheck_5997_;
goto v_resetjp_5991_;
}
v_resetjp_5991_:
{
lean_object* v___x_5995_; 
if (v_isShared_5993_ == 0)
{
v___x_5995_ = v___x_5992_;
goto v_reusejp_5994_;
}
else
{
lean_object* v_reuseFailAlloc_5996_; 
v_reuseFailAlloc_5996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5996_, 0, v_a_5990_);
v___x_5995_ = v_reuseFailAlloc_5996_;
goto v_reusejp_5994_;
}
v_reusejp_5994_:
{
return v___x_5995_;
}
}
}
}
else
{
lean_object* v___x_5998_; lean_object* v___x_6000_; 
lean_dec(v_a_5941_);
lean_dec_ref(v_ctorVal_5934_);
lean_dec(v_thmName_5933_);
v___x_5998_ = lean_box(0);
if (v_isShared_5944_ == 0)
{
lean_ctor_set(v___x_5943_, 0, v___x_5998_);
v___x_6000_ = v___x_5943_;
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
lean_dec_ref(v_ctorVal_5934_);
lean_dec(v_thmName_5933_);
v_a_6003_ = lean_ctor_get(v___x_5940_, 0);
v_isSharedCheck_6010_ = !lean_is_exclusive(v___x_5940_);
if (v_isSharedCheck_6010_ == 0)
{
v___x_6005_ = v___x_5940_;
v_isShared_6006_ = v_isSharedCheck_6010_;
goto v_resetjp_6004_;
}
else
{
lean_inc(v_a_6003_);
lean_dec(v___x_5940_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f___boxed(lean_object* v_thmName_6011_, lean_object* v_ctorVal_6012_, lean_object* v_a_6013_, lean_object* v_a_6014_, lean_object* v_a_6015_, lean_object* v_a_6016_, lean_object* v_a_6017_){
_start:
{
lean_object* v_res_6018_; 
v_res_6018_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(v_thmName_6011_, v_ctorVal_6012_, v_a_6013_, v_a_6014_, v_a_6015_, v_a_6016_);
lean_dec(v_a_6016_);
lean_dec_ref(v_a_6015_);
lean_dec(v_a_6014_);
lean_dec_ref(v_a_6013_);
return v_res_6018_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(lean_object* v_env_6019_, lean_object* v_n_6020_){
_start:
{
if (lean_obj_tag(v_n_6020_) == 1)
{
lean_object* v_pre_6021_; lean_object* v_str_6022_; lean_object* v___x_6023_; uint8_t v___x_6024_; 
v_pre_6021_ = lean_ctor_get(v_n_6020_, 0);
lean_inc(v_pre_6021_);
v_str_6022_ = lean_ctor_get(v_n_6020_, 1);
lean_inc_ref(v_str_6022_);
lean_dec_ref(v_n_6020_);
v___x_6023_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0));
v___x_6024_ = lean_string_dec_eq(v_str_6022_, v___x_6023_);
lean_dec_ref(v_str_6022_);
if (v___x_6024_ == 0)
{
lean_dec(v_pre_6021_);
lean_dec_ref(v_env_6019_);
return v___x_6024_;
}
else
{
uint8_t v___x_6025_; lean_object* v___x_6026_; 
v___x_6025_ = 0;
v___x_6026_ = l_Lean_Environment_find_x3f(v_env_6019_, v_pre_6021_, v___x_6025_);
if (lean_obj_tag(v___x_6026_) == 1)
{
lean_object* v_val_6027_; 
v_val_6027_ = lean_ctor_get(v___x_6026_, 0);
lean_inc(v_val_6027_);
lean_dec_ref(v___x_6026_);
if (lean_obj_tag(v_val_6027_) == 6)
{
lean_dec_ref(v_val_6027_);
return v___x_6024_;
}
else
{
lean_dec(v_val_6027_);
return v___x_6025_;
}
}
else
{
lean_dec(v___x_6026_);
return v___x_6025_;
}
}
}
else
{
uint8_t v___x_6028_; 
lean_dec(v_n_6020_);
lean_dec_ref(v_env_6019_);
v___x_6028_ = 0;
return v___x_6028_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2____boxed(lean_object* v_env_6029_, lean_object* v_n_6030_){
_start:
{
uint8_t v_res_6031_; lean_object* v_r_6032_; 
v_res_6031_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(v_env_6029_, v_n_6030_);
v_r_6032_ = lean_box(v_res_6031_);
return v_r_6032_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_6035_; lean_object* v___x_6036_; 
v___f_6035_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_));
v___x_6036_ = l_Lean_registerReservedNamePredicate(v___f_6035_);
return v___x_6036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2____boxed(lean_object* v_a_6037_){
_start:
{
lean_object* v_res_6038_; 
v_res_6038_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_();
return v_res_6038_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(lean_object* v_thm_6039_, lean_object* v___y_6040_){
_start:
{
lean_object* v___x_6042_; lean_object* v_env_6043_; lean_object* v_toConstantVal_6044_; lean_object* v_value_6045_; lean_object* v_all_6046_; uint8_t v___y_6048_; lean_object* v_type_6056_; uint8_t v___x_6057_; 
v___x_6042_ = lean_st_ref_get(v___y_6040_);
v_env_6043_ = lean_ctor_get(v___x_6042_, 0);
lean_inc_ref_n(v_env_6043_, 2);
lean_dec(v___x_6042_);
v_toConstantVal_6044_ = lean_ctor_get(v_thm_6039_, 0);
v_value_6045_ = lean_ctor_get(v_thm_6039_, 1);
v_all_6046_ = lean_ctor_get(v_thm_6039_, 2);
v_type_6056_ = lean_ctor_get(v_toConstantVal_6044_, 2);
v___x_6057_ = l_Lean_Environment_hasUnsafe(v_env_6043_, v_type_6056_);
if (v___x_6057_ == 0)
{
uint8_t v___x_6058_; 
v___x_6058_ = l_Lean_Environment_hasUnsafe(v_env_6043_, v_value_6045_);
v___y_6048_ = v___x_6058_;
goto v___jp_6047_;
}
else
{
lean_dec_ref(v_env_6043_);
v___y_6048_ = v___x_6057_;
goto v___jp_6047_;
}
v___jp_6047_:
{
if (v___y_6048_ == 0)
{
lean_object* v___x_6049_; lean_object* v___x_6050_; 
v___x_6049_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_6049_, 0, v_thm_6039_);
v___x_6050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6050_, 0, v___x_6049_);
return v___x_6050_;
}
else
{
lean_object* v___x_6051_; uint8_t v___x_6052_; lean_object* v___x_6053_; lean_object* v___x_6054_; lean_object* v___x_6055_; 
lean_inc(v_all_6046_);
lean_inc_ref(v_value_6045_);
lean_inc_ref(v_toConstantVal_6044_);
lean_dec_ref(v_thm_6039_);
v___x_6051_ = lean_box(0);
v___x_6052_ = 0;
v___x_6053_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_6053_, 0, v_toConstantVal_6044_);
lean_ctor_set(v___x_6053_, 1, v_value_6045_);
lean_ctor_set(v___x_6053_, 2, v___x_6051_);
lean_ctor_set(v___x_6053_, 3, v_all_6046_);
lean_ctor_set_uint8(v___x_6053_, sizeof(void*)*4, v___x_6052_);
v___x_6054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6054_, 0, v___x_6053_);
v___x_6055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6055_, 0, v___x_6054_);
return v___x_6055_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_thm_6059_, lean_object* v___y_6060_, lean_object* v___y_6061_){
_start:
{
lean_object* v_res_6062_; 
v_res_6062_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(v_thm_6059_, v___y_6060_);
lean_dec(v___y_6060_);
return v_res_6062_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0(lean_object* v_thm_6063_, lean_object* v___y_6064_, lean_object* v___y_6065_, lean_object* v___y_6066_, lean_object* v___y_6067_){
_start:
{
lean_object* v___x_6069_; 
v___x_6069_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(v_thm_6063_, v___y_6067_);
return v___x_6069_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___boxed(lean_object* v_thm_6070_, lean_object* v___y_6071_, lean_object* v___y_6072_, lean_object* v___y_6073_, lean_object* v___y_6074_, lean_object* v___y_6075_){
_start:
{
lean_object* v_res_6076_; 
v_res_6076_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0(v_thm_6070_, v___y_6071_, v___y_6072_, v___y_6073_, v___y_6074_);
lean_dec(v___y_6074_);
lean_dec_ref(v___y_6073_);
lean_dec(v___y_6072_);
lean_dec_ref(v___y_6071_);
return v_res_6076_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(lean_object* v_val_6077_, uint8_t v___x_6078_, lean_object* v___y_6079_, lean_object* v___y_6080_, lean_object* v___y_6081_, lean_object* v___y_6082_){
_start:
{
lean_object* v___x_6084_; lean_object* v_a_6085_; lean_object* v___x_6086_; 
v___x_6084_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(v_val_6077_, v___y_6082_);
v_a_6085_ = lean_ctor_get(v___x_6084_, 0);
lean_inc(v_a_6085_);
lean_dec_ref(v___x_6084_);
v___x_6086_ = l_Lean_addDecl(v_a_6085_, v___x_6078_, v___y_6081_, v___y_6082_);
return v___x_6086_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object* v_val_6087_, lean_object* v___x_6088_, lean_object* v___y_6089_, lean_object* v___y_6090_, lean_object* v___y_6091_, lean_object* v___y_6092_, lean_object* v___y_6093_){
_start:
{
uint8_t v___x_2122__boxed_6094_; lean_object* v_res_6095_; 
v___x_2122__boxed_6094_ = lean_unbox(v___x_6088_);
v_res_6095_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(v_val_6087_, v___x_2122__boxed_6094_, v___y_6089_, v___y_6090_, v___y_6091_, v___y_6092_);
lean_dec(v___y_6092_);
lean_dec_ref(v___y_6091_);
lean_dec(v___y_6090_);
lean_dec_ref(v___y_6089_);
return v_res_6095_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6098_; lean_object* v___x_6099_; lean_object* v___x_6100_; 
v___x_6098_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_6099_ = lean_unsigned_to_nat(0u);
v___x_6100_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_6100_, 0, v___x_6099_);
lean_ctor_set(v___x_6100_, 1, v___x_6099_);
lean_ctor_set(v___x_6100_, 2, v___x_6099_);
lean_ctor_set(v___x_6100_, 3, v___x_6099_);
lean_ctor_set(v___x_6100_, 4, v___x_6098_);
lean_ctor_set(v___x_6100_, 5, v___x_6098_);
lean_ctor_set(v___x_6100_, 6, v___x_6098_);
lean_ctor_set(v___x_6100_, 7, v___x_6098_);
lean_ctor_set(v___x_6100_, 8, v___x_6098_);
lean_ctor_set(v___x_6100_, 9, v___x_6098_);
return v___x_6100_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6101_; lean_object* v___x_6102_; 
v___x_6101_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_6102_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6102_, 0, v___x_6101_);
lean_ctor_set(v___x_6102_, 1, v___x_6101_);
lean_ctor_set(v___x_6102_, 2, v___x_6101_);
lean_ctor_set(v___x_6102_, 3, v___x_6101_);
lean_ctor_set(v___x_6102_, 4, v___x_6101_);
lean_ctor_set(v___x_6102_, 5, v___x_6101_);
return v___x_6102_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6103_; lean_object* v___x_6104_; 
v___x_6103_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_6104_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6104_, 0, v___x_6103_);
lean_ctor_set(v___x_6104_, 1, v___x_6103_);
lean_ctor_set(v___x_6104_, 2, v___x_6103_);
lean_ctor_set(v___x_6104_, 3, v___x_6103_);
lean_ctor_set(v___x_6104_, 4, v___x_6103_);
return v___x_6104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(lean_object* v___x_6105_, lean_object* v_name_6106_, lean_object* v___y_6107_, lean_object* v___y_6108_){
_start:
{
if (lean_obj_tag(v_name_6106_) == 1)
{
lean_object* v_pre_6118_; lean_object* v_str_6119_; lean_object* v___x_6120_; uint8_t v___x_6121_; 
v_pre_6118_ = lean_ctor_get(v_name_6106_, 0);
lean_inc(v_pre_6118_);
v_str_6119_ = lean_ctor_get(v_name_6106_, 1);
v___x_6120_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0));
v___x_6121_ = lean_string_dec_eq(v_str_6119_, v___x_6120_);
if (v___x_6121_ == 0)
{
lean_dec(v_pre_6118_);
lean_dec_ref(v_name_6106_);
lean_dec(v___x_6105_);
goto v___jp_6114_;
}
else
{
lean_object* v___x_6122_; lean_object* v_env_6123_; uint8_t v___x_6124_; lean_object* v___x_6125_; 
v___x_6122_ = lean_st_ref_get(v___y_6108_);
v_env_6123_ = lean_ctor_get(v___x_6122_, 0);
lean_inc_ref(v_env_6123_);
lean_dec(v___x_6122_);
v___x_6124_ = 0;
lean_inc(v_pre_6118_);
v___x_6125_ = l_Lean_Environment_find_x3f(v_env_6123_, v_pre_6118_, v___x_6124_);
if (lean_obj_tag(v___x_6125_) == 1)
{
lean_object* v_val_6126_; 
v_val_6126_ = lean_ctor_get(v___x_6125_, 0);
lean_inc(v_val_6126_);
lean_dec_ref(v___x_6125_);
if (lean_obj_tag(v_val_6126_) == 6)
{
lean_object* v_val_6127_; lean_object* v___x_6129_; uint8_t v_isShared_6130_; uint8_t v_isSharedCheck_6177_; 
v_val_6127_ = lean_ctor_get(v_val_6126_, 0);
v_isSharedCheck_6177_ = !lean_is_exclusive(v_val_6126_);
if (v_isSharedCheck_6177_ == 0)
{
v___x_6129_ = v_val_6126_;
v_isShared_6130_ = v_isSharedCheck_6177_;
goto v_resetjp_6128_;
}
else
{
lean_inc(v_val_6127_);
lean_dec(v_val_6126_);
v___x_6129_ = lean_box(0);
v_isShared_6130_ = v_isSharedCheck_6177_;
goto v_resetjp_6128_;
}
v_resetjp_6128_:
{
uint8_t v___x_6131_; uint8_t v___x_6132_; uint8_t v___x_6133_; lean_object* v___x_6134_; uint64_t v___x_6135_; lean_object* v___x_6136_; lean_object* v___x_6137_; lean_object* v___x_6138_; lean_object* v___x_6139_; lean_object* v___x_6140_; lean_object* v___x_6141_; lean_object* v___x_6142_; lean_object* v___x_6143_; lean_object* v___x_6144_; lean_object* v___x_6145_; lean_object* v___x_6146_; lean_object* v___x_6147_; uint8_t v_a_6149_; lean_object* v___x_6155_; 
v___x_6131_ = 1;
v___x_6132_ = 0;
v___x_6133_ = 2;
v___x_6134_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_6134_, 0, v___x_6124_);
lean_ctor_set_uint8(v___x_6134_, 1, v___x_6124_);
lean_ctor_set_uint8(v___x_6134_, 2, v___x_6124_);
lean_ctor_set_uint8(v___x_6134_, 3, v___x_6124_);
lean_ctor_set_uint8(v___x_6134_, 4, v___x_6124_);
lean_ctor_set_uint8(v___x_6134_, 5, v___x_6121_);
lean_ctor_set_uint8(v___x_6134_, 6, v___x_6121_);
lean_ctor_set_uint8(v___x_6134_, 7, v___x_6124_);
lean_ctor_set_uint8(v___x_6134_, 8, v___x_6121_);
lean_ctor_set_uint8(v___x_6134_, 9, v___x_6131_);
lean_ctor_set_uint8(v___x_6134_, 10, v___x_6132_);
lean_ctor_set_uint8(v___x_6134_, 11, v___x_6121_);
lean_ctor_set_uint8(v___x_6134_, 12, v___x_6121_);
lean_ctor_set_uint8(v___x_6134_, 13, v___x_6121_);
lean_ctor_set_uint8(v___x_6134_, 14, v___x_6133_);
lean_ctor_set_uint8(v___x_6134_, 15, v___x_6121_);
lean_ctor_set_uint8(v___x_6134_, 16, v___x_6121_);
lean_ctor_set_uint8(v___x_6134_, 17, v___x_6121_);
lean_ctor_set_uint8(v___x_6134_, 18, v___x_6121_);
v___x_6135_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_6134_);
v___x_6136_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_6136_, 0, v___x_6134_);
lean_ctor_set_uint64(v___x_6136_, sizeof(void*)*1, v___x_6135_);
v___x_6137_ = lean_unsigned_to_nat(0u);
v___x_6138_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_6139_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_6140_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_));
v___x_6141_ = lean_box(0);
lean_inc(v___x_6105_);
v___x_6142_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_6142_, 0, v___x_6136_);
lean_ctor_set(v___x_6142_, 1, v___x_6105_);
lean_ctor_set(v___x_6142_, 2, v___x_6139_);
lean_ctor_set(v___x_6142_, 3, v___x_6140_);
lean_ctor_set(v___x_6142_, 4, v___x_6141_);
lean_ctor_set(v___x_6142_, 5, v___x_6137_);
lean_ctor_set(v___x_6142_, 6, v___x_6141_);
lean_ctor_set_uint8(v___x_6142_, sizeof(void*)*7, v___x_6124_);
lean_ctor_set_uint8(v___x_6142_, sizeof(void*)*7 + 1, v___x_6124_);
lean_ctor_set_uint8(v___x_6142_, sizeof(void*)*7 + 2, v___x_6124_);
lean_ctor_set_uint8(v___x_6142_, sizeof(void*)*7 + 3, v___x_6121_);
v___x_6143_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6144_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6145_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6146_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6146_, 0, v___x_6143_);
lean_ctor_set(v___x_6146_, 1, v___x_6144_);
lean_ctor_set(v___x_6146_, 2, v___x_6105_);
lean_ctor_set(v___x_6146_, 3, v___x_6138_);
lean_ctor_set(v___x_6146_, 4, v___x_6145_);
v___x_6147_ = lean_st_mk_ref(v___x_6146_);
lean_inc_ref(v_name_6106_);
v___x_6155_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(v_name_6106_, v_val_6127_, v___x_6142_, v___x_6147_, v___y_6107_, v___y_6108_);
if (lean_obj_tag(v___x_6155_) == 0)
{
lean_object* v_a_6156_; 
v_a_6156_ = lean_ctor_get(v___x_6155_, 0);
lean_inc(v_a_6156_);
lean_dec_ref(v___x_6155_);
if (lean_obj_tag(v_a_6156_) == 1)
{
lean_object* v_val_6157_; lean_object* v___x_6158_; lean_object* v___f_6159_; lean_object* v___x_6160_; 
v_val_6157_ = lean_ctor_get(v_a_6156_, 0);
lean_inc(v_val_6157_);
lean_dec_ref(v_a_6156_);
v___x_6158_ = lean_box(v___x_6124_);
v___f_6159_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed), 7, 2);
lean_closure_set(v___f_6159_, 0, v_val_6157_);
lean_closure_set(v___f_6159_, 1, v___x_6158_);
v___x_6160_ = l_Lean_Meta_realizeConst(v_pre_6118_, v_name_6106_, v___f_6159_, v___x_6142_, v___x_6147_, v___y_6107_, v___y_6108_);
lean_dec_ref(v___x_6142_);
if (lean_obj_tag(v___x_6160_) == 0)
{
lean_dec_ref(v___x_6160_);
v_a_6149_ = v___x_6121_;
goto v___jp_6148_;
}
else
{
lean_object* v_a_6161_; lean_object* v___x_6163_; uint8_t v_isShared_6164_; uint8_t v_isSharedCheck_6168_; 
lean_dec(v___x_6147_);
lean_del_object(v___x_6129_);
v_a_6161_ = lean_ctor_get(v___x_6160_, 0);
v_isSharedCheck_6168_ = !lean_is_exclusive(v___x_6160_);
if (v_isSharedCheck_6168_ == 0)
{
v___x_6163_ = v___x_6160_;
v_isShared_6164_ = v_isSharedCheck_6168_;
goto v_resetjp_6162_;
}
else
{
lean_inc(v_a_6161_);
lean_dec(v___x_6160_);
v___x_6163_ = lean_box(0);
v_isShared_6164_ = v_isSharedCheck_6168_;
goto v_resetjp_6162_;
}
v_resetjp_6162_:
{
lean_object* v___x_6166_; 
if (v_isShared_6164_ == 0)
{
v___x_6166_ = v___x_6163_;
goto v_reusejp_6165_;
}
else
{
lean_object* v_reuseFailAlloc_6167_; 
v_reuseFailAlloc_6167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6167_, 0, v_a_6161_);
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
lean_dec(v_a_6156_);
lean_dec_ref(v___x_6142_);
lean_dec_ref(v_name_6106_);
lean_dec(v_pre_6118_);
v_a_6149_ = v___x_6124_;
goto v___jp_6148_;
}
}
else
{
lean_object* v_a_6169_; lean_object* v___x_6171_; uint8_t v_isShared_6172_; uint8_t v_isSharedCheck_6176_; 
lean_dec(v___x_6147_);
lean_dec_ref(v___x_6142_);
lean_del_object(v___x_6129_);
lean_dec(v_pre_6118_);
lean_dec_ref(v_name_6106_);
v_a_6169_ = lean_ctor_get(v___x_6155_, 0);
v_isSharedCheck_6176_ = !lean_is_exclusive(v___x_6155_);
if (v_isSharedCheck_6176_ == 0)
{
v___x_6171_ = v___x_6155_;
v_isShared_6172_ = v_isSharedCheck_6176_;
goto v_resetjp_6170_;
}
else
{
lean_inc(v_a_6169_);
lean_dec(v___x_6155_);
v___x_6171_ = lean_box(0);
v_isShared_6172_ = v_isSharedCheck_6176_;
goto v_resetjp_6170_;
}
v_resetjp_6170_:
{
lean_object* v___x_6174_; 
if (v_isShared_6172_ == 0)
{
v___x_6174_ = v___x_6171_;
goto v_reusejp_6173_;
}
else
{
lean_object* v_reuseFailAlloc_6175_; 
v_reuseFailAlloc_6175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6175_, 0, v_a_6169_);
v___x_6174_ = v_reuseFailAlloc_6175_;
goto v_reusejp_6173_;
}
v_reusejp_6173_:
{
return v___x_6174_;
}
}
}
v___jp_6148_:
{
lean_object* v___x_6150_; lean_object* v___x_6151_; lean_object* v___x_6153_; 
v___x_6150_ = lean_st_ref_get(v___x_6147_);
lean_dec(v___x_6147_);
lean_dec(v___x_6150_);
v___x_6151_ = lean_box(v_a_6149_);
if (v_isShared_6130_ == 0)
{
lean_ctor_set_tag(v___x_6129_, 0);
lean_ctor_set(v___x_6129_, 0, v___x_6151_);
v___x_6153_ = v___x_6129_;
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
lean_dec(v_val_6126_);
lean_dec(v_pre_6118_);
lean_dec_ref(v_name_6106_);
lean_dec(v___x_6105_);
goto v___jp_6110_;
}
}
else
{
lean_dec(v___x_6125_);
lean_dec(v_pre_6118_);
lean_dec_ref(v_name_6106_);
lean_dec(v___x_6105_);
goto v___jp_6110_;
}
}
}
else
{
lean_dec(v_name_6106_);
lean_dec(v___x_6105_);
goto v___jp_6114_;
}
v___jp_6110_:
{
uint8_t v___x_6111_; lean_object* v___x_6112_; lean_object* v___x_6113_; 
v___x_6111_ = 0;
v___x_6112_ = lean_box(v___x_6111_);
v___x_6113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6113_, 0, v___x_6112_);
return v___x_6113_;
}
v___jp_6114_:
{
uint8_t v___x_6115_; lean_object* v___x_6116_; lean_object* v___x_6117_; 
v___x_6115_ = 0;
v___x_6116_ = lean_box(v___x_6115_);
v___x_6117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6117_, 0, v___x_6116_);
return v___x_6117_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object* v___x_6178_, lean_object* v_name_6179_, lean_object* v___y_6180_, lean_object* v___y_6181_, lean_object* v___y_6182_){
_start:
{
lean_object* v_res_6183_; 
v_res_6183_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(v___x_6178_, v_name_6179_, v___y_6180_, v___y_6181_);
lean_dec(v___y_6181_);
lean_dec_ref(v___y_6180_);
return v_res_6183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_6187_; lean_object* v___x_6188_; 
v___f_6187_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_));
v___x_6188_ = l_Lean_registerReservedNameAction(v___f_6187_);
return v___x_6188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object* v_a_6189_){
_start:
{
lean_object* v_res_6190_; 
v_res_6190_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_();
return v_res_6190_;
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
res = l_Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_();
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
